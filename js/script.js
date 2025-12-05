let allCodeSets = [];
let currentCodeIndex = 0;

function extractAlphabet(words) {
  const alphabet = new Set();
  words.forEach(w => w.split('').forEach(ch => alphabet.add(ch)));
  return [...alphabet].sort();
}

function findConcatenations(words) {
  const results = [];
  const wordsArr = [...words];

  for (const t of wordsArr) {
    const others = new Set(wordsArr);
    others.delete(t);
    if (others.size === 0) continue;

    const n = t.length;
    const dp = new Array(n + 1).fill(false);
    const prev = new Array(n + 1).fill(-1);
    const prevWord = new Array(n + 1).fill(null);
    dp[0] = true;

    for (let i = 0; i < n; i++) {
      if (!dp[i]) continue;
      for (const w of others) {
        const L = w.length;
        if (i + L <= n && t.substr(i, L) === w) {
          dp[i + L] = true;
          prev[i + L] = i;
          prevWord[i + L] = w;
        }
      }
    }

    if (dp[n]) {
      const parts = [];
      let idx = n;
      while (idx > 0) {
        parts.push(prevWord[idx]);
        idx = prev[idx];
      }
      parts.reverse();
      if (parts.length >= 2) results.push({ word: t, decomposition: parts });
    }
  }

  return results;
}

function buildGraph(words) {
  if (!words.length) return null;

  const nodes = new Map();
  const edges = new Map();
  let nextId = 1;

  const ensureNode = (label) => {
    if (!nodes.has(label)) {
      nodes.set(label, nextId++);
      edges.set(nodes.get(label), new Set());
    }
    return nodes.get(label);
  };

  words.forEach(word => {
    for (let i = 1; i < word.length; i++) {
      const left = word.slice(0, i);
      const right = word.slice(i);
      const leftId = ensureNode(left);
      const rightId = ensureNode(right);
      edges.get(leftId).add(rightId);
    }
  });

  const nodeList = [...nodes.entries()].map(([label, id]) => ({ id, label }));
  return { nodeList, edges, nodes };
}

function findCycleEdges(adj) {
  let id = 0;
  const ids = new Map();       
  const low = new Map();
  const onStack = new Set();
  const stack = [];            
  const nodeToScc = new Map();
  let sccCount = 0;

  const dfs = (at) => {
    stack.push(at);
    onStack.add(at);
    ids.set(at, id);
    low.set(at, id);
    id++;

    const neighbors = adj.get(at) || [];
    for (const to of neighbors) {
      if (!ids.has(to)) {
        dfs(to);
        low.set(at, Math.min(low.get(at), low.get(to)));
      } else if (onStack.has(to)) {
        low.set(at, Math.min(low.get(at), ids.get(to)));
      }
    }

    if (ids.get(at) === low.get(at)) {
      while (stack.length > 0) {
        const node = stack.pop();
        onStack.delete(node);
        nodeToScc.set(node, sccCount);
        if (node === at) break;
      }
      sccCount++;
    }
  };

  for (const key of adj.keys()) {
    if (!ids.has(key)) dfs(key);
  }

  const sccSizes = new Map();
  for (const sccId of nodeToScc.values()) {
    sccSizes.set(sccId, (sccSizes.get(sccId) || 0) + 1);
  }

  const cycleEdges = [];
  
  for (const [u, targets] of adj) {
    const uScc = nodeToScc.get(u);
    
    if (uScc === undefined) continue;

    for (const v of targets) {
      const vScc = nodeToScc.get(v);
      
      if (uScc === vScc) {
        if (sccSizes.get(uScc) > 1 || u === v) {
          cycleEdges.push({ source: u, target: v });
        }
      }
    }
  }

  return cycleEdges;
}

function findLongestPaths(adj, nodeList) {
  const indegree = new Map([...adj.keys()].map(k => [k, 0]));
  adj.forEach((targets) => targets.forEach(v =>
    indegree.set(v, (indegree.get(v) || 0) + 1)
  ));

  const queue = [...indegree.entries()].filter(([_, d]) => d === 0).map(([k]) => k);
  const topo = [];

  while (queue.length) {
    const u = queue.shift();
    topo.push(u);
    adj.get(u).forEach(v => {
      indegree.set(v, indegree.get(v) - 1);
      if (indegree.get(v) === 0) queue.push(v);
    });
  }

  if (topo.length !== adj.size) throw new Error("Graph contains a cycle");

  const dist = new Map();
  const preds = new Map();
  adj.forEach((_, k) => {
    dist.set(k, 0);
    preds.set(k, []);
  });

  topo.forEach(u => {
    adj.get(u).forEach(v => {
      const cand = dist.get(u) + 1;
      if (cand > dist.get(v)) {
        dist.set(v, cand);
        preds.set(v, [u]);
      } else if (cand === dist.get(v)) {
        preds.get(v).push(u);
      }
    });
  });

  const maxDist = Math.max(...dist.values());
  const endNodes = [...dist.entries()].filter(([_, d]) => d === maxDist).map(([k]) => k);

  const idToLabel = new Map(nodeList.map(n => [n.id, n.label]));
  const paths = [];

  const backtrack = (node, stack) => {
    stack.push(node);
    if (dist.get(node) === 0) {
      paths.push([...stack].reverse().map(id => idToLabel.get(id)));
    } else {
      preds.get(node).forEach(p => backtrack(p, stack));
    }
    stack.pop();
  };

  endNodes.forEach(n => backtrack(n, []));
  return { maxDist, paths: paths.slice(0, 200) };
}

let cy = null;
function renderGraph(graph, cycleEdges = []) {
  const container = document.getElementById('graph');
  const loadingOverlay = document.getElementById('loadingOverlay'); 
  
  const elements = [];

  if (cy) cy.destroy();
  
  document.getElementById('searchInput').value = '';

  if (!graph) {
    if (loadingOverlay) loadingOverlay.style.display = 'none';
    return;
  }

  if (loadingOverlay) loadingOverlay.style.display = 'flex';

  let minLength = 1, maxLength = 1;
  if (graph.nodeList.length > 0) {
    const lengths = graph.nodeList.map(n => n.label.length);
    minLength = Math.min(...lengths);
    maxLength = Math.max(...lengths);
  }

  const minLightness = 40; 
  const maxLightness = 85;

  graph.nodeList.forEach(n => {
    elements.push({
      group: 'nodes',
      data: { id: n.id.toString(), label: n.label }
    });
  });

  graph.edges.forEach((targets, u) => {
    targets.forEach(v => {
      elements.push({
        group: 'edges',
        data: { source: u.toString(), target: v.toString() }
      });
    });
  });

  cy = cytoscape({
    container,
    elements,
    layout: { 
      name: 'cose', 
      animate: true, 
      padding: 10,
      stop: () => {
        if (loadingOverlay) loadingOverlay.style.display = 'none';
      }
    },
    style: [
      {
        selector: 'node',
        style: {
          'content': 'data(label)',
          'shape': 'round-rectangle',
          
          'background-color': (ele) => {
            const length = ele.data('label').length;
            
            if (minLength === maxLength) {
              return `hsl(130, 60%, ${minLightness}%)`; 
            }
            const percentage = (length - minLength) / (maxLength - minLength);
            
            const lightness = minLightness + (percentage * (maxLightness - minLightness));
            
            return `hsl(130, 60%, ${lightness}%)`;
          },
          
          'border-width': 1.5,

          'border-color': (ele) => {
            const length = ele.data('label').length;
            
            if (minLength === maxLength) {
              return `hsl(130, 60%, ${minLightness - 10}%)`; 
            }
            
            const percentage = (length - minLength) / (maxLength - minLength);
            const lightness = minLightness + (percentage * (maxLightness - minLightness));
            
            return `hsl(130, 60%, ${lightness - 10}%)`;
          },

          'padding': '12px',
          'text-valign': 'center',
          'font-size': '14px',
          'width': 'label',
          'transition-property': 'background-color, border-color',
          'transition-duration': '0.3s',
          'z-index': 1 
        }
      },

      {
        selector: 'node.searched',
        style: {
          'background-color': '#cfe2ff',
          'border-color': '#0d6efd',
          'border-width': '2.5px',
          'z-index': 999 
        }
      },
      {
        selector: 'edge',
        style: {
          'width': 2,
          'line-color': '#000000',
          'target-arrow-color': '#000000',
          'target-arrow-shape': 'triangle',
          'curve-style': 'bezier',
          'arrow-scale': 1.1,
          'z-index': 0 
        }
      },
      {
        selector: 'edge.in-cycle',
        style: {
          'line-color': '#dc3545',
          'target-arrow-color': '#dc3545',
          'width': 4, 
          'z-index': 10
        }
      }
    ]
  });

  cy.on('layoutstart', () => {
    if (loadingOverlay) loadingOverlay.style.display = 'flex';
  });
  cy.on('layoutstop', () => {
    if (loadingOverlay) loadingOverlay.style.display = 'none';
  });

  cycleEdges.forEach(({source, target}) => {
    cy.edges(`[source = "${source}"][target = "${target}"]`).addClass('in-cycle');
  });
}

document.getElementById('file').addEventListener('change', e => {
  const file = e.target.files[0];
  if (!file) return;
  const reader = new FileReader();
  reader.onload = () => (document.getElementById('words').value = reader.result);
  reader.readAsText(file);
});

const sidebar = document.getElementById('sidebar');
const sidebarToggle = document.getElementById('sidebarToggle');
const resultsBar = document.getElementById('resultsBar');
const resultsToggle = document.getElementById('resultsToggle');
const overlay = document.getElementById('overlayMask');
const processBtn = document.getElementById('processBtn');

sidebarToggle.addEventListener('click', () => {
  sidebar.classList.toggle('hidden');
  overlay.classList.toggle('active', !sidebar.classList.contains('hidden'));
  sidebarToggle.textContent = sidebar.classList.contains('hidden') ? '>' : '<';
});

resultsToggle.addEventListener('click', () => {
  resultsBar.classList.toggle('visible');
  overlay.classList.toggle('active', resultsBar.classList.contains('visible'));
  resultsToggle.textContent = resultsBar.classList.contains('visible') ? 'v' : '^';
  resultsToggle.classList.remove('jumping');
});

overlay.addEventListener('click', () => {
  sidebar.classList.add('hidden');
  resultsBar.classList.remove('visible');
  overlay.classList.remove('active');
  sidebarToggle.textContent = '>';
  resultsToggle.textContent = '^';
});

document.getElementById('fitBtn').addEventListener('click', () => cy?.fit());
document.getElementById('zoomInBtn').addEventListener('click', () => { if (cy) cy.zoom({ level: cy.zoom() * 1.2, renderedPosition: { x: cy.width() / 2, y: cy.height() / 2 } });});
document.getElementById('zoomOutBtn').addEventListener('click', () => { if (cy) cy.zoom({ level: cy.zoom() * 0.8, renderedPosition: { x: cy.width() / 2, y: cy.height() / 2 } }); });

let isFullscreen = false;
document.getElementById('fullscreenBtn').addEventListener('click', async () => {
  try {
    if (!isFullscreen) {
      if (document.documentElement.requestFullscreen) {
        await document.documentElement.requestFullscreen();
      } else if (document.documentElement.webkitRequestFullscreen) {
        await document.documentElement.webkitRequestFullscreen();
      } else if (document.documentElement.mozRequestFullScreen) {
        await document.documentElement.mozRequestFullScreen();
      } else if (document.documentElement.msRequestFullscreen) {
        await document.documentElement.msRequestFullscreen();
      }
      isFullscreen = true;
      enterFullscreenUI();
    } else {
      if (document.exitFullscreen) {
        await document.exitFullscreen();
      } else if (document.webkitExitFullscreen) {
        await document.webkitExitFullscreen();
      } else if (document.mozCancelFullScreen) {
        await document.mozCancelFullScreen();
      } else if (document.msExitFullscreen) {
        await document.msExitFullscreen();
      }
      isFullscreen = false;
      exitFullscreenUI();
    }
  } catch (error) {
    console.error('Error toggling fullscreen:', error);
  }
});

document.addEventListener('fullscreenchange', handleFullscreenChange);
document.addEventListener('webkitfullscreenchange', handleFullscreenChange);
document.addEventListener('mozfullscreenchange', handleFullscreenChange);
document.addEventListener('MSFullscreenChange', handleFullscreenChange);

function handleFullscreenChange() {
  const fullscreenElement = document.fullscreenElement ||
                           document.webkitFullscreenElement ||
                           document.mozFullScreenElement ||
                           document.msFullscreenElement;

  isFullscreen = !!fullscreenElement;

  if (isFullscreen) {
    enterFullscreenUI();
  } else {
    exitFullscreenUI();
  }
}

function enterFullscreenUI() {
  const fullscreenBtn = document.getElementById('fullscreenBtn');
  fullscreenBtn.title = 'Exit Fullscreen';

  const elementsToHide = [
    'openSidebarBtn',
    'sidebar',
    'sidebarToggle',
    'resultsBar',
    'resultsToggle',
    'downloadBtn',
    'fitBtn',
    'searchControls'
  ];

  elementsToHide.forEach(id => {
    const element = document.getElementById(id);
    if (element) {
      element.style.display = 'none';
    }
  });

  overlay.classList.remove('active');
}

function exitFullscreenUI() {
  const fullscreenBtn = document.getElementById('fullscreenBtn');
  fullscreenBtn.title = 'Enter Fullscreen';

  const elementsToShow = [
    'openSidebarBtn',
    'sidebar',
    'sidebarToggle',
    'resultsBar',
    'resultsToggle',
    'downloadBtn',
    'fitBtn',
    'searchControls'
  ];

  elementsToShow.forEach(id => {
    const element = document.getElementById(id);
    if (element) {
      element.style.display = '';
    }
  });
}

document.getElementById('prevBtn').addEventListener('click', () => {
    if (currentCodeIndex > 0) {
        displayCodeSet(currentCodeIndex - 1);
    }
});

document.getElementById('nextBtn').addEventListener('click', () => {
    if (currentCodeIndex < allCodeSets.length - 1) {
        displayCodeSet(currentCodeIndex + 1);
    }
});

const searchInput = document.getElementById('searchInput');
const searchBtn = document.getElementById('searchBtn');

function performSearch() {
  if (!cy) return;
  const searchTerm = searchInput.value.trim();
  
  cy.nodes('.searched').removeClass('searched');

  if (searchTerm === '') return;
  
  const targetNode = cy.nodes(`[label = "${searchTerm}"]`);

  if (targetNode.length > 0) {
    targetNode.addClass('searched');
    cy.animate({
      center: { eles: targetNode },
      zoom: 2
    }, {
      duration: 500
    });
  } else {
    alert('Vertex not found!');
  }
}

searchBtn.addEventListener('click', performSearch);
searchInput.addEventListener('keypress', (e) => {
  if (e.key === 'Enter') {
    performSearch();
  }
});


processBtn.addEventListener('click', () => {
  const input = document.getElementById('words').value;
  const ignoreCase = document.getElementById('ignoreCase').checked;

  const lines = input.split(/\r?\n/).filter(line => line.trim() !== '');
  
  allCodeSets = lines.map(line => {
    const allWords = line.trim().split(/[,\s]+/).filter(Boolean);
    const processedWords = allWords.map(word => ignoreCase ? word.toUpperCase() : word);

    const counts = {};
    processedWords.forEach(word => { counts[word] = (counts[word] || 0) + 1; });

    const uniqueWords = Object.keys(counts);
    const duplicates = Object.entries(counts)
      .filter(([_, count]) => count > 1)
      .map(([word, count]) => `${word} (x${count})`);

    return { words: uniqueWords, duplicates: duplicates };
  });

  const verdictBox = document.getElementById('verdictBox');
  const resultTitle = document.getElementById('resultTitle');
  const resultDesc = document.getElementById('resultDesc');

  if (allCodeSets.length === 0 || allCodeSets.every(set => set.words.length === 0)) {
    verdictBox.className = "error";
    resultTitle.textContent = "Error";
    resultDesc.textContent = "Please provide at least one word.";
    if (cy) { cy.destroy(); cy = null; }
    updateNavUI();
    return;
  }

  currentCodeIndex = 0;
  displayCodeSet(currentCodeIndex);

  sidebar.classList.add('hidden');
  overlay.classList.remove('active');
  sidebarToggle.textContent = '>';
  resultsToggle.classList.add('jumping');
});

document.addEventListener("keydown", function (e) {
  if ((e.ctrlKey || e.metaKey) && e.key === "Enter") {
    processBtn.click();
  }
});

function updateNavUI() {
  const navControls = document.getElementById('graphNavControls');
  const navStatus = document.getElementById('navStatus');
  const prevBtn = document.getElementById('prevBtn');
  const nextBtn = document.getElementById('nextBtn');

  if (allCodeSets.length > 1) {
    navControls.style.display = 'flex';
    navStatus.textContent = `Code ${currentCodeIndex + 1} of ${allCodeSets.length}`;
    prevBtn.disabled = currentCodeIndex === 0;
    nextBtn.disabled = currentCodeIndex === allCodeSets.length - 1;
  } else {
    navControls.style.display = 'none';
  }
}

function displayCodeSet(index) {
  if (index < 0 || index >= allCodeSets.length) return;

  currentCodeIndex = index;
  const { words, duplicates } = allCodeSets[index];
  
  const meta = document.getElementById('meta');
  const verdictBox = document.getElementById('verdictBox');
  const resultTitle = document.getElementById('resultTitle');
  const resultDesc = document.getElementById('resultDesc');
  const pathsDiv = document.getElementById('paths');
  const longestLen = document.getElementById('longestLen');
  const longestSection = document.getElementById('longestSection');
  const graphInfoSection = document.getElementById('graphInfoSection');
  const vertexList = document.getElementById('vertexList');
  const duplicatesWarning = document.getElementById('duplicatesWarning');

  resultTitle.textContent = '';
  resultDesc.textContent = '';
  pathsDiv.textContent = '';
  longestLen.textContent = '';
  verdictBox.className = '';
  meta.innerHTML = '';
  longestSection.style.display = 'none';
  graphInfoSection.style.display = 'none';
  vertexList.innerHTML = '';
  duplicatesWarning.style.display = 'none';

  if (duplicates.length > 0) {
    duplicatesWarning.innerHTML = `<strong>Warning:</strong> Duplicate words were found and ignored: ${duplicates.join(', ')}`;
    duplicatesWarning.style.display = 'block';
  }

  if (!words.length) {
    verdictBox.className = "error";
    resultTitle.textContent = "Error";
    resultDesc.textContent = "This code set is empty after removing duplicates.";
    renderGraph(null);
    updateNavUI();
    return;
  }

  const lengths = words.map(w => w.length);
  const minLen = Math.min(...lengths);
  const maxLen = Math.max(...lengths);

  if (minLen < 2) {
    verdictBox.className = "error";
    resultTitle.textContent = "Error";
    resultDesc.textContent = "All words must have length ≥ 2";
    renderGraph(null);
    updateNavUI();
    return;
  }

  const alphabet = extractAlphabet(words);

  meta.innerHTML = `
    <div><strong>Words:</strong> ${words.length}</div>
    <div><strong>Lengths:</strong> ${minLen === maxLen ? minLen : `${minLen}–${maxLen}`}</div>
    <div><strong>Alphabet:</strong> {${alphabet.join(', ')}}</div>
  `;

  const concatIssues = findConcatenations(words);
  if (concatIssues.length) {
    verdictBox.className = "error";
    resultTitle.textContent = "Not a code";
    resultDesc.textContent = "Some words can be formed by concatenating others.";
    pathsDiv.innerHTML = concatIssues
      .map(i => `<div><strong>${i.word}</strong> = ${i.decomposition.join(' + ')}</div>`)
      .join('');
    longestSection.style.display = 'block';
    renderGraph(null);
    updateNavUI();
    return;
  }

  try {
    const graph = buildGraph(words);
    const cycleEdges = findCycleEdges(graph.edges);
    
    renderGraph(graph, cycleEdges);
    
    if (graph) {
      const edgeCount = [...graph.edges.values()].reduce((sum, set) => sum + set.size, 0);
      meta.innerHTML += `
        <div><strong>Vertices:</strong> ${graph.nodeList.length}</div>
        <div><strong>Edges:</strong> ${edgeCount}</div>
      `;
    }

    if (graph && graph.nodeList.length > 0) {
      const vertices = graph.nodeList.map(node => node.label).sort();
      vertexList.innerHTML = `<div>${vertices.join('</div><div>')}</div>`;
      graphInfoSection.style.display = 'block';
    }

    if (cycleEdges.length > 0) {
      verdictBox.className = "error";
      resultTitle.textContent = "Non-Circular Code";
      resultDesc.textContent = "A cycle was detected. Edges in the cycle are highlighted in red.";
      longestSection.style.display = 'none';
    } else {
      verdictBox.className = "ok";
      resultTitle.textContent = "Circular Code";
      resultDesc.textContent = "No cycles detected - graph is acyclic.";

      const { maxDist, paths } = findLongestPaths(graph.edges, graph.nodeList);
      longestLen.textContent = `Longest path length: ${maxDist}`;
      if (maxDist === 1) longestLen.textContent += " - strong comma-free";
      else if (maxDist === 2) longestLen.textContent += " - comma-free";

      pathsDiv.innerHTML = paths.length
        ? paths.map(p => `<div>${p.join(' -> ')}</div>`).join('')
        : "(no paths)";

      longestSection.style.display = 'block';
    }
  } catch (err) {
    console.error(err);
    verdictBox.className = "error";
    resultTitle.textContent = "Error";
    resultDesc.textContent = err.message;
    longestSection.style.display = 'none';
  }

  updateNavUI();
}

const downloadBtn = document.getElementById('downloadBtn');
const downloadModal = document.getElementById('downloadModal');
const closeDownloadModal = document.getElementById('closeDownloadModal');

downloadBtn.addEventListener('click', () => {
  downloadModal.style.display = 'flex';
});

closeDownloadModal.addEventListener('click', () => {
  downloadModal.style.display = 'none';
});

downloadModal.addEventListener('click', (e) => {
  if (e.target === downloadModal) {
    downloadModal.style.display = 'none';
  }
});

const downloadOptions = document.querySelectorAll('.download-option');

downloadOptions.forEach(btn => {
  btn.addEventListener('click', () => {
    const type = btn.dataset.type;
    if (!cy) {
      alert('Graph is not rendered yet!');
      return;
    }

    if (type === 'png') {
      const pngData = cy.png({ full: true, scale: 2 });
      const a = document.createElement('a');
      a.href = pngData;
      a.download = 'graph.png';
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
    } 
    else if (type === 'json') {
      const jsonData = cy.json();
      const blob = new Blob([JSON.stringify(jsonData, null, 2)], { type: 'application/json' });
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'graph.json';
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
    } 
    downloadModal.style.display = 'none';
  });
});
