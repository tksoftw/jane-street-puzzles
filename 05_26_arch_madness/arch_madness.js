// Arc Madness Simulator — geometry/scoring engine plus UI, in one file.


// The starting puzzle, loaded only on initial page load. This is the exact text
// format produced by "Save to File": one row per line, cells separated by ";",
// each cell a state — "." (empty), "G" (green), or an arc "TL"/"TR"/"BR"/"BL" —
// optionally followed by "/<clue>", e.g. "G/81" or "./21".
const DEFAULT_BOARD = `\
G;.;./21;G;.;G;.;G;.
./21;.;.;G;./27;.;G;./25;G
G;./27;.;.;.;./15;.;G;./9
.;.;.;.;.;.;.;.;G
G/25;.;.;./27;G;./45;.;.;./9
.;.;.;.;.;.;.;G;G
./9;.;.;./63;.;.;.;./45;.
G;./63;.;.;./9;.;.;.;./288
.;G;.;.;G;.;G/35;.;G`;

const TUTORIAL_BOARD = `\
./3;G;./9;G
.;.;.;./6
./8;G;.;G
.;./6;.;./24`;


// ===========================================================================
// Core analysis engine
// ===========================================================================
const Core = (function () {
  "use strict";

  const ARC_TYPES = ["tl", "tr", "br", "bl"];
  const SIDES = ["N", "E", "S", "W"];
  const OPPOSITE = { N: "S", E: "W", S: "N", W: "E" };
  const DELTAS = {
    N: [-1, 0],
    E: [0, 1],
    S: [1, 0],
    W: [0, -1],
  };

  const DISK_SIDES = {
    tl: new Set(["N", "W"]),
    tr: new Set(["N", "E"]),
    br: new Set(["S", "E"]),
    bl: new Set(["S", "W"]),
  };

  const LINE_GEOMETRY = {
    N: {
      tangent: "h",
      endpoints: function (x, y) {
        return [
          [x, y],
          [x + 1, y],
        ];
      },
    },
    E: {
      tangent: "v",
      endpoints: function (x, y) {
        return [
          [x + 1, y],
          [x + 1, y + 1],
        ];
      },
    },
    S: {
      tangent: "h",
      endpoints: function (x, y) {
        return [
          [x, y + 1],
          [x + 1, y + 1],
        ];
      },
    },
    W: {
      tangent: "v",
      endpoints: function (x, y) {
        return [
          [x, y],
          [x, y + 1],
        ];
      },
    },
  };

  const ARC_GEOMETRY = {
    tl: {
      endpoints: function (x, y) {
        return [
          { point: [x + 1, y], tangent: "v", vector: [0, 1] },
          { point: [x, y + 1], tangent: "h", vector: [1, 0] },
        ];
      },
    },
    tr: {
      endpoints: function (x, y) {
        return [
          { point: [x + 1, y + 1], tangent: "h", vector: [-1, 0] },
          { point: [x, y], tangent: "v", vector: [0, 1] },
        ];
      },
    },
    br: {
      endpoints: function (x, y) {
        return [
          { point: [x, y + 1], tangent: "v", vector: [0, -1] },
          { point: [x + 1, y], tangent: "h", vector: [-1, 0] },
        ];
      },
    },
    bl: {
      endpoints: function (x, y) {
        return [
          { point: [x, y], tangent: "h", vector: [1, 0] },
          { point: [x + 1, y + 1], tangent: "v", vector: [0, -1] },
        ];
      },
    },
  };

  class DSU {
    constructor() {
      this.parent = [];
      this.rank = [];
    }

    make() {
      const id = this.parent.length;
      this.parent.push(id);
      this.rank.push(0);
      return id;
    }

    find(x) {
      let p = this.parent[x];
      if (p !== x) {
        p = this.find(p);
        this.parent[x] = p;
      }
      return p;
    }

    union(a, b) {
      let ra = this.find(a);
      let rb = this.find(b);
      if (ra === rb) return ra;
      if (this.rank[ra] < this.rank[rb]) {
        const tmp = ra;
        ra = rb;
        rb = tmp;
      }
      this.parent[rb] = ra;
      if (this.rank[ra] === this.rank[rb]) this.rank[ra] += 1;
      return ra;
    }
  }

  function normalizeSize(size) {
    const n = Number(size);
    if (!Number.isFinite(n)) return 5;
    return Math.max(1, Math.min(30, Math.floor(n)));
  }

  function normalizeNumber(value) {
    if (value === null || value === undefined || value === "") return null;
    const number = Number(value);
    return Number.isInteger(number) ? number : null;
  }

  function normalizeArc(arc) {
    return ARC_TYPES.includes(arc) ? arc : null;
  }

  function normalizeCell(cell) {
    const source = cell || {};
    return {
      green: Boolean(source.green),
      number: normalizeNumber(source.number),
      arc: normalizeArc(source.arc),
    };
  }

  function buildCellMatrix(size, inputCells) {
    const cells = [];
    for (let r = 0; r < size; r += 1) {
      const row = [];
      for (let c = 0; c < size; c += 1) {
        row.push(normalizeCell(inputCells && inputCells[r] && inputCells[r][c]));
      }
      cells.push(row);
    }
    return cells;
  }

  function pieceTouchesSide(piece, side) {
    if (!piece) return false;
    if (piece.kind === "full") return true;
    if (piece.kind === "disk") return DISK_SIDES[piece.arc].has(side);
    return !DISK_SIDES[piece.arc].has(side);
  }

  function pieceForSide(record, side) {
    if (!record || record.blocked) return null;
    if (!record.arc) return record.pieces.full;
    return pieceTouchesSide(record.pieces.disk, side)
      ? record.pieces.disk
      : record.pieces.remainder;
  }

  function pointKey(point) {
    return point[0] + "," + point[1];
  }

  function vectorsAreOpposite(a, b) {
    return a[0] + b[0] === 0 && a[1] + b[1] === 0;
  }

  function endpointsShareSmoothTangent(a, b) {
    if (a.tangent !== b.tangent) return false;
    return vectorsAreOpposite(a.vector, b.vector);
  }

  function sortedEndpointKey(a, b) {
    const ak = pointKey(a);
    const bk = pointKey(b);
    return ak < bk ? ak + "|" + bk : bk + "|" + ak;
  }

  function expressionFor(intPart, piQuarterCoeff) {
    const terms = [];
    if (intPart !== 0 || piQuarterCoeff === 0) {
      terms.push(String(intPart));
    }
    if (piQuarterCoeff !== 0) {
      const sign = piQuarterCoeff < 0 ? "-" : "+";
      const absCoeff = Math.abs(piQuarterCoeff);
      let piTerm;
      if (absCoeff === 1) piTerm = "pi/4";
      else if (absCoeff === 2) piTerm = "pi/2";
      else if (absCoeff === 3) piTerm = "3pi/4";
      else if (absCoeff % 4 === 0) {
        const whole = absCoeff / 4;
        piTerm = whole === 1 ? "pi" : whole + "pi";
      } else {
        piTerm = absCoeff + "pi/4";
      }

      if (terms.length === 0) {
        terms.push(sign === "-" ? "-" + piTerm : piTerm);
      } else {
        terms.push(sign + " " + piTerm);
      }
    }
    return terms.join(" ");
  }

  function multiplyExpression(multiplier, intPart, piQuarterCoeff) {
    if (multiplier === 0) return "0";
    return expressionFor(multiplier * intPart, multiplier * piQuarterCoeff);
  }

  function addLinePrimitive(primitivesByRegion, regionId, x, y, side) {
    const geometry = LINE_GEOMETRY[side];
    const endpoints = geometry.endpoints(x, y);
    primitivesByRegion[regionId].push({
      type: "line",
      geomKey: "line|" + sortedEndpointKey(endpoints[0], endpoints[1]),
      endpoints: [
        {
          point: endpoints[0],
          tangent: geometry.tangent,
          vector: [endpoints[1][0] - endpoints[0][0], endpoints[1][1] - endpoints[0][1]],
        },
        {
          point: endpoints[1],
          tangent: geometry.tangent,
          vector: [endpoints[0][0] - endpoints[1][0], endpoints[0][1] - endpoints[1][1]],
        },
      ],
    });
  }

  function addArcPrimitive(primitivesByRegion, regionId, x, y, arc) {
    primitivesByRegion[regionId].push({
      type: "arc",
      arc: arc,
      geomKey: "arc|" + x + "," + y + "|" + arc,
      endpoints: ARC_GEOMETRY[arc].endpoints(x, y).map(function (endpoint) {
        return {
          point: endpoint.point,
          tangent: endpoint.tangent,
          vector: endpoint.vector,
        };
      }),
    });
  }

  function buildGlobalJunctions(primitivesByRegion) {
    const junctions = new Map();
    primitivesByRegion.forEach(function (primitives) {
      primitives.forEach(function (primitive) {
        primitive.endpoints.forEach(function (endpoint) {
          const key = pointKey(endpoint.point);
          if (!junctions.has(key)) junctions.set(key, new Set());
          junctions.get(key).add(primitive.geomKey);
        });
      });
    });
    return junctions;
  }

  function countSmoothPieces(primitives, globalJunctions) {
    if (primitives.length === 0) return 0;
    const dsu = new DSU();
    for (let i = 0; i < primitives.length; i += 1) dsu.make();

    const buckets = new Map();
    primitives.forEach(function (primitive, index) {
      primitive.endpoints.forEach(function (endpoint) {
        const key = pointKey(endpoint.point);
        if (!buckets.has(key)) buckets.set(key, []);
        buckets.get(key).push({
          index: index,
          tangent: endpoint.tangent,
          type: primitive.type,
          geomKey: primitive.geomKey,
          point: endpoint.point,
          vector: endpoint.vector,
          center: endpoint.center,
        });
      });
    });

    buckets.forEach(function (endpoints, point) {
      const unique = [];
      const seen = new Set();
      endpoints.forEach(function (endpoint) {
        const key = endpoint.index + "|" + endpoint.tangent + "|" + endpoint.type + "|" + endpoint.geomKey;
        if (!seen.has(key)) {
          seen.add(key);
          unique.push(endpoint);
        }
      });

      const globalIncident = globalJunctions.get(point) || new Set();
      if (
        unique.length === 2 &&
        endpointsShareSmoothTangent(unique[0], unique[1]) &&
        (unique[0].type !== "line" || unique[1].type !== "line" || globalIncident.size === 2)
      ) {
        dsu.union(unique[0].index, unique[1].index);
      }
    });

    const roots = new Set();
    for (let i = 0; i < primitives.length; i += 1) roots.add(dsu.find(i));
    return roots.size;
  }

  function inBounds(size, r, c) {
    return r >= 0 && c >= 0 && r < size && c < size;
  }

  function createPiece(dsu, pieces, record, kind, areaInt, piQuarterCoeff) {
    const id = dsu.make();
    const piece = {
      id: id,
      row: record.row,
      col: record.col,
      kind: kind,
      arc: record.arc,
      areaInt: areaInt,
      piQuarterCoeff: piQuarterCoeff,
      region: null,
    };
    pieces.push(piece);
    return piece;
  }

  function analyzeGrid(options) {
    const size = normalizeSize(options && options.size);
    const greenMode = "open";
    const enforceClues = Boolean(options && options.enforceClues);
    const cells = buildCellMatrix(size, options && options.cells);
    const dsu = new DSU();
    const pieces = [];
    const records = [];
    const issues = [];

    for (let r = 0; r < size; r += 1) {
      const row = [];
      for (let c = 0; c < size; c += 1) {
        const cell = cells[r][c];
        const record = {
          row: r,
          col: c,
          green: cell.green,
          number: cell.number,
          arc: cell.arc,
          blocked: false,
          pieces: {},
          labelRegion: null,
        };

        if (cell.green && cell.arc) {
          issues.push({
            code: "arc-in-green",
            severity: "error",
            message:
              "Cell " + (r + 1) + "," + (c + 1) + " is green and cannot contain an arc.",
            row: r,
            col: c,
          });
          record.arc = null;
        }

        if (record.arc) {
          record.pieces.disk = createPiece(dsu, pieces, record, "disk", 0, 1);
          record.pieces.remainder = createPiece(dsu, pieces, record, "remainder", 1, -1);
        } else {
          record.pieces.full = createPiece(dsu, pieces, record, "full", 1, 0);
        }

        row.push(record);
      }
      records.push(row);
    }

    for (let r = 0; r < size; r += 1) {
      for (let c = 0; c < size; c += 1) {
        const record = records[r][c];
        if (record.blocked) continue;
        ["E", "S"].forEach(function (side) {
          const delta = DELTAS[side];
          const nr = r + delta[0];
          const nc = c + delta[1];
          if (!inBounds(size, nr, nc)) return;
          const neighbor = records[nr][nc];
          const a = pieceForSide(record, side);
          const b = pieceForSide(neighbor, OPPOSITE[side]);
          if (a && b) dsu.union(a.id, b.id);
        });
      }
    }

    const regionIndexByRoot = new Map();
    const regions = [];
    pieces.forEach(function (piece) {
      const root = dsu.find(piece.id);
      if (!regionIndexByRoot.has(root)) {
        regionIndexByRoot.set(root, regions.length);
        regions.push({
          id: regions.length,
          pieceIds: [],
          cells: [],
          areaInt: 0,
          piQuarterCoeff: 0,
          piQuarterArcs: 0,
          oneMinusPiQuarterArcs: 0,
          totalArcs: 0,
          exactArea: "",
          approximateArea: 0,
          integerArea: null,
          hasIntegerArea: false,
          smoothPieces: 0,
          score: null,
          scoreExpression: "",
          scoreApproximate: 0,
        });
      }
      const region = regions[regionIndexByRoot.get(root)];
      piece.region = region.id;
      region.pieceIds.push(piece.id);
      region.areaInt += piece.areaInt;
      region.piQuarterCoeff += piece.piQuarterCoeff;
      if (piece.kind === "disk") {
        region.piQuarterArcs += 1;
        region.totalArcs += 1;
      } else if (piece.kind === "remainder") {
        region.oneMinusPiQuarterArcs += 1;
        region.totalArcs += 1;
      }
      region.cells.push([piece.row, piece.col, piece.kind]);
    });

    for (let r = 0; r < size; r += 1) {
      for (let c = 0; c < size; c += 1) {
        const record = records[r][c];
        Object.keys(record.pieces).forEach(function (key) {
          const piece = record.pieces[key];
          piece.region = pieces[piece.id].region;
        });
        if (!record.blocked) {
          record.labelRegion = record.arc
            ? record.pieces.disk.region
            : record.pieces.full.region;
        }
      }
    }

    records.forEach(function (row) {
      row.forEach(function (record) {
        if (!record.arc || record.blocked) return;
        const diskRegion = record.pieces.disk.region;
        const remainderRegion = record.pieces.remainder.region;
        if (diskRegion === remainderRegion) {
          issues.push({
            code: "dangling-arc",
            severity: "error",
            message:
              "The arc in cell " +
              (record.row + 1) +
              "," +
              (record.col + 1) +
              " dangles because both sides reconnect.",
            row: record.row,
            col: record.col,
            region: diskRegion,
          });
        }
      });
    });

    const primitivesByRegion = regions.map(function () {
      return [];
    });

    for (let r = 0; r < size; r += 1) {
      for (let c = 0; c < size; c += 1) {
        const record = records[r][c];
        if (record.blocked) continue;
        SIDES.forEach(function (side) {
          const piece = pieceForSide(record, side);
          if (!piece) return;
          const regionId = piece.region;
          const delta = DELTAS[side];
          const nr = r + delta[0];
          const nc = c + delta[1];
          let neighborRegion = null;
          if (inBounds(size, nr, nc)) {
            const neighborPiece = pieceForSide(records[nr][nc], OPPOSITE[side]);
            neighborRegion = neighborPiece ? neighborPiece.region : null;
          }
          if (neighborRegion !== regionId) addLinePrimitive(primitivesByRegion, regionId, c, r, side);
        });

        if (record.arc) {
          const diskRegion = record.pieces.disk.region;
          const remainderRegion = record.pieces.remainder.region;
          if (diskRegion !== remainderRegion) {
            addArcPrimitive(primitivesByRegion, diskRegion, c, r, record.arc);
            addArcPrimitive(primitivesByRegion, remainderRegion, c, r, record.arc);
          }
        }
      }
    }

    const globalJunctions = buildGlobalJunctions(primitivesByRegion);

    regions.forEach(function (region, index) {
      region.exactArea = expressionFor(region.areaInt, region.piQuarterCoeff);
      region.approximateArea = region.areaInt + (region.piQuarterCoeff * Math.PI) / 4;
      region.hasIntegerArea = region.piQuarterCoeff === 0;
      region.integerArea = region.hasIntegerArea ? region.areaInt : null;
      region.smoothPieces = countSmoothPieces(primitivesByRegion[index], globalJunctions);
      region.score = region.hasIntegerArea ? region.smoothPieces * region.integerArea : null;
      region.scoreExpression = multiplyExpression(
        region.smoothPieces,
        region.areaInt,
        region.piQuarterCoeff
      );
      region.scoreApproximate = region.smoothPieces * region.approximateArea;

      if (!region.hasIntegerArea) {
        issues.push({
          code: "noninteger-area",
          severity: "error",
          message:
            "Region R" +
            (region.id + 1) +
            " has non-integer area " +
            region.exactArea +
            ".",
          region: region.id,
        });
      }
    });

    for (let r = 0; r < size; r += 1) {
      for (let c = 0; c < size; c += 1) {
        const record = records[r][c];
        if (!enforceClues) continue;
        if (record.number === null) continue;
        if (record.blocked || record.labelRegion === null) continue;
        const region = regions[record.labelRegion];
        if (region.score === null) {
          issues.push({
            code: "numbered-noninteger",
            severity: "error",
            message:
              "Cell " +
              (r + 1) +
              "," +
              (c + 1) +
              " is numbered, but R" +
              (region.id + 1) +
              " does not have an integer score yet.",
            row: r,
            col: c,
            region: region.id,
          });
        } else if (region.score !== record.number) {
          issues.push({
            code: "number-error",
            severity: "error",
            message:
              "Cell " +
              (r + 1) +
              "," +
              (c + 1) +
              " says " +
              record.number +
              ", but R" +
              (region.id + 1) +
              " scores " +
              region.score +
              ".",
            row: r,
            col: c,
            region: region.id,
          });
        }
      }
    }

    return {
      size: size,
      greenMode: greenMode,
      cells: records,
      regions: regions,
      issues: issues,
      valid: issues.filter(function (issue) {
        return issue.severity === "error";
      }).length === 0,
    };
  }

  function createEmptyCells(size) {
    const n = normalizeSize(size);
    const cells = [];
    for (let r = 0; r < n; r += 1) {
      const row = [];
      for (let c = 0; c < n; c += 1) {
        row.push({ green: false, number: null, arc: null });
      }
      cells.push(row);
    }
    return cells;
  }

  return {
    analyzeGrid: analyzeGrid,
    createEmptyCells: createEmptyCells,
  };
})();

// ===========================================================================
// UI layer
// ===========================================================================
(function () {
  "use strict";

  const SVG_NS = "http://www.w3.org/2000/svg";
  // Region colors live in CSS as --region-0..--region-(PALETTE_SIZE - 1); JS only
  // references them. Regions beyond the palette fall back to a generated hue.
  const PALETTE_SIZE = 12;

  // The states a cell can be set to from the Selected editor, in cycle order.
  const CELL_STATES = [
    { key: "empty", short: "Empty", title: "Empty", green: false, arc: null },
    { key: "tl", short: "TL", title: "Arc TL", green: false, arc: "tl" },
    { key: "tr", short: "TR", title: "Arc TR", green: false, arc: "tr" },
    { key: "br", short: "BR", title: "Arc BR", green: false, arc: "br" },
    { key: "bl", short: "BL", title: "Arc BL", green: false, arc: "bl" },
    { key: "green", short: "Green", title: "Green", green: true, arc: null },
  ];

  const isTutorial = localStorage.getItem("arcboard_mode") === "tutorial";
  const initialBoard = boardFromText(isTutorial ? TUTORIAL_BOARD : DEFAULT_BOARD);
  const state = {
    size: initialBoard.size,
    cells: initialBoard.cells,
    selected: { row: 0, col: 0 },
    showClues: true,
    showScores: false,
    showRegions: false,
    enforceClues: false,
    editClues: false,
    editGreen: false,
    wonShown: false,
    analysis: null,
  };

  const els = {
    svg: document.getElementById("gridSvg"),
    sizeInput: document.getElementById("sizeInput"),
    resizeButton: document.getElementById("resizeButton"),
    showClues: document.getElementById("showClues"),
    showScores: document.getElementById("showScores"),
    showRegions: document.getElementById("showRegions"),
    enforceClues: document.getElementById("enforceClues"),
    editClues: document.getElementById("editClues"),
    editGreen: document.getElementById("editGreen"),
    clueControl: document.getElementById("clueControl"),
    saveFile: document.getElementById("saveFile"),
    loadFile: document.getElementById("loadFile"),
    loadFileInput: document.getElementById("loadFileInput"),
    selectedCard: document.querySelector(".selected-card"),
    selectedName: document.getElementById("selectedName"),
    selectedRegion: document.getElementById("selectedRegion"),
    statePicker: document.getElementById("statePicker"),
    selectedClueInput: document.getElementById("selectedClueInput"),
    statusDot: document.getElementById("statusDot"),
    statusWord: document.getElementById("statusWord"),
    regionCount: document.getElementById("regionCount"),
    statusSummary: document.getElementById("statusSummary"),
    issueList: document.getElementById("issueList"),
    regionsPanel: document.getElementById("regionsPanel"),
    regionList: document.getElementById("regionList"),
    winModal: document.getElementById("winModal"),
    winCta: document.getElementById("winCta"),
    solution: document.getElementById("solution"),
    boardFrame: document.querySelector(".board-frame"),
    app: document.getElementById("app"),
    collapseLeft: document.getElementById("collapseLeft"),
    collapseRight: document.getElementById("collapseRight"),
  };

  function svgEl(tag, attrs, parent) {
    const node = document.createElementNS(SVG_NS, tag);
    Object.keys(attrs || {}).forEach(function (key) {
      node.setAttribute(key, attrs[key]);
    });
    if (parent) parent.appendChild(node);
    return node;
  }

  // A small SVG showing what a cell-state option looks like on the board.
  function cellPreviewSvg(opt) {
    const svg = document.createElementNS(SVG_NS, "svg");
    svg.setAttribute("viewBox", "0 0 1 1");
    svg.setAttribute("class", "cell-preview");
    setFill(
      svgEl("rect", { class: "preview-cell", x: 0, y: 0, width: 1, height: 1 }, svg),
      opt.green ? "var(--green-fill)" : "var(--cell-empty)"
    );
    if (opt.arc) {
      svgEl("path", { class: "preview-disk", d: diskPath(0, 0, opt.arc) }, svg);
      svgEl("path", { class: "preview-arc", d: arcPath(0, 0, opt.arc) }, svg);
    }
    return svg;
  }

  function buildStatePicker() {
    els.statePicker.innerHTML = "";
    CELL_STATES.forEach(function (opt) {
      // Green is only an option when green editing is enabled in Custom.
      if (opt.green && !state.editGreen) return;
      const btn = document.createElement("button");
      btn.type = "button";
      btn.className = "state-option";
      btn.title = opt.title;
      btn.setAttribute("data-key", opt.key);
      btn.appendChild(cellPreviewSvg(opt));
      const label = document.createElement("span");
      label.textContent = opt.short;
      btn.appendChild(label);
      btn.addEventListener("click", function () {
        selectCell(state.selected.row, state.selected.col);
        const cell = state.cells[state.selected.row][state.selected.col];
        // Green cells are locked while green editing is off.
        if (!state.editGreen && cell.green) return;
        cell.green = opt.green;
        cell.arc = opt.arc;
        render();
      });
      els.statePicker.appendChild(btn);
    });
  }

  // A cell token is "<state>" or "<state>/<clue>", where state is "." (empty),
  // "G" (green), or an arc "TL"/"TR"/"BR"/"BL". Examples: "G/81", "./21", "TL".
  function applyBoardToken(cell, token) {
    cell.green = false;
    cell.arc = null;
    cell.number = null;

    const text = String(token === undefined ? "" : token).trim();
    if (text === "") return;

    const slash = text.indexOf("/");
    const statePart = (slash === -1 ? text : text.slice(0, slash)).trim().toUpperCase();
    const cluePart = slash === -1 ? "" : text.slice(slash + 1).trim();

    if (statePart === "G") {
      cell.green = true;
    } else if (["TL", "TR", "BR", "BL"].includes(statePart)) {
      cell.arc = statePart.toLowerCase();
    }

    if (/^-?\d+$/.test(cluePart)) cell.number = Number(cluePart);
  }

  // Cells within a row are separated by ";".
  function tokensFromBoardRow(row) {
    if (Array.isArray(row)) return row;
    return String(row || "").split(";").map(function (token) {
      return token.trim();
    });
  }

  function createCellsFromBoard(board) {
    const rows = board && Array.isArray(board.rows) ? board.rows : [];
    const size = Math.max(1, Math.min(30, Math.floor(Number(board && board.size) || rows.length || 5)));
    const cells = Core.createEmptyCells(size);
    for (let r = 0; r < size; r += 1) {
      const row = rows[r] || "";
      const tokens = tokensFromBoardRow(row);
      for (let c = 0; c < size; c += 1) applyBoardToken(cells[r][c], tokens[c]);
    }
    return cells;
  }

  // Inverse of applyBoardToken: render a cell as a "<state>" or "<state>/<clue>"
  // token, matching the DEFAULT_BOARD text format.
  function cellToToken(cell) {
    let stateText = ".";
    if (cell.green) stateText = "G";
    else if (cell.arc) stateText = cell.arc.toUpperCase();
    if (cell.number !== null && cell.number !== undefined && cell.number !== "") {
      return stateText + "/" + cell.number;
    }
    return stateText;
  }

  // Serialize the current board to text: one row per line, cells joined by ";".
  function serializeBoard() {
    const lines = [];
    for (let r = 0; r < state.size; r += 1) {
      const tokens = [];
      for (let c = 0; c < state.size; c += 1) tokens.push(cellToToken(state.cells[r][c]));
      lines.push(tokens.join(";"));
    }
    return lines.join("\n") + "\n";
  }

  function saveToFile() {
    const blob = new Blob([serializeBoard()], { type: "text/plain" });
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = "board_" + Math.floor(Date.now() / 1000) + ".arcboard";
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    URL.revokeObjectURL(url);
  }

  // Parse the text board format (one row per line, cells joined by ";") into a
  // { size, cells } pair. The square size is inferred from rows and columns.
  function boardFromText(text) {
    const rows = String(text)
      .replace(/\r/g, "")
      .split("\n")
      .filter(function (line) {
        return line.trim() !== "";
      });

    let cols = 0;
    rows.forEach(function (line) {
      cols = Math.max(cols, tokensFromBoardRow(line).length);
    });
    const size = Math.max(1, Math.min(30, Math.max(rows.length, cols) || 5));

    return { size: size, cells: createCellsFromBoard({ size: size, rows: rows }) };
  }

  function loadFromText(text) {
    const board = boardFromText(text);
    state.size = board.size;
    state.cells = board.cells;
    state.selected = { row: 0, col: 0 };
    els.sizeInput.value = board.size;
    render();
  }

  function regionColor(regionId) {
    if (regionId === null || regionId === undefined) return "var(--cell-empty)";
    if (regionId < PALETTE_SIZE) return "var(--region-" + regionId + ")";
    const hue = (regionId * 137.508) % 360;
    return "hsl(" + hue.toFixed(1) + " 62% 72%)";
  }

  function boardRegionColor(regionId) {
    return state.showRegions ? regionColor(regionId) : "var(--cell-empty)";
  }

  // Region/green fills reference CSS variables, so they must be applied via
  // inline style (var() does not resolve in SVG presentation attributes).
  function setFill(node, color) {
    node.style.fill = color;
    return node;
  }

  function fmt(value) {
    return Number(value).toFixed(3).replace(/\.?0+$/, "");
  }

  function pointText(point) {
    return fmt(point[0]) + " " + fmt(point[1]);
  }

  function sampleArcPoints(x, y, arc, steps) {
    const spec = {
      tl: { cx: x, cy: y, start: 0, end: Math.PI / 2 },
      tr: { cx: x + 1, cy: y, start: Math.PI / 2, end: Math.PI },
      br: { cx: x + 1, cy: y + 1, start: Math.PI, end: (3 * Math.PI) / 2 },
      bl: { cx: x, cy: y + 1, start: (3 * Math.PI) / 2, end: 2 * Math.PI },
    }[arc];
    const points = [];
    for (let i = 0; i <= steps; i += 1) {
      const t = spec.start + ((spec.end - spec.start) * i) / steps;
      points.push([spec.cx + Math.cos(t), spec.cy + Math.sin(t)]);
    }
    return points;
  }

  function arcCenter(x, y, arc) {
    return {
      tl: [x, y],
      tr: [x + 1, y],
      br: [x + 1, y + 1],
      bl: [x, y + 1],
    }[arc];
  }

  function pathFromPoints(points, closed) {
    if (!points.length) return "";
    let d = "M " + pointText(points[0]);
    for (let i = 1; i < points.length; i += 1) d += " L " + pointText(points[i]);
    if (closed) d += " Z";
    return d;
  }

  function diskPath(x, y, arc) {
    const center = arcCenter(x, y, arc);
    const points = [center].concat(sampleArcPoints(x, y, arc, 24));
    return pathFromPoints(points, true);
  }

  function arcPath(x, y, arc) {
    return pathFromPoints(sampleArcPoints(x, y, arc, 36), false);
  }

  function labelInfoForCell(record, analysis) {
    if (record.blocked) return null;
    if (record.labelRegion === null || record.labelRegion === undefined) return null;
    const cell = state.cells[record.row][record.col];
    const region = analysis.regions[record.labelRegion];

    const hasScore = Boolean(region && region.score !== null);
    const clue =
      cell.number !== null && cell.number !== undefined && cell.number !== ""
        ? cell.number
        : null;

    // A clued cell's number is grey by default, green when the region matches the
    // hint. "Show scores" swaps the grey hint for the region's computed score;
    // "invalidates" forces the hint back, shown yellow when it isn't met (and
    // green still wins when it is).
    if (clue !== null && state.showClues) {
      if (hasScore && region.score === clue) return { text: String(clue), className: "match" };
      if (state.enforceClues) return { text: String(clue), className: "wrong" };
      if (state.showScores && hasScore) return { text: String(region.score), className: "" };
      return { text: String(clue), className: "" };
    }

    // Un-clued cell: show the region's computed score only when "Show scores" is on.
    if (state.showScores && hasScore) {
      return { text: String(region.score), className: "" };
    }
    return null;
  }

  function issueCellSet(analysis) {
    const set = new Set();
    analysis.issues.forEach(function (issue) {
      if (Number.isInteger(issue.row) && Number.isInteger(issue.col)) {
        set.add(issue.row + "," + issue.col);
      }
    });
    return set;
  }

  function danglingCellSet(analysis) {
    const set = new Set();
    analysis.issues.forEach(function (issue) {
      if (issue.code === "dangling-arc") set.add(issue.row + "," + issue.col);
    });
    return set;
  }

  function renderBoard(analysis) {
    const n = state.size;
    els.svg.innerHTML = "";
    els.svg.setAttribute("viewBox", "0 0 " + n + " " + n);
    els.svg.classList.toggle("show-regions", state.showRegions);

    const issueCells = issueCellSet(analysis);
    const danglingCells = danglingCellSet(analysis);
    const cellLayer = svgEl("g", {}, els.svg);
    const arcLayer = svgEl("g", {}, els.svg);
    const gridLayer = svgEl("g", {}, els.svg);
    const labelLayer = svgEl("g", {}, els.svg);
    const overlayLayer = svgEl("g", {}, els.svg);

    for (let r = 0; r < n; r += 1) {
      for (let c = 0; c < n; c += 1) {
        const record = analysis.cells[r][c];
        const x = c;
        const y = r;

        if (record.arc) {
          const remainderRegion = record.pieces.remainder.region;
          const diskRegion = record.pieces.disk.region;
          setFill(svgEl("rect", {
            class: "cell-shape",
            x: x,
            y: y,
            width: 1,
            height: 1,
          }, cellLayer), boardRegionColor(remainderRegion));
          setFill(svgEl("path", {
            class: "cell-shape",
            d: diskPath(x, y, record.arc),
          }, cellLayer), boardRegionColor(diskRegion));
        } else {
          setFill(svgEl("rect", {
            class: "cell-shape",
            x: x,
            y: y,
            width: 1,
            height: 1,
          }, cellLayer), boardRegionColor(record.pieces.full.region));
        }

        if (record.green) {
          svgEl("rect", {
            class: "green-overlay",
            x: x,
            y: y,
            width: 1,
            height: 1,
          }, cellLayer);
        }

        if (record.arc) {
          svgEl("path", {
            class:
              "arc-stroke" + (danglingCells.has(r + "," + c) ? " dangling" : ""),
            d: arcPath(x, y, record.arc),
          }, arcLayer);
        }

        const labelInfo = labelInfoForCell(record, analysis);
        if (labelInfo) {
          svgEl("text", {
            class: "cell-label " + labelInfo.className,
            x: x + 0.5,
            y: y + 0.52,
          }, labelLayer).textContent = labelInfo.text;
        }

        if (issueCells.has(r + "," + c)) {
          svgEl("rect", {
            class: "issue-outline",
            x: x + 0.04,
            y: y + 0.04,
            width: 0.92,
            height: 0.92,
            rx: 0.035,
          }, overlayLayer);
        }

        if (state.selected.row === r && state.selected.col === c) {
          svgEl("rect", {
            class: "select-outline",
            x: x + 0.035,
            y: y + 0.035,
            width: 0.93,
            height: 0.93,
            rx: 0.035,
          }, overlayLayer);
        }

        const hit = svgEl("rect", {
          class: "cell-hit",
          x: x,
          y: y,
          width: 1,
          height: 1,
          "data-row": r,
          "data-col": c,
        }, overlayLayer);
        hit.addEventListener("click", function () {
          cycleCell(Number(this.getAttribute("data-row")), Number(this.getAttribute("data-col")));
        });
        hit.addEventListener("contextmenu", function (event) {
          event.preventDefault();
          makeGreen(Number(this.getAttribute("data-row")), Number(this.getAttribute("data-col")));
        });
      }
    }

    for (let i = 0; i <= n; i += 1) {
      svgEl("line", { class: "grid-line", x1: 0, y1: i, x2: n, y2: i }, gridLayer);
      svgEl("line", { class: "grid-line", x1: i, y1: 0, x2: i, y2: n }, gridLayer);
    }
  }

  function renderStatus(analysis) {
    els.statusDot.classList.toggle("valid", analysis.valid);
    els.statusWord.textContent = analysis.valid ? "Valid" : "Not valid";
    els.regionCount.textContent = state.showRegions
      ? analysis.regions.length + (analysis.regions.length === 1 ? " region" : " regions")
      : "";
    
    els.issueList.innerHTML = "";
    if (analysis.issues.length === 0) {
      const ok = document.createElement("div");
      ok.className = "summary";
      ok.textContent = "No issues found.";
      els.issueList.appendChild(ok);
    } else {
      analysis.issues.slice(0, 9).forEach(function (issue) {
        const node = document.createElement("div");
        node.className = "issue";
        node.textContent = issue.message;
        els.issueList.appendChild(node);
      });
      if (analysis.issues.length > 9) {
        const more = document.createElement("div");
        more.className = "summary";
        more.textContent = "+" + (analysis.issues.length - 9) + " more issues";
        els.issueList.appendChild(more);
      }
    }
  }

  function renderRegions(analysis) {
    els.regionsPanel.hidden = !state.showRegions;
    els.regionList.innerHTML = "";
    if (!state.showRegions) return;
    if (analysis.regions.length === 0) {
      const empty = document.createElement("div");
      empty.className = "empty-note";
      empty.textContent = "No regions yet.";
      els.regionList.appendChild(empty);
      return;
    }

    analysis.regions.forEach(function (region) {
      const card = document.createElement("div");
      card.className = "region-card";

      const swatch = document.createElement("div");
      swatch.className = "swatch";
      swatch.style.background = regionColor(region.id);
      card.appendChild(swatch);

      const body = document.createElement("div");
      const head = document.createElement("div");
      head.className = "region-head";
      const name = document.createElement("span");
      name.textContent = "R" + (region.id + 1);
      const score = document.createElement("span");
      score.className = "region-score";
      score.textContent = "score " + (region.score === null ? region.scoreExpression : region.score);
      head.appendChild(name);
      head.appendChild(score);
      body.appendChild(head);

      const metrics = document.createElement("div");
      metrics.className = "metric-grid";
      metrics.innerHTML =
        "<span>area</span><strong>" +
        region.exactArea +
        "</strong><span>approx</span><strong>" +
        fmt(region.approximateArea) +
        "</strong><span>smooth</span><strong>" +
        region.smoothPieces +
        "</strong><span>pi/4 arcs</span><strong>" +
        region.piQuarterArcs +
        "</strong><span>1-pi/4 arcs</span><strong>" +
        region.oneMinusPiQuarterArcs +
        "</strong><span>total</span><strong>" +
        region.totalArcs +
        "</strong>";
      body.appendChild(metrics);
      card.appendChild(body);
      els.regionList.appendChild(card);
    });
  }

  function renderSelected(analysis) {
    const row = state.selected.row;
    const col = state.selected.col;
    const cell = state.cells[row][col];
    const record = analysis.cells[row][col];
    els.selectedName.textContent = "Cell " + (row + 1) + "," + (col + 1);
    els.selectedRegion.textContent =
      record.labelRegion === null || record.labelRegion === undefined
        ? "R-"
        : "R" + (record.labelRegion + 1);
    // A green cell can't be edited unless green editing is on, so grey the
    // whole Selected card to signal it's locked.
    els.selectedCard.classList.toggle("locked", cell.green && !state.editGreen);
    const activeKey = cell.green ? "green" : cell.arc || "empty";
    Array.from(els.statePicker.children).forEach(function (btn) {
      btn.classList.toggle("active", btn.getAttribute("data-key") === activeKey);
    });
    els.selectedClueInput.value =
      cell.number === null || cell.number === undefined ? "" : cell.number;
  }

  // Each cell takes its region's score; the answer is the sum of squared row
  // sums plus the sum of squared column sums (see sums.py). Returns null if any
  // cell has no integer region score.
  function computeSolution(analysis) {
    const n = analysis.size;
    const grid = [];
    for (let r = 0; r < n; r += 1) {
      const row = [];
      for (let c = 0; c < n; c += 1) {
        const record = analysis.cells[r][c];
        const region =
          record.labelRegion === null || record.labelRegion === undefined
            ? null
            : analysis.regions[record.labelRegion];
        if (!region || region.score === null || region.score === undefined) return null;
        row.push(region.score);
      }
      grid.push(row);
    }

    let rows = 0;
    let cols = 0;
    for (let r = 0; r < n; r += 1) {
      let sum = 0;
      for (let c = 0; c < n; c += 1) sum += grid[r][c];
      rows += sum * sum;
    }
    for (let c = 0; c < n; c += 1) {
      let sum = 0;
      for (let r = 0; r < n; r += 1) sum += grid[r][c];
      cols += sum * sum;
    }
    return { rows: rows, cols: cols, total: rows + cols };
  }

  function allCluesMatch(analysis) {
    // A board with no clues isn't a solved puzzle (e.g. a freshly built blank
    // grid), so require at least one clue before declaring victory.
    let hasClue = false;
    for (let r = 0; r < analysis.size; r += 1) {
      for (let c = 0; c < analysis.size; c += 1) {
        const cell = state.cells[r][c];
        if (cell.number === null || cell.number === undefined) continue;
        hasClue = true;
        const record = analysis.cells[r][c];
        const region =
          record.labelRegion === null || record.labelRegion === undefined
            ? null
            : analysis.regions[record.labelRegion];
        if (!region || region.score !== cell.number) return false;
      }
    }
    return hasClue;
  }

  function renderSolution(analysis) {
    const result = analysis.valid ? computeSolution(analysis) : null;
    if (!result) {
      els.solution.className = "solution invalid";
      els.solution.textContent = "solution: invalid board";
      return;
    }
    const solved = allCluesMatch(analysis);
    els.solution.className = "solution" + (solved ? " solved" : "");
    els.solution.textContent = "solution: " + result.total.toLocaleString();
    if (solved && isTutorial && !state.wonShown) {
      state.wonShown = true;
      els.winModal.hidden = false;
    }
  }

  function render() {
    state.analysis = Core.analyzeGrid({
      size: state.size,
      cells: state.cells,
      enforceClues: state.enforceClues,
    });
    renderBoard(state.analysis);
    renderStatus(state.analysis);
    renderRegions(state.analysis);
    renderSelected(state.analysis);
    renderSolution(state.analysis);
  }

  function selectCell(row, col) {
    state.selected = { row: row, col: col };
  }

  function cellStateIndex(cell) {
    if (cell.green) return 5;
    const order = [null, "tl", "tr", "br", "bl"];
    const index = order.indexOf(cell.arc || null);
    return index === -1 ? 0 : index;
  }

  function cycleCell(row, col) {
    selectCell(row, col);
    const cell = state.cells[row][col];
    // With green editing off, green cells are locked and green is dropped from
    // the cycle (clicking only moves through empty + the four arcs).
    if (!state.editGreen && cell.green) {
      render();
      return;
    }
    const states = [
      { green: false, arc: null },
      { green: false, arc: "tl" },
      { green: false, arc: "tr" },
      { green: false, arc: "br" },
      { green: false, arc: "bl" },
    ];
    if (state.editGreen) states.push({ green: true, arc: null });
    const next = states[(cellStateIndex(cell) + 1) % states.length];
    cell.green = next.green;
    cell.arc = next.arc;
    render();
  }

  function makeGreen(row, col) {
    // Right-click shortcut for green only works while green editing is on.
    if (!state.editGreen) return;
    selectCell(row, col);
    const cell = state.cells[row][col];
    cell.green = true;
    cell.arc = null;
    render();
  }

  // Build always starts a fresh, empty board at the requested size — it never
  // carries over the current cells or the starter puzzle.
  function resizeGrid(nextSize) {
    const size = Math.max(1, Math.min(30, Math.floor(Number(nextSize) || 5)));
    state.size = size;
    state.cells = Core.createEmptyCells(size);
    state.selected = { row: 0, col: 0 };
    els.sizeInput.value = size;
    render();
  }

  els.resizeButton.addEventListener("click", function () {
    resizeGrid(els.sizeInput.value);
  });

  els.sizeInput.addEventListener("keydown", function (event) {
    if (event.key === "Enter") resizeGrid(els.sizeInput.value);
  });

  els.showClues.addEventListener("change", function () {
    state.showClues = els.showClues.checked;
    render();
  });

  els.showScores.addEventListener("change", function () {
    state.showScores = els.showScores.checked;
    els.svg.classList.toggle("compact-numbers", state.showScores);
    render();
  });

  els.showRegions.addEventListener("change", function () {
    state.showRegions = els.showRegions.checked;
    render();
  });

  els.enforceClues.addEventListener("change", function () {
    state.enforceClues = els.enforceClues.checked;
    render();
  });

  // Reflect the Custom edit toggles into the editor: hide the clue input when
  // clue editing is off, and rebuild the state picker so green appears only when
  // green editing is on.
  function applyEditModes() {
    // Note: `.control` sets display:grid, which would override the [hidden]
    // attribute, so toggle display directly instead.
    els.clueControl.style.display = state.editClues ? "" : "none";
    buildStatePicker();
    render();
  }

  els.editClues.addEventListener("change", function () {
    state.editClues = els.editClues.checked;
    applyEditModes();
  });

  els.editGreen.addEventListener("change", function () {
    state.editGreen = els.editGreen.checked;
    applyEditModes();
  });

  els.saveFile.addEventListener("click", saveToFile);

  els.loadFile.addEventListener("click", function () {
    els.loadFileInput.click();
  });

  els.loadFileInput.addEventListener("change", function (event) {
    const file = event.target.files && event.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = function () {
      loadFromText(reader.result);
    };
    reader.readAsText(file);
    els.loadFileInput.value = "";
  });

  els.collapseLeft.addEventListener("click", function () {
    const collapsed = els.app.classList.toggle("left-collapsed");
    els.collapseLeft.classList.toggle("collapsed", collapsed);
    els.collapseLeft.setAttribute(
      "aria-label",
      collapsed ? "Expand left panel" : "Collapse left panel"
    );
  });

  els.collapseRight.addEventListener("click", function () {
    const collapsed = els.app.classList.toggle("right-collapsed");
    els.collapseRight.classList.toggle("collapsed", collapsed);
    els.collapseRight.setAttribute(
      "aria-label",
      collapsed ? "Expand right panel" : "Collapse right panel"
    );
  });

  els.selectedClueInput.addEventListener("input", function () {
    const cell = state.cells[state.selected.row][state.selected.col];
    const raw = els.selectedClueInput.value;
    if (raw === "") {
      cell.number = null;
    } else {
      const number = Number(raw);
      if (!Number.isInteger(number)) return;
      cell.number = number;
    }
    render();
  });

  // Reflect the initial state into the controls so the checkboxes match the
  // defaults set on `state` above (otherwise they always render unchecked).
  els.sizeInput.value = state.size;
  els.showClues.checked = state.showClues;
  els.showScores.checked = state.showScores;
  els.showRegions.checked = state.showRegions;
  els.enforceClues.checked = state.enforceClues;
  els.editClues.checked = state.editClues;
  els.editGreen.checked = state.editGreen;

  // On mobile, default the left options panel to collapsed (it can still be
  // expanded with the existing collapse toggle).
  if (window.matchMedia("(max-width: 720px)").matches) {
    els.app.classList.add("left-collapsed");
    els.collapseLeft.classList.add("collapsed");
    els.collapseLeft.setAttribute("aria-label", "Expand left panel");
  }

  els.winCta.addEventListener("click", function () {
    localStorage.removeItem("arcboard_mode");
  });
  applyEditModes();
})();
