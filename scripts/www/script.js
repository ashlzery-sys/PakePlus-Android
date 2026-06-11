(function(){
    const gridCanvas = document.getElementById('c-a');
    const drawingCanvas = document.getElementById('c-b');
    const gridCtx = gridCanvas.getContext('2d');
    const drawCtx = drawingCanvas.getContext('2d');
    const customCursor = document.getElementById('customCursor');
    const pencilBtn = document.getElementById('pencilBtn');
    const eraserBtn = document.getElementById('eraserBtn');
    const lassoBtn = document.getElementById('lassoBtn');
    const pinBtn = document.getElementById('pinBtn');
    const brushPanelEl = document.getElementById('brushPanel');
    const brushSlider = document.getElementById('brushSizeSlider');
    const brushValue = document.getElementById('brushSizeValue');
    const brushLabel = document.getElementById('brushLabel');
    const smoothTrigger = document.getElementById('smoothTrigger');
    const smoothDropdown = document.getElementById('smoothDropdown');
    const zoomSpan = document.getElementById('zoomPercent');
    const saveBtn = document.getElementById('saveBtn');
    const importBtn = document.getElementById('importBtn');
    const fileInput = document.getElementById('fileInput');
    const pinListContainer = document.getElementById('pinListContainer');
    const bottomPanel = document.getElementById('bottomPanel');
    const pinPanel = document.getElementById('pinPanel');
    const panelToggle = document.getElementById('panelToggle');
    
    let dpr = window.devicePixelRatio || 1;
    let strokes = [];
    let pins = [];
    let nextPinId = 1;
    let currentStroke = null, currentTool = '';
    let pencilWorldWidth = 4, eraserWorldWidth = 12;
    let smoothFactor = 0.5;
    const MIN_SCALE = 0.5, MAX_SCALE = 1.5;
    let scale = 1.0, offsetX = 0, offsetY = 0;
    let canvasWidth = window.innerWidth * dpr;
    let canvasHeight = window.innerHeight * dpr;
    let isDrawing = false, isPanning = false, spacePressed = false, lastPanX = 0, lastPanY = 0, activePointerId = null;
    let lastMouseScreenX = 0, lastMouseScreenY = 0;
    let isLassoDrawing = false, lassoPoints = [];
    
    let shapeRecogTimer = null;
    let strokeModifiedByRecog = false;
    let shiftPressed = false;
    
    let selectedItems = new Set();
    const PIN_RADIUS_WORLD = 28;
    let selectionLocalBounds = { x:0,y:0,w:0,h:0 }, selectionCenter = { x:0,y:0 }, selectionRotation = 0;
    let isTransforming = false, transformType = null, transformStartMouseScreen = null;
    let transformStartSelectedSnapshot = null;
    let transformStartLocalBounds = null, transformStartCenter = null, transformStartRotation = 0, transformStartCornerIdx = 0, transformStartEdgeIdx = 0;
    const BORDER_WORLD_WIDTH = 1.5;
    const CONTROL_POINT_WORLD_SIZE = 6;
    const ROTATE_HANDLE_WORLD_SIZE = 17;
    const ROTATE_ICON_WORLD_SIZE = 24;
    let lassoModifier = 'replace';
    const PENCIL_COLOR = '#1e293b';
    const GRID_WORLD_WIDTH = 0.6;
    
    let currentEditingPinId = null;
    let justOpenedPanel = false;
    let currentLevelMenu = null;
    let isNameModalActive = false;
    let modalMask = null;
    let modalPanel = null;
    
    let bgCanvas = null;
    let bgCtx = null;
    let bgCacheValid = false;
    
    const GRID_CELL_SIZE = 200;
    let strokeGrid = new Map();
    
    // 辅助函数：根据基准宽度和压力(0~1)计算实际世界宽度
    function getWidthFromPressure(baseWidth, pressure) {
        // pressure 0 -> baseWidth - 2, 1 -> baseWidth + 2, 限定最小为1
        let w = baseWidth + (pressure - 0.5) * 4;
        return Math.max(1, Math.round(w));
    }
    
    // 从点获取当前实际宽度（用于绘制时的半径）
    function getRadiusFromPoint(point, baseWidth) {
        const w = getWidthFromPressure(baseWidth, point.pressure);
        return w / 2;
    }
    
    function getGridKey(worldX, worldY) {
        const gx = Math.floor(worldX / GRID_CELL_SIZE);
        const gy = Math.floor(worldY / GRID_CELL_SIZE);
        return `${gx},${gy}`;
    }
    
    function addStrokeToGrid(strokeIdx) {
        const stroke = strokes[strokeIdx];
        if (!stroke || !stroke.bbox) return;
        const minX = stroke.bbox.minX, maxX = stroke.bbox.maxX;
        const minY = stroke.bbox.minY, maxY = stroke.bbox.maxY;
        const startGx = Math.floor(minX / GRID_CELL_SIZE);
        const endGx = Math.floor(maxX / GRID_CELL_SIZE);
        const startGy = Math.floor(minY / GRID_CELL_SIZE);
        const endGy = Math.floor(maxY / GRID_CELL_SIZE);
        for (let gx = startGx; gx <= endGx; gx++) {
            for (let gy = startGy; gy <= endGy; gy++) {
                const key = `${gx},${gy}`;
                if (!strokeGrid.has(key)) strokeGrid.set(key, new Set());
                strokeGrid.get(key).add(strokeIdx);
            }
        }
    }
    
    function rebuildStrokeGrid() {
        strokeGrid.clear();
        for (let i = 0; i < strokes.length; i++) {
            if (strokes[i].type === 'pencil') {
                addStrokeToGrid(i);
            }
        }
    }
    
    function queryStrokesInWorldRect(worldRect) {
        const startGx = Math.floor(worldRect.minX / GRID_CELL_SIZE);
        const endGx = Math.floor(worldRect.maxX / GRID_CELL_SIZE);
        const startGy = Math.floor(worldRect.minY / GRID_CELL_SIZE);
        const endGy = Math.floor(worldRect.maxY / GRID_CELL_SIZE);
        const result = new Set();
        for (let gx = startGx; gx <= endGx; gx++) {
            for (let gy = startGy; gy <= endGy; gy++) {
                const key = `${gx},${gy}`;
                const cell = strokeGrid.get(key);
                if (cell) {
                    for (let idx of cell) result.add(idx);
                }
            }
        }
        return Array.from(result);
    }
    
    let pendingDirtyRects = [];
    let renderScheduled = false;
    
    function addDirtyRect(rect) {
        if (!rect) return;
        pendingDirtyRects.push(rect);
        if (!renderScheduled) {
            renderScheduled = true;
            requestAnimationFrame(() => {
                flushRendering();
                renderScheduled = false;
            });
        }
    }
    
    function addDirtyRectFromWorld(worldX, worldY, worldW, worldH) {
        const topLeft = worldToScreen(worldX, worldY);
        const bottomRight = worldToScreen(worldX + worldW, worldY + worldH);
        const w = bottomRight.x - topLeft.x;
        const h = bottomRight.y - topLeft.y;
        if (w > 0 && h > 0) {
            addDirtyRect({ x: topLeft.x, y: topLeft.y, w, h });
        }
    }
    
    function addDirtyRectFromStroke(stroke, marginWorld = 10) {
        if (!stroke.bbox) updateStrokeBBox(stroke);
        const b = stroke.bbox;
        addDirtyRectFromWorld(b.minX - marginWorld, b.minY - marginWorld, b.maxX - b.minX + marginWorld*2, b.maxY - b.minY + marginWorld*2);
    }
    
    function mergeRects(rects) {
        if (rects.length === 0) return [];
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (let r of rects) {
            minX = Math.min(minX, r.x);
            minY = Math.min(minY, r.y);
            maxX = Math.max(maxX, r.x + r.w);
            maxY = Math.max(maxY, r.y + r.h);
        }
        return [{ x: minX, y: minY, w: maxX - minX, h: maxY - minY }];
    }
    
    function flushRendering() {
        if (pendingDirtyRects.length === 0) return;
        const rects = mergeRects(pendingDirtyRects);
        pendingDirtyRects = [];
        for (let rect of rects) {
            renderDrawing(rect);
        }
    }
    
    function fullRepaint() {
        pendingDirtyRects = [];
        renderDrawing(null);
    }
    
    let undoStack = [];
    let redoStack = [];
    const MAX_HISTORY = 30;
    
    class Command {
        undo() {}
        redo() {}
    }
    
    class AddStrokeCommand extends Command {
        constructor(stroke, index, skipRedraw = false) {
            super();
            this.stroke = {
                type: stroke.type,
                baseWidth: stroke.baseWidth,
                points: stroke.points.map(p => ({ x: p.x, y: p.y, pressure: p.pressure }))
            };
            this.index = index;
            this.skipRedraw = skipRedraw;
        }
        undo() {
            strokes.splice(this.index, 1);
            const newSelected = new Set();
            for (let s of selectedItems) {
                if (s[0] === 's') {
                    let idx = parseInt(s.slice(1));
                    if (idx > this.index) newSelected.add('s' + (idx - 1));
                    else if (idx < this.index) newSelected.add(s);
                } else newSelected.add(s);
            }
            selectedItems = newSelected;
            rebuildStrokeGrid();
            bgCacheValid = false;
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            const strokeCopy = {
                type: this.stroke.type,
                baseWidth: this.stroke.baseWidth,
                points: this.stroke.points.map(p => ({ x: p.x, y: p.y, pressure: p.pressure }))
            };
            strokes.splice(this.index, 0, strokeCopy);
            updateStrokeBBox(strokes[this.index]);
            const newSelected = new Set();
            for (let s of selectedItems) {
                if (s[0] === 's') {
                    let idx = parseInt(s.slice(1));
                    if (idx >= this.index) newSelected.add('s' + (idx + 1));
                    else newSelected.add(s);
                } else newSelected.add(s);
            }
            selectedItems = newSelected;
            rebuildStrokeGrid();
            if (!this.skipRedraw) {
                bgCacheValid = false;
                fullRepaint();
            } else {
                if (!bgCacheValid) {
                    rebuildBackgroundCache();
                } else {
                    const boundsWorld = strokeCopy.bbox;
                    const topLeft = worldToScreen(boundsWorld.minX, boundsWorld.minY);
                    const bottomRight = worldToScreen(boundsWorld.maxX, boundsWorld.maxY);
                    const dirtyRect = { x: topLeft.x, y: topLeft.y, w: bottomRight.x - topLeft.x, h: bottomRight.y - topLeft.y };
                    if (dirtyRect.w > 0 && dirtyRect.h > 0) {
                        bgCtx.save();
                        bgCtx.beginPath();
                        bgCtx.rect(dirtyRect.x, dirtyRect.y, dirtyRect.w, dirtyRect.h);
                        bgCtx.clip();
                        drawSingleStrokeToContext(bgCtx, strokeCopy);
                        bgCtx.restore();
                        addDirtyRect(dirtyRect);
                    } else {
                        bgCacheValid = false;
                        fullRepaint();
                    }
                }
            }
            updatePinsListUI();
            updateBottomPanel();
        }
    }
    
    class DeleteStrokesCommand extends Command {
        constructor(deleted) {
            super();
            this.deleted = JSON.parse(JSON.stringify(deleted));
        }
        undo() {
            for (let item of this.deleted.slice().sort((a,b)=>a.index-b.index)) {
                strokes.splice(item.index, 0, JSON.parse(JSON.stringify(item.stroke)));
            }
            let newSelected = new Set();
            for (let s of selectedItems) {
                if (s[0] === 's') {
                    let idx = parseInt(s.slice(1));
                    let offset = 0;
                    for (let d of this.deleted) if (d.index <= idx) offset++;
                    newSelected.add('s'+(idx+offset));
                } else newSelected.add(s);
            }
            for (let d of this.deleted) {
                if (d.wasSelected) newSelected.add('s'+d.index);
            }
            selectedItems = newSelected;
            rebuildStrokeGrid();
            bgCacheValid = false;
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            for (let item of this.deleted.slice().sort((a,b)=>b.index-a.index)) {
                strokes.splice(item.index, 1);
            }
            let newSelected = new Set();
            for (let s of selectedItems) {
                if (s[0] === 's') {
                    let idx = parseInt(s.slice(1));
                    let offset = 0;
                    for (let d of this.deleted) if (d.index < idx) offset++;
                    if (!this.deleted.some(d => d.index === idx - offset))
                        newSelected.add('s'+(idx-offset));
                } else newSelected.add(s);
            }
            selectedItems = newSelected;
            rebuildStrokeGrid();
            bgCacheValid = false;
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
    }
    
    class ModifyStrokesCommand extends Command {
        constructor(mods) {
            super();
            this.mods = mods.map(m => ({
                index: m.index,
                oldPoints: m.oldPoints.map(p=>({x:p.x,y:p.y,pressure:p.pressure})),
                newPoints: m.newPoints.map(p=>({x:p.x,y:p.y,pressure:p.pressure}))
            }));
        }
        undo() {
            for (let m of this.mods) {
                strokes[m.index].points = m.oldPoints.map(p=>({x:p.x,y:p.y,pressure:p.pressure}));
                updateStrokeBBox(strokes[m.index]);
            }
            rebuildStrokeGrid();
            bgCacheValid = false;
            fullRepaint();
        }
        redo() {
            for (let m of this.mods) {
                strokes[m.index].points = m.newPoints.map(p=>({x:p.x,y:p.y,pressure:p.pressure}));
                updateStrokeBBox(strokes[m.index]);
            }
            rebuildStrokeGrid();
            bgCacheValid = false;
            fullRepaint();
        }
    }
    
    class AddPinCommand extends Command {
        constructor(pin, index) {
            super();
            this.pin = JSON.parse(JSON.stringify(pin));
            this.index = index;
        }
        undo() {
            pins.splice(this.index, 1);
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            pins.splice(this.index, 0, JSON.parse(JSON.stringify(this.pin)));
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
    }
    
    class DeletePinsCommand extends Command {
        constructor(deleted) {
            super();
            this.deleted = JSON.parse(JSON.stringify(deleted));
        }
        undo() {
            for (let d of this.deleted.slice().sort((a,b)=>a.index-b.index)) {
                pins.splice(d.index, 0, JSON.parse(JSON.stringify(d.pin)));
            }
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            for (let d of this.deleted.slice().sort((a,b)=>b.index-a.index)) {
                pins.splice(d.index, 1);
            }
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
    }
    
    class UpdatePinCommand extends Command {
        constructor(index, oldPin, newPin) {
            super();
            this.index = index;
            this.oldPin = JSON.parse(JSON.stringify(oldPin));
            this.newPin = JSON.parse(JSON.stringify(newPin));
        }
        undo() {
            pins[this.index] = this.oldPin;
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            pins[this.index] = this.newPin;
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
    }
    
    class ModifyPinsCommand extends Command {
        constructor(mods) {
            super();
            this.mods = mods.map(m=>({...m}));
        }
        undo() {
            for (let m of this.mods) {
                pins[m.index].x = m.oldX;
                pins[m.index].y = m.oldY;
            }
            fullRepaint();
            updatePinsListUI();
        }
        redo() {
            for (let m of this.mods) {
                pins[m.index].x = m.newX;
                pins[m.index].y = m.newY;
            }
            fullRepaint();
            updatePinsListUI();
        }
    }
    
    class ReplaceAllCommand extends Command {
        constructor(oldStrokes, oldPins, newStrokes, newPins) {
            super();
            this.oldStrokes = JSON.parse(JSON.stringify(oldStrokes));
            this.oldPins = JSON.parse(JSON.stringify(oldPins));
            this.newStrokes = JSON.parse(JSON.stringify(newStrokes));
            this.newPins = JSON.parse(JSON.stringify(newPins));
        }
        undo() {
            strokes = this.oldStrokes.map(s=>JSON.parse(JSON.stringify(s)));
            pins = this.oldPins.map(p=>JSON.parse(JSON.stringify(p)));
            clearSelection();
            rebuildStrokeGrid();
            bgCacheValid = false;
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            strokes = this.newStrokes.map(s=>JSON.parse(JSON.stringify(s)));
            pins = this.newPins.map(p=>JSON.parse(JSON.stringify(p)));
            clearSelection();
            rebuildStrokeGrid();
            bgCacheValid = false;
            fullRepaint();
            updatePinsListUI();
            updateBottomPanel();
        }
    }
    
    class CompositeCommand extends Command {
        constructor(cmds) {
            super();
            this.cmds = cmds;
        }
        undo() {
            for (let i=this.cmds.length-1; i>=0; i--) this.cmds[i].undo();
        }
        redo() {
            for (let cmd of this.cmds) cmd.redo();
        }
    }
    
    function executeCommand(cmd) {
        cmd.redo();
        undoStack.push(cmd);
        redoStack.length = 0;
        if (undoStack.length > MAX_HISTORY) undoStack.shift();
    }
    
    function undo() {
        if (undoStack.length === 0) return;
        const cmd = undoStack.pop();
        cmd.undo();
        redoStack.push(cmd);
        if (redoStack.length > MAX_HISTORY) redoStack.shift();
        updatePinsListUI();
        updateBottomPanel();
    }
    
    function redo() {
        if (redoStack.length === 0) return;
        const cmd = redoStack.pop();
        cmd.redo();
        undoStack.push(cmd);
        if (undoStack.length > MAX_HISTORY) undoStack.shift();
        updatePinsListUI();
        updateBottomPanel();
    }
    
    function markCacheDirty() {
        bgCacheValid = false;
    }
    
    function rebuildBackgroundCache() {
        if (!bgCanvas) return;
        bgCtx.clearRect(0, 0, canvasWidth, canvasHeight);
        const visibleRect = getVisibleWorldRect();
        for (const stroke of strokes) {
            if (stroke.type === 'pencil' && isStrokeVisible(stroke, visibleRect)) {
                drawSingleStrokeToContext(bgCtx, stroke);
            }
        }
        bgCacheValid = true;
    }
    
    function updateStrokeBBox(stroke) {
        if (!stroke.points || stroke.points.length === 0) {
            stroke.bbox = { minX:0, minY:0, maxX:0, maxY:0 };
            return;
        }
        let minX=Infinity, minY=Infinity, maxX=-Infinity, maxY=-Infinity;
        for (let p of stroke.points) {
            const r = getRadiusFromPoint(p, stroke.baseWidth);
            minX = Math.min(minX, p.x - r);
            minY = Math.min(minY, p.y - r);
            maxX = Math.max(maxX, p.x + r);
            maxY = Math.max(maxY, p.y + r);
        }
        stroke.bbox = { minX, minY, maxX, maxY };
    }
    
    function getVisibleWorldRect() {
        const tl = screenToWorld(0,0);
        const br = screenToWorld(canvasWidth,canvasHeight);
        return { minX:tl.x, minY:tl.y, maxX:br.x, maxY:br.y };
    }
    
    function isStrokeVisible(stroke, rect) {
        if (!stroke.bbox) updateStrokeBBox(stroke);
        const b = stroke.bbox;
        return !(b.maxX<rect.minX || b.minX>rect.maxX || b.maxY<rect.minY || b.minY>rect.maxY);
    }
    
    function pointToSegmentDistance(px,py,x1,y1,x2,y2) {
        const ax=px-x1, ay=py-y1;
        const bx=x2-x1, by=y2-y1;
        const dot=ax*bx+ay*by;
        const len2=bx*bx+by*by;
        if(len2===0) return Math.hypot(ax,ay);
        let t=dot/len2;
        t=Math.max(0,Math.min(1,t));
        const projX=x1+t*bx, projY=y1+t*by;
        return Math.hypot(px-projX, py-projY);
    }
    
    function collectEraserChanges(eraserStroke) {
        if(!eraserStroke || eraserStroke.points.length<2) return {toDelete:[]};
        const eraserRadius = eraserStroke.worldWidth/2;
        let eraserMinX=Infinity, eraserMinY=Infinity, eraserMaxX=-Infinity, eraserMaxY=-Infinity;
        for(let p of eraserStroke.points){
            eraserMinX=Math.min(eraserMinX,p.x); eraserMinY=Math.min(eraserMinY,p.y);
            eraserMaxX=Math.max(eraserMaxX,p.x); eraserMaxY=Math.max(eraserMaxY,p.y);
        }
        eraserMinX-=eraserRadius; eraserMinY-=eraserRadius;
        eraserMaxX+=eraserRadius; eraserMaxY+=eraserRadius;
        const eraserWorldRect = { minX: eraserMinX, minY: eraserMinY, maxX: eraserMaxX, maxY: eraserMaxY };
        const candidates = queryStrokesInWorldRect(eraserWorldRect);
        const toDelete=[];
        for(let idx of candidates){
            const st=strokes[idx];
            if(!st) continue;
            if(st.type==='pencil'){
                let hit=false;
                const pts=st.points;
                if(pts.length<2) continue;
                outer: for(let ep of eraserStroke.points){
                    for(let i=0;i<pts.length-1;i++){
                        const r0 = getRadiusFromPoint(pts[i], st.baseWidth);
                        const r1 = getRadiusFromPoint(pts[i+1], st.baseWidth);
                        // 粗略检测：线段到点距离小于两半径之和即碰撞
                        if(pointToSegmentDistance(ep.x,ep.y, pts[i].x,pts[i].y, pts[i+1].x,pts[i+1].y) <= eraserRadius + Math.max(r0,r1)){
                            hit=true; break outer;
                        }
                    }
                    for(let pt of pts){
                        const r = getRadiusFromPoint(pt, st.baseWidth);
                        if(Math.hypot(ep.x-pt.x, ep.y-pt.y) <= eraserRadius + r){
                            hit=true; break outer;
                        }
                    }
                }
                if(hit) toDelete.push({index:idx, stroke:JSON.parse(JSON.stringify(st)), wasSelected:selectedItems.has('s'+idx)});
            }
        }
        return {toDelete};
    }
    
    function isParallel(v1, v2, threshold = 0.95) {
        const dot = v1.x * v2.x + v1.y * v2.y;
        const len1 = Math.hypot(v1.x, v1.y);
        const len2 = Math.hypot(v2.x, v2.y);
        if (len1 === 0 || len2 === 0) return false;
        const cos = dot / (len1 * len2);
        return Math.abs(cos) >= threshold;
    }
    
    function detectEllipse(points, A, B) {
        const AB = { x: B.x - A.x, y: B.y - A.y };
        const ABlen = Math.hypot(AB.x, AB.y);
        if (ABlen < 0.01) return false;
        for (let i = 0; i < points.length; i++) {
            for (let j = i+1; j < points.length; j++) {
                const p = points[i], q = points[j];
                const vec = { x: q.x - p.x, y: q.y - p.y };
                const len = Math.hypot(vec.x, vec.y);
                if (len > ABlen * 2 && isParallel(vec, AB)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    function fitEllipsePCA(points) {
        const n = points.length;
        if (n < 2) return null;
        let sumX = 0, sumY = 0;
        for (let p of points) { sumX += p.x; sumY += p.y; }
        const center = { x: sumX / n, y: sumY / n };
        let covxx = 0, covxy = 0, covyy = 0;
        for (let p of points) {
            const dx = p.x - center.x;
            const dy = p.y - center.y;
            covxx += dx * dx;
            covxy += dx * dy;
            covyy += dy * dy;
        }
        covxx /= n;
        covxy /= n;
        covyy /= n;
        const trace = covxx + covyy;
        const det = covxx * covyy - covxy * covxy;
        const sqrtTerm = Math.sqrt(Math.max(0, trace * trace - 4 * det));
        const lambda1 = (trace + sqrtTerm) / 2;
        const lambda2 = (trace - sqrtTerm) / 2;
        let eigenVec;
        if (Math.abs(covxy) > 1e-8) {
            const vx = lambda1 - covyy;
            const vy = covxy;
            const len = Math.hypot(vx, vy);
            eigenVec = { x: vx / len, y: vy / len };
        } else {
            if (covxx >= covyy) eigenVec = { x: 1, y: 0 };
            else eigenVec = { x: 0, y: 1 };
        }
        const perpVec = { x: -eigenVec.y, y: eigenVec.x };
        let minProj = Infinity, maxProj = -Infinity;
        let minPerp = Infinity, maxPerp = -Infinity;
        for (let p of points) {
            const dx = p.x - center.x;
            const dy = p.y - center.y;
            const proj = dx * eigenVec.x + dy * eigenVec.y;
            const perp = dx * perpVec.x + dy * perpVec.y;
            if (proj < minProj) minProj = proj;
            if (proj > maxProj) maxProj = proj;
            if (perp < minPerp) minPerp = perp;
            if (perp > maxPerp) maxPerp = perp;
        }
        let a = (maxProj - minProj) / 2;
        let b = (maxPerp - minPerp) / 2;
        if (a < 0.01 || b < 0.01) return null;
        const theta = Math.atan2(eigenVec.y, eigenVec.x);
        return { center, a, b, theta };
    }
    
    function generateEllipsePoints(center, a, b, theta, maxGap = 2.5) {
        const rawPoints = [];
        const cosTheta = Math.cos(theta);
        const sinTheta = Math.sin(theta);
        const numRaw = Math.max(400, Math.ceil((Math.PI * 2 * Math.sqrt((a*a + b*b)/2)) / (maxGap * 0.5)));
        for (let i = 0; i <= numRaw; i++) {
            const t = i / numRaw * 2 * Math.PI;
            const x0 = a * Math.cos(t);
            const y0 = b * Math.sin(t);
            const x = center.x + x0 * cosTheta - y0 * sinTheta;
            const y = center.y + x0 * sinTheta + y0 * cosTheta;
            rawPoints.push({ x, y });
        }
        return resamplePointsByDistance(rawPoints, maxGap);
    }
    
    function cubicBezierPoint(p0, p1, p2, p3, t) {
        const mt = 1 - t;
        const x = mt*mt*mt * p0.x + 3*mt*mt*t * p1.x + 3*mt*t*t * p2.x + t*t*t * p3.x;
        const y = mt*mt*mt * p0.y + 3*mt*mt*t * p1.y + 3*mt*t*t * p2.y + t*t*t * p3.y;
        return { x, y };
    }
    
    function fitCubicBezierThroughThreePoints(A, C, B, maxGap = 2.5) {
        const sum = { x: (8*C.x - A.x - B.x)/3, y: (8*C.y - A.y - B.y)/3 };
        const dir = { x: B.x - A.x, y: B.y - A.y };
        const lenDir = Math.hypot(dir.x, dir.y);
        if (lenDir < 1e-6) return [A, B];
        const midAB = { x: (A.x+B.x)/2, y: (A.y+B.y)/2 };
        const offset = { x: C.x - midAB.x, y: C.y - midAB.y };
        const offsetLen = Math.hypot(offset.x, offset.y);
        let k = (offsetLen / lenDir) * 1.6;
        k = Math.min(k, 2.0);
        const P1 = { x: (sum.x - k*dir.x)/2, y: (sum.y - k*dir.y)/2 };
        const P2 = { x: (sum.x + k*dir.x)/2, y: (sum.y + k*dir.y)/2 };
        const numRaw = Math.max(300, Math.ceil(lenDir / (maxGap * 0.5)));
        const rawPoints = [];
        for (let i = 0; i <= numRaw; i++) {
            const t = i / numRaw;
            rawPoints.push(cubicBezierPoint(A, P1, P2, B, t));
        }
        rawPoints[0] = A;
        rawPoints[rawPoints.length-1] = B;
        return resamplePointsByDistance(rawPoints, maxGap);
    }
    
    function interpolateLinePoints(A, B, maxGap = 2.5) {
        const dx = B.x - A.x, dy = B.y - A.y;
        const len = Math.hypot(dx, dy);
        if (len <= maxGap) return [A, B];
        const steps = Math.ceil(len / maxGap);
        const points = [];
        for (let i = 0; i <= steps; i++) {
            const t = i / steps;
            points.push({ x: A.x + dx * t, y: A.y + dy * t });
        }
        return points;
    }
    
    function resamplePointsByDistance(points, maxGap) {
        if(!points || points.length<2) return points;
        const result=[points[0]];
        let cur={x:points[0].x, y:points[0].y};
        for(let i=1;i<points.length;i++){
            const p1=cur, p2=points[i];
            const dx=p2.x-p1.x, dy=p2.y-p1.y;
            const segLen=Math.hypot(dx,dy);
            if(segLen<=maxGap){
                result.push(p2);
                cur=p2;
                continue;
            }
            const steps=Math.ceil(segLen/maxGap);
            for(let j=1;j<=steps;j++){
                const t=j/steps;
                result.push({x:p1.x+dx*t, y:p1.y+dy*t});
            }
            cur=p2;
        }
        if(result[result.length-1]!==points[points.length-1]) result[result.length-1]=points[points.length-1];
        return result;
    }
    
    // 压力插值辅助：根据原始点数组和插值坐标，通过比例插值压力
    function interpolatePressure(rawPoints, x, y) {
        if (!rawPoints || rawPoints.length === 0) return 0.5;
        if (rawPoints.length === 1) return rawPoints[0].pressure;
        // 找到曲线上最近的两个点，按距离加权
        let minDist = Infinity, bestIdx = 0;
        for (let i = 0; i < rawPoints.length; i++) {
            const d = Math.hypot(x - rawPoints[i].x, y - rawPoints[i].y);
            if (d < minDist) { minDist = d; bestIdx = i; }
        }
        // 取邻近两点（前后）加权平均
        let left = rawPoints[bestIdx];
        let right = rawPoints[bestIdx];
        if (bestIdx > 0) left = rawPoints[bestIdx-1];
        if (bestIdx < rawPoints.length-1) right = rawPoints[bestIdx+1];
        const distLeft = Math.hypot(x - left.x, y - left.y);
        const distRight = Math.hypot(x - right.x, y - right.y);
        const total = distLeft + distRight;
        if (total < 1e-6) return left.pressure;
        const wLeft = distRight / total;
        const wRight = distLeft / total;
        return left.pressure * wLeft + right.pressure * wRight;
    }
    
    function attemptStraightenStroke() {
        if (!currentStroke || strokeModifiedByRecog) return false;
        const points = currentStroke.points;
        if (points.length < 2) return false;
        
        const A = { x: points[0].x, y: points[0].y };
        const B = { x: points[points.length - 1].x, y: points[points.length - 1].y };
        const ABlen = Math.hypot(B.x - A.x, B.y - A.y);
        if (ABlen < 0.01) return false;
        
        const maxGap = 1.5;
        
        if (detectEllipse(points, A, B)) {
            strokeModifiedByRecog = true;
            let ellipse = fitEllipsePCA(points);
            if (!ellipse) {
                strokeModifiedByRecog = false;
                return false;
            }
            if (shiftPressed) {
                const r = (ellipse.a + ellipse.b) / 2;
                ellipse.a = r;
                ellipse.b = r;
            }
            const ellipsePoints = generateEllipsePoints(ellipse.center, ellipse.a, ellipse.b, ellipse.theta, maxGap);
            if (ellipsePoints.length >= 2) {
                // 识别后：所有点压力设为0.5，baseWidth为当前笔刷基准宽度
                const newPoints = ellipsePoints.map(p => ({ x: p.x, y: p.y, pressure: 0.5 }));
                currentStroke.type = 'pencil';
                currentStroke.points = newPoints;
                currentStroke.rawPoints = newPoints.slice();
                currentStroke.baseWidth = pencilWorldWidth;
            } else {
                strokeModifiedByRecog = false;
                return false;
            }
            finalizeCurrentStroke();
            return true;
        }
        
        let maxDist = 0;
        let farthestIndex = 0;
        for (let i = 0; i < points.length; i++) {
            const p = points[i];
            const dist = pointToSegmentDistance(p.x, p.y, A.x, A.y, B.x, B.y);
            if (dist > maxDist) {
                maxDist = dist;
                farthestIndex = i;
            }
        }
        const C = { x: points[farthestIndex].x, y: points[farthestIndex].y };
        const threshold = ABlen / 14;
        
        if (maxDist < threshold) {
            strokeModifiedByRecog = true;
            let linePoints;
            if (shiftPressed) {
                const dx = Math.abs(B.x - A.x);
                const dy = Math.abs(B.y - A.y);
                if (dx > dy) {
                    const end = { x: B.x, y: A.y };
                    linePoints = interpolateLinePoints(A, end, maxGap);
                } else {
                    const end = { x: A.x, y: B.y };
                    linePoints = interpolateLinePoints(A, end, maxGap);
                }
            } else {
                linePoints = interpolateLinePoints(A, B, maxGap);
            }
            const newPoints = linePoints.map(p => ({ x: p.x, y: p.y, pressure: 0.5 }));
            currentStroke.type = 'pencil';
            currentStroke.points = newPoints;
            currentStroke.rawPoints = newPoints.slice();
            currentStroke.baseWidth = pencilWorldWidth;
            finalizeCurrentStroke();
            return true;
        } else {
            strokeModifiedByRecog = true;
            const bezierPoints = fitCubicBezierThroughThreePoints(A, C, B, maxGap);
            if (bezierPoints.length >= 2) {
                const newPoints = bezierPoints.map(p => ({ x: p.x, y: p.y, pressure: 0.5 }));
                currentStroke.type = 'pencil';
                currentStroke.points = newPoints;
                currentStroke.rawPoints = newPoints.slice();
                currentStroke.baseWidth = pencilWorldWidth;
            } else {
                strokeModifiedByRecog = false;
                return false;
            }
            finalizeCurrentStroke();
            return true;
        }
    }
    
    function movingAverageFilter(points, windowSize) {
        if (points.length < 2 || windowSize < 1) return points.slice();
        const result = [];
        const half = Math.floor(windowSize / 2);
        for (let i = 0; i < points.length; i++) {
            let sumX = 0, sumY = 0, sumP = 0, count = 0;
            for (let j = -half; j <= half; j++) {
                const idx = Math.min(Math.max(i + j, 0), points.length - 1);
                sumX += points[idx].x;
                sumY += points[idx].y;
                sumP += points[idx].pressure;
                count++;
            }
            result.push({ x: sumX / count, y: sumY / count, pressure: sumP / count });
        }
        return result;
    }
    
    function catmullRomInterpolate(p0, p1, p2, p3, stepWorld) {
        const dx = p2.x - p1.x, dy = p2.y - p1.y;
        const dist = Math.hypot(dx, dy);
        if (dist < 0.01) return [p2];
        const steps = Math.max(1, Math.ceil(dist / stepWorld));
        const points = [];
        for (let i = 0; i <= steps; i++) {
            const t = i / steps;
            const t2 = t * t;
            const t3 = t2 * t;
            const x = 0.5 * ((2 * p1.x) +
                (-p0.x + p2.x) * t +
                (2 * p0.x - 5 * p1.x + 4 * p2.x - p3.x) * t2 +
                (-p0.x + 3 * p1.x - 3 * p2.x + p3.x) * t3);
            const y = 0.5 * ((2 * p1.y) +
                (-p0.y + p2.y) * t +
                (2 * p0.y - 5 * p1.y + 4 * p2.y - p3.y) * t2 +
                (-p0.y + 3 * p1.y - 3 * p2.y + p3.y) * t3);
            // 压力也线性插值（基于t）
            const pressure = p1.pressure * (1 - t) + p2.pressure * t;
            points.push({ x, y, pressure });
        }
        return points;
    }
    
    function regenerateSmoothedPoints(rawPoints, smoothFactor) {
        if (!rawPoints || rawPoints.length === 0) return [];
        if (rawPoints.length === 1) return [rawPoints[0]];
        
        const windowSize = Math.max(1, Math.floor(1 + smoothFactor * 6));
        const stepWorld = Math.max(0.5, 1.5 - smoothFactor * 1.0);
        
        const filtered = movingAverageFilter(rawPoints, windowSize);
        const extended = [filtered[0], filtered[0], ...filtered, filtered[filtered.length-1], filtered[filtered.length-1]];
        const result = [];
        for (let i = 1; i < extended.length - 2; i++) {
            const p0 = extended[i-1];
            const p1 = extended[i];
            const p2 = extended[i+1];
            const p3 = extended[i+2];
            const segPoints = catmullRomInterpolate(p0, p1, p2, p3, stepWorld);
            if (i === 1) {
                result.push(...segPoints);
            } else {
                result.push(...segPoints.slice(1));
            }
        }
        if (result.length > 0 && rawPoints.length > 0) {
            result[0] = { ...rawPoints[0] };
            result[result.length-1] = { ...rawPoints[rawPoints.length-1] };
        }
        return result;
    }
    
    function worldToScreen(wx, wy) {
        const physicalX = (wx - offsetX) * scale * dpr;
        const physicalY = (wy - offsetY) * scale * dpr;
        return { x: physicalX, y: physicalY };
    }
    function screenToWorld(sx, sy) {
        const worldX = offsetX + sx / (scale * dpr);
        const worldY = offsetY + sy / (scale * dpr);
        return { x: worldX, y: worldY };
    }
    
    function drawSingleStrokeToContext(ctx, stroke) {
    if(stroke.type !== 'pencil') {
        // 橡皮擦原样绘制（固定宽度虚线）
        if(stroke.points.length < 2) return;
        ctx.save();
        ctx.beginPath();
        ctx.lineCap='round';
        ctx.lineJoin='round';
        ctx.lineWidth=stroke.worldWidth * scale;
        ctx.strokeStyle='rgba(100,116,139,0.4)';
        ctx.setLineDash([8, 6]);
        const first = worldToScreen(stroke.points[0].x, stroke.points[0].y);
        ctx.moveTo(first.x, first.y);
        for(let i=1;i<stroke.points.length;i++){
            const p = worldToScreen(stroke.points[i].x, stroke.points[i].y);
            ctx.lineTo(p.x, p.y);
        }
        ctx.stroke();
        ctx.setLineDash([]);
        ctx.restore();
        return;
    }
    
    // 铅笔：可变宽度，通过绘制圆形 + 四边形实现平滑连接
    const points = stroke.points;
    if (points.length < 2) return;
    const baseWidth = stroke.baseWidth;
    ctx.save();
    ctx.fillStyle = PENCIL_COLOR;
    
    // 获取屏幕坐标及半径
    const screenPoints = points.map(p => {
        const sp = worldToScreen(p.x, p.y);
        const r = getRadiusFromPoint(p, baseWidth) * scale;
        return { x: sp.x, y: sp.y, r };
    });
    
    // 辅助函数：计算两点间的外公切线四边形顶点（返回四个点）
    function getConnectingQuad(p0, p1) {
        const dx = p1.x - p0.x;
        const dy = p1.y - p0.y;
        const len = Math.hypot(dx, dy);
        if (len < 0.001) return null;
        const nx = dy / len;   // 单位法线（垂直于连线）
        const ny = -dx / len;
        // 两个圆的切点偏移
        const off0x = nx * p0.r;
        const off0y = ny * p0.r;
        const off1x = nx * p1.r;
        const off1y = ny * p1.r;
        return [
            { x: p0.x - off0x, y: p0.y - off0y },  // p0 左侧
            { x: p1.x - off1x, y: p1.y - off1y },  // p1 左侧
            { x: p1.x + off1x, y: p1.y + off1y },  // p1 右侧
            { x: p0.x + off0x, y: p0.y + off0y }   // p0 右侧
        ];
    }
    
    // 绘制所有线段之间的四边形
    for (let i = 0; i < screenPoints.length - 1; i++) {
        const quad = getConnectingQuad(screenPoints[i], screenPoints[i+1]);
        if (!quad) continue;
        ctx.beginPath();
        ctx.moveTo(quad[0].x, quad[0].y);
        ctx.lineTo(quad[1].x, quad[1].y);
        ctx.lineTo(quad[2].x, quad[2].y);
        ctx.lineTo(quad[3].x, quad[3].y);
        ctx.closePath();
        ctx.fill();
    }
    
    // 绘制每个点的圆形（保证端点圆润，并覆盖四边形连接处的微小缝隙）
    for (let i = 0; i < screenPoints.length; i++) {
        const p = screenPoints[i];
        ctx.beginPath();
        ctx.arc(p.x, p.y, p.r, 0, 2 * Math.PI);
        ctx.fill();
    }
    
    ctx.restore();
}
    
    function renderDrawing(dirtyRect) {
        if (!bgCacheValid) {
            rebuildBackgroundCache();
        }
        if (!dirtyRect) {
            drawCtx.clearRect(0, 0, canvasWidth, canvasHeight);
            drawCtx.drawImage(bgCanvas, 0, 0);
            drawCurrentStrokeToMain();
            for(let pin of pins) drawPin(drawCtx, pin);
            drawLassoSelection();
            drawSelectedHighlights();
            drawTransformControls();
            return;
        }
        const { x, y, w, h } = dirtyRect;
        drawCtx.clearRect(x, y, w, h);
        drawCtx.drawImage(bgCanvas, x, y, w, h, x, y, w, h);
        if (currentStroke && currentStroke.points && currentStroke.points.length >= 2) {
            const currentBounds = getStrokeScreenBounds(currentStroke);
            if (currentBounds && rectIntersect(currentBounds, dirtyRect)) {
                drawSingleStrokeToContext(drawCtx, currentStroke);
            }
        }
        for (let pin of pins) {
            const pinScreen = worldToScreen(pin.x, pin.y);
            const pinRect = { x: pinScreen.x - PIN_RADIUS_WORLD*scale, y: pinScreen.y - PIN_RADIUS_WORLD*scale, w: PIN_RADIUS_WORLD*scale*2, h: PIN_RADIUS_WORLD*scale*2 };
            if (rectIntersect(pinRect, dirtyRect)) {
                drawPin(drawCtx, pin);
            }
        }
        if (isLassoDrawing && lassoPoints.length >= 2) {
            drawLassoSelection();
        }
        drawSelectedHighlights();
        drawTransformControls();
    }
    
    function getStrokeScreenBounds(stroke) {
        if (!stroke.points.length) return null;
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (let p of stroke.points) {
            const sp = worldToScreen(p.x, p.y);
            const r = getRadiusFromPoint(p, stroke.baseWidth) * scale;
            minX = Math.min(minX, sp.x - r);
            minY = Math.min(minY, sp.y - r);
            maxX = Math.max(maxX, sp.x + r);
            maxY = Math.max(maxY, sp.y + r);
        }
        return { x: minX, y: minY, w: maxX - minX, h: maxY - minY };
    }
    
    function rectIntersect(r1, r2) {
        return !(r2.x > r1.x + r1.w || r2.x + r2.w < r1.x || r2.y > r1.y + r1.h || r2.y + r2.h < r1.y);
    }
    
    function drawSelectedHighlights() {
        if(selectedItems.size===0) return;
        drawCtx.save();
        const visibleRect = getVisibleWorldRect();
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idx=parseInt(item.slice(1));
                const stroke=strokes[idx];
                if(!stroke) continue;
                if (!isStrokeVisible(stroke, visibleRect)) continue;
                if(stroke.type === 'pencil') {
                    if(stroke.points.length>=2){
                        drawCtx.beginPath();
                        const first=worldToScreen(stroke.points[0].x,stroke.points[0].y);
                        drawCtx.moveTo(first.x,first.y);
                        for(let i=1;i<stroke.points.length;i++){
                            const p=worldToScreen(stroke.points[i].x,stroke.points[i].y);
                            drawCtx.lineTo(p.x,p.y);
                        }
                        drawCtx.lineWidth=3*scale;
                        drawCtx.strokeStyle='#3b82f6';
                        drawCtx.stroke();
                    }
                }
            } else if(item[0]==='p'){
                const idx=parseInt(item.slice(1));
                const pin=pins[idx];
                if(pin){
                    const cs=worldToScreen(pin.x,pin.y);
                    drawCtx.beginPath();
                    drawCtx.arc(cs.x,cs.y,PIN_RADIUS_WORLD*scale,0,2*Math.PI);
                    drawCtx.lineWidth=3*scale;
                    drawCtx.strokeStyle='#3b82f6';
                    drawCtx.stroke();
                }
            }
        }
        drawCtx.restore();
    }
    
    function applyMove(dx,dy){
        for(let item of selectedItems) {
            if(item[0]==='s'){
                const idx=parseInt(item.slice(1));
                const stroke=strokes[idx];
                if(stroke) {
                    for(let p of stroke.points){ p.x+=dx; p.y+=dy; }
                    updateStrokeBBox(stroke);
                }
            } else if(item[0]==='p'){
                const idx=parseInt(item.slice(1));
                const pin=pins[idx];
                if(pin){ pin.x+=dx; pin.y+=dy; }
            }
        }
        selectionLocalBounds.x+=dx; selectionLocalBounds.y+=dy;
        selectionCenter.x+=dx; selectionCenter.y+=dy;
        rebuildStrokeGrid();
        markCacheDirty();
        fullRepaint();
    }
    function applyRotate(delta){
        const cos=Math.cos(delta), sin=Math.sin(delta), cx=selectionCenter.x, cy=selectionCenter.y;
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idx=parseInt(item.slice(1));
                const stroke=strokes[idx];
                if(stroke) {
                    for(let p of stroke.points){
                        const dx=p.x-cx, dy=p.y-cy;
                        p.x=cx+dx*cos-dy*sin;
                        p.y=cy+dx*sin+dy*cos;
                    }
                    updateStrokeBBox(stroke);
                }
            } else if(item[0]==='p'){
                const idx=parseInt(item.slice(1));
                const pin=pins[idx];
                if(pin){
                    const dx=pin.x-cx, dy=pin.y-cy;
                    pin.x=cx+dx*cos-dy*sin;
                    pin.y=cy+dx*sin+dy*cos;
                }
            }
        }
        selectionRotation+=delta;
        selectionRotation=((selectionRotation%(2*Math.PI))+2*Math.PI)%(2*Math.PI);
        rebuildStrokeGrid();
        markCacheDirty();
        fullRepaint();
    }
    function applyCornerScale(fixed,factor){
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idx=parseInt(item.slice(1));
                const stroke=strokes[idx];
                if(stroke) {
                    for(let p of stroke.points){
                        p.x=fixed.x+(p.x-fixed.x)*factor;
                        p.y=fixed.y+(p.y-fixed.y)*factor;
                    }
                    updateStrokeBBox(stroke);
                }
            } else if(item[0]==='p'){
                const idx=parseInt(item.slice(1));
                const pin=pins[idx];
                if(pin){
                    pin.x=fixed.x+(pin.x-fixed.x)*factor;
                    pin.y=fixed.y+(pin.y-fixed.y)*factor;
                }
            }
        }
        recomputeSelectionBounds();
        rebuildStrokeGrid();
        markCacheDirty();
        fullRepaint();
    }
    function applyEdgeScale(fixed,axis,factor){
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idx=parseInt(item.slice(1));
                const stroke=strokes[idx];
                if(stroke) {
                    for(let p of stroke.points){
                        const dx=p.x-fixed.x, dy=p.y-fixed.y;
                        const dot=dx*axis.x+dy*axis.y;
                        const perpX=dx-dot*axis.x, perpY=dy-dot*axis.y;
                        const newDot=dot*factor;
                        p.x=fixed.x+newDot*axis.x+perpX;
                        p.y=fixed.y+newDot*axis.y+perpY;
                    }
                    updateStrokeBBox(stroke);
                }
            } else if(item[0]==='p'){
                const idx=parseInt(item.slice(1));
                const pin=pins[idx];
                if(pin){
                    const dx=pin.x-fixed.x, dy=pin.y-fixed.y;
                    const dot=dx*axis.x+dy*axis.y;
                    const perpX=dx-dot*axis.x, perpY=dy-dot*axis.y;
                    const newDot=dot*factor;
                    pin.x=fixed.x+newDot*axis.x+perpX;
                    pin.y=fixed.y+newDot*axis.y+perpY;
                }
            }
        }
        recomputeSelectionBounds();
        rebuildStrokeGrid();
        markCacheDirty();
        fullRepaint();
    }
    
    function isStrokeSelected(stroke, poly){
        if(stroke.type === 'pencil') {
            for(let p of stroke.points) if(pointInPolygon(p.x,p.y,poly)) return true;
            return false;
        }
        return false;
    }
    
    function pointInPolygon(px,py,poly){
        let inside=false;
        for(let i=0,j=poly.length-1;i<poly.length;j=i++){
            const xi=poly[i].x, yi=poly[i].y, xj=poly[j].x, yj=poly[j].y;
            const intersect=((yi>py)!=(yj>py)) && (px<(xj-xi)*(py-yi)/(yj-yi)+xi);
            if(intersect) inside=!inside;
        }
        return inside;
    }
    
    function recomputeSelectionBounds() {
        if(selectedItems.size===0){ selectionLocalBounds={x:0,y:0,w:0,h:0}; selectionCenter={x:0,y:0}; return; }
        let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity;
        for(let item of selectedItems){
            if(item[0]==='s'){ const idx=parseInt(item.slice(1)); const stroke=strokes[idx]; if(stroke) for(let p of stroke.points){ const r = getRadiusFromPoint(p, stroke.baseWidth); if(p.x-r<minX)minX=p.x-r; if(p.y-r<minY)minY=p.y-r; if(p.x+r>maxX)maxX=p.x+r; if(p.y+r>maxY)maxY=p.y+r;} }
            else if(item[0]==='p'){ const idx=parseInt(item.slice(1)); const pin=pins[idx]; if(pin){ const r=PIN_RADIUS_WORLD; minX=Math.min(minX,pin.x-r); minY=Math.min(minY,pin.y-r); maxX=Math.max(maxX,pin.x+r); maxY=Math.max(maxY,pin.y+r); } }
        }
        selectionLocalBounds={x:minX,y:minY,w:maxX-minX,h:maxY-minY}; selectionCenter={x:minX+(maxX-minX)/2,y:minY+(maxY-minY)/2};
    }
    
    function getRotatedCorners() { const cx=selectionCenter.x, cy=selectionCenter.y, halfW=selectionLocalBounds.w/2, halfH=selectionLocalBounds.h/2; const localCorners = [{x:-halfW,y:-halfH},{x: halfW,y:-halfH},{x: halfW,y: halfH},{x:-halfW,y: halfH}]; const cos=Math.cos(selectionRotation), sin=Math.sin(selectionRotation); return localCorners.map(p=>({ x:cx+p.x*cos-p.y*sin, y:cy+p.x*sin+p.y*cos })); }
    function getEdgeCenterWorld(edgeIdx) { const corners=getRotatedCorners(); const idx1=edgeIdx, idx2=(edgeIdx+1)%4; return { x:(corners[idx1].x+corners[idx2].x)/2, y:(corners[idx1].y+corners[idx2].y)/2 }; }
    function getRotateHandleWorld() { const topMid=getEdgeCenterWorld(0); const dir={x:topMid.x-selectionCenter.x, y:topMid.y-selectionCenter.y}; const len=Math.hypot(dir.x,dir.y); if(len===0) return topMid; const norm={x:dir.x/len, y:dir.y/len}; const offsetWorld = ROTATE_HANDLE_WORLD_SIZE + 16; return { x:topMid.x+norm.x*offsetWorld, y:topMid.y+norm.y*offsetWorld }; }
    function drawRotateIcon(ctx, worldSize) { ctx.save(); ctx.scale(worldSize/24,worldSize/24); ctx.translate(-12,-12); ctx.strokeStyle='#fff'; ctx.fillStyle='#fff'; ctx.lineWidth=2; ctx.lineCap='round'; ctx.lineJoin='round'; const p1=new Path2D("M21 12a9 9 0 0 0-9-9 9.75 9.75 0 0 0-6.74 2.74L3 8"); const p2=new Path2D("M3 3v5h5"); const p3=new Path2D("M3 12a9 9 0 0 0 9 9 9.75 9.75 0 0 0 6.74-2.74L21 16"); const p4=new Path2D("M16 16h5v5"); ctx.stroke(p1); ctx.stroke(p2); ctx.stroke(p3); ctx.stroke(p4); ctx.beginPath(); ctx.arc(12,12,1,0,2*Math.PI); ctx.fill(); ctx.restore(); }
    function hitTestTransformControls(screenX, screenY) { 
        if (selectedItems.size === 0) return null;
        const world = screenToWorld(screenX, screenY);
        const corners = getRotatedCorners();
        const hitRadiusScreen = 12;
        const hitRadiusWorld = hitRadiusScreen / scale;
        for (let i = 0; i < corners.length; i++) {
            const cw = corners[i];
            if (Math.hypot(world.x - cw.x, world.y - cw.y) <= hitRadiusWorld) return { type: 'corner', index: i };
        }
        for (let i = 0; i < 4; i++) {
            const edgeCenter = getEdgeCenterWorld(i);
            if (Math.hypot(world.x - edgeCenter.x, world.y - edgeCenter.y) <= hitRadiusWorld) return { type: 'edge', index: i };
        }
        const rotHandleWorld = getRotateHandleWorld();
        if (Math.hypot(world.x - rotHandleWorld.x, world.y - rotHandleWorld.y) <= hitRadiusWorld) return { type: 'rotate' };
        if (pointInPolygon(world.x, world.y, corners)) return { type: 'move' };
        return null;
    }
    function drawTransformControls() {
        if(selectedItems.size===0) return;
        const corners=getRotatedCorners();
        const screenCorners=corners.map(p=>worldToScreen(p.x,p.y));
        drawCtx.save();
        drawCtx.fillStyle='rgba(59,130,246,0.15)';
        drawCtx.strokeStyle='#3b82f6';
        drawCtx.lineWidth=BORDER_WORLD_WIDTH*scale;
        drawCtx.beginPath();
        drawCtx.moveTo(screenCorners[0].x,screenCorners[0].y);
        for(let i=1;i<4;i++) drawCtx.lineTo(screenCorners[i].x,screenCorners[i].y);
        drawCtx.closePath();
        drawCtx.fill();
        drawCtx.stroke();
        drawCtx.fillStyle='#3b82f6';
        for(let pt of screenCorners){ drawCtx.beginPath(); drawCtx.arc(pt.x, pt.y, CONTROL_POINT_WORLD_SIZE*scale, 0, 2*Math.PI); drawCtx.fill(); }
        for(let i=0;i<4;i++){ const edgeCenterWorld = getEdgeCenterWorld(i); const edgeScreen = worldToScreen(edgeCenterWorld.x, edgeCenterWorld.y); drawCtx.beginPath(); drawCtx.arc(edgeScreen.x, edgeScreen.y, CONTROL_POINT_WORLD_SIZE*scale, 0, 2*Math.PI); drawCtx.fill(); }
        const rotHandleWorld=getRotateHandleWorld();
        const rotScreen=worldToScreen(rotHandleWorld.x,rotHandleWorld.y);
        drawCtx.beginPath();
        drawCtx.arc(rotScreen.x,rotScreen.y, ROTATE_HANDLE_WORLD_SIZE*scale,0,2*Math.PI);
        drawCtx.fillStyle='#3b82f6';
        drawCtx.fill();
        drawCtx.save();
        drawCtx.translate(rotScreen.x,rotScreen.y);
        drawCtx.rotate(selectionRotation);
        drawRotateIcon(drawCtx, ROTATE_ICON_WORLD_SIZE * scale);
        drawCtx.restore();
        drawCtx.restore();
    }
    
    function startTransform(type, sx, sy, idx=0){
        isTransforming=true;
        transformType=type;
        transformStartMouseScreen={x:sx,y:sy};
        transformStartSelectedSnapshot = {
            strokes: [],
            pins: []
        };
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idxS = parseInt(item.slice(1));
                const st = strokes[idxS];
                if(st){
                    transformStartSelectedSnapshot.strokes.push({
                        index: idxS,
                        points: st.points.map(p=>({x:p.x,y:p.y,pressure:p.pressure}))
                    });
                }
            } else if(item[0]==='p'){
                const idxP = parseInt(item.slice(1));
                const pin = pins[idxP];
                if(pin){
                    transformStartSelectedSnapshot.pins.push({
                        index: idxP,
                        x: pin.x, y: pin.y
                    });
                }
            }
        }
        transformStartLocalBounds={...selectionLocalBounds};
        transformStartCenter={...selectionCenter};
        transformStartRotation=selectionRotation;
        if(type==='corner') transformStartCornerIdx=idx;
        if(type==='edge') transformStartEdgeIdx=idx;
    }
    function onTransformMove(sx,sy){
        if(!isTransforming) return;
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idxS = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.strokes.find(s=>s.index===idxS);
                if(orig){
                    strokes[idxS].points = orig.points.map(p=>({x:p.x,y:p.y,pressure:p.pressure}));
                    updateStrokeBBox(strokes[idxS]);
                }
            } else if(item[0]==='p'){
                const idxP = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.pins.find(p=>p.index===idxP);
                if(orig){
                    pins[idxP].x = orig.x;
                    pins[idxP].y = orig.y;
                }
            }
        }
        selectionLocalBounds={...transformStartLocalBounds};
        selectionCenter={...transformStartCenter};
        selectionRotation=transformStartRotation;
        
        if(transformType==='move'){
            const dx=(sx-transformStartMouseScreen.x)/scale, dy=(sy-transformStartMouseScreen.y)/scale;
            applyMove(dx,dy);
        } else if(transformType==='rotate'){
            const cs=worldToScreen(selectionCenter.x,selectionCenter.y);
            const sa=Math.atan2(transformStartMouseScreen.y-cs.y, transformStartMouseScreen.x-cs.x);
            const ca=Math.atan2(sy-cs.y, sx-cs.x);
            applyRotate(ca-sa);
        } else if(transformType==='corner'){
            const corners=getRotatedCorners();
            const fixed=corners[(transformStartCornerIdx+2)%4];
            const startMouse=screenToWorld(transformStartMouseScreen.x,transformStartMouseScreen.y);
            const curMouse=screenToWorld(sx,sy);
            const vecStart={x:corners[transformStartCornerIdx].x-fixed.x, y:corners[transformStartCornerIdx].y-fixed.y};
            const vecCur={x:curMouse.x-fixed.x, y:curMouse.y-fixed.y};
            const startLen=Math.hypot(vecStart.x,vecStart.y);
            const curLen=Math.hypot(vecCur.x,vecCur.y);
            const factor=startLen>0?curLen/startLen:1;
            applyCornerScale(fixed,factor);
        } else if(transformType==='edge'){
            const movingEdge=getEdgeCenterWorld(transformStartEdgeIdx);
            const fixedEdge=getEdgeCenterWorld((transformStartEdgeIdx+2)%4);
            const axis={x:movingEdge.x-fixedEdge.x, y:movingEdge.y-fixedEdge.y};
            const len=Math.hypot(axis.x,axis.y);
            if(len>0){ axis.x/=len; axis.y/=len; }
            const startMouse=screenToWorld(transformStartMouseScreen.x,transformStartMouseScreen.y);
            const curMouse=screenToWorld(sx,sy);
            const startProj=(startMouse.x-fixedEdge.x)*axis.x+(startMouse.y-fixedEdge.y)*axis.y;
            const curProj=(curMouse.x-fixedEdge.x)*axis.x+(curMouse.y-fixedEdge.y)*axis.y;
            const factor=startProj!==0?curProj/startProj:1;
            applyEdgeScale(fixedEdge,axis,factor);
        }
        fullRepaint();
        updatePinsListUI();
    }
    function endTransform(){
        if(!isTransforming) return;
        const strokeMods = [];
        const pinMods = [];
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idxS = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.strokes.find(s=>s.index===idxS);
                if(orig){
                    const currentPoints = strokes[idxS].points.map(p=>({x:p.x,y:p.y,pressure:p.pressure}));
                    if(JSON.stringify(orig.points) !== JSON.stringify(currentPoints)){
                        strokeMods.push({
                            index: idxS,
                            oldPoints: orig.points,
                            newPoints: currentPoints
                        });
                    }
                }
            } else if(item[0]==='p'){
                const idxP = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.pins.find(p=>p.index===idxP);
                if(orig){
                    const curPin = pins[idxP];
                    if(orig.x !== curPin.x || orig.y !== curPin.y){
                        pinMods.push({
                            index: idxP,
                            oldX: orig.x, oldY: orig.y,
                            newX: curPin.x, newY: curPin.y
                        });
                    }
                }
            }
        }
        const cmds = [];
        if(strokeMods.length) cmds.push(new ModifyStrokesCommand(strokeMods));
        if(pinMods.length) cmds.push(new ModifyPinsCommand(pinMods));
        if(cmds.length) executeCommand(new CompositeCommand(cmds));
        isTransforming = false;
        transformType = null;
        transformStartSelectedSnapshot = null;
        updatePinsListUI();
        updateBottomPanel();
    }
    
    function getSelectedItemsInsidePolygon(poly){ const items=[]; for(let i=0;i<strokes.length;i++) if(isStrokeSelected(strokes[i],poly)) items.push('s'+i); for(let i=0;i<pins.length;i++) if(pointInPolygon(pins[i].x,pins[i].y,poly)) items.push('p'+i); return items; }
    function updateSelectionWithModifier(newItems, mod){ if(mod==='add') for(let it of newItems) selectedItems.add(it); else if(mod==='subtract') for(let it of newItems) selectedItems.delete(it); else { selectedItems.clear(); for(let it of newItems) selectedItems.add(it); } if(selectedItems.size===0){ selectionLocalBounds={x:0,y:0,w:0,h:0}; selectionRotation=0; } else { recomputeSelectionBounds(); selectionRotation=0; } fullRepaint(); updateBottomPanel(); }
    function clearSelection(){ selectedItems.clear(); selectionLocalBounds={x:0,y:0,w:0,h:0}; selectionRotation=0; fullRepaint(); updateBottomPanel(); }
    function deleteSelected(){
        if(selectedItems.size===0) return;
        const toDeleteStrokes = [];
        const toDeletePins = [];
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idx = parseInt(item.slice(1));
                toDeleteStrokes.push({index: idx, stroke: JSON.parse(JSON.stringify(strokes[idx])), wasSelected: true});
            } else if(item[0]==='p'){
                const idx = parseInt(item.slice(1));
                toDeletePins.push({index: idx, pin: JSON.parse(JSON.stringify(pins[idx])), wasSelected: true});
            }
        }
        const cmds = [];
        if(toDeleteStrokes.length) cmds.push(new DeleteStrokesCommand(toDeleteStrokes));
        if(toDeletePins.length) cmds.push(new DeletePinsCommand(toDeletePins));
        if(cmds.length) executeCommand(new CompositeCommand(cmds));
        clearSelection();
        fullRepaint();
        updatePinsListUI();
        closeEditPanel();
        updateBottomPanel();
    }
    
    function drawLassoSelection(){ if(!isLassoDrawing||lassoPoints.length<2) return; drawCtx.save(); drawCtx.beginPath(); const first=worldToScreen(lassoPoints[0].x,lassoPoints[0].y); drawCtx.moveTo(first.x,first.y); for(let i=1;i<lassoPoints.length;i++){ const p=worldToScreen(lassoPoints[i].x,lassoPoints[i].y); drawCtx.lineTo(p.x,p.y); } drawCtx.closePath(); drawCtx.fillStyle='rgba(59,130,246,0.2)'; drawCtx.fill(); drawCtx.strokeStyle='#3b82f6'; drawCtx.lineWidth=2; drawCtx.setLineDash([6,6]); drawCtx.stroke(); drawCtx.setLineDash([]); drawCtx.restore(); }
    function drawPin(ctx, pin){ const centerScreen = worldToScreen(pin.x, pin.y); const radiusScreen = PIN_RADIUS_WORLD * scale; ctx.save(); ctx.shadowBlur = 8; ctx.shadowColor = "rgba(0,0,0,0.4)"; ctx.beginPath(); ctx.arc(centerScreen.x, centerScreen.y, radiusScreen, 0, 2*Math.PI); ctx.fillStyle = (currentEditingPinId === pin.id) ? "#3b82f6" : "#f1c40f"; ctx.fill(); ctx.restore(); }
    function drawCurrentStrokeToMain(){ if(currentStroke&&currentStroke.points&&currentStroke.points.length>=2) drawSingleStrokeToContext(drawCtx,currentStroke); }
    function fullRender(){ renderGrid(); fullRepaint(); }
    function renderGrid(){ gridCtx.clearRect(0,0,canvasWidth,canvasHeight); gridCtx.fillStyle='#f8f9fc'; gridCtx.fillRect(0,0,canvasWidth,canvasHeight); const topLeft=screenToWorld(0,0); const bottomRight=screenToWorld(canvasWidth,canvasHeight); const startX=Math.floor(topLeft.x/50)*50; const startY=Math.floor(topLeft.y/50)*50; const endX=bottomRight.x+50, endY=bottomRight.y+50; gridCtx.save(); gridCtx.strokeStyle='#d4dcec'; gridCtx.lineWidth=GRID_WORLD_WIDTH*scale; gridCtx.globalAlpha=0.7; for(let x=startX;x<=endX;x+=50){ const from=worldToScreen(x,topLeft.y); const to=worldToScreen(x,bottomRight.y); gridCtx.beginPath(); gridCtx.moveTo(from.x,from.y); gridCtx.lineTo(to.x,to.y); gridCtx.stroke(); } for(let y=startY;y<=endY;y+=50){ const from=worldToScreen(topLeft.x,y); const to=worldToScreen(bottomRight.x,y); gridCtx.beginPath(); gridCtx.moveTo(from.x,from.y); gridCtx.lineTo(to.x,to.y); gridCtx.stroke(); } gridCtx.restore(); }
    function focusOnPin(worldX, worldY) { offsetX=worldX-canvasWidth/(2*scale*dpr); offsetY=worldY-canvasHeight/(2*scale*dpr); markCacheDirty(); fullRender(); updateZoomDisplay(); }
    function getPinByWorldClick(worldX, worldY) { for(let i=0;i<pins.length;i++) if(Math.hypot(pins[i].x-worldX, pins[i].y-worldY)<=PIN_RADIUS_WORLD) return {idx:i, pin:pins[i]}; return null; }
    function updateBottomPanel() { 
        if (currentEditingPinId !== null) {
            const pin = pins.find(p => p.id === currentEditingPinId);
            if (pin) {
                bottomPanel.innerHTML = `<button class="bottom-action-btn" id="pinRenameBtn">✏️ 重命名</button><button class="bottom-action-btn" id="pinLevelBtn">📊 等级</button><button class="bottom-action-btn delete-btn" id="pinDeleteBtn">🗑️ 删除</button>`;
                bottomPanel.classList.add('show');
                const renameBtn = document.getElementById('pinRenameBtn');
                const levelBtn = document.getElementById('pinLevelBtn');
                const deleteBtn = document.getElementById('pinDeleteBtn');
                if (renameBtn) renameBtn.onclick = (e) => { e.stopPropagation(); showModalRename(pin); closeEditPanel(); };
                if (levelBtn) levelBtn.onclick = (e) => { e.stopPropagation(); showLevelMenu(levelBtn, currentEditingPinId); };
                if (deleteBtn) deleteBtn.onclick = (e) => { e.stopPropagation(); deleteCurrentPinAndClose(); };
                return;
            } else { currentEditingPinId = null; }
        }
        if (selectedItems.size > 0 && currentTool !== 'pin') {
            bottomPanel.innerHTML = `<button class="bottom-action-btn delete-btn" id="deleteSelectedBtn">🗑️ 删除选中</button>`;
            bottomPanel.classList.add('show');
            const delBtn = document.getElementById('deleteSelectedBtn');
            if (delBtn) delBtn.onclick = () => deleteSelected();
            return;
        }
        bottomPanel.classList.remove('show');
        bottomPanel.innerHTML = '';
    }
    function showModalRename(pin) { if (isNameModalActive) return; isNameModalActive = true; updateBottomPanel(); const mask = document.createElement('div'); mask.className = 'modal-mask'; document.body.appendChild(mask); modalMask = mask; const panel = document.createElement('div'); panel.className = 'pin-name-modal'; panel.innerHTML = `<input type="text" id="modalRenameInput" value="${escapeHtml(pin.name)}" maxlength="40" autocomplete="off" placeholder="输入图钉名称">`; document.body.appendChild(panel); modalPanel = panel; const input = panel.querySelector('#modalRenameInput'); input.focus(); input.select(); const closeModal = (save) => { if (!isNameModalActive) return; if (save) { const newName = input.value.trim(); if (newName !== "") { const oldPin = JSON.parse(JSON.stringify(pin)); pin.name = newName; const idx = pins.findIndex(p=>p.id===pin.id); if(idx!==-1) executeCommand(new UpdatePinCommand(idx, oldPin, pin)); updatePinsListUI(); fullRepaint(); } } mask.remove(); panel.remove(); modalMask = null; modalPanel = null; isNameModalActive = false; updateBottomPanel(); }; mask.onclick = () => closeModal(true); input.addEventListener('keypress', (e) => { if (e.key === 'Enter') { e.stopPropagation(); closeModal(true); } }); const escHandler = (e) => { if (e.key === 'Escape') { e.preventDefault(); closeModal(false); document.removeEventListener('keydown', escHandler); } }; document.addEventListener('keydown', escHandler); panel.addEventListener('click', (e) => e.stopPropagation()); }
    function openEditPanel(pinId) { const pin = pins.find(p=>p.id===pinId); if(!pin) return; if (isNameModalActive) return; currentEditingPinId = pinId; clearSelection(); updateBottomPanel(); justOpenedPanel = true; setTimeout(()=>{ justOpenedPanel = false; }, 200); fullRepaint(); }
    function showLevelMenu(btn, pinId) { if(currentLevelMenu) currentLevelMenu.remove(); const menu = document.createElement('div'); menu.className = 'level-menu'; const levels = [{ name: "一级", value: 0 },{ name: "二级", value: 1 },{ name: "三级", value: 2 }]; levels.forEach(lv => { const opt = document.createElement('div'); opt.className = 'level-option'; opt.textContent = lv.name; opt.onclick = (e) => { e.stopPropagation(); const pin = pins.find(p=>p.id===pinId); if(pin) { const oldPin = JSON.parse(JSON.stringify(pin)); pin.level = lv.value; const idx = pins.findIndex(p=>p.id===pinId); if(idx!==-1) executeCommand(new UpdatePinCommand(idx, oldPin, pin)); updatePinsListUI(); fullRepaint(); } menu.remove(); if(currentLevelMenu === menu) currentLevelMenu = null; }; menu.appendChild(opt); }); const rect = btn.getBoundingClientRect(); menu.style.left = `${rect.left}px`; menu.style.top = `${rect.bottom + 4}px`; document.body.appendChild(menu); currentLevelMenu = menu; const closeMenu = (e) => { if(menu && !menu.contains(e.target)) { menu.remove(); if(currentLevelMenu===menu) currentLevelMenu=null; document.removeEventListener('click', closeMenu); } }; setTimeout(()=> document.addEventListener('click', closeMenu), 10); }
    function deleteCurrentPinAndClose() { if(currentEditingPinId===null) return; const idx = pins.findIndex(p=>p.id===currentEditingPinId); if(idx!==-1) { const oldPin = JSON.parse(JSON.stringify(pins[idx])); executeCommand(new DeletePinsCommand([{index: idx, pin: oldPin, wasSelected: false}])); closeEditPanel(); clearSelection(); fullRepaint(); updatePinsListUI(); } }
    function closeEditPanel() { currentEditingPinId = null; updateBottomPanel(); fullRepaint(); }
    function placePin(worldX, worldY){ const newId = nextPinId++; const newPin = { id: newId, x: worldX, y: worldY, name: `图钉${newId}`, level: 0 }; executeCommand(new AddPinCommand(newPin, pins.length)); fullRepaint(); updatePinsListUI(); }
    function updatePinsListUI() { if(!pinListContainer) return; pinListContainer.innerHTML = ''; if(pins.length===0){ pinListContainer.innerHTML='<div class="empty-pins">暂无图钉<br>点击 📌 放置图钉</div>'; return; } pins.forEach(pin=>{ const div=document.createElement('div'); div.className='pin-item'; const info=document.createElement('div'); info.className='pin-info'; info.style.paddingLeft=`${pin.level*16}px`; info.innerHTML=`<span class="pin-icon">📌</span><span class="pin-name">${escapeHtml(pin.name)}</span><span class="pin-level-badge">${pin.level===0?'一级':(pin.level===1?'二级':'三级')}</span>`; div.appendChild(info); div.addEventListener('click',()=>focusOnPin(pin.x,pin.y)); pinListContainer.appendChild(div); }); }
    function escapeHtml(str){ return str.replace(/[&<>]/g, m=> m==='&'?'&amp;':m==='<'?'&lt;':'&gt;'); }
    
    function addPointWithSmoothingAndInterp(rawX, rawY, pressure) {
        if (!currentStroke) return;
        const raw = { x: rawX, y: rawY, pressure: Math.min(1, Math.max(0, pressure)) };
        currentStroke.rawPoints.push(raw);
        const newSmoothed = regenerateSmoothedPoints(currentStroke.rawPoints, smoothFactor);
        currentStroke.points = newSmoothed;
        if (currentStroke.points.length >= 2) {
            const bounds = getStrokeScreenBounds(currentStroke);
            if (bounds) addDirtyRect(bounds);
        }
        if (currentTool === 'pencil' && currentStroke && !strokeModifiedByRecog) {
            if (shapeRecogTimer) clearTimeout(shapeRecogTimer);
            shapeRecogTimer = setTimeout(() => { attemptStraightenStroke(); shapeRecogTimer = null; }, 300);
        }
    }
    
    function startStroke(worldX, worldY, toolType, width, pressure = 0.5) {
        if (shapeRecogTimer) { clearTimeout(shapeRecogTimer); shapeRecogTimer = null; }
        strokeModifiedByRecog = false;
        const rawPoint = { x: worldX, y: worldY, pressure: Math.min(1, Math.max(0, pressure)) };
        currentStroke = {
            type: toolType,
            baseWidth: width,   // 基准宽度（滑块值）
            rawPoints: [rawPoint],
            points: [rawPoint]
        };
        if (toolType === 'eraser') {
            currentStroke.worldWidth = width;   // 橡皮擦固定宽度
        }
        isDrawing = true;
        const bounds = getStrokeScreenBounds(currentStroke);
        if (bounds) addDirtyRect(bounds);
        drawingCanvas.style.cursor = 'none';
        updateCursorVisibility();
    }
    
    function startLasso(worldX,worldY,modifier){ lassoModifier=modifier; if(modifier==='replace') clearSelection(); isLassoDrawing=true; lassoPoints=[{x:worldX,y:worldY}]; fullRepaint(); updateCursorVisibility(); }
    function addLassoPoint(worldX,worldY){ if(!isLassoDrawing) return; lassoPoints.push({x:worldX,y:worldY}); fullRepaint(); }
    function finalizeLasso(){ if(lassoPoints.length<3){ isLassoDrawing=false; lassoPoints=[]; fullRepaint(); return; } const inside = getSelectedItemsInsidePolygon(lassoPoints); updateSelectionWithModifier(inside, lassoModifier); isLassoDrawing=false; lassoPoints=[]; fullRepaint(); }
    function getCurrentWorldWidth(){ return currentTool==='pencil'?pencilWorldWidth:(currentTool==='eraser'?eraserWorldWidth:4); }
    function updateBrushPanelUI(){ if(currentTool==='pencil'){ brushLabel.textContent='笔刷粗细'; brushSlider.value=pencilWorldWidth; brushValue.textContent=pencilWorldWidth; brushPanelEl.classList.remove('show'); } else if(currentTool==='eraser'){ brushLabel.textContent='橡皮粗细'; brushSlider.value=eraserWorldWidth; brushValue.textContent=eraserWorldWidth; brushPanelEl.classList.remove('show'); } else brushPanelEl.classList.remove('show'); }
    function setCurrentWorldWidthFromSlider(v){ const w=parseInt(v,10); if(currentTool==='pencil') pencilWorldWidth=w; else if(currentTool==='eraser') eraserWorldWidth=w; brushSlider.value=w; brushValue.textContent=w; updateCursorSize(); }
    function showBrushPanelRelativeToButton(btn){ if(!btn) return; const toolbarRect = document.querySelector('.toolbar').getBoundingClientRect(); const btnRect = btn.getBoundingClientRect(); brushPanelEl.style.left = (toolbarRect.right + 12) + 'px'; brushPanelEl.style.top = (btnRect.top + btnRect.height/2) + 'px'; brushPanelEl.style.transform = 'translateY(-50%)'; brushPanelEl.classList.add('show'); }
    function setTool(tool,showPanel=false,srcBtn=null){ if(tool===currentTool&&!showPanel) return; if(isNameModalActive) return; clearSelection(); if(isLassoDrawing){ isLassoDrawing=false; lassoPoints=[]; fullRepaint(); } closeEditPanel(); currentTool=tool; pencilBtn.classList.remove('active'); eraserBtn.classList.remove('active'); lassoBtn.classList.remove('active'); pinBtn.classList.remove('active','pin-active'); customCursor.classList.remove('pencil-mode','eraser-mode','lasso-mode','pin-mode'); if(tool==='pencil'){ pencilBtn.classList.add('active'); customCursor.classList.add('pencil-mode'); } else if(tool==='eraser'){ eraserBtn.classList.add('active'); customCursor.classList.add('eraser-mode'); } else if(tool==='lasso'){ lassoBtn.classList.add('active'); customCursor.classList.add('lasso-mode'); } else if(tool==='pin'){ pinBtn.classList.add('active','pin-active'); customCursor.classList.add('pin-mode'); } updateBrushPanelUI(); if(showPanel&&(tool==='pencil'||tool==='eraser')){ const btn=srcBtn||(tool==='pencil'?pencilBtn:eraserBtn); showBrushPanelRelativeToButton(btn); } else brushPanelEl.classList.remove('show'); updateCursorSize(); if(!isPanning&&!isDrawing&&!isLassoDrawing) updateCursorVisibility(); updateBottomPanel(); fullRepaint(); }
    function hideBrushPanel(){ brushPanelEl.classList.remove('show'); }
    function updateZoomDisplay(){ zoomSpan.textContent=`${Math.round(scale*100)}%`; }
    function panView(dx,dy){ 
        const dxWorld = dx / (scale * dpr);
        const dyWorld = dy / (scale * dpr);
        offsetX -= dxWorld;
        offsetY -= dyWorld;
        markCacheDirty();
        fullRender(); updateZoomDisplay(); updateCursorSize();
    }
    function zoomAtScreen(sx,sy,delta){
        let ns = scale * delta;
        ns = Math.min(Math.max(ns, MIN_SCALE), MAX_SCALE);
        if (ns === scale) return;
        const before = screenToWorld(sx, sy);
        scale = ns;
        offsetX = before.x - sx / (scale * dpr);
        offsetY = before.y - sy / (scale * dpr);
        markCacheDirty();
        fullRender();
        updateZoomDisplay();
        updateCursorSize();
    }
    function maintainCenterOnResize(){
        const prevCenter = screenToWorld(canvasWidth/2, canvasHeight/2);
        canvasWidth = window.innerWidth * dpr;
        canvasHeight = window.innerHeight * dpr;
        gridCanvas.width = canvasWidth;
        gridCanvas.height = canvasHeight;
        drawingCanvas.width = canvasWidth;
        drawingCanvas.height = canvasHeight;
        bgCanvas.width = canvasWidth;
        bgCanvas.height = canvasHeight;
        bgCtx = bgCanvas.getContext('2d');
        gridCanvas.style.width = window.innerWidth + 'px';
        gridCanvas.style.height = window.innerHeight + 'px';
        drawingCanvas.style.width = window.innerWidth + 'px';
        drawingCanvas.style.height = window.innerHeight + 'px';
        offsetX = prevCenter.x - canvasWidth/(2 * scale * dpr);
        offsetY = prevCenter.y - canvasHeight/(2 * scale * dpr);
        markCacheDirty();
        fullRender();
    }
    function updateCursorSize(){ if(currentTool==='lasso'){ customCursor.style.width='24px'; customCursor.style.height='24px'; return; } if(currentTool==='pin'){ customCursor.style.width='28px'; customCursor.style.height='28px'; return; } const w=getCurrentWorldWidth(); const d=Math.max(8,w*scale); customCursor.style.width=`${d}px`; customCursor.style.height=`${d}px`; }
    function saveCanvas(){ 
        const saveStrokes = strokes.filter(s => s.type !== 'eraser');
        const data={
            version:"2.1",  // 版本升级，支持压力
            view:{offsetX,offsetY,scale},
            strokes:saveStrokes.map(s=>({
                type:s.type,
                baseWidth:s.baseWidth,
                points:s.points.map(p=>({x:p.x,y:p.y,pressure:p.pressure}))
            })),
            pins:pins.map(p=>({id:p.id,x:p.x,y:p.y,name:p.name,level:p.level}))
        };
        const json=JSON.stringify(data,null,2); const blob=new Blob([json],{type:"application/json"}); const url=URL.createObjectURL(blob); const a=document.createElement('a'); a.href=url; a.download=`canvas_${new Date().toISOString().slice(0,19).replace(/:/g,'-')}.infcanvas`; document.body.appendChild(a); a.click(); document.body.removeChild(a); URL.revokeObjectURL(url); 
    }
    function importCanvas(file){ 
        const reader=new FileReader(); 
        reader.onload=e=>{ 
            try{ 
                const data=JSON.parse(e.target.result); 
                let newStrokes = [], newPins = []; 
                if(data.strokes && Array.isArray(data.strokes)) newStrokes=data.strokes.filter(s=>s.type==='pencil'||s.type==='pointcloud').map(s=>{ 
                    const points = s.points.map(p=>{
                        let pressure = (p.pressure !== undefined) ? p.pressure : 0.5;
                        return { x:p.x, y:p.y, pressure };
                    });
                    const st={
                        type:(s.type==='pointcloud'?'pencil':s.type),
                        baseWidth: s.baseWidth !== undefined ? s.baseWidth : (s.worldWidth || 4),
                        points: points
                    };
                    updateStrokeBBox(st);
                    return st;
                });
                if(data.pins && Array.isArray(data.pins)) newPins=data.pins.map(p=>({id:p.id??(nextPinId++),x:p.x,y:p.y,name:p.name??`图钉${p.id}`,level:p.level??0}));
                let newOffsetX=offsetX, newOffsetY=offsetY, newScale=scale;
                if(data.view){ newOffsetX=data.view.offsetX??offsetX; newOffsetY=data.view.offsetY??offsetY; let ns=data.view.scale??scale; ns=Math.min(Math.max(ns,MIN_SCALE),MAX_SCALE); newScale=ns; }
                const cmd = new ReplaceAllCommand(strokes, pins, newStrokes, newPins);
                executeCommand(cmd);
                offsetX = newOffsetX; offsetY = newOffsetY; scale = newScale;
                if(currentStroke){ currentStroke=null; isDrawing=false; }
                markCacheDirty();
                clearSelection();
                fullRender();
                updateZoomDisplay();
                updateCursorSize();
                updatePinsListUI();
            }catch(err){ alert("导入失败"); } 
        }; reader.readAsText(file); 
    }
    function triggerImport(){ fileInput.click(); }
    function onFileSelected(e){ const file=e.target.files[0]; if(file) importCanvas(file); fileInput.value=''; }
    function updateCursorVisibility(){ if(isNameModalActive){ customCursor.style.display='none'; return; } if(isDrawing||isPanning||isLassoDrawing||isTransforming){ customCursor.style.display='block'; return; } const hover=document.elementFromPoint(lastMouseScreenX/dpr, lastMouseScreenY/dpr); const uiElements=[document.querySelector('.toolbar'), brushPanelEl, document.querySelector('.smooth-container'), document.querySelector('.panel'), bottomPanel]; let onUI=false; for(let ui of uiElements) if(ui&&ui.contains(hover)){ onUI=true; break; } customCursor.style.display=onUI?'none':'block'; }
    function moveCursor(sx,sy){ if(isNameModalActive) return; customCursor.style.left=`${sx/dpr}px`; customCursor.style.top=`${sy/dpr}px`; }
    function onGlobalMouseMove(e){ 
        lastMouseScreenX = e.clientX * dpr;
        lastMouseScreenY = e.clientY * dpr;
        updateCursorVisibility(); 
    }
    function updateSmoothUI(){ const p=Math.round(smoothFactor*100); smoothTrigger.textContent=`防抖 ${p}%`; document.querySelectorAll('.smooth-option').forEach(opt=>{ const val=parseFloat(opt.dataset.value); if(Math.abs(val-smoothFactor)<0.01) opt.classList.add('selected'); else opt.classList.remove('selected'); }); }
    function setSmoothFactor(v){ smoothFactor=v; updateSmoothUI(); smoothDropdown.classList.remove('show'); }
    function toggleDropdown(e){ e.stopPropagation(); smoothDropdown.classList.toggle('show'); }
    function onOptionClick(e){ setSmoothFactor(parseFloat(e.currentTarget.dataset.value)); }
    function closeDropdownOnOutside(e){ if(!smoothDropdown.contains(e.target)&&e.target!==smoothTrigger) smoothDropdown.classList.remove('show'); }
    function handleDocumentClick(e){ if(brushPanelEl.classList.contains('show')){ const inside=brushPanelEl.contains(e.target); const isPencil=pencilBtn.contains(e.target); const isEraser=eraserBtn.contains(e.target); if(!inside&&!isPencil&&!isEraser) hideBrushPanel(); } if(!bottomPanel.contains(e.target) && !(currentTool==='pin' && e.target.closest('.pin-item')) && !justOpenedPanel) closeEditPanel(); }
    let pointerDownScreen=null, coordsCache=null;
    function getCanvasCoordsFromEvent(e,rect){
        const cssX = e.clientX - rect.left;
        const cssY = e.clientY - rect.top;
        if (cssX < 0 || cssX > window.innerWidth || cssY < 0 || cssY > window.innerHeight) return null;
        return { x: cssX * dpr, y: cssY * dpr };
    }
    function onPointerDown(e){ 
        if(isNameModalActive) return; 
        e.preventDefault(); 
        drawingCanvas.setPointerCapture(e.pointerId); 
        const rect=drawingCanvas.getBoundingClientRect(); 
        const coords=getCanvasCoordsFromEvent(e,rect); 
        if(!coords) return; 
        const {x:sx,y:sy}=coords; 
        lastMouseScreenX=sx; lastMouseScreenY=sy; 
        pointerDownScreen={x:sx,y:sy}; 
        const world=screenToWorld(sx,sy); 
        if((spacePressed&&e.button===0)||e.button===2){ 
            if(isDrawing) finalizeCurrentStroke(); 
            if(isLassoDrawing) finalizeLasso(); 
            cancelTransform(); 
            isPanning=true; 
            activePointerId=e.pointerId; 
            lastPanX=sx; lastPanY=sy; 
            drawingCanvas.style.cursor='grabbing'; 
            updateCursorVisibility(); 
            return; 
        } 
        if(currentTool==='lasso'){ 
            const hit = hitTestTransformControls(sx, sy); 
            if(hit && selectedItems.size>0){ 
                if(hit.type==='move') startTransform('move',sx,sy); 
                else if(hit.type==='corner') startTransform('corner',sx,sy,hit.index); 
                else if(hit.type==='edge') startTransform('edge',sx,sy,hit.index); 
                else if(hit.type==='rotate') startTransform('rotate',sx,sy); 
                activePointerId=e.pointerId; 
                return; 
            } 
            let mod='replace'; 
            if(e.shiftKey) mod='add'; 
            else if(e.altKey) mod='subtract'; 
            startLasso(world.x,world.y,mod); 
            activePointerId=e.pointerId; 
            return; 
        } 
        if(currentTool==='pin'){ 
            const wasPanelOpen = bottomPanel.classList.contains('show') && currentEditingPinId !== null; 
            let clickedPin = getPinByWorldClick(world.x, world.y); 
            if(wasPanelOpen){ 
                const wasEditingId = currentEditingPinId; 
                closeEditPanel(); 
                if(clickedPin && clickedPin.pin.id === wasEditingId) return; 
            } 
            if(clickedPin){ 
                openEditPanel(clickedPin.pin.id); 
                return; 
            } 
            if(!wasPanelOpen) placePin(world.x, world.y); 
            return; 
        } 
        if(e.button===0&&!isPanning){ 
            if(isDrawing) return; 
            if(isLassoDrawing) finalizeLasso(); 
            cancelTransform(); 
            const pressure = e.pressure !== undefined ? e.pressure : 0.5;
            startStroke(world.x,world.y,currentTool,getCurrentWorldWidth(), pressure); 
            activePointerId=e.pointerId; 
        } 
    }
    function onPointerMove(e){ 
        if(isNameModalActive) return; 
        const rect=drawingCanvas.getBoundingClientRect(); 
        const coords=getCanvasCoordsFromEvent(e,rect); 
        if(coords){ 
            lastMouseScreenX=coords.x; lastMouseScreenY=coords.y; 
            coordsCache=coords; 
        } 
        if(isPanning&&activePointerId===e.pointerId&&coords){ 
            const dx=coords.x-lastPanX, dy=coords.y-lastPanY; 
            if(dx!==0||dy!==0) panView(dx,dy); 
            lastPanX=coords.x; lastPanY=coords.y; 
            if(coords) moveCursor(coords.x,coords.y); 
            return; 
        } 
        if(isTransforming&&activePointerId===e.pointerId&&coords){ 
            onTransformMove(coords.x,coords.y); 
            return; 
        } 
        if(coords){ 
            moveCursor(coords.x,coords.y); 
            if(!isDrawing&&!isPanning&&!isLassoDrawing&&!isTransforming) updateCursorVisibility(); 
        } 
        if(isDrawing&&activePointerId===e.pointerId&&currentStroke&&coords){ 
            const w=screenToWorld(coords.x,coords.y); 
            const pressure = e.pressure !== undefined ? e.pressure : 0.5;
            addPointWithSmoothingAndInterp(w.x,w.y, pressure); 
        } 
        if(isLassoDrawing&&activePointerId===e.pointerId&&coords){ 
            const w=screenToWorld(coords.x,coords.y); 
            addLassoPoint(w.x,w.y); 
        } 
    }
    function onPointerUp(e){ 
        if(isNameModalActive) return; 
        e.preventDefault(); 
        drawingCanvas.releasePointerCapture(e.pointerId); 
        if(shapeRecogTimer){ clearTimeout(shapeRecogTimer); shapeRecogTimer=null; } 
        if(isPanning&&activePointerId===e.pointerId){ 
            isPanning=false; 
            activePointerId=null; 
            drawingCanvas.style.cursor='none'; 
            updateCursorVisibility(); 
            return; 
        } 
        if(isTransforming&&activePointerId===e.pointerId){ 
            endTransform(); 
            activePointerId=null; 
            drawingCanvas.style.cursor='none'; 
            updateCursorVisibility(); 
            return; 
        } 
        if(isDrawing&&activePointerId===e.pointerId){ 
            finalizeCurrentStroke(); 
            activePointerId=null; 
            isDrawing=false; 
            updateCursorVisibility(); 
            return; 
        } 
        if(isLassoDrawing&&activePointerId===e.pointerId){ 
            finalizeLasso(); 
            activePointerId=null; 
            isLassoDrawing=false; 
            updateCursorVisibility(); 
            return; 
        } 
        if(currentTool==='lasso'&&!isLassoDrawing&&!isTransforming&&pointerDownScreen&&coordsCache){ 
            const dx=coordsCache.x-pointerDownScreen.x, dy=coordsCache.y-pointerDownScreen.y; 
            if(Math.hypot(dx,dy)<5) clearSelection(); 
        } 
        pointerDownScreen=null; coordsCache=null; 
    }
    function onPointerCancel(e){ 
        if(isNameModalActive) return; 
        if(shapeRecogTimer){ clearTimeout(shapeRecogTimer); shapeRecogTimer=null; } 
        if(isDrawing&&activePointerId===e.pointerId) finalizeCurrentStroke(); 
        if(isLassoDrawing&&activePointerId===e.pointerId) finalizeLasso(); 
        if(isPanning&&activePointerId===e.pointerId) isPanning=false; 
        if(isTransforming&&activePointerId===e.pointerId) cancelTransform(); 
        activePointerId=null; 
        pointerDownScreen=null; 
        coordsCache=null; 
    }
    function cancelTransform(){ if(isTransforming && transformStartSelectedSnapshot){
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idxS = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.strokes.find(s=>s.index===idxS);
                if(orig){
                    strokes[idxS].points = orig.points.map(p=>({x:p.x,y:p.y,pressure:p.pressure}));
                    updateStrokeBBox(strokes[idxS]);
                }
            } else if(item[0]==='p'){
                const idxP = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.pins.find(p=>p.index===idxP);
                if(orig){
                    pins[idxP].x = orig.x;
                    pins[idxP].y = orig.y;
                }
            }
        }
        selectionLocalBounds={...transformStartLocalBounds};
        selectionCenter={...transformStartCenter};
        selectionRotation=transformStartRotation;
        markCacheDirty();
        fullRepaint();
        isTransforming=false;
        transformStartSelectedSnapshot=null;
        updatePinsListUI();
    } }
    function onWheel(e){ if(isNameModalActive) return; e.preventDefault(); const rect=drawingCanvas.getBoundingClientRect(); const cssX = e.clientX - rect.left, cssY = e.clientY - rect.top; if(cssX >=0 && cssX <= window.innerWidth && cssY >=0 && cssY <= window.innerHeight){
        const mx = cssX * dpr, my = cssY * dpr;
        lastMouseScreenX = mx; lastMouseScreenY = my;
        const delta = e.deltaY > 0 ? 0.9 : 1.1;
        zoomAtScreen(mx, my, delta);
        if(!isPanning && !isDrawing && !isLassoDrawing && !isTransforming){
            moveCursor(mx, my);
            updateCursorVisibility();
        }
    } }
    function onKeyDown(e){ 
        if(isNameModalActive){ if(e.code==='Escape' && modalMask) modalMask.click(); return; }
        if(e.code === 'ShiftLeft' || e.code === 'ShiftRight') { shiftPressed = true; return; }
        if(e.code==='Space'){ e.preventDefault(); if(!spacePressed){ spacePressed=true; if(isDrawing) finalizeCurrentStroke(); if(isLassoDrawing) finalizeLasso(); if(!isPanning) drawingCanvas.style.cursor='grab'; updateCursorVisibility(); } return; }
        if(e.code==='KeyQ'){ e.preventDefault(); setTool('pencil',false); return; }
        if(e.code==='KeyE'){ e.preventDefault(); setTool('eraser',false); return; }
        if(e.code==='KeyL'){ e.preventDefault(); setTool('lasso',false); return; }
        if(e.code==='KeyP'){ e.preventDefault(); setTool('pin',false); return; }
        if(e.ctrlKey&&e.code==='KeyZ'){ e.preventDefault(); undo(); return; }
        if(e.ctrlKey&&e.code==='KeyY'){ e.preventDefault(); redo(); return; }
        if(e.code==='Delete'||e.code==='Backspace'){ if(selectedItems.size>0){ e.preventDefault(); deleteSelected(); } }
        if(e.code==='Escape'){ clearSelection(); if(isLassoDrawing){ isLassoDrawing=false; lassoPoints=[]; fullRepaint(); } closeEditPanel(); }
    }
    function onKeyUp(e){ 
        if(isNameModalActive) return;
        if(e.code === 'ShiftLeft' || e.code === 'ShiftRight') { shiftPressed = false; return; }
        if(e.code==='Space'){ e.preventDefault(); spacePressed=false; if(isPanning) isPanning=false; if(!isPanning&&!isDrawing&&!isLassoDrawing&&!isTransforming) drawingCanvas.style.cursor='none'; updateCursorVisibility(); }
    }
    function disableContextMenu(e){ e.preventDefault(); return false; }
    function onMouseLeaveCanvas(){ if(!isNameModalActive) customCursor.style.display='none'; }
    function onMouseEnterCanvas(e){ if(isNameModalActive) return; if(!isPanning&&!isDrawing&&!isLassoDrawing&&!isTransforming){ const rect=drawingCanvas.getBoundingClientRect(); const cssX=e.clientX-rect.left, cssY=e.clientY-rect.top; if(cssX>=0 && cssX<=window.innerWidth && cssY>=0 && cssY<=window.innerHeight){ const sx=cssX*dpr, sy=cssY*dpr; lastMouseScreenX=sx; lastMouseScreenY=sy; moveCursor(sx,sy); updateCursorVisibility(); } } }
    
    function finalizeCurrentStroke(){
        if(!currentStroke) return;
        if (shapeRecogTimer) {
            clearTimeout(shapeRecogTimer);
            shapeRecogTimer = null;
        }
        if(currentStroke.type === 'eraser') {
            const changes = collectEraserChanges(currentStroke);
            if(changes.toDelete.length) {
                const cmd = new DeleteStrokesCommand(changes.toDelete);
                executeCommand(cmd);
            }
            currentStroke = null;
            isDrawing = false;
            fullRepaint();
            updateCursorVisibility();
            strokeModifiedByRecog = false;
            return;
        }
        if(currentStroke.points.length >= 2){
            const newStroke = {
                type: currentStroke.type,
                baseWidth: currentStroke.baseWidth,
                points: currentStroke.points.slice()
            };
            updateStrokeBBox(newStroke);
            strokes.push(newStroke);
            addStrokeToGrid(strokes.length-1);
            if (!bgCacheValid) {
                rebuildBackgroundCache();
            } else {
                const boundsWorld = newStroke.bbox;
                const topLeft = worldToScreen(boundsWorld.minX, boundsWorld.minY);
                const bottomRight = worldToScreen(boundsWorld.maxX, boundsWorld.maxY);
                const dirtyRect = { x: topLeft.x, y: topLeft.y, w: bottomRight.x - topLeft.x, h: bottomRight.y - topLeft.y };
                if (dirtyRect.w > 0 && dirtyRect.h > 0) {
                    bgCtx.save();
                    bgCtx.beginPath();
                    bgCtx.rect(dirtyRect.x, dirtyRect.y, dirtyRect.w, dirtyRect.h);
                    bgCtx.clip();
                    drawSingleStrokeToContext(bgCtx, newStroke);
                    bgCtx.restore();
                    addDirtyRect(dirtyRect);
                } else {
                    bgCacheValid = false;
                    fullRepaint();
                }
            }
            const cmd = new AddStrokeCommand(newStroke, strokes.length-1, true);
            executeCommand(cmd);
        }
        currentStroke = null;
        isDrawing = false;
        updateCursorVisibility();
        strokeModifiedByRecog = false;
    }
    
    function init(){
        dpr = window.devicePixelRatio || 1;
        canvasWidth = window.innerWidth * dpr;
        canvasHeight = window.innerHeight * dpr;
        gridCanvas.width = canvasWidth; gridCanvas.height = canvasHeight;
        drawingCanvas.width = canvasWidth; drawingCanvas.height = canvasHeight;
        bgCanvas = document.createElement('canvas');
        bgCanvas.width = canvasWidth;
        bgCanvas.height = canvasHeight;
        bgCtx = bgCanvas.getContext('2d');
        gridCanvas.style.width = window.innerWidth + 'px';
        gridCanvas.style.height = window.innerHeight + 'px';
        drawingCanvas.style.width = window.innerWidth + 'px';
        drawingCanvas.style.height = window.innerHeight + 'px';
        offsetX = -canvasWidth/(2 * scale * dpr) - 80;
        offsetY = -canvasHeight/(2 * scale * dpr) - 60;
        markCacheDirty();
        fullRender(); updateZoomDisplay();
        setTool('pencil',false);
        updateCursorSize(); updateSmoothUI();
        updatePinsListUI();
        
        const savedCollapsed = localStorage.getItem('panelCollapsed');
        if (savedCollapsed === 'true') {
            pinPanel.classList.add('collapsed');
            panelToggle.textContent = '▶';
        } else {
            panelToggle.textContent = '◀';
        }
        panelToggle.addEventListener('click', (e) => {
            e.stopPropagation();
            pinPanel.classList.toggle('collapsed');
            const isCollapsed = pinPanel.classList.contains('collapsed');
            panelToggle.textContent = isCollapsed ? '▶' : '◀';
            localStorage.setItem('panelCollapsed', isCollapsed);
        });
        
        window.addEventListener('mousemove',onGlobalMouseMove);
        brushSlider.addEventListener('input',e=>setCurrentWorldWidthFromSlider(e.target.value));
        pencilBtn.addEventListener('click',e=>setTool('pencil',true,pencilBtn));
        eraserBtn.addEventListener('click',e=>setTool('eraser',true,eraserBtn));
        lassoBtn.addEventListener('click',e=>setTool('lasso',false));
        pinBtn.addEventListener('click',e=>setTool('pin',false));
        saveBtn.addEventListener('click',saveCanvas);
        importBtn.addEventListener('click',triggerImport);
        fileInput.addEventListener('change',onFileSelected);
        smoothTrigger.addEventListener('click',toggleDropdown);
        document.querySelectorAll('.smooth-option').forEach(opt=>opt.addEventListener('click',onOptionClick));
        document.addEventListener('click',closeDropdownOnOutside);
        drawingCanvas.addEventListener('pointerdown',onPointerDown);
        drawingCanvas.addEventListener('pointermove',onPointerMove);
        drawingCanvas.addEventListener('pointerup',onPointerUp);
        drawingCanvas.addEventListener('pointercancel',onPointerCancel);
        drawingCanvas.addEventListener('wheel',onWheel,{passive:false});
        drawingCanvas.addEventListener('contextmenu',disableContextMenu);
        drawingCanvas.addEventListener('mouseleave',onMouseLeaveCanvas);
        drawingCanvas.addEventListener('mouseenter',onMouseEnterCanvas);
        window.addEventListener('keydown',onKeyDown);
        window.addEventListener('keyup',onKeyUp);
        window.addEventListener('resize',()=>maintainCenterOnResize());
        window.addEventListener('mouseup',()=>{ if(isDrawing) finalizeCurrentStroke(); if(isLassoDrawing) finalizeLasso(); if(isTransforming) endTransform(); if(isPanning){ isPanning=false; drawingCanvas.style.cursor='none'; updateCursorVisibility(); } });
        document.addEventListener('click',handleDocumentClick);
        rebuildStrokeGrid();
    }
    init();
})();