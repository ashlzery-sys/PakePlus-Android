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
    let transformHistoryDirtyScreenRect = null;
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
    
    // 复制剪贴板
    let copyBuffer = { strokes: [], pins: [] };
    
    let isZooming = false;
    let zoomEndTimer = null;
    function scheduleZoomEnd() {
        if (zoomEndTimer) clearTimeout(zoomEndTimer);
        isZooming = true;
        zoomEndTimer = setTimeout(() => {
            isZooming = false;
            addDirtyRectForSelectionAndControls();
            flushRendering();
        }, 120);
    }
    
    const GRID_CELL_SIZE = 100;
    let strokeGrid = new Map();
    
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
        let x = Math.floor(topLeft.x - 2);
        let y = Math.floor(topLeft.y - 2);
        let w = Math.ceil(bottomRight.x - topLeft.x + 4);
        let h = Math.ceil(bottomRight.y - topLeft.y + 4);
        if (w > 0 && h > 0) {
            addDirtyRect({ x, y, w, h });
        }
    }
    
    function addDirtyRectFromStroke(stroke, marginWorld = 10) {
        if (!stroke.bbox) updateStrokeBBox(stroke);
        const b = stroke.bbox;
        addDirtyRectFromWorld(b.minX - marginWorld, b.minY - marginWorld, b.maxX - b.minX + marginWorld*2, b.maxY - b.minY + marginWorld*2);
    }
    
    function getWorldRectFromStrokes(strokesList) {
        if (!strokesList || strokesList.length === 0) return null;
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (let item of strokesList) {
            const stroke = item.stroke;
            if (!stroke.bbox) updateStrokeBBox(stroke);
            const b = stroke.bbox;
            minX = Math.min(minX, b.minX);
            minY = Math.min(minY, b.minY);
            maxX = Math.max(maxX, b.maxX);
            maxY = Math.max(maxY, b.maxY);
        }
        if (minX === Infinity) return null;
        return { minX, minY, maxX, maxY };
    }
    
    function addDirtyRectForPin(pin, marginWorld = 10) {
        if (!pin) return;
        const r = PIN_RADIUS_WORLD + marginWorld;
        addDirtyRectFromWorld(pin.x - r, pin.y - r, r * 2, r * 2);
    }
    
    function addDirtyRectForSelectionAndControls() {
    if (selectedItems.size === 0) return;
    const SHADOW_EXTRA = 10; // 屏幕像素，包裹阴影模糊范围
    let screenMinX = Infinity, screenMinY = Infinity, screenMaxX = -Infinity, screenMaxY = -Infinity;
    
    for (let item of selectedItems) {
        if (item[0] === 's') {
            const idx = parseInt(item.slice(1));
            const stroke = strokes[idx];
            if (!stroke || stroke.type !== 'pencil') continue;
            if (!stroke.points.length) continue;
            const radius = stroke.worldWidth * scale;
            for (let p of stroke.points) {
                const sp = worldToScreen(p.x, p.y);
                screenMinX = Math.min(screenMinX, sp.x - radius);
                screenMinY = Math.min(screenMinY, sp.y - radius);
                screenMaxX = Math.max(screenMaxX, sp.x + radius);
                screenMaxY = Math.max(screenMaxY, sp.y + radius);
            }
        } else if (item[0] === 'p') {
            const idx = parseInt(item.slice(1));
            const pin = pins[idx];
            if (pin) {
                const center = worldToScreen(pin.x, pin.y);
                const r = PIN_RADIUS_WORLD * scale;
                screenMinX = Math.min(screenMinX, center.x - r);
                screenMinY = Math.min(screenMinY, center.y - r);
                screenMaxX = Math.max(screenMaxX, center.x + r);
                screenMaxY = Math.max(screenMaxY, center.y + r);
            }
        }
    }
    
    if (selectedItems.size > 0) {
        const corners = getRotatedCorners();
        for (let c of corners) {
            const sp = worldToScreen(c.x, c.y);
            // 增加阴影安全边距
            const r = CONTROL_POINT_WORLD_SIZE * scale + SHADOW_EXTRA;
            screenMinX = Math.min(screenMinX, sp.x - r);
            screenMinY = Math.min(screenMinY, sp.y - r);
            screenMaxX = Math.max(screenMaxX, sp.x + r);
            screenMaxY = Math.max(screenMaxY, sp.y + r);
        }
        for (let i = 0; i < 4; i++) {
            const edgeCenterWorld = getEdgeCenterWorld(i);
            const sp = worldToScreen(edgeCenterWorld.x, edgeCenterWorld.y);
            const r = CONTROL_POINT_WORLD_SIZE * scale + SHADOW_EXTRA;
            screenMinX = Math.min(screenMinX, sp.x - r);
            screenMinY = Math.min(screenMinY, sp.y - r);
            screenMaxX = Math.max(screenMaxX, sp.x + r);
            screenMaxY = Math.max(screenMaxY, sp.y + r);
        }
        const rotHandleWorld = getRotateHandleWorld();
        const sp = worldToScreen(rotHandleWorld.x, rotHandleWorld.y);
        // 旋转手柄背景半径 + 阴影余量
        const r = Math.max(ROTATE_HANDLE_WORLD_SIZE * scale, ROTATE_ICON_WORLD_SIZE * scale) + SHADOW_EXTRA;
        screenMinX = Math.min(screenMinX, sp.x - r);
        screenMinY = Math.min(screenMinY, sp.y - r);
        screenMaxX = Math.max(screenMaxX, sp.x + r);
        screenMaxY = Math.max(screenMaxY, sp.y + r);
    }
    
    if (screenMinX < Infinity && screenMaxX > -Infinity) {
        const rect = {
            x: Math.floor(screenMinX - 2),
            y: Math.floor(screenMinY - 2),
            w: Math.ceil(screenMaxX - screenMinX + 4),
            h: Math.ceil(screenMaxY - screenMinY + 4)
        };
        if (rect.w > 0 && rect.h > 0) {
            addDirtyRect(rect);
        }
    }
}
    
    function getSelectionAndControlsScreenRect() {
    if (selectedItems.size === 0) return null;
    const SHADOW_EXTRA = 10;
    let screenMinX = Infinity, screenMinY = Infinity, screenMaxX = -Infinity, screenMaxY = -Infinity;
    for (let item of selectedItems) {
        if (item[0] === 's') {
            const idx = parseInt(item.slice(1));
            const stroke = strokes[idx];
            if (!stroke || stroke.type !== 'pencil') continue;
            if (!stroke.points.length) continue;
            const radius = stroke.worldWidth * scale;
            for (let p of stroke.points) {
                const sp = worldToScreen(p.x, p.y);
                screenMinX = Math.min(screenMinX, sp.x - radius);
                screenMinY = Math.min(screenMinY, sp.y - radius);
                screenMaxX = Math.max(screenMaxX, sp.x + radius);
                screenMaxY = Math.max(screenMaxY, sp.y + radius);
            }
        } else if (item[0] === 'p') {
            const idx = parseInt(item.slice(1));
            const pin = pins[idx];
            if (pin) {
                const center = worldToScreen(pin.x, pin.y);
                const r = PIN_RADIUS_WORLD * scale;
                screenMinX = Math.min(screenMinX, center.x - r);
                screenMinY = Math.min(screenMinY, center.y - r);
                screenMaxX = Math.max(screenMaxX, center.x + r);
                screenMaxY = Math.max(screenMaxY, center.y + r);
            }
        }
    }
    if (selectedItems.size > 0) {
        const corners = getRotatedCorners();
        for (let c of corners) {
            const sp = worldToScreen(c.x, c.y);
            const r = CONTROL_POINT_WORLD_SIZE * scale + SHADOW_EXTRA;
            screenMinX = Math.min(screenMinX, sp.x - r);
            screenMinY = Math.min(screenMinY, sp.y - r);
            screenMaxX = Math.max(screenMaxX, sp.x + r);
            screenMaxY = Math.max(screenMaxY, sp.y + r);
        }
        for (let i = 0; i < 4; i++) {
            const edgeCenterWorld = getEdgeCenterWorld(i);
            const sp = worldToScreen(edgeCenterWorld.x, edgeCenterWorld.y);
            const r = CONTROL_POINT_WORLD_SIZE * scale + SHADOW_EXTRA;
            screenMinX = Math.min(screenMinX, sp.x - r);
            screenMinY = Math.min(screenMinY, sp.y - r);
            screenMaxX = Math.max(screenMaxX, sp.x + r);
            screenMaxY = Math.max(screenMaxY, sp.y + r);
        }
        const rotHandleWorld = getRotateHandleWorld();
        const sp = worldToScreen(rotHandleWorld.x, rotHandleWorld.y);
        const r = Math.max(ROTATE_HANDLE_WORLD_SIZE * scale, ROTATE_ICON_WORLD_SIZE * scale) + SHADOW_EXTRA;
        screenMinX = Math.min(screenMinX, sp.x - r);
        screenMinY = Math.min(screenMinY, sp.y - r);
        screenMaxX = Math.max(screenMaxX, sp.x + r);
        screenMaxY = Math.max(screenMaxY, sp.y + r);
    }
    if (screenMinX === Infinity) return null;
    const rect = {
        x: Math.floor(screenMinX - 2),
        y: Math.floor(screenMinY - 2),
        w: Math.ceil(screenMaxX - screenMinX + 4),
        h: Math.ceil(screenMaxY - screenMinY + 4)
    };
    return rect;
}
    
    function getLassoScreenBounds() {
        if (lassoPoints.length === 0) return null;
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (let p of lassoPoints) {
            const sp = worldToScreen(p.x, p.y);
            minX = Math.min(minX, sp.x);
            minY = Math.min(minY, sp.y);
            maxX = Math.max(maxX, sp.x);
            maxY = Math.max(maxY, sp.y);
        }
        const extend = 4;
        const rect = {
            x: Math.floor(minX - extend),
            y: Math.floor(minY - extend),
            w: Math.ceil(maxX - minX + extend * 2),
            h: Math.ceil(maxY - minY + extend * 2)
        };
        return rect;
    }
    
    function addDirtyRectForLasso() {
        const rect = getLassoScreenBounds();
        if (rect && rect.w > 0 && rect.h > 0) addDirtyRect(rect);
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
        let rects = mergeRects(pendingDirtyRects);
        rects = rects.map(r => ({
            x: Math.floor(r.x - 1),
            y: Math.floor(r.y - 1),
            w: Math.ceil(r.w + 2),
            h: Math.ceil(r.h + 2)
        }));
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
                worldWidth: stroke.worldWidth,
                points: stroke.points.map(p => ({ x: p.x, y: p.y }))
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
            updateBottomPanel();
        }
        redo() {
            const strokeCopy = {
                type: this.stroke.type,
                worldWidth: this.stroke.worldWidth,
                points: this.stroke.points.map(p => ({ x: p.x, y: p.y }))
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
                    let x = Math.floor(topLeft.x - 2);
                    let y = Math.floor(topLeft.y - 2);
                    let w = Math.ceil(bottomRight.x - topLeft.x + 4);
                    let h = Math.ceil(bottomRight.y - topLeft.y + 4);
                    if (w > 0 && h > 0) {
                        const dirtyRect = { x, y, w, h };
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
            updateBottomPanel();
        }
    }
    
    class DeleteStrokesCommand extends Command {
        constructor(deleted, dirtyWorldRect = null) {
            super();
            this.deleted = JSON.parse(JSON.stringify(deleted));
            this.dirtyWorldRect = dirtyWorldRect ? { ...dirtyWorldRect } : null;
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
            if (this.dirtyWorldRect) {
                addDirtyRectFromWorld(this.dirtyWorldRect.minX, this.dirtyWorldRect.minY, this.dirtyWorldRect.maxX - this.dirtyWorldRect.minX, this.dirtyWorldRect.maxY - this.dirtyWorldRect.minY);
                updateBackgroundCacheInRect(this.dirtyWorldRect);
                flushRendering();
            } else {
                bgCacheValid = false;
                fullRepaint();
            }
            updateBottomPanel();
        }
        redo() {
            if (this.dirtyWorldRect) {
                addDirtyRectFromWorld(this.dirtyWorldRect.minX, this.dirtyWorldRect.minY, this.dirtyWorldRect.maxX - this.dirtyWorldRect.minX, this.dirtyWorldRect.maxY - this.dirtyWorldRect.minY);
            }
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
            if (this.dirtyWorldRect) {
                updateBackgroundCacheInRect(this.dirtyWorldRect);
                addDirtyRectFromWorld(this.dirtyWorldRect.minX, this.dirtyWorldRect.minY, this.dirtyWorldRect.maxX - this.dirtyWorldRect.minX, this.dirtyWorldRect.maxY - this.dirtyWorldRect.minY);
                flushRendering();
            } else {
                bgCacheValid = false;
                fullRepaint();
            }
            updateBottomPanel();
        }
    }
    
    function updateBackgroundCacheInRect(worldRect) {
        if (!bgCacheValid) {
            rebuildBackgroundCache();
            return;
        }
        const topLeft = worldToScreen(worldRect.minX, worldRect.minY);
        const bottomRight = worldToScreen(worldRect.maxX, worldRect.maxY);
        let x = Math.floor(topLeft.x - 2);
        let y = Math.floor(topLeft.y - 2);
        let w = Math.ceil(bottomRight.x - topLeft.x + 4);
        let h = Math.ceil(bottomRight.y - topLeft.y + 4);
        if (w <= 0 || h <= 0) return;
        bgCtx.save();
        bgCtx.beginPath();
        bgCtx.rect(x, y, w, h);
        bgCtx.clip();
        bgCtx.clearRect(x, y, w, h);
        for (const stroke of strokes) {
            if (stroke.type === 'pencil' && isStrokeVisible(stroke, worldRect)) {
                drawSingleStrokeToContext(bgCtx, stroke);
            }
        }
        bgCtx.restore();
        addDirtyRect({ x, y, w, h });
    }
    
    class ModifyStrokesCommand extends Command {
        constructor(mods, dirtyWorldRect = null) {
            super();
            this.mods = mods.map(m => ({
                index: m.index,
                oldPoints: m.oldPoints.map(p=>({x:p.x,y:p.y})),
                newPoints: m.newPoints.map(p=>({x:p.x,y:p.y}))
            }));
            this.dirtyWorldRect = dirtyWorldRect ? { ...dirtyWorldRect } : null;
        }
        undo() {
            for (let m of this.mods) {
                strokes[m.index].points = m.oldPoints.map(p=>({x:p.x,y:p.y}));
                updateStrokeBBox(strokes[m.index]);
            }
            rebuildStrokeGrid();
            if (this.dirtyWorldRect) {
                updateBackgroundCacheInRect(this.dirtyWorldRect);
                addDirtyRectFromWorld(this.dirtyWorldRect.minX, this.dirtyWorldRect.minY, this.dirtyWorldRect.maxX - this.dirtyWorldRect.minX, this.dirtyWorldRect.maxY - this.dirtyWorldRect.minY);
                flushRendering();
            } else {
                bgCacheValid = false;
                fullRepaint();
            }
        }
        redo() {
            for (let m of this.mods) {
                strokes[m.index].points = m.newPoints.map(p=>({x:p.x,y:p.y}));
                updateStrokeBBox(strokes[m.index]);
            }
            rebuildStrokeGrid();
            if (this.dirtyWorldRect) {
                updateBackgroundCacheInRect(this.dirtyWorldRect);
                addDirtyRectFromWorld(this.dirtyWorldRect.minX, this.dirtyWorldRect.minY, this.dirtyWorldRect.maxX - this.dirtyWorldRect.minX, this.dirtyWorldRect.maxY - this.dirtyWorldRect.minY);
                flushRendering();
            } else {
                bgCacheValid = false;
                fullRepaint();
            }
        }
    }
    
    class AddPinCommand extends Command {
        constructor(pin, index) {
            super();
            this.pin = JSON.parse(JSON.stringify(pin));
            this.index = index;
        }
        undo() {
            addDirtyRectForPin(this.pin);
            pins.splice(this.index, 1);
            flushRendering();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            pins.splice(this.index, 0, JSON.parse(JSON.stringify(this.pin)));
            addDirtyRectForPin(pins[this.index]);
            flushRendering();
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
                addDirtyRectForPin(pins[d.index]);
            }
            flushRendering();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            for (let d of this.deleted.slice().sort((a,b)=>b.index-a.index)) {
                addDirtyRectForPin(d.pin);
                pins.splice(d.index, 1);
            }
            flushRendering();
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
            addDirtyRectForPin(pins[this.index]);
            pins[this.index] = this.oldPin;
            addDirtyRectForPin(pins[this.index]);
            flushRendering();
            updatePinsListUI();
            updateBottomPanel();
        }
        redo() {
            addDirtyRectForPin(pins[this.index]);
            pins[this.index] = this.newPin;
            addDirtyRectForPin(pins[this.index]);
            flushRendering();
            updatePinsListUI();
            updateBottomPanel();
        }
    }
    
    class ModifyPinsCommand extends Command {
        constructor(mods) {
            super();
            this.mods = mods.map(m=>({...m}));
            if (mods.length > 0) {
                let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
                for (let m of mods) {
                    const r = PIN_RADIUS_WORLD;
                    minX = Math.min(minX, m.oldX - r, m.newX - r);
                    minY = Math.min(minY, m.oldY - r, m.newY - r);
                    maxX = Math.max(maxX, m.oldX + r, m.newX + r);
                    maxY = Math.max(maxY, m.oldY + r, m.newY + r);
                }
                this.dirtyWorldRect = { minX, minY, maxX, maxY };
            } else {
                this.dirtyWorldRect = null;
            }
        }
        undo() {
            for (let m of this.mods) {
                const pin = pins[m.index];
                if (pin) {
                    pin.x = m.oldX;
                    pin.y = m.oldY;
                }
            }
            if (this.dirtyWorldRect) {
                addDirtyRectFromWorld(this.dirtyWorldRect.minX, this.dirtyWorldRect.minY, this.dirtyWorldRect.maxX - this.dirtyWorldRect.minX, this.dirtyWorldRect.maxY - this.dirtyWorldRect.minY);
                flushRendering();
            } else {
                fullRepaint();
            }
            updatePinsListUI();
        }
        redo() {
            for (let m of this.mods) {
                const pin = pins[m.index];
                if (pin) {
                    pin.x = m.newX;
                    pin.y = m.newY;
                }
            }
            if (this.dirtyWorldRect) {
                addDirtyRectFromWorld(this.dirtyWorldRect.minX, this.dirtyWorldRect.minY, this.dirtyWorldRect.maxX - this.dirtyWorldRect.minX, this.dirtyWorldRect.maxY - this.dirtyWorldRect.minY);
                flushRendering();
            } else {
                fullRepaint();
            }
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
            if (p.x<minX) minX=p.x;
            if (p.y<minY) minY=p.y;
            if (p.x>maxX) maxX=p.x;
            if (p.y>maxY) maxY=p.y;
        }
        const r = stroke.worldWidth/2;
        stroke.bbox = { minX:minX-r, minY:minY-r, maxX:maxX+r, maxY:maxY+r };
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
    
    function pointToSegmentDistance(px, py, x1, y1, x2, y2) {
    const ax = px - x1, ay = py - y1;
    const bx = x2 - x1, by = y2 - y1;
    const dot = ax * bx + ay * by;
    const len2 = bx * bx + by * by;
    if (len2 === 0) return ax * ax + ay * ay;
    let t = dot / len2;
    t = Math.max(0, Math.min(1, t));
    const projX = x1 + t * bx, projY = y1 + t * by;
    const dx = px - projX, dy = py - projY;
    return dx * dx + dy * dy;
}
    
    function collectEraserChanges(eraserStroke) {
    
    if (!eraserStroke || eraserStroke.points.length === 0) return { toDelete: [] };
    const eraserRadius = eraserStroke.worldWidth / 2;
    const eraserRadiusSq = eraserRadius * eraserRadius;
    
    // 橡皮擦包围盒（用于网格查询）
    let eraserMinX = Infinity, eraserMinY = Infinity, eraserMaxX = -Infinity, eraserMaxY = -Infinity;
    for (let p of eraserStroke.points) {
        eraserMinX = Math.min(eraserMinX, p.x);
        eraserMinY = Math.min(eraserMinY, p.y);
        eraserMaxX = Math.max(eraserMaxX, p.x);
        eraserMaxY = Math.max(eraserMaxY, p.y);
    }
    eraserMinX -= eraserRadius;
    eraserMinY -= eraserRadius;
    eraserMaxX += eraserRadius;
    eraserMaxY += eraserRadius;
    const eraserWorldRect = { minX: eraserMinX, minY: eraserMinY, maxX: eraserMaxX, maxY: eraserMaxY };
    const candidates = queryStrokesInWorldRect(eraserWorldRect);
    const toDelete = [];
    
    // 对橡皮擦点进行采样，步长为2（减少点数，同时保留足够覆盖）
    const sampledPoints = [];
    const step = 2;  // 每隔一个点取一个
    for (let i = 0; i < eraserStroke.points.length; i += step) {
        sampledPoints.push(eraserStroke.points[i]);
    }
    // 确保包含最后一个点
    if (sampledPoints[sampledPoints.length - 1] !== eraserStroke.points[eraserStroke.points.length - 1]) {
        sampledPoints.push(eraserStroke.points[eraserStroke.points.length - 1]);
    }
    
    for (let idx of candidates) {
        const st = strokes[idx];
        if (!st) continue;
        if (st.type === 'pencil') {
            const strokeRadius = st.worldWidth / 2;
            const strokeRadiusSq = strokeRadius * strokeRadius;
            const combinedRadiusSq = eraserRadiusSq + strokeRadiusSq + 2 * eraserRadius * strokeRadius; // (r1+r2)^2
            let hit = false;
            const pts = st.points;
            if (pts.length === 0) continue;
            
            // 如果橡皮擦只有一个采样点，直接比较点与笔画点的距离
            if (sampledPoints.length === 1) {
                const center = sampledPoints[0];
                for (let pt of pts) {
                    const dx = pt.x - center.x, dy = pt.y - center.y;
                    if (dx * dx + dy * dy <= combinedRadiusSq) {
                        hit = true;
                        break;
                    }
                }
            } else {
                // 遍历橡皮擦采样点，对每个点检测到笔画线段的平方距离
                outer: for (let ep of sampledPoints) {
                    for (let i = 0; i < pts.length - 1; i++) {
                        const distSq = pointToSegmentDistance(ep.x, ep.y, pts[i].x, pts[i].y, pts[i+1].x, pts[i+1].y);
                        if (distSq <= combinedRadiusSq) {
                            hit = true;
                            break outer;
                        }
                    }
                    // 检测到笔画端点的距离
                    for (let pt of pts) {
                        const dx = ep.x - pt.x, dy = ep.y - pt.y;
                        if (dx * dx + dy * dy <= combinedRadiusSq) {
                            hit = true;
                            break outer;
                        }
                    }
                }
            }
            if (hit) {
                toDelete.push({ index: idx, stroke: JSON.parse(JSON.stringify(st)), wasSelected: selectedItems.has('s' + idx) });
            }
        }
    }
    return { toDelete };
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
    
    function attemptStraightenStroke() {
        if (!currentStroke || strokeModifiedByRecog) return false;
        const points = currentStroke.points;
        if (points.length < 2) return false;
        
        const A = points[0];
        const B = points[points.length - 1];
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
            const oldBounds = getStrokeScreenBounds(currentStroke);
            if (oldBounds) addDirtyRect(oldBounds);
            
            const ellipsePoints = generateEllipsePoints(ellipse.center, ellipse.a, ellipse.b, ellipse.theta, maxGap);
            if (ellipsePoints.length >= 2) {
                currentStroke.type = 'pencil';
                currentStroke.points = ellipsePoints;
                currentStroke.rawPoints = ellipsePoints.slice();
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
        const C = points[farthestIndex];
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
            const oldBounds = getStrokeScreenBounds(currentStroke);
            if (oldBounds) addDirtyRect(oldBounds);
            
            currentStroke.type = 'pencil';
            currentStroke.points = linePoints;
            currentStroke.rawPoints = linePoints.slice();
            finalizeCurrentStroke();
            return true;
        } else {
            strokeModifiedByRecog = true;
            const bezierPoints = fitCubicBezierThroughThreePoints(A, C, B, maxGap);
            if (bezierPoints.length >= 2) {
                const oldBounds = getStrokeScreenBounds(currentStroke);
                if (oldBounds) addDirtyRect(oldBounds);
                
                currentStroke.type = 'pencil';
                currentStroke.points = bezierPoints;
                currentStroke.rawPoints = bezierPoints.slice();
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
            let sumX = 0, sumY = 0, count = 0;
            for (let j = -half; j <= half; j++) {
                const idx = Math.min(Math.max(i + j, 0), points.length - 1);
                sumX += points[idx].x;
                sumY += points[idx].y;
                count++;
            }
            result.push({ x: sumX / count, y: sumY / count });
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
            points.push({ x, y });
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
            result[0] = rawPoints[0];
            result[result.length-1] = rawPoints[rawPoints.length-1];
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
        if(!stroke.points || stroke.points.length < 2) return;
        ctx.save();
        if(stroke.type === 'pencil') {
            ctx.beginPath();
            ctx.lineCap='round';
            ctx.lineJoin='round';
            ctx.lineWidth=stroke.worldWidth * scale;
            ctx.strokeStyle=PENCIL_COLOR;
            const first = worldToScreen(stroke.points[0].x, stroke.points[0].y);
            ctx.moveTo(first.x, first.y);
            for(let i=1;i<stroke.points.length;i++){
                const p = worldToScreen(stroke.points[i].x, stroke.points[i].y);
                ctx.lineTo(p.x, p.y);
            }
            ctx.stroke();
        } else if(stroke.type === 'eraser') {
            ctx.beginPath();
            ctx.lineCap = 'round';
            ctx.lineJoin = 'round';
            ctx.lineWidth = stroke.worldWidth * scale;
            ctx.strokeStyle = 'rgba(100,116,139,0.4)';
            ctx.setLineDash([8, 6]);
            const first = worldToScreen(stroke.points[0].x, stroke.points[0].y);
            ctx.moveTo(first.x, first.y);
            for(let i=1; i<stroke.points.length; i++) {
                const p = worldToScreen(stroke.points[i].x, stroke.points[i].y);
                ctx.lineTo(p.x, p.y);
            }
            ctx.stroke();
            ctx.setLineDash([]);
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
        let x = Math.floor(dirtyRect.x);
        let y = Math.floor(dirtyRect.y);
        let w = Math.ceil(dirtyRect.w);
        let h = Math.ceil(dirtyRect.h);
        
        drawCtx.save();
        drawCtx.beginPath();
        drawCtx.rect(x, y, w, h);
        drawCtx.clip();
        
        drawCtx.clearRect(x, y, w, h);
        drawCtx.drawImage(bgCanvas, x, y, w, h, x, y, w, h);
        if (currentStroke && currentStroke.points && currentStroke.points.length >= 2) {
            const currentBounds = getStrokeScreenBounds(currentStroke);
            if (currentBounds && rectIntersect(currentBounds, { x, y, w, h })) {
                drawSingleStrokeToContext(drawCtx, currentStroke);
            }
        }
        for (let pin of pins) {
            const pinScreen = worldToScreen(pin.x, pin.y);
            const pinRect = { x: pinScreen.x - PIN_RADIUS_WORLD*scale, y: pinScreen.y - PIN_RADIUS_WORLD*scale, w: PIN_RADIUS_WORLD*scale*2, h: PIN_RADIUS_WORLD*scale*2 };
            if (rectIntersect(pinRect, { x, y, w, h })) {
                drawPin(drawCtx, pin);
            }
        }
        if (isLassoDrawing && lassoPoints.length >= 2) {
            drawLassoSelection();
        }
        drawSelectedHighlights();
        drawTransformControls();
        
        drawCtx.restore();
    }
    
    function getStrokeScreenBounds(stroke) {
        if (!stroke.points.length) return null;
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (let p of stroke.points) {
            const sp = worldToScreen(p.x, p.y);
            minX = Math.min(minX, sp.x);
            minY = Math.min(minY, sp.y);
            maxX = Math.max(maxX, sp.x);
            maxY = Math.max(maxY, sp.y);
        }
        const radius = stroke.worldWidth * scale;
        return { x: minX - radius, y: minY - radius, w: maxX - minX + radius*2, h: maxY - minY + radius*2 };
    }
    
    function rectIntersect(r1, r2) {
        return !(r2.x > r1.x + r1.w || r2.x + r2.w < r1.x || r2.y > r1.y + r1.h || r2.y + r2.h < r1.y);
    }
    
    function drawSelectedHighlights() {
        if(selectedItems.size===0) return;
        if (isZooming) return; 
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
                    
                        drawCtx.lineWidth = 3;
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
                    drawCtx.lineWidth = 3;
                    drawCtx.strokeStyle='#3b82f6';
                    drawCtx.stroke();
                }
            }
        }
        drawCtx.restore();
    }
    
    function applyMove(dx,dy){
        addDirtyRectForSelectionAndControls();
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
        addDirtyRectForSelectionAndControls();
        flushRendering();
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
            if(item[0]==='s'){ const idx=parseInt(item.slice(1)); const stroke=strokes[idx]; if(stroke) for(let p of stroke.points){ if(p.x<minX)minX=p.x; if(p.y<minY)minY=p.y; if(p.x>maxX)maxX=p.x; if(p.y>maxY)maxY=p.y;} }
            else if(item[0]==='p'){ const idx=parseInt(item.slice(1)); const pin=pins[idx]; if(pin){ const r=PIN_RADIUS_WORLD; minX=Math.min(minX,pin.x-r); minY=Math.min(minY,pin.y-r); maxX=Math.max(maxX,pin.x+r); maxY=Math.max(maxY,pin.y+r); } }
        }
        selectionLocalBounds={x:minX,y:minY,w:maxX-minX,h:maxY-minY}; selectionCenter={x:minX+(maxX-minX)/2,y:minY+(maxY-minY)/2};
        addDirtyRectForSelectionAndControls();
    }
    
    function getRotatedCorners() { const cx=selectionCenter.x, cy=selectionCenter.y, halfW=selectionLocalBounds.w/2, halfH=selectionLocalBounds.h/2; const localCorners = [{x:-halfW,y:-halfH},{x: halfW,y:-halfH},{x: halfW,y: halfH},{x:-halfW,y: halfH}]; const cos=Math.cos(selectionRotation), sin=Math.sin(selectionRotation); return localCorners.map(p=>({ x:cx+p.x*cos-p.y*sin, y:cy+p.x*sin+p.y*cos })); }
    function getEdgeCenterWorld(edgeIdx) { const corners=getRotatedCorners(); const idx1=edgeIdx, idx2=(edgeIdx+1)%4; return { x:(corners[idx1].x+corners[idx2].x)/2, y:(corners[idx1].y+corners[idx2].y)/2 }; }
    function getRotateHandleWorld() {
        const topMid = getEdgeCenterWorld(0);
        const topMidScreen = worldToScreen(topMid.x, topMid.y);
        const centerScreen = worldToScreen(selectionCenter.x, selectionCenter.y);
        const dirScreen = { x: topMidScreen.x - centerScreen.x, y: topMidScreen.y - centerScreen.y };
        const lenScreen = Math.hypot(dirScreen.x, dirScreen.y);
        if (lenScreen === 0) return topMid;
        const normScreen = { x: dirScreen.x / lenScreen, y: dirScreen.y / lenScreen };
        const offsetScreen = 50;   
        const handleScreen = {
            x: topMidScreen.x + normScreen.x * offsetScreen,
            y: topMidScreen.y + normScreen.y * offsetScreen
        };
        return screenToWorld(handleScreen.x, handleScreen.y);
    }
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
        if (selectedItems.size === 0) return;
        if (isZooming) return; 
        const corners = getRotatedCorners();
        const screenCorners = corners.map(p => worldToScreen(p.x, p.y));
        drawCtx.save();
        
        drawCtx.fillStyle = 'rgba(59,130,246,0.15)';
        drawCtx.strokeStyle = '#3b82f6';
        drawCtx.lineWidth = 2;
        drawCtx.beginPath();
        drawCtx.moveTo(screenCorners[0].x, screenCorners[0].y);
        for (let i = 1; i < 4; i++) drawCtx.lineTo(screenCorners[i].x, screenCorners[i].y);
        drawCtx.closePath();
        drawCtx.fill();
        drawCtx.stroke();

        function drawPointWithStyle(x, y, radius) {
            drawCtx.save();
            drawCtx.shadowBlur = 6;
            drawCtx.shadowColor = "rgba(0,0,0,0.3)";
            drawCtx.shadowOffsetX = 1;
            drawCtx.shadowOffsetY = 1;
            drawCtx.beginPath();
            drawCtx.arc(x, y, radius, 0, 2 * Math.PI);
            drawCtx.fillStyle = '#3b82f6';
            drawCtx.fill();
            drawCtx.strokeStyle = 'white';
            drawCtx.lineWidth = 2;
            drawCtx.stroke();
            drawCtx.restore();
        }

        const controlPointRadius = 8; 
        for (let pt of screenCorners) {
            drawPointWithStyle(pt.x, pt.y, controlPointRadius);
        }
        for (let i = 0; i < 4; i++) {
            const edgeCenterWorld = getEdgeCenterWorld(i);
            const edgeScreen = worldToScreen(edgeCenterWorld.x, edgeCenterWorld.y);
            drawPointWithStyle(edgeScreen.x, edgeScreen.y, controlPointRadius);
        }

        const rotHandleWorld = getRotateHandleWorld();
        const rotScreen = worldToScreen(rotHandleWorld.x, rotHandleWorld.y);
        const rotateHandleRadius = 18;
        
        drawCtx.save();
        drawCtx.shadowBlur = 6;
        drawCtx.shadowColor = "rgba(0,0,0,0.3)";
        drawCtx.shadowOffsetX = 1;
        drawCtx.shadowOffsetY = 1;
        drawCtx.beginPath();
        drawCtx.arc(rotScreen.x, rotScreen.y, rotateHandleRadius, 0, 2 * Math.PI);
        drawCtx.fillStyle = '#3b82f6';
        drawCtx.fill();
        drawCtx.strokeStyle = 'white';
        drawCtx.lineWidth = 2;
        drawCtx.stroke();
        drawCtx.restore();

        drawCtx.save();
        drawCtx.translate(rotScreen.x, rotScreen.y);
        drawCtx.rotate(selectionRotation);
        const rotateIconSize = 24;
        drawRotateIcon(drawCtx, rotateIconSize);
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
                        points: st.points.map(p=>({x:p.x,y:p.y}))
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
        transformHistoryDirtyScreenRect = getSelectionAndControlsScreenRect();
    }
    
    function onTransformMove(sx,sy){
        if(!isTransforming) return;
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idxS = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.strokes.find(s=>s.index===idxS);
                if(orig){
                    strokes[idxS].points = orig.points.map(p=>({x:p.x,y:p.y}));
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
        
        const currentRect = getSelectionAndControlsScreenRect();
        if (currentRect) {
            if (transformHistoryDirtyScreenRect) {
                const minX = Math.min(transformHistoryDirtyScreenRect.x, currentRect.x);
                const minY = Math.min(transformHistoryDirtyScreenRect.y, currentRect.y);
                const maxX = Math.max(transformHistoryDirtyScreenRect.x + transformHistoryDirtyScreenRect.w, currentRect.x + currentRect.w);
                const maxY = Math.max(transformHistoryDirtyScreenRect.y + transformHistoryDirtyScreenRect.h, currentRect.y + currentRect.h);
                transformHistoryDirtyScreenRect = { x: minX, y: minY, w: maxX - minX, h: maxY - minY };
            } else {
                transformHistoryDirtyScreenRect = currentRect;
            }
            addDirtyRect(transformHistoryDirtyScreenRect);
        }
        flushRendering();
    }
    
    function endTransform() {
        if (!isTransforming) return;
        const strokeMods = [];
        const pinMods = [];
        let dirtyWorldRect = null;

        for (let item of selectedItems) {
            if (item[0] === 's') {
                const idxS = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.strokes.find(s => s.index === idxS);
                if (orig) {
                    const currentPoints = strokes[idxS].points.map(p => ({ x: p.x, y: p.y }));
                    if (JSON.stringify(orig.points) !== JSON.stringify(currentPoints)) {
                        strokeMods.push({
                            index: idxS,
                            oldPoints: orig.points,
                            newPoints: currentPoints
                        });
                        const oldStroke = { points: orig.points, worldWidth: strokes[idxS].worldWidth };
                        updateStrokeBBox(oldStroke);
                        const newStroke = strokes[idxS];
                        if (oldStroke.bbox && newStroke.bbox) {
                            const minX = Math.min(oldStroke.bbox.minX, newStroke.bbox.minX);
                            const minY = Math.min(oldStroke.bbox.minY, newStroke.bbox.minY);
                            const maxX = Math.max(oldStroke.bbox.maxX, newStroke.bbox.maxX);
                            const maxY = Math.max(oldStroke.bbox.maxY, newStroke.bbox.maxY);
                            if (!dirtyWorldRect) dirtyWorldRect = { minX, minY, maxX, maxY };
                            else {
                                dirtyWorldRect.minX = Math.min(dirtyWorldRect.minX, minX);
                                dirtyWorldRect.minY = Math.min(dirtyWorldRect.minY, minY);
                                dirtyWorldRect.maxX = Math.max(dirtyWorldRect.maxX, maxX);
                                dirtyWorldRect.maxY = Math.max(dirtyWorldRect.maxY, maxY);
                            }
                        }
                    }
                }
            } else if (item[0] === 'p') {
                const idxP = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.pins.find(p => p.index === idxP);
                if (orig) {
                    const curPin = pins[idxP];
                    if (orig.x !== curPin.x || orig.y !== curPin.y) {
                        pinMods.push({
                            index: idxP,
                            oldX: orig.x, oldY: orig.y,
                            newX: curPin.x, newY: curPin.y
                        });
                        const r = PIN_RADIUS_WORLD;
                        const minX = Math.min(orig.x - r, curPin.x - r);
                        const minY = Math.min(orig.y - r, curPin.y - r);
                        const maxX = Math.max(orig.x + r, curPin.x + r);
                        const maxY = Math.max(orig.y + r, curPin.y + r);
                        if (!dirtyWorldRect) dirtyWorldRect = { minX, minY, maxX, maxY };
                        else {
                            dirtyWorldRect.minX = Math.min(dirtyWorldRect.minX, minX);
                            dirtyWorldRect.minY = Math.min(dirtyWorldRect.minY, minY);
                            dirtyWorldRect.maxX = Math.max(dirtyWorldRect.maxX, maxX);
                            dirtyWorldRect.maxY = Math.max(dirtyWorldRect.maxY, maxY);
                        }
                    }
                }
            }
        }

        const cmds = [];
        if (strokeMods.length) cmds.push(new ModifyStrokesCommand(strokeMods, dirtyWorldRect));
        if (pinMods.length) cmds.push(new ModifyPinsCommand(pinMods));
        if (cmds.length) executeCommand(new CompositeCommand(cmds));

        if (transformType === 'rotate') {
            recomputeSelectionBounds();
            selectionRotation = 0;
            addDirtyRectForSelectionAndControls();
        }

        if (transformHistoryDirtyScreenRect) addDirtyRect(transformHistoryDirtyScreenRect);
        flushRendering();

        isTransforming = false;
        transformType = null;
        transformStartSelectedSnapshot = null;
        transformHistoryDirtyScreenRect = null;
        addDirtyRectForSelectionAndControls();
        flushRendering();
        updatePinsListUI();
        updateBottomPanel();
    }
    
    function getSelectedItemsInsidePolygon(poly){ const items=[]; for(let i=0;i<strokes.length;i++) if(isStrokeSelected(strokes[i],poly)) items.push('s'+i); for(let i=0;i<pins.length;i++) if(pointInPolygon(pins[i].x,pins[i].y,poly)) items.push('p'+i); return items; }
    
    function updateSelectionWithModifier(newItems, mod){ 
        addDirtyRectForSelectionAndControls();
        if(mod==='add') 
            for(let it of newItems) selectedItems.add(it); 
        else if(mod==='subtract') 
            for(let it of newItems) selectedItems.delete(it); 
        else { 
            selectedItems.clear(); 
            for(let it of newItems) selectedItems.add(it); 
        } 
        if(selectedItems.size===0){ 
            selectionLocalBounds={x:0,y:0,w:0,h:0}; 
            selectionRotation=0; 
        } else { 
            recomputeSelectionBounds(); 
            selectionRotation=0; 
        } 
        addDirtyRectForSelectionAndControls();
        flushRendering(); 
        updateBottomPanel(); 
    }
    
    function clearSelection(){ 
        addDirtyRectForSelectionAndControls();
        selectedItems.clear(); 
        selectionLocalBounds={x:0,y:0,w:0,h:0}; 
        selectionRotation=0; 
        addDirtyRectForSelectionAndControls();
        flushRendering(); 
        updateBottomPanel(); 
    }
    
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
                bottomPanel.innerHTML = `<button class="bottom-action-btn" id="pinRenameBtn">重命名</button><button class="bottom-action-btn" id="pinLevelBtn">等级</button><button class="bottom-action-btn delete-btn" id="pinDeleteBtn">删除</button>`;
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
            bottomPanel.innerHTML = `
                <button class="bottom-action-btn" id="copySelectedBtn">复制</button>
                <button class="bottom-action-btn" id="pasteBtn">粘贴</button>
                <button class="bottom-action-btn delete-btn" id="deleteSelectedBtn">删除</button>
            `;
            bottomPanel.classList.add('show');
            const copyBtn = document.getElementById('copySelectedBtn');
            const pasteBtn = document.getElementById('pasteBtn');
            const delBtn = document.getElementById('deleteSelectedBtn');
            if (copyBtn) copyBtn.onclick = () => copySelected();
            if (pasteBtn) pasteBtn.onclick = () => paste();
            if (delBtn) delBtn.onclick = () => deleteSelected();
            return;
        }
        bottomPanel.classList.remove('show');
        bottomPanel.innerHTML = '';
    }
    function showModalRename(pin) { if (isNameModalActive) return; isNameModalActive = true; updateBottomPanel(); const mask = document.createElement('div'); mask.className = 'modal-mask'; document.body.appendChild(mask); modalMask = mask; const panel = document.createElement('div'); panel.className = 'pin-name-modal'; panel.innerHTML = `<input type="text" id="modalRenameInput" value="${escapeHtml(pin.name)}" maxlength="40" autocomplete="off" placeholder="输入图钉名称">`; document.body.appendChild(panel); modalPanel = panel; const input = panel.querySelector('#modalRenameInput'); input.focus(); input.select(); const closeModal = (save) => { if (!isNameModalActive) return; if (save) { const newName = input.value.trim(); if (newName !== "") { const oldPin = JSON.parse(JSON.stringify(pin)); pin.name = newName; const idx = pins.findIndex(p=>p.id===pin.id); if(idx!==-1) executeCommand(new UpdatePinCommand(idx, oldPin, pin)); updatePinsListUI(); fullRepaint(); } } mask.remove(); panel.remove(); modalMask = null; modalPanel = null; isNameModalActive = false; updateBottomPanel(); }; mask.onclick = () => closeModal(true); input.addEventListener('keypress', (e) => { if (e.key === 'Enter') { e.stopPropagation(); closeModal(true); } }); const escHandler = (e) => { if (e.key === 'Escape') { e.preventDefault(); closeModal(false); document.removeEventListener('keydown', escHandler); } }; document.addEventListener('keydown', escHandler); panel.addEventListener('click', (e) => e.stopPropagation()); }
    
    function openEditPanel(pinId) { 
        const newPin = pins.find(p=>p.id===pinId); 
        if(!newPin) return; 
        if (isNameModalActive) return;
        if (currentEditingPinId !== null) {
            const oldPin = pins.find(p => p.id === currentEditingPinId);
            if (oldPin) addDirtyRectForPin(oldPin);
        }
        currentEditingPinId = pinId; 
        clearSelection();
        addDirtyRectForPin(newPin);
        flushRendering();
        updateBottomPanel(); 
        justOpenedPanel = true; 
        setTimeout(()=>{ justOpenedPanel = false; }, 200); 
    }
    
    function showLevelMenu(btn, pinId) { if(currentLevelMenu) currentLevelMenu.remove(); const menu = document.createElement('div'); menu.className = 'level-menu'; const levels = [{ name: "一级", value: 0 },{ name: "二级", value: 1 },{ name: "三级", value: 2 }]; levels.forEach(lv => { const opt = document.createElement('div'); opt.className = 'level-option'; opt.textContent = lv.name; opt.onclick = (e) => { e.stopPropagation(); const pin = pins.find(p=>p.id===pinId); if(pin) { const oldPin = JSON.parse(JSON.stringify(pin)); pin.level = lv.value; const idx = pins.findIndex(p=>p.id===pinId); if(idx!==-1) executeCommand(new UpdatePinCommand(idx, oldPin, pin)); updatePinsListUI(); fullRepaint(); } menu.remove(); if(currentLevelMenu === menu) currentLevelMenu = null; }; menu.appendChild(opt); }); const rect = btn.getBoundingClientRect(); menu.style.left = `${rect.left}px`; menu.style.top = `${rect.bottom + 4}px`; document.body.appendChild(menu); currentLevelMenu = menu; const closeMenu = (e) => { if(menu && !menu.contains(e.target)) { menu.remove(); if(currentLevelMenu===menu) currentLevelMenu=null; document.removeEventListener('click', closeMenu); } }; setTimeout(()=> document.addEventListener('click', closeMenu), 10); }
    
    function deleteCurrentPinAndClose() { 
        if(currentEditingPinId===null) return; 
        const idx = pins.findIndex(p=>p.id===currentEditingPinId); 
        if(idx!==-1) { 
            const oldPin = JSON.parse(JSON.stringify(pins[idx])); 
            addDirtyRectForPin(pins[idx]);
            executeCommand(new DeletePinsCommand([{index: idx, pin: oldPin, wasSelected: false}])); 
            closeEditPanel(); 
            clearSelection(); 
            updatePinsListUI(); 
        } 
    }
    
    function closeEditPanel() {
        if (currentEditingPinId === null) return;
        const pin = pins.find(p => p.id === currentEditingPinId);
        if (pin) addDirtyRectForPin(pin);
        currentEditingPinId = null;
        flushRendering();
        updateBottomPanel();
    }
    
    function placePin(worldX, worldY){ 
        const newId = nextPinId++; 
        const newPin = { id: newId, x: worldX, y: worldY, name: `图钉${newId}`, level: 0 }; 
        executeCommand(new AddPinCommand(newPin, pins.length)); 
        updatePinsListUI(); 
    }
    function updatePinsListUI() { if(!pinListContainer) return; pinListContainer.innerHTML = ''; if(pins.length===0){ pinListContainer.innerHTML='<div class="empty-pins">暂无图钉<br>点击 📌 放置图钉</div>'; return; } pins.forEach(pin=>{ const div=document.createElement('div'); div.className='pin-item'; const info=document.createElement('div'); info.className='pin-info'; info.style.paddingLeft=`${pin.level*16}px`; info.innerHTML=`<span class="pin-icon">📌</span><span class="pin-name">${escapeHtml(pin.name)}</span><span class="pin-level-badge">${pin.level===0?'一级':(pin.level===1?'二级':'三级')}</span>`; div.appendChild(info); div.addEventListener('click',()=>focusOnPin(pin.x,pin.y)); pinListContainer.appendChild(div); }); }
    function escapeHtml(str){ return str.replace(/[&<>]/g, m=> m==='&'?'&amp;':m==='<'?'&lt;':'&gt;'); }
    
    function addPointWithSmoothingAndInterp(rawX, rawY) {
        if (!currentStroke) return;
        const raw = { x: rawX, y: rawY };
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
    
    function startStroke(worldX, worldY, toolType, width) {
        if (shapeRecogTimer) { clearTimeout(shapeRecogTimer); shapeRecogTimer = null; }
        strokeModifiedByRecog = false;
        const rawPoint = { x: worldX, y: worldY };
        currentStroke = {
            type: toolType,
            worldWidth: width,
            rawPoints: [rawPoint],
            points: [rawPoint]
        };
        isDrawing = true;
        const bounds = getStrokeScreenBounds(currentStroke);
        if (bounds) addDirtyRect(bounds);
        drawingCanvas.style.cursor = 'none';
        updateCursorVisibility();
    }
    
    function startLasso(worldX,worldY,modifier){ 
        lassoModifier=modifier; 
        if(modifier==='replace') clearSelection(); 
        isLassoDrawing=true; 
        lassoPoints=[{x:worldX,y:worldY}]; 
        addDirtyRectForLasso();
        flushRendering(); 
        updateCursorVisibility(); 
    }
    function addLassoPoint(worldX,worldY){ 
        if(!isLassoDrawing) return; 
        const oldBounds = getLassoScreenBounds();
        lassoPoints.push({x:worldX,y:worldY});
        const newBounds = getLassoScreenBounds();
        if (oldBounds && newBounds) {
            const mergedRect = {
                x: Math.min(oldBounds.x, newBounds.x),
                y: Math.min(oldBounds.y, newBounds.y),
                w: Math.max(oldBounds.x + oldBounds.w, newBounds.x + newBounds.w) - Math.min(oldBounds.x, newBounds.x),
                h: Math.max(oldBounds.y + oldBounds.h, newBounds.y + newBounds.h) - Math.min(oldBounds.y, newBounds.y)
            };
            addDirtyRect(mergedRect);
        } else if (newBounds) {
            addDirtyRect(newBounds);
        }
        flushRendering();
    }
    function finalizeLasso(){ 
        if(lassoPoints.length < 3){ 
            isLassoDrawing = false; 
            const oldPoints = lassoPoints.slice();
            lassoPoints = []; 
            if (oldPoints.length >= 2) {
                let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
                for (let p of oldPoints) {
                    const sp = worldToScreen(p.x, p.y);
                    minX = Math.min(minX, sp.x);
                    minY = Math.min(minY, sp.y);
                    maxX = Math.max(maxX, sp.x);
                    maxY = Math.max(maxY, sp.y);
                }
                const extend = 4;
                if (minX !== Infinity) {
                    const rect = {
                        x: Math.floor(minX - extend),
                        y: Math.floor(minY - extend),
                        w: Math.ceil(maxX - minX + extend * 2),
                        h: Math.ceil(maxY - minY + extend * 2)
                    };
                    if (rect.w > 0 && rect.h > 0) addDirtyRect(rect);
                }
            }
            flushRendering(); 
            return; 
        } 
        const currentLassoPoints = lassoPoints.slice();
        const currentModifier = lassoModifier;
        isLassoDrawing = false;
        lassoPoints = [];
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (let p of currentLassoPoints) {
            const sp = worldToScreen(p.x, p.y);
            minX = Math.min(minX, sp.x);
            minY = Math.min(minY, sp.y);
            maxX = Math.max(maxX, sp.x);
            maxY = Math.max(maxY, sp.y);
        }
        const extend = 4;
        if (minX !== Infinity) {
            const rect = {
                x: Math.floor(minX - extend),
                y: Math.floor(minY - extend),
                w: Math.ceil(maxX - minX + extend * 2),
                h: Math.ceil(maxY - minY + extend * 2)
            };
            if (rect.w > 0 && rect.h > 0) addDirtyRect(rect);
        }
        flushRendering();
        const inside = getSelectedItemsInsidePolygon(currentLassoPoints); 
        updateSelectionWithModifier(inside, currentModifier);
    }
    function getCurrentWorldWidth(){ return currentTool==='pencil'?pencilWorldWidth:(currentTool==='eraser'?eraserWorldWidth:4); }
    function updateBrushPanelUI(){ if(currentTool==='pencil'){ brushLabel.textContent='笔刷粗细'; brushSlider.value=pencilWorldWidth; brushValue.textContent=pencilWorldWidth; brushPanelEl.classList.remove('show'); } else if(currentTool==='eraser'){ brushLabel.textContent='橡皮粗细'; brushSlider.value=eraserWorldWidth; brushValue.textContent=eraserWorldWidth; brushPanelEl.classList.remove('show'); } else brushPanelEl.classList.remove('show'); }
    function setCurrentWorldWidthFromSlider(v){ const w=parseInt(v,10); if(currentTool==='pencil') pencilWorldWidth=w; else if(currentTool==='eraser') eraserWorldWidth=w; brushSlider.value=w; brushValue.textContent=w; updateCursorSize(); }
    function showBrushPanelRelativeToButton(btn){ if(!btn) return; const toolbarRect = document.querySelector('.toolbar').getBoundingClientRect(); const btnRect = btn.getBoundingClientRect(); brushPanelEl.style.left = (toolbarRect.right + 12) + 'px'; brushPanelEl.style.top = (btnRect.top + btnRect.height/2) + 'px'; brushPanelEl.style.transform = 'translateY(-50%)'; brushPanelEl.classList.add('show'); }
    function setTool(tool,showPanel=false,srcBtn=null){ 
        if(tool===currentTool&&!showPanel) return; 
        if(isNameModalActive) return; 
        clearSelection(); 
        if(isLassoDrawing){ 
            addDirtyRectForLasso();
            isLassoDrawing=false; 
            lassoPoints=[]; 
            flushRendering();
        } 
        closeEditPanel(); 
        currentTool=tool; 
        pencilBtn.classList.remove('active'); 
        eraserBtn.classList.remove('active'); 
        lassoBtn.classList.remove('active'); 
        pinBtn.classList.remove('active','pin-active'); 
        customCursor.classList.remove('pencil-mode','eraser-mode','lasso-mode','pin-mode'); 
        if(tool==='pencil'){ 
            pencilBtn.classList.add('active'); 
            customCursor.classList.add('pencil-mode'); 
        } else if(tool==='eraser'){ 
            eraserBtn.classList.add('active'); 
            customCursor.classList.add('eraser-mode'); 
        } else if(tool==='lasso'){ 
            lassoBtn.classList.add('active'); 
            customCursor.classList.add('lasso-mode'); 
        } else if(tool==='pin'){ 
            pinBtn.classList.add('active','pin-active'); 
            customCursor.classList.add('pin-mode'); 
        } 
        updateBrushPanelUI(); 
        if(showPanel&&(tool==='pencil'||tool==='eraser')){ 
            const btn=srcBtn||(tool==='pencil'?pencilBtn:eraserBtn); 
            showBrushPanelRelativeToButton(btn); 
        } else brushPanelEl.classList.remove('show'); 
        updateCursorSize(); 
        if(!isPanning&&!isDrawing&&!isLassoDrawing) updateCursorVisibility(); 
        updateBottomPanel(); 
    }
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
        scheduleZoomEnd(); 
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
    function saveCanvas(){ const saveStrokes = strokes.filter(s => s.type !== 'eraser');
        const data={version:"2.0",view:{offsetX,offsetY,scale},strokes:saveStrokes.map(s=>({type:s.type,worldWidth:s.worldWidth,points:s.points.map(p=>({x:p.x,y:p.y}))})), pins:pins.map(p=>({id:p.id,x:p.x,y:p.y,name:p.name,level:p.level}))};
        const json=JSON.stringify(data,null,2); const blob=new Blob([json],{type:"application/json"}); const url=URL.createObjectURL(blob); const a=document.createElement('a'); a.href=url; a.download=`canvas_${new Date().toISOString().slice(0,19).replace(/:/g,'-')}.infcanvas`; document.body.appendChild(a); a.click(); document.body.removeChild(a); URL.revokeObjectURL(url); }
    function importCanvas(file){ const reader=new FileReader(); reader.onload=e=>{ try{ const data=JSON.parse(e.target.result); let newStrokes = [], newPins = []; if(data.strokes && Array.isArray(data.strokes)) newStrokes=data.strokes.filter(s=>s.type==='pencil'||s.type==='pointcloud').map(s=>{ 
            const st={type:(s.type==='pointcloud'?'pencil':s.type),worldWidth:s.worldWidth,points:s.points.map(p=>({x:p.x,y:p.y}))};
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
        }catch(err){ alert("导入失败"); } }; reader.readAsText(file); }
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
    
    function onPointerDown(e) {
    if (isNameModalActive) return;
    e.preventDefault();
    drawingCanvas.setPointerCapture(e.pointerId);
    const rect = drawingCanvas.getBoundingClientRect();
    const coords = getCanvasCoordsFromEvent(e, rect);
    if (!coords) return;
    const { x: sx, y: sy } = coords;
    lastMouseScreenX = sx;
    lastMouseScreenY = sy;
    pointerDownScreen = { x: sx, y: sy };
    const world = screenToWorld(sx, sy);

    // 1. 优先处理平移（空格+左键 或 右键）
    if ((spacePressed && e.button === 0) || e.button === 2) {
        if (isDrawing) finalizeCurrentStroke();
        if (isLassoDrawing) finalizeLasso();
        cancelTransform();
        isPanning = true;
        activePointerId = e.pointerId;
        lastPanX = sx;
        lastPanY = sy;
        drawingCanvas.style.cursor = 'grabbing';
        updateCursorVisibility();
        return;
    }

    // 2. 套索工具下的 Shift/Alt：直接进入套索多选/减选（不进入变换）
    const isShiftPressed = e.shiftKey;
    const isAltPressed = e.altKey;
    if (currentTool === 'lasso' && (isShiftPressed || isAltPressed)) {
        let mod = 'replace';
        if (isShiftPressed) mod = 'add';
        else if (isAltPressed) mod = 'subtract';
        startLasso(world.x, world.y, mod);
        activePointerId = e.pointerId;
        return;
    }

    // 3. 通用变换：任何工具下，如果命中选中的对象，则启动移动/缩放/旋转
    //    但套索工具下且按下修饰键的情况已经在上一步处理，这里不再命中
    if (!isDrawing && !isLassoDrawing && !isPanning && !isTransforming && selectedItems.size > 0) {
        const hit = hitTestTransformControls(sx, sy);
        if (hit) {
            if (hit.type === 'move') startTransform('move', sx, sy);
            else if (hit.type === 'corner') startTransform('corner', sx, sy, hit.index);
            else if (hit.type === 'edge') startTransform('edge', sx, sy, hit.index);
            else if (hit.type === 'rotate') startTransform('rotate', sx, sy);
            activePointerId = e.pointerId;
            return;
        }
    }

    // 4. 点击空白区域：清除选中
    //    对于铅笔/橡皮/图钉工具，清除选中后直接返回，不执行工具操作
    //    对于套索工具，清除选中后继续执行套索绘制（如果没有按修饰键）
    if (selectedItems.size > 0) {
        clearSelection();
        if (currentTool !== 'lasso') {
            return;
        }
        // 套索工具：清除选中后继续往下走，开始新套索（不加修饰键）
    }

    // 5. 根据当前工具执行原生操作
    if (currentTool === 'lasso') {
        let mod = 'replace';
        if (isShiftPressed) mod = 'add';
        else if (isAltPressed) mod = 'subtract';
        startLasso(world.x, world.y, mod);
        activePointerId = e.pointerId;
        return;
    }

    if (currentTool === 'pin') {
        const wasPanelOpen = bottomPanel.classList.contains('show') && currentEditingPinId !== null;
        let clickedPin = getPinByWorldClick(world.x, world.y);
        if (wasPanelOpen) {
            const wasEditingId = currentEditingPinId;
            closeEditPanel();
            if (clickedPin && clickedPin.pin.id === wasEditingId) return;
        }
        if (clickedPin) {
            openEditPanel(clickedPin.pin.id);
            return;
        }
        if (!wasPanelOpen) placePin(world.x, world.y);
        return;
    }

    // 铅笔 / 橡皮
    if (e.button === 0 && !isPanning) {
        if (isDrawing) return;
        if (isLassoDrawing) finalizeLasso();
        cancelTransform();
        startStroke(world.x, world.y, currentTool, getCurrentWorldWidth());
        activePointerId = e.pointerId;
    }
}
    
    function onPointerMove(e){ if(isNameModalActive) return; const rect=drawingCanvas.getBoundingClientRect(); const coords=getCanvasCoordsFromEvent(e,rect); if(coords){ lastMouseScreenX=coords.x; lastMouseScreenY=coords.y; coordsCache=coords; } if(isPanning&&activePointerId===e.pointerId&&coords){ const dx=coords.x-lastPanX, dy=coords.y-lastPanY; if(dx!==0||dy!==0) panView(dx,dy); lastPanX=coords.x; lastPanY=coords.y; if(coords) moveCursor(coords.x,coords.y); return; } if(isTransforming&&activePointerId===e.pointerId&&coords){ onTransformMove(coords.x,coords.y); return; } if(coords){ moveCursor(coords.x,coords.y); if(!isDrawing&&!isPanning&&!isLassoDrawing&&!isTransforming) updateCursorVisibility(); } if(isDrawing&&activePointerId===e.pointerId&&currentStroke&&coords){ const w=screenToWorld(coords.x,coords.y); addPointWithSmoothingAndInterp(w.x,w.y); } if(isLassoDrawing&&activePointerId===e.pointerId&&coords){ const w=screenToWorld(coords.x,coords.y); addLassoPoint(w.x,w.y); } }
    function onPointerUp(e){ if(isNameModalActive) return; e.preventDefault(); drawingCanvas.releasePointerCapture(e.pointerId); if(shapeRecogTimer){ clearTimeout(shapeRecogTimer); shapeRecogTimer=null; } if(isPanning&&activePointerId===e.pointerId){ isPanning=false; activePointerId=null; drawingCanvas.style.cursor='none'; updateCursorVisibility(); return; } if(isTransforming&&activePointerId===e.pointerId){ endTransform(); activePointerId=null; drawingCanvas.style.cursor='none'; updateCursorVisibility(); return; } if(isDrawing&&activePointerId===e.pointerId){ finalizeCurrentStroke(); activePointerId=null; isDrawing=false; updateCursorVisibility(); return; } if(isLassoDrawing&&activePointerId===e.pointerId){ finalizeLasso(); activePointerId=null; isLassoDrawing=false; updateCursorVisibility(); return; } if(currentTool==='lasso'&&!isLassoDrawing&&!isTransforming&&pointerDownScreen&&coordsCache){ const dx=coordsCache.x-pointerDownScreen.x, dy=coordsCache.y-pointerDownScreen.y; if(Math.hypot(dx,dy)<5) clearSelection(); } pointerDownScreen=null; coordsCache=null; }
    function onPointerCancel(e){ if(isNameModalActive) return; if(shapeRecogTimer){ clearTimeout(shapeRecogTimer); shapeRecogTimer=null; } if(isDrawing&&activePointerId===e.pointerId) finalizeCurrentStroke(); if(isLassoDrawing&&activePointerId===e.pointerId) finalizeLasso(); if(isPanning&&activePointerId===e.pointerId) isPanning=false; if(isTransforming&&activePointerId===e.pointerId) cancelTransform(); activePointerId=null; pointerDownScreen=null; coordsCache=null; }
    function cancelTransform(){ if(isTransforming && transformStartSelectedSnapshot){
        for(let item of selectedItems){
            if(item[0]==='s'){
                const idxS = parseInt(item.slice(1));
                const orig = transformStartSelectedSnapshot.strokes.find(s=>s.index===idxS);
                if(orig){
                    strokes[idxS].points = orig.points.map(p=>({x:p.x,y:p.y}));
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
    
    // ========== 复制粘贴功能 ==========
    function copySelected() {
        if (selectedItems.size === 0) return;
        copyBuffer.strokes = [];
        copyBuffer.pins = [];
        for (let item of selectedItems) {
            if (item[0] === 's') {
                const idx = parseInt(item.slice(1));
                const st = strokes[idx];
                if (st && st.type === 'pencil') {
                    copyBuffer.strokes.push({
                        type: st.type,
                        worldWidth: st.worldWidth,
                        points: st.points.map(p => ({ x: p.x, y: p.y }))
                    });
                }
            } else if (item[0] === 'p') {
                const idx = parseInt(item.slice(1));
                const pin = pins[idx];
                if (pin) {
                    copyBuffer.pins.push({
                        x: pin.x,
                        y: pin.y,
                        name: pin.name,
                        level: pin.level
                    });
                }
            }
        }
    }

    function paste() {
        if (copyBuffer.strokes.length === 0 && copyBuffer.pins.length === 0) return;
        
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (let st of copyBuffer.strokes) {
            for (let p of st.points) {
                if (p.x < minX) minX = p.x;
                if (p.y < minY) minY = p.y;
                if (p.x > maxX) maxX = p.x;
                if (p.y > maxY) maxY = p.y;
            }
        }
        for (let pin of copyBuffer.pins) {
            if (pin.x < minX) minX = pin.x;
            if (pin.y < minY) minY = pin.y;
            if (pin.x > maxX) maxX = pin.x;
            if (pin.y > maxY) maxY = pin.y;
        }
        if (minX === Infinity) return;
        
        const clipboardCenter = { x: (minX + maxX) / 2, y: (minY + maxY) / 2 };
        const screenCenterScreen = { x: canvasWidth / 2, y: canvasHeight / 2 };
        const screenCenterWorld = screenToWorld(screenCenterScreen.x, screenCenterScreen.y);
        const offsetXWorld = screenCenterWorld.x - clipboardCenter.x;
        const offsetYWorld = screenCenterWorld.y - clipboardCenter.y;
        
        const newStrokes = [];
        const newPins = [];
        let worldMinX = Infinity, worldMinY = Infinity, worldMaxX = -Infinity, worldMaxY = -Infinity;
        
        for (let st of copyBuffer.strokes) {
            const newStroke = {
                type: st.type,
                worldWidth: st.worldWidth,
                points: st.points.map(p => ({ x: p.x + offsetXWorld, y: p.y + offsetYWorld }))
            };
            updateStrokeBBox(newStroke);
            newStrokes.push(newStroke);
            const b = newStroke.bbox;
            if (b.minX < worldMinX) worldMinX = b.minX;
            if (b.minY < worldMinY) worldMinY = b.minY;
            if (b.maxX > worldMaxX) worldMaxX = b.maxX;
            if (b.maxY > worldMaxY) worldMaxY = b.maxY;
        }
        for (let pin of copyBuffer.pins) {
            const newPin = {
                id: nextPinId++,
                x: pin.x + offsetXWorld,
                y: pin.y + offsetYWorld,
                name: pin.name,
                level: pin.level
            };
            newPins.push(newPin);
            if (newPin.x - PIN_RADIUS_WORLD < worldMinX) worldMinX = newPin.x - PIN_RADIUS_WORLD;
            if (newPin.y - PIN_RADIUS_WORLD < worldMinY) worldMinY = newPin.y - PIN_RADIUS_WORLD;
            if (newPin.x + PIN_RADIUS_WORLD > worldMaxX) worldMaxX = newPin.x + PIN_RADIUS_WORLD;
            if (newPin.y + PIN_RADIUS_WORLD > worldMaxY) worldMaxY = newPin.y + PIN_RADIUS_WORLD;
        }
        
        const oldStrokeCount = strokes.length;
        const oldPinCount = pins.length;
        const cmds = [];
        
        for (let i = 0; i < newStrokes.length; i++) {
            cmds.push(new AddStrokeCommand(newStrokes[i], oldStrokeCount + i, true));
        }
        for (let i = 0; i < newPins.length; i++) {
            cmds.push(new AddPinCommand(newPins[i], oldPinCount + i));
        }
        
        if (cmds.length === 0) return;
        const compositeCmd = new CompositeCommand(cmds);
        executeCommand(compositeCmd);
        
        if (worldMinX !== Infinity) {
            const worldRect = { minX: worldMinX - 5, minY: worldMinY - 5, maxX: worldMaxX + 5, maxY: worldMaxY + 5 };
            updateBackgroundCacheInRect(worldRect);
            const topLeft = worldToScreen(worldRect.minX, worldRect.minY);
            const bottomRight = worldToScreen(worldRect.maxX, worldRect.maxY);
            const dirtyScreen = {
                x: Math.floor(topLeft.x - 2),
                y: Math.floor(topLeft.y - 2),
                w: Math.ceil(bottomRight.x - topLeft.x + 4),
                h: Math.ceil(bottomRight.y - topLeft.y + 4)
            };
            if (dirtyScreen.w > 0 && dirtyScreen.h > 0) {
                addDirtyRect(dirtyScreen);
            }
        } else {
            bgCacheValid = false;
            fullRepaint();
        }
        
        const newStrokesIndices = [];
        for (let i = 0; i < newStrokes.length; i++) {
            newStrokesIndices.push(oldStrokeCount + i);
        }
        const newPinsIndices = [];
        for (let i = 0; i < newPins.length; i++) {
            newPinsIndices.push(oldPinCount + i);
        }
        
        clearSelection();
        for (let idx of newStrokesIndices) {
            selectedItems.add('s' + idx);
        }
        for (let idx of newPinsIndices) {
            selectedItems.add('p' + idx);
        }
        recomputeSelectionBounds();
        selectionRotation = 0;
        rebuildStrokeGrid();
        addDirtyRectForSelectionAndControls();
        flushRendering();
        updatePinsListUI();
        updateBottomPanel();
    }
    
    function onKeyDown(e){ 
        if(isNameModalActive){ if(e.code==='Escape' && modalMask) modalMask.click(); return; }
        if(e.code === 'ShiftLeft' || e.code === 'ShiftRight') { shiftPressed = true; return; }
        if(e.code==='Space'){ e.preventDefault(); if(!spacePressed){ spacePressed=true; if(isDrawing) finalizeCurrentStroke(); if(isLassoDrawing) finalizeLasso(); if(!isPanning) drawingCanvas.style.cursor='grab'; updateCursorVisibility(); } return; }
        if(e.code==='KeyQ'){ e.preventDefault(); setTool('pencil',false); return; }
        if(e.code==='KeyE'){ e.preventDefault(); setTool('eraser',false); return; }
        if(e.code==='KeyL'){ e.preventDefault(); setTool('lasso',false); return; }
        if(e.code==='KeyP'){ e.preventDefault(); setTool('pin',false); return; }
        if(e.ctrlKey && e.code === 'KeyC'){ e.preventDefault(); copySelected(); return; }
        if(e.ctrlKey && e.code === 'KeyV'){ e.preventDefault(); paste(); return; }
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
            const eraserStroke = currentStroke;
            currentStroke = null;
            isDrawing = false;
            
            const eraserBounds = getStrokeScreenBounds(eraserStroke);
            if (eraserBounds) addDirtyRect(eraserBounds);
            
            const changes = collectEraserChanges(eraserStroke);
            if(changes.toDelete.length) {
                const dirtyWorldRect = getWorldRectFromStrokes(changes.toDelete);
                const cmd = new DeleteStrokesCommand(changes.toDelete, dirtyWorldRect);
                executeCommand(cmd);
            } else {
                flushRendering();
            }
            updateCursorVisibility();
            strokeModifiedByRecog = false;
            return;
        }
        
        if(currentStroke.type === 'pencil' && currentStroke.points.length === 1) {
            const singlePoint = currentStroke.points[0];
            const eps = 1e-6;
            const secondPoint = { x: singlePoint.x + eps, y: singlePoint.y + eps };
            currentStroke.points.push(secondPoint);
            currentStroke.rawPoints.push(secondPoint);
        }
        
        if(currentStroke.points.length >= 2){
            const newStroke = {
                type: currentStroke.type,
                worldWidth: currentStroke.worldWidth,
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
                let x = Math.floor(topLeft.x - 2);
                let y = Math.floor(topLeft.y - 2);
                let w = Math.ceil(bottomRight.x - topLeft.x + 4);
                let h = Math.ceil(bottomRight.y - topLeft.y + 4);
                if (w > 0 && h > 0) {
                    const dirtyRect = { x, y, w, h };
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