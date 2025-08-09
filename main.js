"use strict";

// Vibeants — Ant Pheromone Trails
// Browser-based simulation game of ants using pheromones to find and return food

(function () {
  // ----------------------- Constants & Types -----------------------
  const CELL_SIZE = 6; // pixels per grid cell
  function computeCanvasSize() {
    const isMobile = window.matchMedia && window.matchMedia("(max-width: 768px)").matches;
    if (isMobile) {
      const available = Math.max(240, Math.min(700, Math.floor(window.innerWidth - 32)));
      const cells = Math.max(40, Math.floor(available / CELL_SIZE));
      const side = cells * CELL_SIZE;
      return { width: side, height: side, isMobile: true };
    }
    return { width: 1400, height: 560, isMobile: false };
  }
  let { width: CANVAS_WIDTH, height: CANVAS_HEIGHT, isMobile: IS_MOBILE } = computeCanvasSize();
  const GRID_WIDTH = Math.floor(CANVAS_WIDTH / CELL_SIZE);
  const GRID_HEIGHT = Math.floor(CANVAS_HEIGHT / CELL_SIZE);

  const INITIAL_ANT_COUNT = 200;
  const MAX_ANTS = 1000;
  const ANT_STEP_SPEED = 0.1; // base grid cells per tick (10x slower)
  const ANT_TURN_ANGLE = (Math.PI / 180) * 18; // radians per decision
  const SENSOR_ANGLE = (Math.PI / 180) * 28;
  const SENSOR_OFFSET = 2; // cells ahead
  const SENSOR_SPREAD = 1; // lateral cells sampled

  const EVAPORATION = 0.006; // slower fade for clearer trails
  const DIFFUSION_WEIGHT = 0.0; // no diffusion: trails stay exactly where placed
  const PHEROMONE_DEPOSIT_FOOD = 0.45; // strong trail to food when carrying
  const PHEROMONE_DEPOSIT_HOME = 0.0; // searching ants do NOT lay trail
  const PHEROMONE_MAX = 5.0;
  const SCENT_THRESHOLD = 0.05; // min field strength to influence turning

  const FOOD_RADIUS_CELLS = 2;
  const NEST_RADIUS_CELLS = 3;

  const TOOL = {
    FOOD: "food",
    WALL: "wall",
    ERASE: "erase",
  };

  // ----------------------- Utilities -----------------------
  function clamp(value, min, max) {
    return Math.max(min, Math.min(max, value));
  }

  function indexOf(x, y) {
    return y * GRID_WIDTH + x;
  }

  function wrapAngle(angle) {
    while (angle < -Math.PI) angle += Math.PI * 2;
    while (angle > Math.PI) angle -= Math.PI * 2;
    return angle;
  }

  function randomBetween(min, max) {
    return min + Math.random() * (max - min);
  }

  function distanceCells(ax, ay, bx, by) {
    const dx = ax - bx;
    const dy = ay - by;
    return Math.hypot(dx, dy);
  }

  // ----------------------- World State -----------------------
  class World {
    constructor() {
      this.gridWidth = GRID_WIDTH;
      this.gridHeight = GRID_HEIGHT;
      this.toFood = new Float32Array(this.gridWidth * this.gridHeight);
      // Removed home pheromone
      this.obstacles = new Uint8Array(this.gridWidth * this.gridHeight);
      this.foodPiles = []; // {x,y,amount}
      this.ants = [];
      this.nest = { x: Math.floor(this.gridWidth / 2), y: Math.floor(this.gridHeight / 2) };
      this.score = 0;
      this.ticks = 0;

      this.tempToFood = new Float32Array(this.gridWidth * this.gridHeight);

      this.flags = {
        showFoodPheromone: true,
        showHomePheromone: false,
      };
    }

    reset(antCount) {
      this.toFood.fill(0);
      // no home field
      this.obstacles.fill(0);
      this.foodPiles = [];
      this.ants = [];
      this.score = 0;
      this.ticks = 0;
      for (let i = 0; i < antCount; i++) {
        this.ants.push(Ant.spawnAtNest(this.nest.x + Math.random() - 0.5, this.nest.y + Math.random() - 0.5));
      }
    }

    setAntCount(targetCount) {
      targetCount = clamp(targetCount, 1, MAX_ANTS);
      if (targetCount > this.ants.length) {
        const toAdd = targetCount - this.ants.length;
        for (let i = 0; i < toAdd; i++) {
          this.ants.push(Ant.spawnAtNest(this.nest.x + Math.random() - 0.5, this.nest.y + Math.random() - 0.5));
        }
      } else if (targetCount < this.ants.length) {
        this.ants.length = targetCount;
      }
    }

    addFood(cellX, cellY, amount) {
      const existing = this.foodPiles.find((f) => distanceCells(f.x, f.y, cellX, cellY) <= FOOD_RADIUS_CELLS + 1);
      if (existing) {
        existing.amount += amount;
      } else {
        this.foodPiles.push({ x: cellX, y: cellY, amount });
      }
    }

    setWall(cellX, cellY, isWall, radiusCells = 1) {
      for (let y = cellY - radiusCells; y <= cellY + radiusCells; y++) {
        for (let x = cellX - radiusCells; x <= cellX + radiusCells; x++) {
          if (x < 0 || x >= this.gridWidth || y < 0 || y >= this.gridHeight) continue;
          if (distanceCells(x, y, this.nest.x, this.nest.y) <= NEST_RADIUS_CELLS) continue;
          if (distanceCells(x, y, cellX, cellY) <= radiusCells) {
            this.obstacles[indexOf(x, y)] = isWall ? 1 : 0;
          }
        }
      }
    }

    // spray removed

    pickUpFoodAt(cellX, cellY) {
      for (let i = 0; i < this.foodPiles.length; i++) {
        const f = this.foodPiles[i];
        if (distanceCells(f.x, f.y, cellX, cellY) <= FOOD_RADIUS_CELLS && f.amount > 0) {
          f.amount -= 1;
          if (f.amount <= 0) {
            this.foodPiles.splice(i, 1);
          }
          return true;
        }
      }
      return false;
    }

    deliverFood() {
      this.score += 1;
    }

    diffuseAndEvaporate() {
      // Simple 3x3 blur (if enabled) and evaporation for toFood field only
      const w = this.gridWidth;
      const h = this.gridHeight;
      const srcF = this.toFood;
      const dstF = this.tempToFood;

      for (let y = 0; y < h; y++) {
        const yTop = y > 0 ? y - 1 : y;
        const yBot = y < h - 1 ? y + 1 : y;
        for (let x = 0; x < w; x++) {
          const xL = x > 0 ? x - 1 : x;
          const xR = x < w - 1 ? x + 1 : x;

          const i = indexOf(x, y);
          // Neighbors for toFood
          const c = srcF[i];
          const n = srcF[indexOf(x, yTop)];
          const s = srcF[indexOf(x, yBot)];
          const e = srcF[indexOf(xR, y)];
          const wv = srcF[indexOf(xL, y)];
          const ne = srcF[indexOf(xR, yTop)];
          const nw = srcF[indexOf(xL, yTop)];
          const se = srcF[indexOf(xR, yBot)];
          const sw = srcF[indexOf(xL, yBot)];
          const neighborAvgF = (n + s + e + wv + ne + nw + se + sw) / 8;
          let blendedF = c * (1 - DIFFUSION_WEIGHT) + neighborAvgF * DIFFUSION_WEIGHT;
          blendedF = Math.max(0, blendedF * (1 - EVAPORATION));
          dstF[i] = blendedF;
        }
      }

      // Swap buffers
      this.toFood.set(dstF);
    }
  }

  // ----------------------- Ant -----------------------
  class Ant {
    constructor(x, y, angle) {
      this.x = x;
      this.y = y;
      this.angle = angle;
      this.hasFood = false;
      this.wiggle = randomBetween(-Math.PI, Math.PI);
    }

    static spawnAtNest(x, y) {
      return new Ant(x, y, randomBetween(-Math.PI, Math.PI));
    }

    get cellX() {
      return Math.floor(this.x);
    }
    get cellY() {
      return Math.floor(this.y);
    }

    step(world, speedMultiplier) {
      const preferredField = this.hasFood ? null : world.toFood; // follow to-food only when searching
      const depositField = world.toFood; // only deposit to-food field when carrying
      const depositRate = this.hasFood ? PHEROMONE_DEPOSIT_FOOD : PHEROMONE_DEPOSIT_HOME;

      // Sense left, forward, right on the appropriate field
      const sensed = preferredField ? this.senseDirections(world, preferredField) : { forward: 0, left: 0, right: 0 };
      const signalStrength = Math.max(sensed.forward, sensed.left, sensed.right);

      // Decide turning
      let turn = 0;
      if (this.hasFood) {
        // Strongly steer toward the nest when carrying (no home pheromone)
        const dx = world.nest.x - this.x;
        const dy = world.nest.y - this.y;
        const homeAngle = Math.atan2(dy, dx);
        const delta = wrapAngle(homeAngle - this.angle);
        // Clamp the homeward turn
        const maxTurn = ANT_TURN_ANGLE;
        turn = clamp(delta, -maxTurn, maxTurn);

        // If home pheromone is strong, allow it to fine-tune left/right choice
        if (signalStrength >= SCENT_THRESHOLD) {
          if (sensed.left > sensed.right && sensed.left > sensed.forward) turn += SENSOR_ANGLE * 0.25;
          if (sensed.right > sensed.left && sensed.right > sensed.forward) turn -= SENSOR_ANGLE * 0.25;
        }
      } else {
        // Searching: only follow to-food trail if strong enough, else wander
        if (signalStrength >= SCENT_THRESHOLD) {
          if (sensed.forward >= sensed.left && sensed.forward >= sensed.right) {
            turn = 0;
          } else if (sensed.left > sensed.right) {
            turn = SENSOR_ANGLE;
          } else if (sensed.right > sensed.left) {
            turn = -SENSOR_ANGLE;
          } else {
            turn = (Math.random() - 0.5) * ANT_TURN_ANGLE;
          }
        } else {
          // Free exploration
          turn = (Math.random() - 0.5) * ANT_TURN_ANGLE;
        }
      }

      // Turn and move
      this.angle = wrapAngle(this.angle + turn);
      const step = ANT_STEP_SPEED * (speedMultiplier || 1);
      const nx = this.x + Math.cos(this.angle) * step;
      const ny = this.y + Math.sin(this.angle) * step;

      // Collision with walls or borders: reflect direction
      const bounced = this.handleCollisions(world, nx, ny);
      if (!bounced) {
        this.x = nx;
        this.y = ny;
      }

      // Deposit pheromone (only to-food field when carrying)
      const ix = clamp(Math.floor(this.x), 0, world.gridWidth - 1);
      const iy = clamp(Math.floor(this.y), 0, world.gridHeight - 1);
      const i = indexOf(ix, iy);
      if (this.hasFood) {
        depositField[i] = Math.min(PHEROMONE_MAX, depositField[i] + depositRate);
      }

      // Interact with food and nest
      if (!this.hasFood) {
        // pick up food if near
        if (world.pickUpFoodAt(ix, iy)) {
          this.hasFood = true;
          // Immediately orient toward nest to start heading home
          const dx = world.nest.x - this.x;
          const dy = world.nest.y - this.y;
          this.angle = Math.atan2(dy, dx);
        }
      } else {
        // deliver to nest if near
        if (distanceCells(ix, iy, world.nest.x, world.nest.y) <= NEST_RADIUS_CELLS) {
          this.hasFood = false;
          world.deliverFood();
        }
      }
    }

    senseDirections(world, field) {
      // Sample field in three directions relative to current heading
      const { x, y, angle } = this;
      const leftAngle = angle + SENSOR_ANGLE;
      const rightAngle = angle - SENSOR_ANGLE;

      const f = this.sampleCone(world, field, angle);
      const l = this.sampleCone(world, field, leftAngle);
      const r = this.sampleCone(world, field, rightAngle);
      return { forward: f, left: l, right: r };
    }

    sampleCone(world, field, angle) {
      let sum = 0;
      let samples = 0;
      for (let d = 1; d <= SENSOR_OFFSET + 1; d++) {
        const sx = Math.floor(this.x + Math.cos(angle) * d);
        const sy = Math.floor(this.y + Math.sin(angle) * d);
        for (let s = -SENSOR_SPREAD; s <= SENSOR_SPREAD; s++) {
          const ox = Math.floor(sx + Math.cos(angle + Math.PI / 2) * s);
          const oy = Math.floor(sy + Math.sin(angle + Math.PI / 2) * s);
          if (ox < 0 || oy < 0 || ox >= world.gridWidth || oy >= world.gridHeight) continue;
          if (world.obstacles[indexOf(ox, oy)] === 1) continue;
          sum += field[indexOf(ox, oy)];
          samples++;
        }
      }
      return samples > 0 ? sum / samples : 0;
    }

    handleCollisions(world, nx, ny) {
      let bounced = false;
      let cx = Math.floor(nx);
      let cy = Math.floor(ny);

      // Border collisions
      if (cx < 0 || cx >= world.gridWidth) {
        this.angle = Math.PI - this.angle;
        bounced = true;
      }
      if (cy < 0 || cy >= world.gridHeight) {
        this.angle = -this.angle;
        bounced = true;
      }

      cx = clamp(cx, 0, world.gridWidth - 1);
      cy = clamp(cy, 0, world.gridHeight - 1);

      // Wall collision
      if (world.obstacles[indexOf(cx, cy)] === 1) {
        // simple reflect
        this.angle = wrapAngle(this.angle + Math.PI / 2 + (Math.random() - 0.5));
        bounced = true;
      }
      return bounced;
    }
  }

  // ----------------------- Rendering -----------------------
  function drawWorld(ctx, world, view) {
      ctx.save();
      ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height);

      // Draw pheromones as translucent heatmaps
      const showFood = world.flags.showFoodPheromone;

      const imgData = ctx.getImageData(0, 0, ctx.canvas.width, ctx.canvas.height);
      const data = imgData.data;
      for (let gy = 0; gy < world.gridHeight; gy++) {
        for (let gx = 0; gx < world.gridWidth; gx++) {
          const idx = indexOf(gx, gy);
          const baseX = gx * CELL_SIZE;
          const baseY = gy * CELL_SIZE;
          const rMax = CELL_SIZE;
          const gMax = CELL_SIZE;
          const toFoodVal = world.toFood[idx];
          const toHomeVal = 0; // removed
          // Map concentration to color channels
          const foodAlpha = showFood ? clamp(toFoodVal / PHEROMONE_MAX, 0, 1) : 0;
          const homeAlpha = 0;
          const cellR = Math.floor(160 * homeAlpha);
          const cellG = Math.floor(180 * foodAlpha);
          const cellB = Math.floor(220 * (foodAlpha * 0.2 + homeAlpha * 0.2));
          const cellA = Math.floor(255 * Math.max(foodAlpha * 0.55, homeAlpha * 0.55));

          for (let py = 0; py < gMax; py++) {
            let pIndex = ((baseY + py) * ctx.canvas.width + baseX) * 4;
            for (let px = 0; px < rMax; px++) {
              data[pIndex] = Math.max(data[pIndex], cellR);
              data[pIndex + 1] = Math.max(data[pIndex + 1], cellG);
              data[pIndex + 2] = Math.max(data[pIndex + 2], cellB);
              data[pIndex + 3] = Math.max(data[pIndex + 3], cellA);
              pIndex += 4;
            }
          }
        }
      }
      ctx.putImageData(imgData, 0, 0);

      // Draw obstacles
      ctx.fillStyle = "#1b1410"; // soil-like wall background remains
      for (let y = 0; y < world.gridHeight; y++) {
        for (let x = 0; x < world.gridWidth; x++) {
          if (world.obstacles[indexOf(x, y)] === 1) {
            ctx.fillStyle = "#2a211a"; // soil block
            ctx.fillRect(x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE);
          }
        }
      }

      // Draw food piles
      for (const f of world.foodPiles) {
        const px = f.x * CELL_SIZE + CELL_SIZE / 2;
        const py = f.y * CELL_SIZE + CELL_SIZE / 2;
        const r = Math.max(2, Math.min(10, Math.sqrt(f.amount) * 0.8));
        ctx.beginPath();
        ctx.fillStyle = "#c1d38a"; // food
        ctx.arc(px, py, r, 0, Math.PI * 2);
        ctx.fill();
        ctx.strokeStyle = "#6f7f43";
        ctx.lineWidth = 1;
        ctx.stroke();
      }

      // Draw nest
      const nx = world.nest.x * CELL_SIZE + CELL_SIZE / 2;
      const ny = world.nest.y * CELL_SIZE + CELL_SIZE / 2;
      ctx.beginPath();
      ctx.fillStyle = "#d1b65c"; // nest
      ctx.arc(nx, ny, NEST_RADIUS_CELLS * CELL_SIZE * 0.8, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = "#e5d59a";
      ctx.stroke();

      // Draw ants
      for (const ant of world.ants) {
        const ax = ant.x * CELL_SIZE + CELL_SIZE / 2;
        const ay = ant.y * CELL_SIZE + CELL_SIZE / 2;
        const dir = ant.angle;
        const size = ant.hasFood ? 3 : 2;
        ctx.save();
        ctx.translate(ax, ay);
        ctx.rotate(dir);
        ctx.beginPath();
        ctx.moveTo(size + 2, 0);
        ctx.lineTo(-size, size);
        ctx.lineTo(-size, -size);
        ctx.closePath();
        ctx.fillStyle = ant.hasFood ? "#eab308" : "#f3efe6";
        ctx.fill();
        ctx.restore();
      }

      ctx.restore();
  }

  // ----------------------- Input & Camera -----------------------
  class Interaction {
    constructor(canvas, world, state) {
      this.canvas = canvas;
      this.world = world;
      this.state = state;
      this.activeTool = TOOL.FOOD;
      this.isMouseDown = false;

      this._bindEvents();
    }

    getMouseCell(evt) {
      const rect = this.canvas.getBoundingClientRect();
      const scaleX = this.canvas.width / rect.width;
      const scaleY = this.canvas.height / rect.height;
      const x = (evt.clientX - rect.left) * scaleX;
      const y = (evt.clientY - rect.top) * scaleY;
      const cellX = clamp(Math.floor(x / CELL_SIZE), 0, this.world.gridWidth - 1);
      const cellY = clamp(Math.floor(y / CELL_SIZE), 0, this.world.gridHeight - 1);
      return { cellX, cellY };
    }

    _bindEvents() {
      // Tools
      const tFood = document.getElementById("tool-food");
      const tWall = document.getElementById("tool-wall");
      const tErase = document.getElementById("tool-erase");
      const toolButtons = [tFood, tWall, tErase];
      const setActive = (tool) => {
        this.activeTool = tool;
        toolButtons.forEach((b) => b.classList.remove("active"));
        if (tool === TOOL.FOOD) tFood.classList.add("active");
        if (tool === TOOL.WALL) tWall.classList.add("active");
        if (tool === TOOL.ERASE) tErase.classList.add("active");
        // spray removed
      };
      tFood.addEventListener("click", () => setActive(TOOL.FOOD));
      tWall.addEventListener("click", () => setActive(TOOL.WALL));
      tErase.addEventListener("click", () => setActive(TOOL.ERASE));
      // spray removed

      // Pheromone toggles
      document.getElementById("toggle-food-pher").addEventListener("change", (e) => {
        this.world.flags.showFoodPheromone = e.target.checked;
      });
      // home pheromone toggle removed

      // Sliders
      const antsRange = document.getElementById("ants-range");
      const antsValue = document.getElementById("ants-value");
      antsRange.addEventListener("input", (e) => {
        const v = parseInt(e.target.value, 10);
        antsValue.textContent = String(v);
        this.world.setAntCount(v);
      });

      const speedRange = document.getElementById("speed-range");
      const speedValue = document.getElementById("speed-value");
      speedRange.addEventListener("input", (e) => {
        const v = parseFloat(e.target.value);
        speedValue.textContent = v.toFixed(2).replace(/\.00$/, "") + "x";
        this.state.speedMultiplier = v;
      });

      const foodRange = document.getElementById("food-range");
      const foodValue = document.getElementById("food-value");
      foodRange.addEventListener("input", (e) => {
        const v = parseInt(e.target.value, 10);
        foodValue.textContent = String(v);
        this.state.foodSize = v;
      });

      // Play/Pause/Reset
      document.getElementById("btn-play").addEventListener("click", () => {
        this.state.running = true;
      });
      document.getElementById("btn-pause").addEventListener("click", () => {
        this.state.running = false;
      });
      document.getElementById("btn-reset").addEventListener("click", () => {
        this.world.reset(parseInt(antsRange.value, 10));
        document.getElementById("score").textContent = String(this.world.score);
      });

      // Canvas interactions
      this.canvas.addEventListener("mousedown", (e) => {
        this.isMouseDown = true;
        this._act(e);
      });
      window.addEventListener("mouseup", () => {
        this.isMouseDown = false;
      });
      this.canvas.addEventListener("mousemove", (e) => {
        if (this.isMouseDown) this._act(e);
      });
      // Prevent context menu to keep right-click free if we extend later
      this.canvas.addEventListener("contextmenu", (e) => e.preventDefault());
    }

    _act(evt) {
      const { cellX, cellY } = this.getMouseCell(evt);
      switch (this.activeTool) {
        case TOOL.FOOD: {
          this.world.addFood(cellX, cellY, this.state.foodSize);
          break;
        }
        case TOOL.WALL: {
          this.world.setWall(cellX, cellY, true, 2);
          break;
        }
        case TOOL.ERASE: {
          this.world.setWall(cellX, cellY, false, 2);
          break;
        }
        // spray removed
      }
    }
  }

  // ----------------------- Main Loop -----------------------
  function main() {
    const canvas = document.getElementById("world");
    const ctx = canvas.getContext("2d", { alpha: true, willReadFrequently: true });

    let world = new World();
    function applyCanvasSize() {
      ({ width: CANVAS_WIDTH, height: CANVAS_HEIGHT, isMobile: IS_MOBILE } = computeCanvasSize());
      canvas.width = CANVAS_WIDTH;
      canvas.height = CANVAS_HEIGHT;
      // Recompute grid-dependent globals in world by recreating it
      world = new World();
      world.reset(parseInt(document.getElementById("ants-range").value, 10) || INITIAL_ANT_COUNT);
    }

    applyCanvasSize();

    const state = {
      running: false,
      speedMultiplier: 1,
      foodSize: 100,
    };

    const ui = new Interaction(canvas, world, state);

    const scoreEl = document.getElementById("score");
    const antsRange = document.getElementById("ants-range");
    const antsValue = document.getElementById("ants-value");
    antsValue.textContent = antsRange.value;
    // Initialize speed/food labels to match slider defaults
    const speedRange = document.getElementById("speed-range");
    const speedValue = document.getElementById("speed-value");
    speedValue.textContent = parseFloat(speedRange.value).toFixed(2).replace(/\.00$/, "") + "x";
    const foodRange = document.getElementById("food-range");
    const foodValue = document.getElementById("food-value");
    foodValue.textContent = foodRange.value;

    let last = performance.now();

    function loop(now) {
      const dt = (now - last) / 16.6667; // relative to ~60fps ticks
      last = now;
      const steps = state.running ? Math.max(1, Math.floor(dt)) : 0;

      for (let s = 0; s < steps; s++) {
        // update ants
        for (let i = 0; i < world.ants.length; i++) {
          world.ants[i].step(world, state.speedMultiplier);
        }

        // diffuse + evaporate pheromones
        world.diffuseAndEvaporate();

        // book-keeping
        world.ticks++;
      }

      // render always
      drawWorld(ctx, world);
      scoreEl.textContent = String(world.score);

      requestAnimationFrame(loop);
    }
    requestAnimationFrame(loop);

    // Resize handling for responsive square on mobile
    let resizeTimeout;
    function onResize() {
      clearTimeout(resizeTimeout);
      resizeTimeout = setTimeout(() => {
        const prevRunning = state.running;
        applyCanvasSize();
        state.running = prevRunning; // preserve play/pause
      }, 100);
    }
    window.addEventListener("resize", onResize);
  }

  window.addEventListener("DOMContentLoaded", main);
})();


