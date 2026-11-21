function initOccultBackground() {
  const canvas = document.createElement('canvas');
  canvas.id = 'occult-canvas';
  canvas.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;z-index:-1;pointer-events:none;';
  document.body.prepend(canvas);

  const ctx = canvas.getContext('2d');
  let width, height;
  let symbols = [];

  function resize() {
    width = canvas.width = window.innerWidth;
    height = canvas.height = window.innerHeight;
  }
  window.addEventListener('resize', resize);
  resize();

  // Create symbols
  for (let i = 0; i < 18; i++) {
    symbols.push({
      x: Math.random() * width,
      y: Math.random() * height,
      size: 18 + Math.random() * 28,
      speedX: (Math.random() - 0.5) * 0.4,
      speedY: (Math.random() - 0.5) * 0.4,
      rotation: Math.random() * Math.PI * 2,
      rotSpeed: (Math.random() - 0.5) * 0.01,
      type: 'pentagram',
      opacity: 0.08 + Math.random() * 0.12
    });
  }

  function drawPentagram(x, y, size, rotation, opacity) {
    ctx.save();
    ctx.translate(x, y);
    ctx.rotate(rotation);
    ctx.beginPath();
    for (let i = 0; i < 5; i++) {
      const angle = (i * 4 * Math.PI) / 5 - Math.PI / 2;
      const px = Math.cos(angle) * size;
      const py = Math.sin(angle) * size;
      if (i === 0) ctx.moveTo(px, py);
      else ctx.lineTo(px, py);
    }
    ctx.closePath();
    ctx.strokeStyle = `rgba(0, 255, 157, ${opacity})`;
    ctx.lineWidth = 1.5;
    ctx.stroke();
    ctx.restore();
  }

  function animate() {
    ctx.clearRect(0, 0, width, height);

    symbols.forEach(s => {
      s.x += s.speedX;
      s.y += s.speedY;
      s.rotation += s.rotSpeed;

      // Wrap around
      if (s.x < -50) s.x = width + 50;
      if (s.x > width + 50) s.x = -50;
      if (s.y < -50) s.y = height + 50;
      if (s.y > height + 50) s.y = -50;

      if (s.type === 'pentagram') {
        drawPentagram(s.x, s.y, s.size, s.rotation, s.opacity);
      }
    });

    requestAnimationFrame(animate);
  }

  animate();
}

// Auto start
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', initOccultBackground);
} else {
  initOccultBackground();
    }
