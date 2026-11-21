const API = window.location.origin;

function showToast(msg, isError = true) {
  let t = document.getElementById('toast');
  if (!t) {
    t = document.createElement('div');
    t.id = 'toast';
    t.className = 'toast';
    document.body.appendChild(t);
  }
  t.textContent = msg;
  t.className = 'toast show' + (isError ? ' error' : '');
  setTimeout(() => t.classList.remove('show'), 3200);
}

function getToken() {
  return localStorage.getItem('xeon_token');
}

function authHeaders() {
  return {
    'Content-Type': 'application/json',
    'Authorization': 'Bearer ' + getToken()
  };
}

// ---------- CLAIM HELPERS (per-username) ----------
function getClaim(username) {
  if (!username) return null;
  return localStorage.getItem('xeon_claim_' + username.toLowerCase()) || null;
}

function setClaim(username, claimId) {
  if (!username || !claimId) return;
  localStorage.setItem('xeon_claim_' + username.toLowerCase(), claimId);
}

function preserveAllClaims() {
  const claims = {};
  for (let i = 0; i < localStorage.length; i++) {
    const key = localStorage.key(i);
    if (key && key.startsWith('xeon_claim_')) {
      claims[key] = localStorage.getItem(key);
    }
  }
  return claims;
}

function restoreClaims(claims) {
  Object.keys(claims).forEach(k => localStorage.setItem(k, claims[k]));
}

// ---------- AUTH CHECK ----------
async function checkAuth() {
  try {
    const res = await fetch(API + '/api/usage', { headers: authHeaders() });
    if (res.status === 401 || res.status === 403) {
      const claims = preserveAllClaims();
      localStorage.clear();
      restoreClaims(claims);
      location.href = '/';
      return false;
    }
    return true;
  } catch (err) {
    return true; // network error → don't force logout
  }
}

async function doLogin() {
  const username = document.getElementById('username').value.trim();
  const password = document.getElementById('password').value;
  if (!username || !password) return showToast('Fill all fields');

  // Get the claim that belongs to THIS username only
  const claimId = getClaim(username);

  try {
    const res = await fetch(API + '/api/login', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ username, password, claimId })
    });
    const data = await res.json();
    if (!data.success) return showToast(data.message || 'Login failed');

    localStorage.setItem('xeon_token', data.token);
    localStorage.setItem('xeon_user', data.username);
    localStorage.setItem('xeon_expiry', data.expiry || '');

    // Save the permanent claim under the correct username key
    if (data.claimId) {
      setClaim(data.username, data.claimId);
    }

    location.href = '/dashboard';
  } catch {
    showToast('Connection error');
  }
}

async function loadDashboard() {
  if (!getToken()) return location.href = '/';

  const isValid = await checkAuth();
  if (!isValid) return;

  document.getElementById('user-name').textContent = localStorage.getItem('xeon_user') || 'User';

  const exp = localStorage.getItem('xeon_expiry');
  if (exp) {
    document.getElementById('expiry-text').style.display = 'block';
    document.getElementById('expiry-text').textContent = 'Expires: ' + new Date(exp).toLocaleString();
  }

  // Status
  try {
    const r = await fetch(API + '/api/status', { headers: authHeaders() });
    const d = await r.json();
    const dot = document.getElementById('status-dot');
    const txt = document.getElementById('status-text');
    if (d.active) {
      dot.className = 'dot on';
      txt.textContent = 'ACTIVE';
      txt.style.color = '#00ff9d';
    } else {
      dot.className = 'dot off';
      txt.textContent = 'MAINTENANCE';
      txt.style.color = '#ff4d4d';
    }
  } catch {}

  await refreshUsage();
  startLiveConsole();
}

async function refreshUsage() {
  try {
    const r = await fetch(API + '/api/usage', { headers: authHeaders() });

    if (r.status === 401 || r.status === 403) {
      const claims = preserveAllClaims();
      localStorage.clear();
      restoreClaims(claims);
      location.href = '/';
      return;
    }

    const d = await r.json();
    
    const richEl     = document.getElementById('c-richcrash');
const blokEl     = document.getElementById('c-blokcrash');
const iosEl      = document.getElementById('c-ios');
const iosv2El    = document.getElementById('c-richxiosv2');

if (richEl)  richEl.textContent  = d.richcrash || 0;
if (blokEl)  blokEl.textContent  = d.blokcrash || 0;
if (iosEl)   iosEl.textContent   = d.ios || 0;
if (iosv2El) iosv2El.textContent = d.richxiosv2 || 0;
  } catch (err) {
    console.log('Usage refresh error:', err);
  }
}

function startLiveConsole() {
  const box = document.getElementById('console');
  if (!box) return;

  setInterval(async () => {
    try {
      const r = await fetch(API + '/api/liveconsole', { headers: authHeaders() });

      if (r.status === 401 || r.status === 403) {
        const claims = preserveAllClaims();
        localStorage.clear();
        restoreClaims(claims);
        location.href = '/';
        return;
      }

      const list = await r.json();
      box.innerHTML = '';

      list.slice(0, 13).forEach((item, index) => {
        const div = document.createElement('div');
        div.className = 'console-line ok';
        div.style.cssText = 'font-size:0.84rem; line-height:1.4;';
        div.textContent = `${item.user} just executed ${item.type} to ${item.target}`;
        box.appendChild(div);

        if (item.createdAt) {
          const timeDiv = document.createElement('div');
          timeDiv.style.cssText = `
            font-size: 0.71rem;
            color: #5d8a6a;
            margin-top: 3px;
            margin-bottom: 2px;
            opacity: 0.85;
          `;
          const date = new Date(item.createdAt);
          timeDiv.textContent = date.toLocaleString(undefined, {
            day: '2-digit',
            month: '2-digit',
            year: '2-digit',
            hour: '2-digit',
            minute: '2-digit',
            second: '2-digit',
            hour12: true
          });
          box.appendChild(timeDiv);
        }

        if (index < list.slice(0, 13).length - 1) {
          const divider = document.createElement('div');
          divider.style.cssText = `
            height: 1px;
            background: linear-gradient(to right, transparent, #1a3a1a, transparent);
            margin: 10px 0;
            opacity: 0.7;
          `;
          box.appendChild(divider);
        }
      });

      await refreshUsage();
    } catch (err) {
      // silent
    }
  }, 3000);
}

async function sendGreeting(type) {
  const input = document.getElementById('target');
  let target = input.value.trim();
  if (!target) return showToast('Enter target');

  if (type !== 'group') {
    target = target.replace(/[^0-9]/g, '');
    if (target.length < 8 || target.length > 15) return showToast('Invalid number');
  }

  const btn = document.getElementById('send-btn');
  if (!btn) return;

  btn.disabled = true;
  btn.textContent = 'SENDING...';

  const safetyTimer = setTimeout(() => {
    btn.disabled = false;
    btn.textContent = 'EXECUTE';
    showToast('Request timed out. Try again.');
  }, 25000);

  try {
    const res = await fetch(API + `/api/greeting/${type}`, {
      method: 'POST',
      headers: authHeaders(),
      body: JSON.stringify({ target })
    });

    clearTimeout(safetyTimer);

    if (res.status === 401 || res.status === 403) {
      const claims = preserveAllClaims();
      localStorage.clear();
      restoreClaims(claims);
      location.href = '/';
      return;
    }

    const data = await res.json();

    if (data.success) {
      showToast('Sent successfully', false);
    } else {
      showToast(data.message || 'Failed');
    }
  } catch (err) {
    clearTimeout(safetyTimer);
    console.error(err);
    showToast('Server error');
  }

  btn.disabled = false;
  btn.textContent = 'EXECUTE';
}

async function sendGreetingCustom(type, inputId, btnId) {
  const input = document.getElementById(inputId);
  let target = input.value.trim();
  if (!target) return showToast('Enter target');

  if (type !== 'group') {
    target = target.replace(/[^0-9]/g, '');
    if (target.length < 8 || target.length > 15) return showToast('Invalid number');
  }

  const btn = document.getElementById(btnId);
  if (!btn) return;

  btn.disabled = true;
  btn.textContent = 'SENDING...';

  // Safety timeout – button will never stay stuck longer than 25 seconds
  const safetyTimer = setTimeout(() => {
    btn.disabled = false;
    btn.textContent = 'EXECUTE';
    showToast('Request timed out. Try again.');
  }, 25000);

  try {
    const res = await fetch(API + `/api/greeting/${type}`, {
      method: 'POST',
      headers: authHeaders(),
      body: JSON.stringify({ target })
    });

    clearTimeout(safetyTimer);

    if (res.status === 401 || res.status === 403) {
      const claims = preserveAllClaims();
      localStorage.clear();
      restoreClaims(claims);
      location.href = '/';
      return;
    }

    const data = await res.json();

    if (data.success) {
      showToast('Sent successfully', false);
    } else {
      showToast(data.message || 'Failed');
    }
  } catch (err) {
    clearTimeout(safetyTimer);
    console.error(err);
    showToast('Server error');
  }

  // Always reset
  btn.disabled = false;
  btn.textContent = 'EXECUTE';
}

function logout() {
  const token = getToken();
  if (token) {
    fetch(API + '/api/logout', {
      method: 'POST',
      headers: authHeaders()
    }).catch(() => {});
  }

  // Keep ALL permanent claims
  const claims = preserveAllClaims();
  localStorage.removeItem('xeon_token');
  localStorage.removeItem('xeon_user');
  localStorage.removeItem('xeon_expiry');
  restoreClaims(claims);

  location.href = '/';
}

function toggleMenu() {
  document.getElementById('sidebar').classList.toggle('open');
}

// Close drawer when clicking outside
document.addEventListener('click', function(e) {
  const sidebar = document.getElementById('sidebar');
  const menuBtn = document.querySelector('.menu-btn');

  if (!sidebar || !menuBtn) return;

  if (sidebar.classList.contains('open')) {
    if (!sidebar.contains(e.target) && !menuBtn.contains(e.target)) {
      sidebar.classList.remove('open');
    }
  }
});