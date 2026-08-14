process.env['NODE_TLS_REJECT_UNAUTHORIZED'] = '1';

import './config.js';
import './api.js';

import { createRequire } from 'module';
import path, { join } from 'path';
import { fileURLToPath, pathToFileURL } from 'url';
import { platform } from 'process';

import fs, {
  readdirSync,
  statSync,
  unlinkSync,
  existsSync,
  readFileSync,
  watch,
  mkdirSync
} from 'fs';

import os from 'os';
import * as cp from 'child_process';

import yargs from 'yargs';
import { spawn } from 'child_process';
import lodash from 'lodash';
import chalk from 'chalk';
import syntaxerror from 'syntax-error';
import { format } from 'util';
import pino from 'pino';
import Pino from 'pino';
import { Boom } from '@hapi/boom';

import {
  makeWASocket,
  protoType,
  serialize
} from './src/libraries/simple.js';

import { initializeSubBots } from './src/libraries/subBotManager.js';

import { Low } from 'lowdb';
import { JSONFile } from 'lowdb/node';

import store from './src/libraries/store.js';
import LidResolver from './src/libraries/LidResolver.js';

const {
  DisconnectReason,
  useMultiFileAuthState,
  fetchLatestBaileysVersion,
  makeCacheableSignalKeyStore,
  jidNormalizedUser,
  PHONENUMBER_MCC
} = await import('baileys');

import readline from 'readline';
import NodeCache from 'node-cache';

const { chain } = lodash;

const PORT = process.env.PORT || process.env.SERVER_PORT || 3000;

let stopped = 'close';
let conn = null;
let handler = null;

protoType();
serialize();

const msgRetryCounterMap = new Map();

const msgRetryCounterCache = new NodeCache({
  stdTTL: 0,
  checkperiod: 0
});

const userDevicesCache = new NodeCache({
  stdTTL: 0,
  checkperiod: 0
});

global.__filename = function filename(
  pathURL = import.meta.url,
  rmPrefix = platform !== 'win32'
) {
  return rmPrefix
    ? /file:\/\/\//.test(pathURL)
      ? fileURLToPath(pathURL)
      : pathURL
    : pathToFileURL(pathURL).toString();
};

global.__dirname = function dirname(pathURL) {
  return path.dirname(global.__filename(pathURL, true));
};

global.__require = function require(dir = import.meta.url) {
  return createRequire(dir);
};

global.API = (
  name,
  apiPath = '/',
  query = {},
  apikeyqueryname
) => {
  const apiName = name in global.APIs ? global.APIs[name] : name;

  return (
    apiName +
    apiPath +
    (
      query || apikeyqueryname
        ? '?' +
          new URLSearchParams(
            Object.entries({
              ...query,
              ...(apikeyqueryname
                ? {
                    [apikeyqueryname]:
                      global.APIKeys?.[apiName]
                  }
                : {})
            })
          )
        : ''
    )
  );
};

global.timestamp = {
  start: new Date()
};

global.videoList = [];
global.videoListXXX = [];

const __dirname = global.__dirname(import.meta.url);

global.opts = new Object(
  yargs(process.argv.slice(2))
    .exitProcess(false)
    .parse()
);

const opts = global.opts;

global.prefix = new RegExp('^[#!/.]');

const databasePath = `${opts._?.[0] ? opts._[0] + '_' : ''}database.json`;

let databaseAdapter;

if (
  typeof global.cloudDBAdapter === 'function' &&
  /https?:\/\//.test(opts.db || '')
) {
  databaseAdapter = new global.cloudDBAdapter(opts.db);
} else {
  databaseAdapter = new JSONFile(databasePath);
}

global.db = new Low(databaseAdapter);

global.loadDatabase = async function loadDatabase() {
  if (global.db.READ) {
    return new Promise((resolve) => {
      const interval = setInterval(async () => {
        if (!global.db.READ) {
          clearInterval(interval);

          resolve(
            global.db.data == null
              ? global.loadDatabase()
              : global.db.data
          );
        }
      }, 1000);
    });
  }

  if (global.db.data !== null) {
    return global.db.data;
  }

  global.db.READ = true;

  try {
    await global.db.read();
  } catch (error) {
    console.error('❌ Error leyendo la base de datos:', error);
  }

  global.db.READ = null;

  global.db.data = {
    users: {},
    chats: {},
    stats: {},
    msgs: {},
    sticker: {},
    settings: {},
    ...(global.db.data || {})
  };

  global.db.chain = chain(global.db.data);

  return global.db.data;
};

await global.loadDatabase();

/* ------------------------------------------------ */

/**
 * Clase auxiliar para acceso a datos LID desde JSON
 */
class LidDataManager {
  constructor(cacheFile = './src/lidsresolve.json') {
    this.cacheFile = cacheFile;
  }

  /**
   * Cargar datos del archivo JSON
   */
  loadData() {
    try {
      if (fs.existsSync(this.cacheFile)) {
        const data = fs.readFileSync(this.cacheFile, 'utf8');

        if (!data.trim()) {
          return {};
        }

        return JSON.parse(data);
      }

      return {};
    } catch (error) {
      console.error(
        '❌ Error cargando cache LID:',
        error.message
      );

      return {};
    }
  }

  /**
   * Obtener información de usuario por LID
   */
  getUserInfo(lidNumber) {
    const data = this.loadData();

    return data[lidNumber] || null;
  }

  /**
   * Obtener información de usuario por JID
   */
  getUserInfoByJid(jid) {
    const data = this.loadData();

    for (const [, entry] of Object.entries(data)) {
      if (entry && entry.jid === jid) {
        return entry;
      }
    }

    return null;
  }

  /**
   * Encontrar LID por JID
   */
  findLidByJid(jid) {
    const data = this.loadData();

    for (const [, entry] of Object.entries(data)) {
      if (entry && entry.jid === jid) {
        return entry.lid;
      }
    }

    return null;
  }

  /**
   * Listar todos los usuarios válidos
   */
  getAllUsers() {
    const data = this.loadData();
    const users = [];

    for (const [, entry] of Object.entries(data)) {
      if (entry && !entry.notFound && !entry.error) {
        users.push({
          lid: entry.lid,
          jid: entry.jid,
          name: entry.name || 'Desconocido',
          country: entry.country,
          phoneNumber: entry.phoneNumber,
          isPhoneDetected:
            entry.phoneDetected || entry.corrected,
          timestamp: entry.timestamp
            ? new Date(entry.timestamp).toLocaleString()
            : 'Sin fecha'
        });
      }
    }

    return users.sort((a, b) =>
      String(a.name).localeCompare(String(b.name))
    );
  }

  /**
   * Obtener estadísticas
   */
  getStats() {
    const data = this.loadData();

    let valid = 0;
    let notFound = 0;
    let errors = 0;
    let phoneNumbers = 0;
    let corrected = 0;

    for (const [, entry] of Object.entries(data)) {
      if (entry) {
        if (entry.phoneDetected || entry.corrected) {
          phoneNumbers++;
        }

        if (entry.corrected) {
          corrected++;
        }

        if (entry.notFound) {
          notFound++;
        } else if (entry.error) {
          errors++;
        } else {
          valid++;
        }
      }
    }

    return {
      total: Object.keys(data).length,
      valid,
      notFound,
      errors,
      phoneNumbers,
      corrected,
      cacheFile: this.cacheFile,
      fileExists: fs.existsSync(this.cacheFile)
    };
  }

  /**
   * Obtener usuarios por país
   */
  getUsersByCountry() {
    const data = this.loadData();
    const countries = {};

    for (const [, entry] of Object.entries(data)) {
      if (
        entry &&
        !entry.notFound &&
        !entry.error &&
        entry.country
      ) {
        if (!countries[entry.country]) {
          countries[entry.country] = [];
        }

        countries[entry.country].push({
          lid: entry.lid,
          jid: entry.jid,
          name: entry.name || 'Desconocido',
          phoneNumber: entry.phoneNumber
        });
      }
    }

    for (const country of Object.keys(countries)) {
      countries[country].sort((a, b) =>
        String(a.name).localeCompare(String(b.name))
      );
    }

    return countries;
  }
}

const lidDataManager = new LidDataManager();

/**
 * Procesar texto para resolver LIDs
 */
async function processTextMentions(
  text,
  groupId,
  lidResolver
) {
  if (
    typeof text !== 'string' ||
    !groupId ||
    !text.includes('@') ||
    !lidResolver
  ) {
    return text;
  }

  try {
    const mentionRegex = /@(\d{8,20})/g;
    const mentions = [...text.matchAll(mentionRegex)];

    if (!mentions.length) {
      return text;
    }

    let processedText = text;

    const processedMentions = new Set();
    const replacements = new Map();

    for (const mention of mentions) {
      const [, lidNumber] = mention;

      if (processedMentions.has(lidNumber)) {
        continue;
      }

      processedMentions.add(lidNumber);

      const lidJid = `${lidNumber}@lid`;

      try {
        const resolvedJid =
          await lidResolver.resolveLid(
            lidJid,
            groupId
          );

        if (
          resolvedJid &&
          resolvedJid !== lidJid &&
          !resolvedJid.endsWith('@lid')
        ) {
          const resolvedNumber =
            resolvedJid.split('@')[0];

          if (
            resolvedNumber &&
            resolvedNumber !== lidNumber
          ) {
            replacements.set(
              lidNumber,
              resolvedNumber
            );
          }
        }
      } catch (error) {
        console.error(
          `❌ Error procesando mención LID ${lidNumber}:`,
          error.message
        );
      }
    }

    for (const [
      lidNumber,
      resolvedNumber
    ] of replacements.entries()) {
      const globalRegex = new RegExp(
        `@${lidNumber}(?!\\d)`,
        'g'
      );

      processedText = processedText.replace(
        globalRegex,
        `@${resolvedNumber}`
      );
    }

    return processedText;
  } catch (error) {
    console.error(
      '❌ Error en processTextMentions:',
      error
    );

    return text;
  }
}

/**
 * Procesar contenido de mensaje recursivamente
 */
async function processMessageContent(
  messageContent,
  groupChatId,
  lidResolver
) {
  if (
    !messageContent ||
    typeof messageContent !== 'object'
  ) {
    return;
  }

  const messageTypes =
    Object.keys(messageContent);

  for (const msgType of messageTypes) {
    const msgContent =
      messageContent[msgType];

    if (
      !msgContent ||
      typeof msgContent !== 'object'
    ) {
      continue;
    }

    if (typeof msgContent.text === 'string') {
      try {
        msgContent.text =
          await processTextMentions(
            msgContent.text,
            groupChatId,
            lidResolver
          );
      } catch (error) {
        console.error(
          '❌ Error procesando texto:',
          error
        );
      }
    }

    if (typeof msgContent.caption === 'string') {
      try {
        msgContent.caption =
          await processTextMentions(
            msgContent.caption,
            groupChatId,
            lidResolver
          );
      } catch (error) {
        console.error(
          '❌ Error procesando caption:',
          error
        );
      }
    }

    if (msgContent.contextInfo) {
      await processContextInfo(
        msgContent.contextInfo,
        groupChatId,
        lidResolver
      );
    }
  }
}

/**
 * Procesar contextInfo recursivamente
 */
async function processContextInfo(
  contextInfo,
  groupChatId,
  lidResolver
) {
  if (
    !contextInfo ||
    typeof contextInfo !== 'object'
  ) {
    return;
  }

  if (
    contextInfo.mentionedJid &&
    Array.isArray(contextInfo.mentionedJid)
  ) {
    const resolvedMentions = [];

    for (const jid of contextInfo.mentionedJid) {
      if (
        typeof jid === 'string' &&
        jid.endsWith('@lid')
      ) {
        try {
          const resolved =
            await lidResolver.resolveLid(
              jid,
              groupChatId
            );

          resolvedMentions.push(
            resolved &&
            !resolved.endsWith('@lid')
              ? resolved
              : jid
          );
        } catch {
          resolvedMentions.push(jid);
        }
      } else {
        resolvedMentions.push(jid);
      }
    }

    contextInfo.mentionedJid =
      resolvedMentions;
  }

  if (
    typeof contextInfo.participant === 'string' &&
    contextInfo.participant.endsWith('@lid')
  ) {
    try {
      const resolved =
        await lidResolver.resolveLid(
          contextInfo.participant,
          groupChatId
        );

      if (
        resolved &&
        !resolved.endsWith('@lid')
      ) {
        contextInfo.participant = resolved;
      }
    } catch (error) {
      console.error(
        '❌ Error resolviendo participant en contextInfo:',
        error
      );
    }
  }

  if (contextInfo.quotedMessage) {
    await processMessageContent(
      contextInfo.quotedMessage,
      groupChatId,
      lidResolver
    );
  }
}

/**
 * Procesar mensaje completo
 */
async function processMessageForDisplay(
  message,
  lidResolver
) {
  if (!message || !lidResolver) {
    return message;
  }

  try {
    const processedMessage =
      JSON.parse(JSON.stringify(message));

    const groupChatId =
      processedMessage.key?.remoteJid?.endsWith?.('@g.us')
        ? processedMessage.key.remoteJid
        : null;

    if (!groupChatId) {
      return processedMessage;
    }

    if (
      processedMessage.key?.participant?.endsWith?.(
        '@lid'
      )
    ) {
      try {
        const resolved =
          await lidResolver.resolveLid(
            processedMessage.key.participant,
            groupChatId
          );

        if (
          resolved &&
          resolved !==
            processedMessage.key.participant &&
          !resolved.endsWith('@lid')
        ) {
          processedMessage.key.participant =
            resolved;
        }
      } catch (error) {
        console.error(
          '❌ Error resolviendo participant:',
          error
        );
      }
    }

    if (
      processedMessage.mentionedJid &&
      Array.isArray(processedMessage.mentionedJid)
    ) {
      const resolvedMentions = [];

      for (const jid of processedMessage.mentionedJid) {
        if (
          typeof jid === 'string' &&
          jid.endsWith('@lid')
        ) {
          try {
            const resolved =
              await lidResolver.resolveLid(
                jid,
                groupChatId
              );

            resolvedMentions.push(
              resolved &&
              !resolved.endsWith('@lid')
                ? resolved
                : jid
            );
          } catch {
            resolvedMentions.push(jid);
          }
        } else {
          resolvedMentions.push(jid);
        }
      }

      processedMessage.mentionedJid =
        resolvedMentions;
    }

    if (processedMessage.message) {
      await processMessageContent(
        processedMessage.message,
        groupChatId,
        lidResolver
      );
    }

    return processedMessage;
  } catch (error) {
    console.error(
      '❌ Error procesando mensaje para display:',
      error
    );

    return message;
  }
}

/**
 * Extraer todo el texto de un mensaje
 */
function extractAllText(message) {
  if (!message?.message) {
    return '';
  }

  let allText = '';

  const extractFromContent = (content) => {
    if (!content) {
      return '';
    }

    let text = '';

    if (typeof content.text === 'string') {
      text += content.text + ' ';
    }

    if (typeof content.caption === 'string') {
      text += content.caption + ' ';
    }

    if (content.contextInfo?.quotedMessage) {
      const quotedTypes = Object.keys(
        content.contextInfo.quotedMessage
      );

      for (const quotedType of quotedTypes) {
        const quotedContent =
          content.contextInfo.quotedMessage[
            quotedType
          ];

        text += extractFromContent(
          quotedContent
        );
      }
    }

    return text;
  };

  const messageTypes =
    Object.keys(message.message);

  for (const msgType of messageTypes) {
    allText += extractFromContent(
      message.message[msgType]
    );
  }

  return allText.trim();
}

/**
 * Interceptar mensajes
 */
async function interceptMessages(
  messages,
  lidResolver
) {
  if (!Array.isArray(messages)) {
    return messages;
  }

  const processedMessages = [];

  for (const message of messages) {
    try {
      let processedMessage = message;

      if (
        lidResolver &&
        typeof lidResolver.processMessage ===
          'function'
      ) {
        try {
          processedMessage =
            await lidResolver.processMessage(
              message
            );
        } catch (error) {
          console.error(
            '❌ Error en lidResolver.processMessage:',
            error
          );
        }
      }

      processedMessage =
        await processMessageForDisplay(
          processedMessage,
          lidResolver
        );

      processedMessages.push(
        processedMessage
      );
    } catch (error) {
      console.error(
        '❌ Error interceptando mensaje:',
        error
      );

      processedMessages.push(message);
    }
  }

  return processedMessages;
}

/* ------------------------------------------------ */
/* CONEXIÓN BAILEYS                                 */
/* ------------------------------------------------ */

const { state, saveCreds } =
  await useMultiFileAuthState(
    global.authFile
  );

let version;

try {
  const version22 =
    await fetchLatestBaileysVersion();

  console.log(version22);

  version =
    version22?.version || [
      2,
      3000,
      1033893291
    ];
} catch (error) {
  console.error(
    '⚠️ No se pudo obtener la versión de Baileys. Usando versión de respaldo.',
    error.message
  );

  version = [
    2,
    3000,
    1033893291
  ];
}

let phoneNumber =
  global.botnumber ||
  process.argv
    .find((arg) =>
      arg.startsWith('--phone=')
    )
    ?.split('=')[1];

const methodCodeQR =
  process.argv.includes('--method=qr');

const methodCode =
  !!phoneNumber ||
  process.argv.includes('--method=code');

const MethodMobile =
  process.argv.includes('mobile');

const rl =
  readline.createInterface({
    input: process.stdin,
    output: process.stdout
  });

const question = (texto) =>
  new Promise((resolver) =>
    rl.question(texto, resolver)
  );

let opcion;

if (methodCodeQR) {
  opcion = '1';
}

if (
  !methodCodeQR &&
  !methodCode &&
  !fs.existsSync(
    `./${global.authFile}/creds.json`
  )
) {
  do {
    opcion = await question(
      '[ ℹ️ ] Seleccione una opción:\n' +
      '1. Con código QR\n' +
      '2. Con código de texto de 8 dígitos\n' +
      '---> '
    );

    if (!/^[1-2]$/.test(opcion)) {
      console.log(
        '[ ⚠️ ] Por favor, seleccione solo 1 o 2.\n'
      );
    }
  } while (
    opcion !== '1' &&
    opcion !== '2'
  );
}

const filterStrings = [
  'Q2xvc2luZyBzdGFsZSBvcGVu',
  'Q2xvc2luZyBvcGVuIHNlc3Npb24=',
  'RmFpbGVkIHRvIGRlY3J5cHQ=',
  'U2Vzc2lvbiBlcnJvcg==',
  'RXJyb3I6IEJhZCBNQUM=',
  'RGVjcnlwdGVkIG1lc3NhZ2U='
];

console.info = () => {};
console.debug = () => {};

[
  'log',
  'warn',
  'error'
].forEach((methodName) => {
  const originalMethod =
    console[methodName];

  console[methodName] = function (...args) {
    const firstMessage = args[0];

    if (
      typeof firstMessage === 'string' &&
      filterStrings.some(
        (filterString) =>
          firstMessage.includes(
            Buffer.from(
              filterString,
              'base64'
            ).toString()
          )
      )
    ) {
      args[0] = '';
    }

    originalMethod.apply(
      console,
      args
    );
  };
});

process.on(
  'uncaughtException',
  (err) => {
    if (
      err?.message &&
      filterStrings.includes(
        Buffer.from(
          err.message
        ).toString('base64')
      )
    ) {
      return;
    }

    console.error(
      'Uncaught Exception:',
      err
    );
  }
);

const connectionOptions = {
  logger: pino({
    level: 'silent'
  }),

  printQRInTerminal:
    opcion === '1' ||
    methodCodeQR,

  mobile: MethodMobile,

  browser:
    opcion === '1' || methodCodeQR
      ? [
          'TheMystic-Bot-MD',
          'Safari',
          '2.0.0'
        ]
      : [
          'Ubuntu',
          'Chrome',
          '20.0.04'
        ],

  auth: {
    creds: state.creds,

    keys:
      makeCacheableSignalKeyStore(
        state.keys,
        Pino({
          level: 'fatal'
        }).child({
          level: 'fatal'
        })
      )
  },

  markOnlineOnConnect: false,

  generateHighQualityLinkPreview:
    true,

  syncFullHistory: false,

  getMessage: async (key) => {
    try {
      const jid =
        jidNormalizedUser(
          key.remoteJid
        );

      const msg =
        await store.loadMessage(
          jid,
          key.id
        );

      return msg?.message || undefined;
    } catch {
      return undefined;
    }
  },

  msgRetryCounterCache,

  userDevicesCache,

  defaultQueryTimeoutMs:
    undefined,

  cachedGroupMetadata: (jid) =>
    global.conn?.chats?.[jid] ?? {},

  keepAliveIntervalMs: 55000,

  maxIdleTimeMs: 60000,

  version
};

global.conn =
  makeWASocket(connectionOptions);

conn = global.conn;

const lidResolver =
  new LidResolver(global.conn);

/* ------------------------------------------------ */
/* CORRECCIÓN AUTOMÁTICA LID                       */
/* ------------------------------------------------ */

setTimeout(async () => {
  try {
    if (
      lidResolver &&
      typeof lidResolver.autoCorrectPhoneNumbers ===
        'function'
    ) {
      await lidResolver.autoCorrectPhoneNumbers();
    }
  } catch (error) {
    console.error(
      '❌ Error en análisis inicial:',
      error.message
    );
  }
}, 5000);

/* ------------------------------------------------ */
/* EMPAREJAMIENTO                                   */
/* ------------------------------------------------ */

if (
  !fs.existsSync(
    `./${global.authFile}/creds.json`
  )
) {
  if (opcion === '2' || methodCode) {
    opcion = '2';

    if (!conn.authState?.creds?.registered) {
      if (MethodMobile) {
        throw new Error(
          'No se puede usar un código de emparejamiento con la API móvil'
        );
      }

      let numeroTelefono;

      if (phoneNumber) {
        numeroTelefono =
          phoneNumber.replace(
            /[^0-9]/g,
            ''
          );

        if (
          !Object.keys(
            PHONENUMBER_MCC
          ).some((v) =>
            numeroTelefono.startsWith(v)
          )
        ) {
          console.log(
            chalk.bgBlack(
              chalk.bold.redBright(
                'Comience con el código de país de su número de WhatsApp.\n' +
                'Ejemplo: +5219992095479\n'
              )
            )
          );

          process.exit(0);
        }
      } else {
        while (true) {
          numeroTelefono =
            await question(
              chalk.bgBlack(
                chalk.bold.yellowBright(
                  'Por favor, escriba su número de WhatsApp.\n' +
                  'Ejemplo: +5219992095479\n'
                )
              )
            );

          numeroTelefono =
            numeroTelefono.replace(
              /[^0-9]/g,
              ''
            );

          if (
            numeroTelefono.match(
              /^\d+$/
            ) &&
            Object.keys(
              PHONENUMBER_MCC
            ).some((v) =>
              numeroTelefono.startsWith(v)
            )
          ) {
            break;
          }

          console.log(
            chalk.bgBlack(
              chalk.bold.redBright(
                'Por favor, escriba un número válido de WhatsApp.\n' +
                'Ejemplo: +5219992095479.\n'
              )
            )
          );
        }

        rl.close();
      }

      setTimeout(async () => {
        try {
          let codigo =
            await conn.requestPairingCode(
              numeroTelefono
            );

          codigo =
            codigo
              ?.match(/.{1,4}/g)
              ?.join('-') ||
            codigo;

          console.log(
            chalk.yellow(
              '[ ℹ️ ] Introduce el código de emparejamiento en WhatsApp.'
            )
          );

          console.log(
            chalk.black(
              chalk.bgGreen(
                'Su código de emparejamiento: '
              )
            ),
            chalk.black(
              chalk.white(codigo)
            )
          );
        } catch (error) {
          console.error(
            '❌ Error solicitando código de emparejamiento:',
            error.message
          );
        }
      }, 3000);
    }
  }
}

conn.isInit = false;
conn.well = false;

conn.logger.info(
  '[　ℹ️　] Cargando...\n'
);

/* ------------------------------------------------ */
/* BASE DE DATOS                                    */
/* ------------------------------------------------ */

if (!opts.test) {
  if (global.db) {
    setInterval(async () => {
      try {
        if (global.db.data) {
          await global.db.write();
        }

        if (
          opts.autocleartmp &&
          global.support?.find
        ) {
          const tmp = [
            os.tmpdir(),
            'tmp',
            'jadibts'
          ];

          tmp.forEach((filename) => {
            try {
              cp.spawn(
                'find',
                [
                  filename,
                  '-amin',
                  '3',
                  '-type',
                  'f',
                  '-delete'
                ],
                {
                  stdio: 'ignore'
                }
              );
            } catch {}
          });
        }
      } catch (error) {
        console.error(
          '❌ Error en mantenimiento de DB:',
          error.message
        );
      }
    }, 30000);
  }
}

/* ------------------------------------------------ */
/* SERVIDOR                                         */
/* ------------------------------------------------ */

if (opts.server) {
  try {
    const server =
      await import('./server.js');

    if (
      typeof server.default ===
      'function'
    ) {
      await server.default(
        global.conn,
        PORT
      );
    }
  } catch (error) {
    console.error(
      '❌ Error iniciando servidor:',
      error
    );
  }
}

/* ------------------------------------------------ */
/* ARCHIVOS TEMPORALES                              */
/* ------------------------------------------------ */

function clearTmp() {
  const tmp = [
    join(__dirname, './src/tmp')
  ];

  const filename = [];

  for (const dirname of tmp) {
    if (!existsSync(dirname)) {
      continue;
    }

    for (const file of readdirSync(
      dirname
    )) {
      filename.push(
        join(dirname, file)
      );
    }
  }

  return filename.map((file) => {
    try {
      const stats = statSync(file);

      if (
        stats.isFile() &&
        Date.now() -
          stats.mtimeMs >=
          1000 * 60 * 3
      ) {
        unlinkSync(file);
        return true;
      }
    } catch {}

    return false;
  });
}

/* ------------------------------------------------ */
/* ELIMINAR CORE DUMPS                              */
/* ------------------------------------------------ */

const dirToWatchccc =
  path.join(__dirname, './');

function deleteCoreFiles(filePath) {
  const coreFilePattern =
    /^core\.\d+$/i;

  const filename =
    path.basename(filePath);

  if (
    coreFilePattern.test(filename)
  ) {
    fs.unlink(
      filePath,
      (err) => {
        if (err && err.code !== 'ENOENT') {
          console.error(
            `Error eliminando el archivo ${filePath}:`,
            err
          );
        }
      }
    );
  }
}

try {
  fs.watch(
    dirToWatchccc,
    (eventType, filename) => {
      if (
        eventType !== 'rename' ||
        !filename
      ) {
        return;
      }

      const filePath =
        path.join(
          dirToWatchccc,
          filename.toString()
        );

      fs.stat(
        filePath,
        (err, stats) => {
          if (
            !err &&
            stats.isFile()
          ) {
            deleteCoreFiles(
              filePath
            );
          }
        }
      );
    }
  );
} catch (error) {
  console.error(
    '⚠️ No se pudo iniciar el watcher de archivos:',
    error.message
  );
}

/* ------------------------------------------------ */
/* SESIONES                                         */
/* ------------------------------------------------ */

function purgeSession() {
  const sessionDir =
    './MysticSession';

  if (!existsSync(sessionDir)) {
    return;
  }

  const directorio =
    readdirSync(sessionDir);

  const filesFolderPreKeys =
    directorio.filter((file) =>
      file.startsWith(
        'pre-key-'
      )
    );

  for (const file of filesFolderPreKeys) {
    try {
      unlinkSync(
        path.join(
          sessionDir,
          file
        )
      );
    } catch {}
  }
}

function purgeSessionSB() {
  try {
    const baseDir =
      './jadibts';

    if (!existsSync(baseDir)) {
      return;
    }

    const listaDirectorios =
      readdirSync(baseDir);

    for (const directorio of listaDirectorios) {
      const fullDirectory =
        path.join(
          baseDir,
          directorio
        );

      try {
        if (
          statSync(
            fullDirectory
          ).isDirectory()
        ) {
          const DSBPreKeys =
            readdirSync(
              fullDirectory
            ).filter(
              (fileInDir) =>
                fileInDir.startsWith(
                  'pre-key-'
                )
            );

          for (const fileInDir of DSBPreKeys) {
            try {
              unlinkSync(
                path.join(
                  fullDirectory,
                  fileInDir
                )
              );
            } catch {}
          }
        }
      } catch {}
    }
  } catch {
    console.log(
      chalk.bold.red(
        '[ ℹ️ ] Algo salió mal durante la eliminación, archivos no eliminados'
      )
    );
  }
}

function purgeOldFiles() {
  const directories = [
    './MysticSession/',
    './jadibts/'
  ];

  const oneHourAgo =
    Date.now() -
    60 * 60 * 1000;

  for (const dir of directories) {
    if (!existsSync(dir)) {
      continue;
    }

    let files = [];

    try {
      files =
        readdirSync(dir);
    } catch {
      continue;
    }

    for (const file of files) {
      if (file === 'creds.json') {
        continue;
      }

      const filePath =
        path.join(
          dir,
          file
        );

      try {
        const stats =
          statSync(filePath);

        if (
          stats.isFile() &&
          stats.mtimeMs <
            oneHourAgo
        ) {
          unlinkSync(filePath);
        }
      } catch {}
    }
  }
}

/* ------------------------------------------------ */
/* ACTUALIZACIÓN DE CONEXIÓN                        */
/* ------------------------------------------------ */

async function connectionUpdate(update) {
  let isFirstConnection = false;

  const {
    connection,
    lastDisconnect,
    isNewLogin
  } = update;

  stopped = connection;

  if (isNewLogin && conn) {
    conn.isInit = true;
  }

  const code =
    lastDisconnect?.error?.output
      ?.statusCode ||
    lastDisconnect?.error?.output
      ?.payload?.statusCode;

  if (
    code &&
    code !==
      DisconnectReason.loggedOut &&
    conn?.ws?.socket == null
  ) {
    await global.reloadHandler(
      true
    ).catch(console.error);

    global.timestamp.connect =
      new Date();
  }

  if (
    global.db.data == null
  ) {
    await global.loadDatabase();
  }

  if (
    (update.qr !== 0 &&
      update.qr !== undefined) ||
    methodCodeQR
  ) {
    if (
      opcion === '1' ||
      methodCodeQR
    ) {
      console.log(
        chalk.yellow(
          '[　ℹ️　　] Escanea el código QR.'
        )
      );
    }
  }

  if (connection === 'open') {
    console.log(
      chalk.yellow(
        '[　ℹ️　　] Conectado correctamente.'
      )
    );

    isFirstConnection = true;

    if (
      !global.subBotsInitialized
    ) {
      global.subBotsInitialized =
        true;

      try {
        await initializeSubBots();
      } catch (error) {
        console.error(
          chalk.red(
            '[ ⚠️ ] Error al inicializar sub-bots:'
          ),
          error
        );
      }
    }
  }

  const reason =
    new Boom(
      lastDisconnect?.error
    )?.output?.statusCode;

  const errorCounters = {};

  function shouldLogError(
    errorType
  ) {
    if (
      !errorCounters[
        errorType
      ]
    ) {
      errorCounters[
        errorType
      ] = {
        count: 0,
        lastShown: 0
      };
    }

    const now =
      Date.now();

    const errorData =
      errorCounters[
        errorType
      ];

    if (
      errorData.count >= 5
    ) {
      return false;
    }

    if (
      now -
        errorData.lastShown <
      2000
    ) {
      return false;
    }

    errorData.count++;
    errorData.lastShown =
      now;

    return true;
  }

  if (reason === 405) {
    console.log(
      chalk.bold.redBright(
        '[ ⚠️ ] Conexión reemplazada. Por favor espere un momento mientras se reconecta...'
      )
    );
  }

  if (connection === 'close') {
    if (
      reason ===
      DisconnectReason.badSession
    ) {
      if (
        shouldLogError(
          'badSession'
        )
      ) {
        conn.logger.error(
          `[ ⚠️ ] Sesión incorrecta, por favor elimina la carpeta ${global.authFile} y escanea nuevamente.`
        );
      }

      await global.reloadHandler(
        true
      ).catch(console.error);
    } else if (
      reason ===
      DisconnectReason.connectionClosed
    ) {
      if (
        shouldLogError(
          'connectionClosed'
        )
      ) {
        conn.logger.warn(
          '[ ⚠️ ] Conexión cerrada, reconectando...'
        );
      }

      await global.reloadHandler(
        true
      ).catch(console.error);
    } else if (
      reason ===
      DisconnectReason.connectionLost
    ) {
      if (
        shouldLogError(
          'connectionLost'
        )
      ) {
        conn.logger.warn(
          '[ ⚠️ ] Conexión perdida con el servidor, reconectando...'
        );
      }

      await global.reloadHandler(
        true
      ).catch(console.error);
    } else if (
      reason ===
      DisconnectReason.connectionReplaced
    ) {
      if (
        shouldLogError(
          'connectionReplaced'
        )
      ) {
        conn.logger.error(
          '[ ⚠️ ] Conexión reemplazada. Se ha abierto otra sesión.'
        );
      }

      await global.reloadHandler(
        true
      ).catch(console.error);
    } else if (
      reason ===
      DisconnectReason.loggedOut
    ) {
      if (
        shouldLogError(
          'loggedOut'
        )
      ) {
        conn.logger.error(
          `[ ⚠️ ] Conexión cerrada. Elimina la carpeta ${global.authFile} y escanea nuevamente.`
        );
      }
    } else if (
      reason ===
      DisconnectReason.restartRequired
    ) {
      if (isFirstConnection) {
        isFirstConnection =
          false;
      } else {
        if (
          shouldLogError(
            'restartRequired'
          )
        ) {
          conn.logger.info(
            '[ ⚠️ ] Reinicio necesario, reconectando...'
          );
        }

        await global.reloadHandler(
          true
        ).catch(console.error);
      }
    } else if (
      reason ===
      DisconnectReason.timedOut
    ) {
      if (
        shouldLogError(
          'timedOut'
        )
      ) {
        conn.logger.warn(
          '[ ⚠️ ] Tiempo de conexión agotado, reconectando...'
        );
      }

      await global.reloadHandler(
        true
      ).catch(console.error);
    } else {
      const unknownError =
        `unknown_${reason || ''}_${connection || ''}`;

      if (
        shouldLogError(
          unknownError
        )
      ) {
        conn.logger.warn(
          `[ ⚠️ ] Razón de desconexión desconocida. ${reason || ''}: ${connection || ''}`
        );
      }

      await global.reloadHandler(
        true
      ).catch(console.error);
    }
  }
}

/* ------------------------------------------------ */
/* HANDLER                                           */
/* ------------------------------------------------ */

process.on(
  'uncaughtException',
  (error) => {
    console.error(
      '❌ Uncaught Exception:',
      error
    );
  }
);

let isInit = true;

try {
  handler =
    await import(
      './handler.js'
    );
} catch (error) {
  console.error(
    '❌ Error cargando handler.js:',
    error
  );

  handler = {};
}

global.reloadHandler =
  async function reloadHandler(
    restatConn
  ) {
    try {
      const Handler =
        await import(
          `./handler.js?update=${Date.now()}`
        );

      if (
        Object.keys(
          Handler || {}
        ).length
      ) {
        handler = Handler;
      }
    } catch (error) {
      console.error(
        '❌ Error recargando handler:',
        error
      );
    }

    if (restatConn) {
      const oldChats =
        global.conn?.chats || {};

      try {
        global.conn?.ws?.close();
      } catch {}

      try {
        global.conn?.ev?.removeAllListeners();
      } catch {}

      global.conn =
        makeWASocket(
          connectionOptions,
          {
            chats: oldChats
          }
        );

      conn = global.conn;

      try {
        store?.bind?.(conn);
      } catch (error) {
        console.error(
          '⚠️ Error vinculando store:',
          error.message
        );
      }

      lidResolver.conn =
        global.conn;

      isInit = true;
    }

    if (!conn) {
      return false;
    }

    if (!isInit) {
      try {
        conn.ev.off(
          'messages.upsert',
          conn.handler
        );

        conn.ev.off(
          'group-participants.update',
          conn.participantsUpdate
        );

        conn.ev.off(
          'groups.update',
          conn.groupsUpdate
        );

        conn.ev.off(
          'message.delete',
          conn.onDelete
        );

        conn.ev.off(
          'call',
          conn.onCall
        );

        conn.ev.off(
          'connection.update',
          conn.connectionUpdate
        );

        conn.ev.off(
          'creds.update',
          conn.credsUpdate
        );
      } catch {}
    }

    conn.welcome =
      '👋 ¡Bienvenido/a!\n@user';

    conn.bye =
      '👋 ¡Hasta luego!\n@user';

    conn.spromote =
      '*[ ℹ️ ] @user Fue promovido a administrador.*';

    conn.sdemote =
      '*[ ℹ️ ] @user Fue degradado de administrador.*';

    conn.sDesc =
      '*[ ℹ️ ] La descripción del grupo ha sido modificada.*';

    conn.sSubject =
      '*[ ℹ️ ] El nombre del grupo ha sido modificado.*';

    conn.sIcon =
      '*[ ℹ️ ] Se ha cambiado la foto de perfil del grupo.*';

    conn.sRevoke =
      '*[ ℹ️ ] El enlace de invitación al grupo ha sido restablecido.*';

    if (
      typeof handler?.handler ===
      'function'
    ) {
      const originalHandler =
        handler.handler.bind(
          global.conn
        );

      conn.handler =
        async function (
          chatUpdate
        ) {
          try {
            if (
              chatUpdate?.messages
            ) {
              chatUpdate.messages =
                await interceptMessages(
                  chatUpdate.messages,
                  lidResolver
                );

              for (
                let i = 0;
                i <
                chatUpdate.messages.length;
                i++
              ) {
                const message =
                  chatUpdate.messages[i];

                if (
                  message?.key?.remoteJid?.endsWith?.(
                    '@g.us'
                  )
                ) {
                  try {
                    const fullyProcessedMessage =
                      await processMessageForDisplay(
                        message,
                        lidResolver
                      );

                    chatUpdate.messages[
                      i
                    ] =
                      fullyProcessedMessage;

                    const messageText =
                      extractAllText(
                        fullyProcessedMessage
                      );

                    if (
                      messageText &&
                      /(@\d{8,20})/.test(
                        messageText
                      )
                    ) {
                      // LID aún no resuelto.
                    }
                  } catch (error) {
                    console.error(
                      '❌ Error en procesamiento final de mensaje:',
                      error
                    );
                  }
                }
              }
            }

            return await originalHandler(
              chatUpdate
            );
          } catch (error) {
            console.error(
              '❌ Error en handler interceptor:',
              error
            );

            try {
              return await originalHandler(
                chatUpdate
              );
            } catch (handlerError) {
              console.error(
                '❌ Error ejecutando handler original:',
                handlerError
              );
            }
          }
        };
    } else {
      conn.handler =
        async function () {
          console.error(
            '❌ handler.handler no está disponible.'
          );
        };
    }

    if (
      typeof handler?.participantsUpdate ===
      'function'
    ) {
      conn.participantsUpdate =
        handler.participantsUpdate.bind(
          global.conn
        );
    } else {
      conn.participantsUpdate =
        async () => {};
    }

    if (
      typeof handler?.groupsUpdate ===
      'function'
    ) {
      conn.groupsUpdate =
        handler.groupsUpdate.bind(
          global.conn
        );
    } else {
      conn.groupsUpdate =
        async () => {};
    }

    if (
      typeof handler?.deleteUpdate ===
      'function'
    ) {
      conn.onDelete =
        handler.deleteUpdate.bind(
          global.conn
        );
    } else {
      conn.onDelete =
        async () => {};
    }

    if (
      typeof handler?.callUpdate ===
      'function'
    ) {
      conn.onCall =
        handler.callUpdate.bind(
          global.conn
        );
    } else {
      conn.onCall =
        async () => {};
    }

    conn.connectionUpdate =
      connectionUpdate.bind(
        global.conn
      );

    conn.credsUpdate =
      saveCreds.bind(
        global.conn,
        true
      );

    conn.ev.on(
      'messages.upsert',
      conn.handler
    );

    conn.ev.on(
      'group-participants.update',
      conn.participantsUpdate
    );

    conn.ev.on(
      'groups.update',
      conn.groupsUpdate
    );

    conn.ev.on(
      'message.delete',
      conn.onDelete
    );

    conn.ev.on(
      'call',
      conn.onCall
    );

    conn.ev.on(
      'connection.update',
      conn.connectionUpdate
    );

    conn.ev.on(
      'creds.update',
      conn.credsUpdate
    );

    isInit = false;

    return true;
  };

/* ------------------------------------------------ */
/* FUNCIONES LID EN CONN                            */
/* ------------------------------------------------ */

conn.lid = {
  getUserInfo: (lidNumber) =>
    lidDataManager.getUserInfo(
      lidNumber
    ),

  getUserInfoByJid: (jid) =>
    lidDataManager.getUserInfoByJid(
      jid
    ),

  findLidByJid: (jid) =>
    lidDataManager.findLidByJid(
      jid
    ),

  getAllUsers: () =>
    lidDataManager.getAllUsers(),

  getStats: () =>
    lidDataManager.getStats(),

  getUsersByCountry: () =>
    lidDataManager.getUsersByCountry(),

  validatePhoneNumber: (
    phoneNumber
  ) => {
    if (
      !lidResolver.phoneValidator ||
      typeof lidResolver.phoneValidator
        .isValidPhoneNumber !==
        'function'
    ) {
      return false;
    }

    return lidResolver.phoneValidator
      .isValidPhoneNumber(
        phoneNumber
      );
  },

  detectPhoneInLid: (
    lidString
  ) => {
    if (
      !lidResolver.phoneValidator ||
      typeof lidResolver.phoneValidator
        .detectPhoneInLid !==
        'function'
    ) {
      return {
        isPhone: false
      };
    }

    return lidResolver.phoneValidator
      .detectPhoneInLid(
        lidString
      );
  },

  forceSave: () => {
    try {
      if (
        typeof lidResolver.forceSave ===
        'function'
      ) {
        lidResolver.forceSave();
      }

      return true;
    } catch (error) {
      console.error(
        'Error guardando caché LID:',
        error
      );

      return false;
    }
  },

  getCacheInfo: () => {
    try {
      const stats =
        lidDataManager.getStats();

      const analysis =
        typeof lidResolver.analyzePhoneNumbers ===
        'function'
          ? lidResolver.analyzePhoneNumbers()
          : {
              stats: {
                phoneNumbersProblematic: 0
              }
            };

      const countries =
        lidDataManager.getUsersByCountry();

      return (
        `📱 *ESTADÍSTICAS DEL CACHÉ LID*\n\n` +
        `📊 *General:*\n` +
        `• Total de entradas: ${stats.total}\n` +
        `• Entradas válidas: ${stats.valid}\n` +
        `• No encontradas: ${stats.notFound}\n` +
        `• Con errores: ${stats.errors}\n\n` +
        `📞 *Números telefónicos:*\n` +
        `• Detectados: ${stats.phoneNumbers}\n` +
        `• Corregidos: ${stats.corrected}\n` +
        `• Problemáticos: ${analysis.stats?.phoneNumbersProblematic || 0}\n\n` +
        `🗂️ *Caché:*\n` +
        `• Archivo: ${stats.cacheFile}\n` +
        `• Existe: ${stats.fileExists ? 'Sí' : 'No'}\n\n` +
        `🌍 *Países detectados:*\n` +
        `${Object.entries(countries)
          .slice(0, 5)
          .map(
            ([country, users]) =>
              `• ${country}: ${users.length} usuarios`
          )
          .join('\n')}`
      );
    } catch (error) {
      return `❌ Error obteniendo información: ${error.message}`;
    }
  },

  forcePhoneCorrection: () => {
    try {
      if (
        typeof lidResolver.autoCorrectPhoneNumbers !==
        'function'
      ) {
        return '⚠️ La función de corrección automática no está disponible.';
      }

      const result =
        lidResolver.autoCorrectPhoneNumbers();

      if (
        result &&
        result.corrected > 0
      ) {
        return `✅ Se corrigieron ${result.corrected} números telefónicos automáticamente.`;
      }

      return '✅ No se encontraron números telefónicos que requieran corrección.';
    } catch (error) {
      return `❌ Error en corrección automática: ${error.message}`;
    }
  },

  resolveLid: async (
    lidJid,
    groupChatId
  ) => {
    try {
      return await lidResolver.resolveLid(
        lidJid,
        groupChatId
      );
    } catch (error) {
      console.error(
        'Error resolviendo LID:',
        error
      );

      return lidJid;
    }
  },

  processTextMentions: async (
    text,
    groupId
  ) => {
    try {
      return await processTextMentions(
        text,
        groupId,
        lidResolver
      );
    } catch (error) {
      console.error(
        'Error procesando menciones en texto:',
        error
      );

      return text;
    }
  }
};

/* ------------------------------------------------ */
/* PLUGINS                                          */
/* ------------------------------------------------ */

const pluginFolder =
  global.__dirname(
    join(
      __dirname,
      './plugins/index'
    )
  );

const pluginFilter =
  (filename) =>
    typeof filename === 'string' &&
    /\.js$/.test(filename);

global.plugins = {};

if (!existsSync(pluginFolder)) {
  try {
    mkdirSync(
      pluginFolder,
      {
        recursive: true
      }
    );
  } catch (error) {
    console.error(
      '❌ No se pudo crear la carpeta de plugins:',
      error
    );
  }
}

async function filesInit() {
  if (!existsSync(pluginFolder)) {
    return;
  }

  for (
    const filename of readdirSync(
      pluginFolder
    ).filter(pluginFilter)
  ) {
    try {
      const file =
        global.__filename(
          join(
            pluginFolder,
            filename
          )
        );

      const module =
        await import(file);

      global.plugins[
        filename
      ] =
        module.default ||
        module;
    } catch (error) {
      conn.logger.error(
        error
      );

      delete global.plugins[
        filename
      ];
    }
  }
}

await filesInit();

global.reload =
  async function reload(
    _ev,
    filename
  ) {
    if (!pluginFilter(filename)) {
      return;
    }

    const dir =
      global.__filename(
        join(
          pluginFolder,
          filename
        ),
        true
      );

    if (
      filename in
      global.plugins
    ) {
      if (
        existsSync(dir)
      ) {
        conn.logger.info(
          ` updated plugin - '${filename}'`
        );
      } else {
        conn.logger.warn(
          `deleted plugin - '${filename}'`
        );

        delete global.plugins[
          filename
        ];

        return;
      }
    } else {
      conn.logger.info(
        `new plugin - '${filename}'`
      );
    }

    if (!existsSync(dir)) {
      return;
    }

    let source;

    try {
      source =
        readFileSync(
          dir,
          'utf8'
        );
    } catch (error) {
      conn.logger.error(
        `error reading plugin '${filename}'\n${format(error)}`
      );

      return;
    }

    const err =
      syntaxerror(
        source,
        filename,
        {
          sourceType:
            'module',
          allowAwaitOutsideFunction:
            true
        }
      );

    if (err) {
      conn.logger.error(
        `syntax error while loading '${filename}'\n${format(err)}`
      );

      return;
    }

    try {
      const module =
        await import(
          `${global.__filename(
            dir
          )}?update=${Date.now()}`
        );

      global.plugins[
        filename
      ] =
        module.default ||
        module;
    } catch (error) {
      conn.logger.error(
        `error require plugin '${filename}'\n${format(error)}`
      );
    } finally {
      global.plugins =
        Object.fromEntries(
          Object.entries(
            global.plugins
          ).sort(
            ([a], [b]) =>
              a.localeCompare(b)
          )
        );
    }
  };

try {
  watch(
    pluginFolder,
    global.reload
  );
} catch (error) {
  console.error(
    '⚠️ No se pudo iniciar el watcher de plugins:',
    error.message
  );
}

/* ------------------------------------------------ */
/* INICIAR HANDLER                                  */
/* ------------------------------------------------ */

await global.reloadHandler();

/* ------------------------------------------------ */
/* LIMPIEZA TEMPORAL                                */
/* ------------------------------------------------ */

setInterval(
  async () => {
    try {
      if (
        stopped === 'close' ||
        !conn ||
        !conn?.user
      ) {
        return;
      }

      await clearTmp();
    } catch (error) {
      console.error(
        '❌ Error limpiando archivos temporales:',
        error.message
      );
    }
  },
  180000
);

/* ------------------------------------------------ */
/* ESTADO DEL PERFIL                                */
/* ------------------------------------------------ */

setInterval(
  async () => {
    try {
      if (
        stopped === 'close' ||
        !conn ||
        !conn?.user
      ) {
        return;
      }

      const uptimeMs =
        process.uptime() *
        1000;

      const uptime =
        clockString(
          uptimeMs
        );

      const bio =
        `• Activo: ${uptime} | TheMystic-Bot-MD`;

      if (
        typeof conn.updateProfileStatus ===
        'function'
      ) {
        await conn
          .updateProfileStatus(
            bio
          )
          .catch(() => {});
      }
    } catch {}
  },
  60000
);

/* ------------------------------------------------ */
/* LIMPIEZA Y OPTIMIZACIÓN DEL CACHÉ LID           */
/* ------------------------------------------------ */

setInterval(
  async () => {
    if (
      stopped === 'close' ||
      !conn ||
      !conn?.user ||
      !lidResolver
    ) {
      return;
    }

    try {
      const stats =
        lidDataManager.getStats();

      if (
        stats.total > 800 &&
        lidResolver.cache
      ) {
        const sevenDaysAgo =
          Date.now() -
          7 *
            24 *
            60 *
            60 *
            1000;

        let cleanedCount = 0;

        for (
          const [
            key,
            entry
          ] of lidResolver.cache.entries()
        ) {
          if (
            entry &&
            entry.timestamp &&
            entry.timestamp <
              sevenDaysAgo &&
            (entry.notFound ||
              entry.error)
          ) {
            lidResolver.cache.delete(
              key
            );

            if (
              entry.jid &&
              lidResolver.jidToLidMap?.has(
                entry.jid
              )
            ) {
              lidResolver.jidToLidMap.delete(
                entry.jid
              );
            }

            cleanedCount++;
          }
        }

        if (
          cleanedCount > 0 &&
          typeof lidResolver.markDirty ===
            'function'
        ) {
          lidResolver.markDirty();
        }
      }

      if (
        Math.random() < 0.1 &&
        typeof lidResolver.autoCorrectPhoneNumbers ===
          'function'
      ) {
        await lidResolver.autoCorrectPhoneNumbers();
      }
    } catch (error) {
      console.error(
        '❌ Error en limpieza de caché LID:',
        error.message
      );
    }
  },
  30 * 60 * 1000
);

/* ------------------------------------------------ */
/* UPTIME                                           */
/* ------------------------------------------------ */

function clockString(ms) {
  const d = Number.isNaN(ms)
    ? '--'
    : Math.floor(
        ms / 86400000
      );

  const h = Number.isNaN(ms)
    ? '--'
    : Math.floor(
        ms / 3600000
      ) % 24;

  const m = Number.isNaN(ms)
    ? '--'
    : Math.floor(
        ms / 60000
      ) % 60;

  const s = Number.isNaN(ms)
    ? '--'
    : Math.floor(
        ms / 1000
      ) % 60;

  return [
    d,
    'd ',
    h,
    'h ',
    m,
    'm ',
    s,
    's '
  ]
    .map((v) =>
      String(v).padStart(
        2,
        '0'
      )
    )
    .join('');
}

/* ------------------------------------------------ */
/* APAGADO SEGURO                                   */
/* ------------------------------------------------ */

const gracefulShutdown =
  () => {
    try {
      if (
        lidResolver?.isDirty &&
        typeof lidResolver.forceSave ===
          'function'
      ) {
        lidResolver.forceSave();
      }
    } catch (error) {
      console.error(
        '❌ Error guardando caché LID:',
        error.message
      );
    }
  };

process.on(
  'exit',
  gracefulShutdown
);

process.on(
  'SIGINT',
  () => {
    gracefulShutdown();
    process.exit(0);
  }
);

process.on(
  'SIGTERM',
  () => {
    gracefulShutdown();
    process.exit(0);
  }
);

/* ------------------------------------------------ */
/* ERRORES NO MANEJADOS                             */
/* ------------------------------------------------ */

process.on(
  'unhandledRejection',
  (reason) => {
    if (
      reason?.message &&
      String(
        reason.message
      ).toLowerCase().includes('lid')
    ) {
      console.error(
        '❌ Error no manejado relacionado con LID:',
        reason
      );
    } else {
      console.error(
        '❌ Unhandled Rejection:',
        reason
      );
    }
  }
);

/* ------------------------------------------------ */
/* PRUEBA DE DEPENDENCIAS                           */
/* ------------------------------------------------ */

async function _quickTest() {
  const commands = [
    ['ffmpeg', []],
    ['ffprobe', []],
    [
      'ffmpeg',
      [
        '-hide_banner',
        '-loglevel',
        'error',
        '-filter_complex',
        'color',
        '-frames:v',
        '1',
        '-f',
        'webp',
        '-'
      ]
    ],
    ['convert', []],
    ['magick', []],
    ['gm', []],
    ['find', ['--version']]
  ];

  const test =
    await Promise.all(
      commands.map(
        ([command, args]) => {
          return new Promise(
            (resolve) => {
              let finished =
                false;

              let child;

              try {
                child =
                  spawn(
                    command,
                    args,
                    {
                      stdio:
                        'ignore'
                    }
                  );
              } catch {
                resolve(
                  false
                );

                return;
              }

              const finish =
                (result) => {
                  if (
                    finished
                  ) {
                    return;
                  }

                  finished =
                    true;

                  resolve(
                    result
                  );
                };

              child.on(
                'close',
                (code) => {
                  finish(
                    code === 0
                  );
                }
              );

              child.on(
                'error',
                () => {
                  finish(
                    false
                  );
                }
              );

              setTimeout(
                () => {
                  try {
                    child.kill();
                  } catch {}

                  finish(
                    false
                  );
                },
                5000
              );
            }
          );
        }
      )
    );

  const [
    ffmpeg,
    ffprobe,
    ffmpegWebp,
    convert,
    magick,
    gm,
    find
  ] = test;

  global.support = {
    ffmpeg,
    ffprobe,
    ffmpegWebp,
    convert,
    magick,
    gm,
    find
  };

  Object.freeze(
    global.support
  );
}

/* Ejecutar prueba de dependencias */
try {
  await _quickTest();
} catch (error) {
  console.error(
    '⚠️ Error comprobando dependencias:',
    error.message
  );
}

/* ------------------------------------------------ */
/* LIMPIEZA INICIAL OPCIONAL                        */
/* ------------------------------------------------ */

try {
  purgeOldFiles();
} catch {}

try {
  purgeSession();
} catch {}

try {
  purgeSessionSB();
} catch {}
