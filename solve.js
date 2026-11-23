// solve.js — a fast drop-in for makefun-site 1.0.0 (site-generator-speed-01).
// run(input) returns the same output tree the reference build returns, byte for byte,
// with the work reorganised for speed: bulk HTML escaping, single-pass Markdown,
// an ASCII fast path for slugs, and a template renderer that walks pre-parsed nodes.
// Original implementation written for this bounty; no dependencies, ES module.

/* ------------------------------------------------------------------ text */

// The HTML escape table: & < > " ' and nothing else.
const ESC_TABLE = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const ESC_RE = /[&<>"']/g;

/** Append s[start..end) HTML-escaped to out (one regex pass, runs pushed whole). */
function escRange(s, start, end, out) {
  ESC_RE.lastIndex = start;
  let m;
  let last = start;
  while ((m = ESC_RE.exec(s)) !== null && m.index < end) {
    if (m.index > last) out.push(s.slice(last, m.index));
    out.push(ESC_TABLE[m[0]]);
    last = m.index + 1;
  }
  if (last < end) out.push(s.slice(last, end));
}

/** s HTML-escaped, as a string (fast path when nothing needs escaping). */
function escStr(s) {
  if (
    s.indexOf('&') === -1 && s.indexOf('<') === -1 && s.indexOf('>') === -1 &&
    s.indexOf('"') === -1 && s.indexOf("'") === -1
  ) {
    return s;
  }
  const out = [];
  escRange(s, 0, s.length, out);
  return out.join('');
}

const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];

/** A validated YYYY-MM-DD date in words, from the string alone. */
function longDate(d) {
  const m = (d.charCodeAt(5) - 48) * 10 + (d.charCodeAt(6) - 48);
  const day = (d.charCodeAt(8) - 48) * 10 + (d.charCodeAt(9) - 48);
  return day + ' ' + MONTHS[m - 1] + ' ' + d.slice(0, 4);
}

const MARK_RE = /\p{M}/gu;

/** Per-build slug memo (reset at the start of every run: nothing carries across cases). */
let slugCache = null;

/**
 * A slug: NFKD, combining marks dropped, A-Z lowered, each run of other characters
 * one '-', none at either end, at most 64 characters (a '-' left at the cut dropped),
 * 'untitled' when nothing is left. Pure-ASCII input skips the normalisation entirely
 * (NFKD is the identity on ASCII and ASCII holds no combining marks).
 */
function slugify(text) {
  const hit = slugCache.get(text);
  if (hit !== undefined) return hit;
  let plain = text;
  let ascii = true;
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) > 127) { ascii = false; break; }
  }
  if (!ascii) plain = text.normalize('NFKD').replace(MARK_RE, '');
  const parts = [];
  let run = '';
  for (let i = 0; i < plain.length; i++) {
    const c = plain.charCodeAt(i);
    if (c >= 65 && c <= 90) run += String.fromCharCode(c + 32);
    else if ((c >= 97 && c <= 122) || (c >= 48 && c <= 57)) run += plain[i];
    else if (run !== '') { parts.push(run); run = ''; }
  }
  if (run !== '') parts.push(run);
  let out = parts.join('-');
  if (out.length > 64) {
    out = out.slice(0, 64);
    let e = out.length;
    while (e > 0 && out.charCodeAt(e - 1) === 45) e--;
    out = out.slice(0, e);
  }
  if (out === '') out = 'untitled';
  slugCache.set(text, out);
  return out;
}

/** `slug` made unique against `taken` (and added to it): slug, slug-2, slug-3 ... */
function uniqueSlug(slug, taken) {
  if (!taken.has(slug)) { taken.add(slug); return slug; }
  let n = 2;
  let out;
  do { out = slug + '-' + n++; } while (taken.has(out));
  taken.add(out);
  return out;
}

/** Whether code unit c is whitespace in JavaScript's \s sense. */
function isWS(c) {
  if (c < 128) return c === 32 || (c >= 9 && c <= 13);
  return c === 0xA0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200A) || c === 0x2028 || c === 0x2029 || c === 0x202F || c === 0x205F || c === 0x3000 || c === 0xFEFF;
}

/** The words of a body: its runs of characters other than whitespace (no allocation). */
function wordsOf(text) {
  let n = 0;
  let inWord = false;
  for (let i = 0; i < text.length; i++) {
    const c = text.charCodeAt(i);
    const ws = c < 128
      ? (c === 32 || (c >= 9 && c <= 13))
      : (c === 0xA0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200A) || c === 0x2028 || c === 0x2029 || c === 0x202F || c === 0x205F || c === 0x3000 || c === 0xFEFF);
    if (ws) inWord = false;
    else if (!inWord) { inWord = true; n++; }
  }
  return n;
}

/** Code-unit order (never the locale's). */
function cmpStr(a, b) {
  return a < b ? -1 : a > b ? 1 : 0;
}

/* ------------------------------------------------------------- front matter */

const FM_KEYS = new Set(['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary']);

function daysIn(y, m) {
  if (m === 2) return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0 ? 29 : 28;
  return m === 4 || m === 6 || m === 9 || m === 11 ? 30 : 31;
}

/** A quoted "..." value: only \" and \\ escapes, no other quote inside. */
function parseQuoted(raw) {
  if (raw.length < 2 || raw.charCodeAt(raw.length - 1) !== 34) return { error: 'a quoted string is not closed' };
  let out = '';
  for (let i = 1; i < raw.length - 1; i++) {
    const c = raw.charCodeAt(i);
    if (c === 92) {
      const n = raw[i + 1];
      if ((n !== '"' && n !== '\\') || i + 1 === raw.length - 1) return { error: 'a quoted string holds an escape other than \\" or \\\\' };
      out += n;
      i++;
    } else if (c === 34) return { error: 'a quoted string holds a stray quote' };
    else out += raw[i];
  }
  return { value: out };
}

/** One key's value, or why it is refused. */
function fmValue(key, raw) {
  switch (key) {
    case 'title':
    case 'summary': {
      if (raw.charCodeAt(0) === 34) {
        const s = parseQuoted(raw);
        return 'error' in s ? { error: `key "${key}": ${s.error}` } : s;
      }
      if (raw.charCodeAt(0) === 91) return { error: `key "${key}": a bare string opens on [` };
      return { value: raw };
    }
    case 'date': {
      const bad = { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
      if (raw.length !== 10 || raw.charCodeAt(4) !== 45 || raw.charCodeAt(7) !== 45) return bad;
      let y = 0;
      let mo = 0;
      let d = 0;
      for (let i = 0; i < 10; i++) {
        if (i === 4 || i === 7) continue;
        const c = raw.charCodeAt(i) - 48;
        if (c < 0 || c > 9) return bad;
        if (i < 4) y = y * 10 + c;
        else if (i < 7) mo = mo * 10 + c;
        else d = d * 10 + c;
      }
      if (y < 1970 || y > 2099 || mo < 1 || mo > 12 || d < 1 || d > daysIn(y, mo)) return bad;
      return { value: raw };
    }
    case 'tags': {
      if (raw.charCodeAt(0) !== 91 || raw.charCodeAt(raw.length - 1) !== 93) return { error: 'key "tags": not a list [a, b]' };
      const inner = raw.slice(1, -1);
      if (inner.trim() === '') return { value: [] };
      const tags = inner.split(',');
      for (let i = 0; i < tags.length; i++) {
        const t = tags[i].trim();
        if (t === '' || t.indexOf('"') !== -1 || t.indexOf('[') !== -1 || t.indexOf(']') !== -1) {
          return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
        }
        tags[i] = t;
      }
      return { value: tags };
    }
    case 'draft':
      if (raw === 'true') return { value: true };
      if (raw === 'false') return { value: false };
      return { error: 'key "draft": true or false' };
    case 'layout': {
      if (raw.length === 0) return { error: 'key "layout": not a template name' };
      for (let i = 0; i < raw.length; i++) {
        const c = raw.charCodeAt(i);
        if (!((c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 45)) return { error: 'key "layout": not a template name' };
      }
      return { value: raw };
    }
    case 'slug': {
      if (raw.length === 0 || raw.length > 64) return { error: 'key "slug": not a slug' };
      let prevDash = true;
      for (let i = 0; i < raw.length; i++) {
        const c = raw.charCodeAt(i);
        if (c === 45) {
          if (prevDash) return { error: 'key "slug": not a slug' };
          prevDash = true;
        } else if ((c >= 97 && c <= 122) || (c >= 48 && c <= 57)) prevDash = false;
        else return { error: 'key "slug": not a slug' };
      }
      if (prevDash) return { error: 'key "slug": not a slug' };
      return { value: raw };
    }
    default:
      return { error: `unknown key "${key}"` };
  }
}

/**
 * A source's front matter and body: { data, body }, or { error } with the first
 * reason it is refused. `text` has "\n" line ends.
 */
function parseFrontMatter(text) {
  if (!text.startsWith('---\n') && text !== '---') return { error: 'no front matter' };
  let close = -1;
  let from = 3;
  for (;;) {
    const p = text.indexOf('\n---', from);
    if (p === -1) break;
    const after = p + 4;
    if (after === text.length || text.charCodeAt(after) === 10) { close = p; break; }
    from = p + 1;
  }
  if (close === -1) return { error: 'the front matter is not closed' };
  const fmText = close <= 4 ? '' : text.slice(4, close);
  const lines = fmText === '' ? [] : fmText.split('\n');
  const data = {};
  for (let k = 0; k < lines.length; k++) {
    const line = lines[k];
    if (line.length === 0) continue;
    const c0 = line.charCodeAt(0);
    if (c0 === 35) continue;
    if (c0 === 32 || c0 === 9) {
      let blank = true;
      for (let j = 1; j < line.length; j++) {
        const c = line.charCodeAt(j);
        if (c !== 32 && c !== 9) { blank = false; break; }
      }
      if (blank) continue;
    }
    const badLine = { error: `line ${k + 2} is not "key: value"` };
    const colon = line.indexOf(':');
    if (colon <= 0) return badLine;
    const key = line.slice(0, colon);
    for (let i = 0; i < key.length; i++) {
      const c = key.charCodeAt(i);
      if (!((c >= 97 && c <= 122) || c === 95)) return badLine;
    }
    let raw;
    if (colon === line.length - 1) raw = '';
    else if (line.charCodeAt(colon + 1) === 32) raw = line.slice(colon + 2);
    else return badLine;
    let e = raw.length;
    while (e > 0) {
      const c = raw.charCodeAt(e - 1);
      if (c === 32 || c === 9) e--;
      else break;
    }
    if (e < raw.length) raw = raw.slice(0, e);
    if (!FM_KEYS.has(key)) return { error: `unknown key "${key}"` };
    if (Object.hasOwn(data, key)) return { error: `key "${key}" is given twice` };
    if (raw === '') return { error: `key "${key}" has no value` };
    const v = fmValue(key, raw);
    if ('error' in v) return v;
    data[key] = v.value;
  }
  if (!Object.hasOwn(data, 'title')) return { error: 'no title' };
  const after = close + 4;
  const body = after === text.length ? '' : text.slice(after + 1);
  return { data, body };
}

/* ----------------------------------------------------------------- markdown */

// The characters a backslash escapes: \ ` * _ [ ] ( ) # + - . ! >
const ESCAPABLE = new Uint8Array(128);
for (const c of [92, 96, 42, 95, 91, 93, 40, 41, 35, 43, 45, 46, 33, 62]) ESCAPABLE[c] = 1;

function isEscapable(code) {
  return code < 128 && ESCAPABLE[code] === 1;
}

/** A line of spaces and tabs only (or empty). */
function isBlankLine(line) {
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

/** A line with spaces and tabs at either end dropped. */
function trimLine(line) {
  let s = 0;
  let e = line.length;
  while (s < e) {
    const c = line.charCodeAt(s);
    if (c === 32 || c === 9) s++;
    else break;
  }
  while (e > s) {
    const c = line.charCodeAt(e - 1);
    if (c === 32 || c === 9) e--;
    else break;
  }
  return s === 0 && e === line.length ? line : line.slice(s, e);
}

/** A fence-open line's language, or null (```lang, then spaces/tabs only). */
function fenceLang(line) {
  if (line.charCodeAt(0) !== 96 || line.charCodeAt(1) !== 96 || line.charCodeAt(2) !== 96) return null;
  let i = 3;
  while (i < line.length) {
    const c = line.charCodeAt(i);
    if ((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 95 || c === 43 || c === 45) i++;
    else break;
  }
  const lang = line.slice(3, i);
  while (i < line.length) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return null;
    i++;
  }
  return lang;
}

/** A fence-close line: ``` then spaces/tabs only. */
function isFenceClose(line) {
  if (line.charCodeAt(0) !== 96 || line.charCodeAt(1) !== 96 || line.charCodeAt(2) !== 96) return false;
  for (let i = 3; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

/** A heading line's { depth, text }, or null (1-6 #, space, non-empty text). */
function headingOf(line) {
  let n = 0;
  while (n < line.length && line.charCodeAt(n) === 35) n++;
  if (n === 0 || n > 6 || n >= line.length) return null;
  const c = line.charCodeAt(n);
  if (c !== 32 && c !== 9) return null;
  let s = n;
  while (s < line.length) {
    const ch = line.charCodeAt(s);
    if (ch === 32 || ch === 9) s++;
    else break;
  }
  let e = line.length;
  while (e > s) {
    const ch = line.charCodeAt(e - 1);
    if (ch === 32 || ch === 9) e--;
    else break;
  }
  if (e === s) return null;
  return { depth: n, text: line.slice(s, e) };
}

/** A thematic break: --- or ***, then spaces/tabs only. */
function isHR(line) {
  const c0 = line.charCodeAt(0);
  if (c0 !== 45 && c0 !== 42) return false;
  if (c0 === 45) {
    if (line.charCodeAt(1) !== 45 || line.charCodeAt(2) !== 45) return false;
  } else if (line.charCodeAt(1) !== 42 || line.charCodeAt(2) !== 42) return false;
  for (let i = 3; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

/** A list-item line's { ordered, start, text }, or null. */
function listMarker(line) {
  const c0 = line.charCodeAt(0);
  if ((c0 === 45 || c0 === 42) && line.charCodeAt(1) === 32) {
    return { ordered: false, start: 1, text: line.slice(2) };
  }
  if (c0 >= 48 && c0 <= 57) {
    let i = 0;
    let num = 0;
    while (i < line.length) {
      const c = line.charCodeAt(i);
      if (c < 48 || c > 57) break;
      num = num * 10 + (c - 48);
      i++;
    }
    if (i >= 1 && i <= 9 && line.charCodeAt(i) === 46 && line.charCodeAt(i + 1) === 32) {
      return { ordered: true, start: num, text: line.slice(i + 2) };
    }
  }
  return null;
}

/** A list continuation line: two or more spaces, then a non-space. */
function isContinued(line) {
  if (line.charCodeAt(0) !== 32 || line.charCodeAt(1) !== 32) return false;
  let i = 2;
  while (i < line.length && line.charCodeAt(i) === 32) i++;
  if (i >= line.length) return false;
  return !isWS(line.charCodeAt(i));
}

/** Whether `line` ends a paragraph: blank, a fence, a heading or a thematic break. */
function endsParagraph(line) {
  if (line.length === 0) return true;
  const c = line.charCodeAt(0);
  if (c === 32 || c === 9) return isBlankLine(line);
  if (c === 96) return fenceLang(line) !== null;
  if (c === 35) return headingOf(line) !== null;
  if (c === 45 || c === 42) return isHR(line);
  return false;
}

/** The first index from `from` where s holds `**` outside a backslash escape, or -1. */
function findStrongClose(s, from, end) {
  for (let j = from; j + 1 < end; j++) {
    if (s.charCodeAt(j) === 92 && j + 1 < end && isEscapable(s.charCodeAt(j + 1))) {
      j++;
      continue;
    }
    if (s.charCodeAt(j) === 42 && s.charCodeAt(j + 1) === 42) return j;
  }
  return -1;
}

/** The first index from `from` where s holds `]` outside a backslash escape, or -1. */
function findBracketClose(s, from, end) {
  for (let j = from; j < end; j++) {
    if (s.charCodeAt(j) === 92 && j + 1 < end && isEscapable(s.charCodeAt(j + 1))) {
      j++;
      continue;
    }
    if (s.charCodeAt(j) === 93) return j;
  }
  return -1;
}

/** The first single * from `from` (one whose run is not **), outside an escape, or -1. */
function findSingleStar(s, from, end) {
  for (let j = from; j < end; j++) {
    const c = s.charCodeAt(j);
    if (c === 92 && j + 1 < end && isEscapable(s.charCodeAt(j + 1))) {
      j++;
      continue;
    }
    if (c !== 42) continue;
    if (j + 1 < end && s.charCodeAt(j + 1) === 42) {
      j++;
      continue;
    }
    return j;
  }
  return -1;
}

/** Whether s holds any whitespace character. */
function hasWS(s) {
  for (let i = 0; i < s.length; i++) {
    if (isWS(s.charCodeAt(i))) return true;
  }
  return false;
}

/**
 * s[start..end) rendered inline into out. One pass: plain runs are pushed whole
 * (escape characters are handled as they are met), spans recurse on ranges so no
 * substring is ever copied for the recursion itself.
 */
function inlineInto(s, start, end, linkFn, out) {
  let i = start;
  let plain = start;
  while (i < end) {
    const c = s.charCodeAt(i);
    if (c === 92) {
      if (i + 1 < end && isEscapable(s.charCodeAt(i + 1))) {
        if (i > plain) out.push(s.slice(plain, i));
        const n = s.charCodeAt(i + 1);
        out.push(n === 62 ? '&gt;' : s[i + 1]);
        i += 2;
        plain = i;
        continue;
      }
      i++;
      continue;
    }
    if (c === 96) {
      const j = s.indexOf('`', i + 1);
      if (j !== -1 && j < end && j > i + 1) {
        if (i > plain) out.push(s.slice(plain, i));
        out.push('<code>');
        escRange(s, i + 1, j, out);
        out.push('</code>');
        i = j + 1;
        plain = i;
        continue;
      }
      i++;
      continue;
    }
    if (c === 42) {
      if (i + 1 < end && s.charCodeAt(i + 1) === 42) {
        const j = findStrongClose(s, i + 2, end);
        if (j !== -1 && j > i + 2) {
          if (i > plain) out.push(s.slice(plain, i));
          out.push('<strong>');
          inlineInto(s, i + 2, j, linkFn, out);
          out.push('</strong>');
          i = j + 2;
          plain = i;
          continue;
        }
        i += 2;
        continue;
      }
      const j = findSingleStar(s, i + 1, end);
      if (j !== -1 && j > i + 1) {
        if (i > plain) out.push(s.slice(plain, i));
        out.push('<em>');
        inlineInto(s, i + 1, j, linkFn, out);
        out.push('</em>');
        i = j + 1;
        plain = i;
        continue;
      }
      i++;
      continue;
    }
    if (c === 91) {
      const k = findBracketClose(s, i + 1, end);
      let m = -1;
      if (k !== -1 && k + 1 < end && s.charCodeAt(k + 1) === 40) {
        const r = s.indexOf(')', k + 2);
        if (r !== -1 && r < end) m = r;
      }
      if (m !== -1) {
        const target = s.slice(k + 2, m);
        if (target !== '' && !hasWS(target)) {
          if (i > plain) out.push(s.slice(plain, i));
          out.push('<a href="');
          const href = linkFn(target);
          if (href.indexOf('&') === -1 && href.indexOf('<') === -1 && href.indexOf('>') === -1 && href.indexOf('"') === -1 && href.indexOf("'") === -1) {
            out.push(href);
          } else {
            escRange(href, 0, href.length, out);
          }
          out.push('">');
          inlineInto(s, i + 1, k, linkFn, out);
          out.push('</a>');
          i = m + 1;
          plain = i;
          continue;
        }
      }
      i++;
      continue;
    }
    if (c === 38 || c === 60 || c === 62 || c === 34 || c === 39) {
      if (i > plain) out.push(s.slice(plain, i));
      out.push(ESC_TABLE[s[i]]);
      i++;
      plain = i;
      continue;
    }
    i++;
  }
  if (end > plain) out.push(s.slice(plain, end));
}

/**
 * A body rendered in one pass over its lines: its HTML (each block followed by
 * "\n"), its table of contents (every level 2 and 3 heading) and its excerpt
 * (the first paragraph's inline HTML, or "").
 */
function renderMarkdown(src, linkFn) {
  const lines = src.split('\n');
  const n = lines.length;
  const out = [];
  const toc = [];
  const ids = new Set();
  let excerpt = null;
  let i = 0;
  while (i < n) {
    const line = lines[i];
    // Dispatch on the first character: only a line starting with that character
    // can be a fence ('`'), a heading ('#'), a break ('-'/'*'), a quote ('>')
    // or a list ('-'/'*'/digit), and only one starting with a space or tab can
    // be blank. Every other line is a paragraph line.
    const c0 = line.length === 0 ? -1 : line.charCodeAt(0);
    let marker = null;
    if (c0 === -1 || c0 === 32 || c0 === 9) {
      if (c0 === -1 || isBlankLine(line)) {
        i++;
        continue;
      }
    } else if (c0 === 96) {
      const lang = fenceLang(line);
      if (lang !== null) {
        i++;
        out.push('<pre><code');
        if (lang !== '') out.push(' class="language-', lang, '">');
        else out.push('>');
        while (i < n && !isFenceClose(lines[i])) {
          escRange(lines[i], 0, lines[i].length, out);
          out.push('\n');
          i++;
        }
        i++;
        out.push('</code></pre>\n');
        continue;
      }
    } else if (c0 === 35) {
      const h = headingOf(line);
      if (h !== null) {
        const id = uniqueSlug(slugify(h.text), ids);
        if (h.depth === 2 || h.depth === 3) {
          // The table of contents needs this heading's HTML as a string.
          const tmp = [];
          inlineInto(h.text, 0, h.text.length, linkFn, tmp);
          const html = tmp.join('');
          out.push(`<h${h.depth} id="${id}">${html}</h${h.depth}>\n`);
          toc.push({ level: h.depth, id, html });
        } else {
          out.push(`<h${h.depth} id="${id}">`);
          inlineInto(h.text, 0, h.text.length, linkFn, out);
          out.push(`</h${h.depth}>\n`);
        }
        i++;
        continue;
      }
    } else if (c0 === 45 || c0 === 42) {
      if (isHR(line)) {
        out.push('<hr>\n');
        i++;
        continue;
      }
      marker = listMarker(line);
    } else if (c0 === 62) {
      const body = [];
      while (i < n && lines[i].charCodeAt(0) === 62) {
        let l = lines[i++];
        l = l.charCodeAt(1) === 32 ? l.slice(2) : l.slice(1);
        l = trimLine(l);
        if (l !== '') body.push(l);
      }
      if (body.length === 0) {
        out.push('<blockquote>\n</blockquote>\n');
      } else {
        const joined = body.join('\n');
        out.push('<blockquote>\n<p>');
        inlineInto(joined, 0, joined.length, linkFn, out);
        out.push('</p>\n</blockquote>\n');
      }
      continue;
    } else if (c0 >= 48 && c0 <= 57) {
      marker = listMarker(line);
    }
    if (marker !== null) {
      const ordered = marker.ordered;
      const start = marker.start;
      const items = [[trimLine(marker.text)]];
      i++;
      while (i < n) {
        const m = listMarker(lines[i]);
        if (m !== null && m.ordered === ordered) {
          items.push([trimLine(m.text)]);
          i++;
        } else if (isContinued(lines[i])) {
          items[items.length - 1].push(trimLine(lines[i]));
          i++;
        } else break;
      }
      const tag = ordered ? 'ol' : 'ul';
      const list = [ordered && start !== 1 ? `<ol start="${start}">\n` : `<${tag}>\n`];
      for (let k = 0; k < items.length; k++) {
        const joined = items[k].join('\n');
        list.push('<li>');
        inlineInto(joined, 0, joined.length, linkFn, list);
        list.push('</li>\n');
      }
      list.push(`</${tag}>\n`);
      out.push(list.join(''));
      continue;
    }
    const body = [trimLine(line)];
    i++;
    while (i < n && !endsParagraph(lines[i])) body.push(trimLine(lines[i++]));
    const joined = body.join('\n');
    if (excerpt === null) {
      // The excerpt is the first paragraph's inline HTML as a string.
      const tmp = [];
      inlineInto(joined, 0, joined.length, linkFn, tmp);
      excerpt = tmp.join('');
      out.push(`<p>${excerpt}</p>\n`);
    } else {
      out.push('<p>');
      inlineInto(joined, 0, joined.length, linkFn, out);
      out.push('</p>\n');
    }
  }
  return { html: out.join(''), toc, excerpt: excerpt === null ? '' : excerpt };
}

/* ---------------------------------------------------------------- templates */

const INCLUDE_DEPTH = 8;

const PATH_RE = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const FOR_RE = /^for ([A-Za-z_][A-Za-z0-9_]*) in (\S+)$/;
const IF_RE = /^if (not )?(\S+)$/;
const INCLUDE_RE = /^include "([a-z0-9-]+)"$/;

/** A template that does not parse: its name and why. */
class TemplateError extends Error {}

/** The path `text` names, split at its dots, or a TemplateError. */
function pathOf(tname, text) {
  if (!PATH_RE.test(text)) throw new TemplateError(`template "${tname}": ${JSON.stringify(text)} is not a path`);
  return text.split('.');
}

// Token kinds: 0 text [0, str], 1 var [1, path], 2 raw [2, path], 3 tag [3, tag].
/** `src`'s tokens: text, {{ }}, {{{ }}} and {% %}, a standalone tag's line taken with it. */
function tokenize(tname, src) {
  const tokens = [];
  let text = '';
  let i = 0;
  const len = src.length;
  while (i < len) {
    const open = src.indexOf('{', i);
    if (open === -1 || open === len - 1) {
      text += src.slice(i);
      break;
    }
    const next = src.charCodeAt(open + 1);
    if (next !== 123 && next !== 37) {
      text += src.slice(i, open + 1);
      i = open + 1;
      continue;
    }
    text += src.slice(i, open);
    if (next === 123) {
      const raw = src.charCodeAt(open + 2) === 123;
      const close = src.indexOf(raw ? '}}}' : '}}', open + (raw ? 3 : 2));
      if (close === -1) throw new TemplateError(`template "${tname}": a ${raw ? '{{{' : '{{'} is not closed`);
      if (text !== '') { tokens.push([0, text]); text = ''; }
      tokens.push([raw ? 2 : 1, pathOf(tname, src.slice(open + (raw ? 3 : 2), close).trim())]);
      i = close + (raw ? 3 : 2);
      continue;
    }
    const close = src.indexOf('%}', open + 2);
    if (close === -1) throw new TemplateError(`template "${tname}": a {% is not closed`);
    const end = close + 2;
    const lineStart = src.lastIndexOf('\n', open - 1) + 1;
    const nl = src.indexOf('\n', end);
    const lineEnd = nl === -1 ? len : nl;
    let standalone = true;
    for (let k = lineStart; k < open; k++) {
      const c = src.charCodeAt(k);
      if (c !== 32 && c !== 9) { standalone = false; break; }
    }
    if (standalone) {
      for (let k = end; k < lineEnd; k++) {
        const c = src.charCodeAt(k);
        if (c !== 32 && c !== 9) { standalone = false; break; }
      }
    }
    if (standalone) text = text.slice(0, text.length - (open - lineStart));
    if (text !== '') { tokens.push([0, text]); text = ''; }
    tokens.push([3, src.slice(open + 2, close).trim()]);
    i = standalone ? (nl === -1 ? len : nl + 1) : end;
  }
  if (text !== '') tokens.push([0, text]);
  return tokens;
}

// Node kinds: 0 text [0, str]; 1 var [1, path]; 2 raw [2, path];
// 3 if [3, not, path, then, else|null]; 4 for [4, name, path, body]; 5 include [5, name].
/** `src` parsed into its tree of nodes (a TemplateError when it does not parse). */
function parseTemplate(tname, src) {
  const tokens = tokenize(tname, src);
  const rootBody = [];
  const stack = [{ kind: 0, body: rootBody }];
  let body = rootBody;
  for (let t = 0; t < tokens.length; t++) {
    const tok = tokens[t];
    const k = tok[0];
    if (k === 0) { body.push([0, tok[1]]); continue; }
    if (k === 1 || k === 2) { body.push([k, tok[1]]); continue; }
    const tag = tok[1];
    const top = stack[stack.length - 1];
    let m;
    if ((m = FOR_RE.exec(tag)) !== null) {
      const node = [4, m[1], pathOf(tname, m[2]), []];
      body.push(node);
      stack.push({ kind: 4, node, body: node[3] });
      body = node[3];
    } else if ((m = IF_RE.exec(tag)) !== null) {
      const node = [3, m[1] !== undefined, pathOf(tname, m[2]), [], null];
      body.push(node);
      stack.push({ kind: 3, node, body: node[3] });
      body = node[3];
    } else if (tag === 'else') {
      if (top.kind !== 3 || top.node[4] !== null) throw new TemplateError(`template "${tname}": an else outside an if`);
      top.node[4] = [];
      top.body = top.node[4];
      body = top.node[4];
    } else if (tag === 'endfor' || tag === 'endif') {
      const want = tag === 'endfor' ? 4 : 3;
      if (top.kind !== want) throw new TemplateError(`template "${tname}": an ${tag} with no open ${tag.slice(3)}`);
      stack.pop();
      body = stack[stack.length - 1].body;
    } else if ((m = INCLUDE_RE.exec(tag)) !== null) {
      body.push([5, m[1]]);
    } else {
      throw new TemplateError(`template "${tname}": {% ${tag} %} is not a tag`);
    }
  }
  if (stack.length > 1) {
    const top = stack[stack.length - 1];
    throw new TemplateError(`template "${tname}": a ${top.kind === 4 ? 'for' : 'if'} is not closed`);
  }
  return rootBody;
}

/** The value at `path` in the scope stack: first name from the nearest scope holding it, then own properties. */
function lookup(scopes, path) {
  const first = path[0];
  for (let k = scopes.length - 1; k >= 0; k--) {
    const vars = scopes[k];
    if (Object.hasOwn(vars, first)) {
      let v = vars[first];
      for (let j = 1; j < path.length; j++) {
        if (v === null || typeof v !== 'object' || !Object.hasOwn(v, path[j])) return undefined;
        v = v[path[j]];
      }
      return v;
    }
  }
  return undefined;
}

/** A value as text: a string itself, a number in JavaScript's digits, true or false, an array's items joined by ", ", else "". */
function textOf(v) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return String(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) {
    let s = '';
    for (let i = 0; i < v.length; i++) {
      if (i > 0) s += ', ';
      s += textOf(v[i]);
    }
    return s;
  }
  return '';
}

/** Whether a value counts as true in an if: not undefined, null, false, "", 0 or an empty array. */
function truthy(v) {
  if (Array.isArray(v)) return v.length > 0;
  return v !== undefined && v !== null && v !== false && v !== '' && v !== 0;
}

/** `nodes` rendered into out, in the scope stack, at include depth `depth`. */
function renderNodes(nodes, scopes, templates, depth, out) {
  for (let n = 0; n < nodes.length; n++) {
    const node = nodes[n];
    const kind = node[0];
    if (kind === 0) {
      out.push(node[1]);
      continue;
    }
    if (kind === 1) {
      const v = textOf(lookup(scopes, node[1]));
      escRange(v, 0, v.length, out);
      continue;
    }
    if (kind === 2) {
      out.push(textOf(lookup(scopes, node[1])));
      continue;
    }
    if (kind === 3) {
      const v = truthy(lookup(scopes, node[2]));
      const branch = v !== node[1] ? node[3] : node[4];
      if (branch !== null) renderNodes(branch, scopes, templates, depth, out);
      continue;
    }
    if (kind === 4) {
      const xs = lookup(scopes, node[2]);
      if (!Array.isArray(xs)) continue;
      const name = node[1];
      const body = node[3];
      const len = xs.length;
      for (let k = 0; k < len; k++) {
        const vars = {};
        vars[name] = xs[k];
        vars.loop = { index: k + 1, first: k === 0, last: k === len - 1, length: len };
        scopes.push(vars);
        renderNodes(body, scopes, templates, depth, out);
        scopes.pop();
      }
      continue;
    }
    const t = templates.get(node[1]);
    if (t !== undefined && depth < INCLUDE_DEPTH) renderNodes(t, scopes, templates, depth + 1, out);
  }
}

/* --------------------------------------------------------------------- build */

/** The top-level directories the generator writes itself, which no page's slug at the root may take. */
const RESERVED = ['posts', 'tags', 'page'];

function dirOf(path) {
  const i = path.lastIndexOf('/');
  return i === -1 ? '' : path.slice(0, i);
}

/** `rel` (a link's path, "/"-separated) from the directory `dir` of a source, or null when it climbs out of the root. */
function resolvePath(dir, rel) {
  // No '.', no '//', no trailing '/': no segment is empty, '.' or '..', so the
  // joined path is already the normalised one.
  if (rel.indexOf('.') === -1 && rel.indexOf('//') === -1 && rel.charCodeAt(rel.length - 1) !== 47) {
    return dir === '' ? rel : dir + '/' + rel;
  }
  const parts = dir === '' ? [] : dir.split('/');
  const segs = rel.split('/');
  for (let i = 0; i < segs.length; i++) {
    const seg = segs[i];
    if (seg === '' || seg === '.') continue;
    if (seg === '..') {
      if (parts.length === 0) return null;
      parts.pop();
    } else parts.push(seg);
  }
  return parts.join('/');
}

/** A link target kept as written: one with a scheme, or opening on / or #. */
function isAbsoluteTarget(t) {
  const c0 = t.charCodeAt(0);
  if (c0 === 47 || c0 === 35) return true;
  if (!((c0 >= 65 && c0 <= 90) || (c0 >= 97 && c0 <= 122))) return false;
  for (let i = 1; i < t.length; i++) {
    const c = t.charCodeAt(i);
    if (c === 58) return true;
    if (!((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 43 || c === 45 || c === 46)) return false;
  }
  return false;
}

/** A page's link record as templates read it. */
function linkOf(s) {
  if (s === null) return null;
  return {
    title: s.data.title,
    url: s.url,
    date: s.data.date !== undefined ? s.data.date : '',
    date_long: s.data.date === undefined ? '' : longDate(s.data.date),
  };
}

/** One site's output tree: path -> text. */
export function run(input) {
  slugCache = new Map();
  const site = input.site;
  let base = site.base_url;
  let be = base.length;
  while (be > 0 && base.charCodeAt(be - 1) === 47) be--;
  if (be < base.length) base = base.slice(0, be);

  // Templates, parsed in code-unit order of name; one that does not parse is reported and left out.
  const templates = new Map();
  const report = [];
  const tnames = Object.keys(input.templates).sort(cmpStr);
  for (let i = 0; i < tnames.length; i++) {
    const name = tnames[i];
    try {
      templates.set(name, parseTemplate(name, input.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      report.push(err.message);
    }
  }

  // Sources, in code-unit order of their paths, line ends made "\n"; the rest is static.
  const files = [...input.files].sort((a, b) => cmpStr(a.path, b.path));
  const sources = [];
  const statics = [];
  for (let i = 0; i < files.length; i++) {
    const f = files[i];
    if (f.path.endsWith('.md')) {
      let text = f.content;
      if (text.indexOf('\r') !== -1) text = text.replace(/\r\n?/g, '\n');
      sources.push({ path: f.path, text });
    } else {
      statics.push({ path: f.path, content: f.content });
    }
  }

  // Front matter and the checks, in order: refused, the generator's own directories,
  // a post with no date, a layout that is no template, then a draft.
  const kept = [];
  for (let i = 0; i < sources.length; i++) {
    const s = sources[i];
    const fm = parseFrontMatter(s.text);
    if ('error' in fm) {
      report.push(`refused ${s.path}: ${fm.error}`);
      continue;
    }
    s.data = fm.data;
    s.body = fm.body;
    s.post = s.path.startsWith('posts/');
    let own = null;
    if (s.path.startsWith('tags/')) own = 'tags';
    else if (s.path.startsWith('page/')) own = 'page';
    if (own !== null) {
      report.push(`refused ${s.path}: ${own}/ is the generator's own`);
      continue;
    }
    if (s.post && !Object.hasOwn(s.data, 'date')) {
      report.push(`refused ${s.path}: a post needs a date`);
      continue;
    }
    const layout = s.data.layout !== undefined ? s.data.layout : (s.post ? 'post' : 'page');
    if (!templates.has(layout)) {
      report.push(`refused ${s.path}: layout "${layout}" is no template that parses`);
      continue;
    }
    s.layout = layout;
    if (s.data.draft === true) {
      report.push(`draft ${s.path}`);
      continue;
    }
    kept.push(s);
  }

  // Permalinks: the slug made unique in its directory, in source order.
  const taken = new Map();
  const bySource = new Map();
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const dir = s.post ? 'posts' : dirOf(s.path);
    let set = taken.get(dir);
    if (set === undefined) {
      set = new Set(dir === '' ? RESERVED : []);
      taken.set(dir, set);
    }
    const slug = uniqueSlug(s.data.slug !== undefined ? s.data.slug : slugify(s.data.title), set);
    s.slug = slug;
    s.outDir = dir === '' ? slug : dir + '/' + slug;
    s.url = base + '/' + s.outDir + '/';
    bySource.set(s.path, s);
  }

  // Markdown, each body's links resolved to the pages and static files they name.
  const staticPaths = new Set();
  for (let i = 0; i < statics.length; i++) staticPaths.add(statics[i].path);
  const broken = new Set();
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const dir = dirOf(s.path);
    const linkFn = (target) => {
      if (isAbsoluteTarget(target)) return target;
      const hash = target.indexOf('#');
      const rel = hash === -1 ? target : target.slice(0, hash);
      const frag = hash === -1 ? '' : target.slice(hash);
      const path = rel === '' ? null : resolvePath(dir, rel);
      if (path !== null) {
        const pg = bySource.get(path);
        if (pg !== undefined) return pg.url + frag;
        if (staticPaths.has(path)) return base + '/' + path + frag;
      }
      broken.add(`broken-link ${s.path} -> ${target}`);
      return target;
    };
    const md = renderMarkdown(s.body, linkFn);
    s.html = md.html;
    s.toc = md.toc;
    s.excerpt = md.excerpt;
  }

  // Collections: the posts, newest first and then by slug; each post's neighbours.
  const posts = [];
  for (let i = 0; i < kept.length; i++) if (kept[i].post) posts.push(kept[i]);
  posts.sort((x, y) => cmpStr(y.data.date, x.data.date) || cmpStr(x.slug, y.slug));
  for (let k = 0; k < posts.length; k++) {
    posts[k].newer = k === 0 ? null : posts[k - 1];
    posts[k].older = k === posts.length - 1 ? null : posts[k + 1];
  }

  // Tags: grouped by slug, each named as first met in the posts' order.
  const bySlug = new Map();
  for (let k = 0; k < posts.length; k++) {
    const p = posts[k];
    const names = p.data.tags;
    const seen = new Set();
    p.tagRefs = [];
    if (names !== undefined) {
      for (let j = 0; j < names.length; j++) {
        const name = names[j];
        const slug = slugify(name);
        if (seen.has(slug)) continue;
        seen.add(slug);
        let tag = bySlug.get(slug);
        if (tag === undefined) {
          tag = { name, slug, url: base + '/tags/' + slug + '/', posts: [] };
          bySlug.set(slug, tag);
        }
        tag.posts.push(p);
        p.tagRefs.push(tag);
      }
    }
  }
  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    if (s.post) continue;
    const names = s.data.tags;
    const seen = new Set();
    s.tagRefs = [];
    if (names !== undefined) {
      for (let j = 0; j < names.length; j++) {
        const name = names[j];
        const slug = slugify(name);
        if (seen.has(slug)) continue;
        seen.add(slug);
        const tag = bySlug.get(slug);
        s.tagRefs.push(tag !== undefined ? tag : { name, slug, url: '', posts: [] });
      }
    }
  }
  const tagList = [...bySlug.values()].sort((x, y) => y.posts.length - x.posts.length || cmpStr(x.slug, y.slug));

  // Cards: one per post, shared by every list that shows it; a page's card is its own.
  function cardOf(s) {
    const tagArr = [];
    const refs = s.tagRefs;
    for (let j = 0; j < refs.length; j++) {
      const t = refs[j];
      tagArr.push({ name: t.name, slug: t.slug, url: t.url });
    }
    return {
      title: s.data.title,
      url: s.url,
      date: s.data.date !== undefined ? s.data.date : '',
      date_long: s.data.date === undefined ? '' : longDate(s.data.date),
      summary: s.data.summary !== undefined ? s.data.summary : '',
      excerpt: s.excerpt,
      reading_minutes: Math.max(1, Math.ceil(wordsOf(s.body) / 200)),
      tags: tagArr,
    };
  }
  const cards = new Map();
  for (let k = 0; k < posts.length; k++) cards.set(posts[k], cardOf(posts[k]));

  const siteOut = { title: site.title, base_url: base };
  const allTags = tagList.map((t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length }));
  const recent = posts.slice(0, site.recent).map((p) => cards.get(p));
  const output = {};
  // The globals are one object shared by every render; the per-page values sit
  // in a scope above it, so a page value still wins over a global of the same
  // name — exactly as the reference's single spread object behaves.
  const globals = { site: siteOut, tags: allTags, recent };
  const render = (name, vars) => {
    const nodes = templates.get(name);
    if (nodes === undefined) return null;
    const scopes = [globals, vars];
    const out = [];
    renderNodes(nodes, scopes, templates, 0, out);
    return out.join('');
  };

  for (let i = 0; i < kept.length; i++) {
    const s = kept[i];
    const card = s.post ? cards.get(s) : cardOf(s);
    const page = {
      ...card,
      slug: s.slug,
      content: s.html,
      toc: s.toc.map((h) => ({ level: h.level, id: h.id, html: h.html })),
      newer: linkOf(s.newer !== undefined ? s.newer : null),
      older: linkOf(s.older !== undefined ? s.older : null),
      is_post: s.post,
    };
    output[s.outDir + '/index.html'] = render(s.layout, { page });
  }

  const per = site.per_page;
  const pages = Math.max(1, Math.ceil(posts.length / per));
  const indexUrl = (k) => (k === 1 ? base + '/' : base + '/page/' + k + '/');
  for (let k = 1; k <= pages; k++) {
    const html = render('index', {
      posts: posts.slice((k - 1) * per, k * per).map((p) => cards.get(p)),
      pager: { number: k, total: pages, url: indexUrl(k), newer_url: k === 1 ? '' : indexUrl(k - 1), older_url: k === pages ? '' : indexUrl(k + 1) },
    });
    if (html !== null) output[k === 1 ? 'index.html' : 'page/' + k + '/index.html'] = html;
  }
  for (let i = 0; i < tagList.length; i++) {
    const t = tagList[i];
    const html = render('tag', { tag: { name: t.name, slug: t.slug, url: t.url, count: t.posts.length, posts: t.posts.map((p) => cards.get(p)) } });
    if (html !== null) output['tags/' + t.slug + '/index.html'] = html;
  }
  const tagsHtml = render('tags', {});
  if (tagsHtml !== null) output['tags/index.html'] = tagsHtml;

  for (let i = 0; i < statics.length; i++) {
    const f = statics[i];
    if (Object.hasOwn(output, f.path)) report.push(`shadowed ${f.path}: a built page has its path`);
    else output[f.path] = f.content;
  }

  const lines = [...report, ...broken].sort(cmpStr);
  let npages = 0;
  for (let i = 0; i < kept.length; i++) if (!kept[i].post) npages++;
  lines.push(`built ${npages} pages, ${posts.length} posts, ${tagList.length} tags and ${statics.length} static files`);
  output['build-report.txt'] = lines.join('\n') + '\n';
  return output;
}
