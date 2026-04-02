/**
 * SideNav TOC v7.1 — 通义千问适配版
 *
 * 修复清单：
 * - 使用内容哈希生成稳定 ID，路由切换后不丢失
 * - 点击时实时查找目标元素，不依赖过期引用
 * - animating 锁超时自动解除
 * - 路由切换后更快恢复
 * - 滚动容器缓存
 * - 更健壮的错误处理
 * - [v6.1] 高亮状态自动检查与修复
 * - [v6.1] throttle 保证最后一次调用不丢失
 * - [v6.1] 切换标签页/获取焦点时刷新高亮
 * - [v6.1] render 后强制重新计算高亮
 * - [v6.2] 修复 clearAllTimers 漏掉 routePollTimer
 * - [v6.2] 修复 throttle timer 内存泄漏
 * - [v6.2] 修复 updateActive 视口判断逻辑错误
 * - [v6.2] 修复 generateSelector 返回不唯一选择器
 * - [v6.2] 修复全局事件监听器内存泄漏
 * - [v6.3] 确保始终有一个项目被高亮（常亮）
 * - [v6.3] activeIdx 无效时自动回退到第一个
 * - [v6.3] 强化 activeCheckTimer 检测逻辑
 * - [v6.4] 优化延迟配置，更快响应
 * - [v6.4] 元素缓存，减少 DOM 查询
 * - [v6.4] requestAnimationFrame 优化滚动
 * - [v6.4] CSS 动画时间缩短
 * - [v6.5] 点击锁定机制，防止相邻项切换失败
 * - [v6.6] debounce 函数添加 cancel 方法
 * - [v6.6] 修复 scrollHandler.cancel 覆盖问题
 * - [v6.6] activeCheckTimer 纳入 clearAllTimers
 * - [v6.6] 全局事件处理器统一管理
 * - [v6.7] jumpTo 滚动目标与 updateActive 判断标准统一（视口30%）
 * - [v6.7] updateActive 增加粘性逻辑，防止相邻项频繁切换
 * - [v6.8] 长内容跳转时，高亮延迟到滚动接近完成后显示
 * - [v6.8] 高亮持续时间延长至 1800ms，确保用户看到
 * - [v6.8] clickLockDuration 延长至 3000ms，覆盖长距离滚动
 * - [v7.0] 新增通义千问(chat.qwen.ai / tongyi.aliyun.com)适配
 * - [v7.0] 支持 Ant Design X Bubble 组件用户消息识别
 * - [v7.0] 多策略回退：data属性 → 类名模式 → 结构推断
 * - [v7.1] 修复 stableId 不稳定导致的虚拟标题 bug（移除索引依赖）
 * - [v7.1] 移除合并策略，恢复直接替换，消除幽灵条目
 * - [v7.1] 高亮圆角永久保持，不再重置为直角
 * - [v7.1] 移除侧边栏自动滚动，解决上下反复横跳
 * - [v7.1] CSS max-height 提升至 90vh，减少内部滚动
 */

(function () {
  'use strict';

  const HOST = location.hostname;
  const IS_CHATGPT = HOST.includes('chatgpt') || HOST.includes('chat.openai');
  const IS_GEMINI = HOST.includes('gemini.google.com');
  const IS_QWEN = HOST.includes('chat.qwen.ai') || HOST.includes('tongyi.aliyun.com') || HOST.includes('qianwen.com');
  const IS_CLAUDE = HOST.includes('claude.ai');

  if (!IS_CHATGPT && !IS_GEMINI && !IS_QWEN && !IS_CLAUDE) return;

  // ── 配置 ──────────────────────────────
  const CONF = {
    maxItems: 500,
    titleMax: 28,
    expandDelay: 30,
    collapseDelay: 280,
    scrollThrottle: 50,
    observerDebounce: 200,
    initDelay: 600,
    routeDelay: 300,
    retryDelay: 800,
    maxRetries: 30,
    animationTimeout: 380,
    elementCacheTTL: 500,
    clickLockDuration: 3000,
    qwenFallbackContainerLimit: 160,
    qwenFallbackMaxChildren: 80,
  };

  // ── 状态 ──────────────────────────────
  let expanded = false;
  let animating = false;
  let animatingTimer = null;  // 动画锁超时清理
  let items = [];  // { id, title, selector } - 不存储 DOM 引用
  let activeIdx = -1;
  let observer = null;
  let enabled = true;
  let retryCount = 0;
  let container = null;
  let lastUrl = location.href;
  let expandTimer = null;
  let collapseTimer = null;
  let retryRenderTimer = null;
  let routeCheckTimer = null;
  let routeRenderTimer = null;
  let rendering = false;
  let scrollListenersBound = false;
  let scrollHandler = null;
  let routeWatchBound = false;
  let routePollTimer = null;
  let routeEventHandler = null;
  let popstateHandler = null;
  let cachedScrollContainer = null;
  let scrollContainerCacheTime = 0;

  // 元素缓存：避免频繁 DOM 查询
  const elementCache = new Map();  // id -> { el, time }
  let lastCacheClear = 0;

  // 点击锁定：防止滚动时切换高亮
  let clickLocked = false;
  let clickLockTimer = null;
  let clickLockedIdx = -1;

  // 全局事件监听器
  let activeCheckTimer = null;
  let visibilityHandler = null;
  let focusHandler = null;

  const ROUTE_HOOK_FLAG = '__snTocRouteHookInstalledV2';
  const ROUTE_EVENT = 'sn-toc-route-change';
  const ID_PREFIX = 'sntoc-';

  // ── 工具函数 ──────────────────────────

  // 改进的 throttle：保证最后一次调用不丢失，支持取消
  function throttle(fn, ms) {
    let last = 0;
    let timer = null;

    function throttled() {
      const now = Date.now();
      const remaining = ms - (now - last);

      if (remaining <= 0) {
        if (timer) { clearTimeout(timer); timer = null; }
        last = now;
        fn();
      } else if (!timer) {
        timer = setTimeout(() => {
          timer = null;
          last = Date.now();
          fn();
        }, remaining);
      }
    }

    // 提供取消方法
    throttled.cancel = function () {
      if (timer) { clearTimeout(timer); timer = null; }
    };

    return throttled;
  }

  function debounce(fn, ms) {
    let t;
    function debounced() {
      clearTimeout(t);
      t = setTimeout(fn, ms);
    }
    debounced.cancel = function () {
      clearTimeout(t);
      t = null;
    };
    return debounced;
  }

  function trunc(s, n) {
    if (!s) return '';
    s = s.replace(/\s+/g, ' ').trim();
    return s.length <= n ? s : s.slice(0, n).replace(/\s\S*$/, '') + '…';
  }

  // 生成稳定的 ID：基于文本内容的哈希（不包含索引，确保虚拟滚动后仍能识别）
  function stableId(text) {
    let hash = 0;
    const str = (text || '').slice(0, 200);  // 使用更多字符确保唯一性
    for (let i = 0; i < str.length; i++) {
      hash = ((hash << 5) - hash + str.charCodeAt(i)) | 0;
    }
    return ID_PREFIX + Math.abs(hash).toString(36);
  }

  function clearAllTimers() {
    // 清理 setTimeout 创建的 timers
    [expandTimer, collapseTimer, retryRenderTimer, routeCheckTimer, routeRenderTimer, animatingTimer, clickLockTimer].forEach(t => {
      if (t) clearTimeout(t);
    });
    expandTimer = collapseTimer = retryRenderTimer = routeCheckTimer = routeRenderTimer = animatingTimer = clickLockTimer = null;

    // 重置点击锁定状态
    clickLocked = false;
    clickLockedIdx = -1;

    // setInterval 创建的 timers 需要用 clearInterval
    if (routePollTimer) {
      clearInterval(routePollTimer);
      routePollTimer = null;
    }
    if (activeCheckTimer) {
      clearInterval(activeCheckTimer);
      activeCheckTimer = null;
    }
  }

  function scheduleRetryRender() {
    if (retryRenderTimer) clearTimeout(retryRenderTimer);
    retryRenderTimer = setTimeout(() => {
      retryRenderTimer = null;
      render();
    }, CONF.retryDelay);
  }

  // ── 容器存活检测 ──────────────────────

  function isContainerAlive() {
    return container && document.body && document.body.contains(container);
  }

  // ── 元素查找（带缓存） ────────────────

  function clearElementCache() {
    elementCache.clear();
    lastCacheClear = Date.now();
  }

  function findElementById(id) {
    if (!id) return null;
    return document.getElementById(id);
  }

  function findElementBySelector(selector) {
    if (!selector) return null;
    try {
      return document.querySelector(selector);
    } catch (e) {
      return null;
    }
  }

  // 获取 item 对应的实际 DOM 元素（带缓存）
  function getItemElement(item) {
    if (!item) return null;

    const now = Date.now();
    const cacheKey = item.id;

    // 检查缓存
    const cached = elementCache.get(cacheKey);
    if (cached && now - cached.time < CONF.elementCacheTTL) {
      if (cached.el && document.body.contains(cached.el)) {
        return cached.el;
      }
    }

    // 定期清理过期缓存
    if (now - lastCacheClear > 5000) {
      for (const [key, val] of elementCache) {
        if (now - val.time > CONF.elementCacheTTL * 2) {
          elementCache.delete(key);
        }
      }
      lastCacheClear = now;
    }

    // 查找元素
    let el = findElementById(item.id);
    if (!el || !document.body.contains(el)) {
      el = findElementBySelector(item.selector);
    }

    // 更新缓存
    if (el && document.body.contains(el)) {
      elementCache.set(cacheKey, { el, time: now });
      return el;
    }

    elementCache.delete(cacheKey);
    return null;
  }

  // ── 滚动容器（带缓存） ────────────────

  function findScrollContainer(el) {
    // 缓存 3 秒有效
    if (cachedScrollContainer && Date.now() - scrollContainerCacheTime < 3000) {
      if (document.body.contains(cachedScrollContainer)) {
        return cachedScrollContainer;
      }
    }

    let cur = el ? el.parentElement : null;
    while (cur && cur !== document.body && cur !== document.documentElement) {
      try {
        const style = getComputedStyle(cur);
        if ((style.overflowY === 'auto' || style.overflowY === 'scroll') &&
          cur.scrollHeight > cur.clientHeight + 10) {
          cachedScrollContainer = cur;
          scrollContainerCacheTime = Date.now();
          return cur;
        }
      } catch (e) { }
      cur = cur.parentElement;
    }
    return document.documentElement;
  }

  // ── 跳转到元素 ────────────────────────

  // 目标位置：视口高度的 30%（与 updateActive 保持一致）
  const SCROLL_TARGET_RATIO = 0.3;

  function jumpTo(element) {
    if (!element || !document.body.contains(element)) return false;

    try {
      const scrollContainer = findScrollContainer(element);
      // 计算目标位置：让元素滚动到视口 30% 的位置
      const viewportTarget = window.innerHeight * SCROLL_TARGET_RATIO;

      if (scrollContainer && scrollContainer !== document.documentElement) {
        const elementRect = element.getBoundingClientRect();
        // 需要滚动的距离 = 元素当前位置 - 目标位置
        const scrollNeeded = elementRect.top - viewportTarget;
        const newScrollTop = scrollContainer.scrollTop + scrollNeeded;
        scrollContainer.scrollTo({ top: Math.max(0, newScrollTop), behavior: 'smooth' });
      } else {
        // 回退：使用 scrollIntoView，但尽量居中
        element.scrollIntoView({ behavior: 'smooth', block: 'center' });
      }
      return true;
    } catch (e) {
      // 回退方案
      try {
        element.scrollIntoView({ behavior: 'smooth', block: 'center' });
        return true;
      } catch (e2) {
        return false;
      }
    }
  }

  // ── 文本提取 ──────────────────────────

  function cleanText(raw) {
    if (!raw) return '';
    let text = raw.replace(/\s+/g, ' ').trim();
    text = text.replace(/^(You said:?\s*|你说:?\s*|You:\s*|User:\s*|ChatGPT said:?\s*)/i, '').trim();
    return text;
  }

  function getUserText(el) {
    if (!el) return '';
    try {
      const c = el.cloneNode(true);
      c.querySelectorAll(
        'script,style,svg,img,video,audio,canvas,[hidden],[aria-hidden="true"],pre,code,button,input,textarea,nav,header,footer'
      ).forEach(x => x.remove());
      return cleanText(c.textContent);
    } catch (e) {
      return '';
    }
  }

  function getUserTextWithoutLabel(el) {
    if (!el) return '';
    try {
      const c = el.cloneNode(true);
      c.querySelectorAll(
        'script,style,svg,img,video,audio,canvas,[hidden],[aria-hidden="true"],pre,code,button,input,textarea,nav,header,footer'
      ).forEach(x => x.remove());

      const walk = document.createTreeWalker(c, NodeFilter.SHOW_ELEMENT);
      const removeList = [];
      while (walk.nextNode()) {
        const node = walk.currentNode;
        const t = (node.textContent || '').trim();
        if ((t === 'You said' || t === 'You said:' || t === 'You' || t === 'Model') &&
          node.children.length <= 1 && t.length < 15) {
          removeList.push(node);
        }
      }
      removeList.forEach(n => { try { n.remove(); } catch (e) { } });

      return cleanText(c.textContent);
    } catch (e) {
      return '';
    }
  }

  // ── 生成元素选择器（用于备用查找） ────

  function generateSelector(el) {
    if (!el || el === document.body) return null;
    try {
      // 只使用唯一性高的选择器
      // data-testid 通常是唯一的（如 conversation-turn-5）
      if (el.dataset.testid && /\d/.test(el.dataset.testid)) {
        return `[data-testid="${CSS.escape(el.dataset.testid)}"]`;
      }
      // 原生 ID（非我们生成的）
      if (el.id && !el.id.startsWith(ID_PREFIX)) {
        return '#' + CSS.escape(el.id);
      }
      // 不返回不唯一的选择器，避免误匹配
      return null;
    } catch (e) {
      return null;
    }
  }

  // ── 对话扫描 ──────────────────────────

  function scan() {
    try {
      let result = [];
      if (IS_CHATGPT) result = scanChatGPT();
      if (IS_GEMINI) result = scanGemini();
      if (IS_QWEN) result = scanQwen();
      if (IS_CLAUDE) result = scanClaude();

      return result;
    } catch (e) {
      console.warn('[SideNav TOC] Scan error:', e);
    }
    return [];
  }

  // ── ChatGPT 扫描 ─────────────────────

  function scanChatGPT() {
    const result = [];
    const seen = new Set();

    // 策略1: data-message-author-role="user"
    const userMsgs = document.querySelectorAll('[data-message-author-role="user"]');
    for (const msg of userMsgs) {
      const turn = msg.closest('[data-testid^="conversation-turn"]') || msg;
      if (seen.has(turn)) continue;
      seen.add(turn);

      const text = getUserText(msg);
      if (!text || text.length < 2) continue;

      const id = stableId(text);
      // 给元素设置 ID（如果还没有或是我们之前设置的）
      if (!turn.id || turn.id.startsWith(ID_PREFIX)) {
        turn.id = id;
      }

      result.push({
        id: turn.id,
        title: trunc(text, CONF.titleMax),
        rawText: text, // <--- 新增这行，把完整的文本存下来
        selector: generateSelector(turn) || `#${CSS.escape(turn.id)}`
      });

      if (result.length >= CONF.maxItems) break;
    }

    if (result.length > 0) return result;

    // 策略2: conversation-turn 过滤
    const turns = document.querySelectorAll('[data-testid^="conversation-turn"]');
    for (const turn of turns) {
      if (turn.querySelector('[data-message-author-role="assistant"]')) continue;
      if (turn.querySelector('[data-message-author-role="system"]')) continue;
      if (seen.has(turn)) continue;
      seen.add(turn);

      const text = getUserText(turn);
      if (!text || text.length < 2) continue;

      const id = stableId(text);
      if (!turn.id || turn.id.startsWith(ID_PREFIX)) {
        turn.id = id;
      }

      result.push({
        id: turn.id,
        title: trunc(text, CONF.titleMax),
        selector: generateSelector(turn) || `#${CSS.escape(turn.id)}`
      });

      if (result.length >= CONF.maxItems) break;
    }

    return result;
  }

  // ── Gemini 扫描 ──────────────────────

  function scanGemini() {
    const result = [];
    const seen = new Set();

    const knownSelectors = [
      '.query-text',
      '.user-query',
      '.query-content',
      '[data-message-author="user"]',
      'message-content[data-author="user"]',
    ];

    for (const sel of knownSelectors) {
      try {
        const els = document.querySelectorAll(sel);
        for (const el of els) {
          if (el.closest('#sidenav-toc-container')) continue;
          const text = getUserTextWithoutLabel(el);
          if (!text || text.length < 1) continue;
          const target = el.closest('[class*="turn"]') || el;
          if (seen.has(target)) continue;
          seen.add(target);

          const id = stableId(text);
          if (!target.id || target.id.startsWith(ID_PREFIX)) {
            target.id = id;
          }

          result.push({
            id: target.id,
            title: trunc(text, CONF.titleMax),
            rawText: text, // <--- 新增这行，把完整的文本存下来
            selector: generateSelector(target) || `#${CSS.escape(target.id)}`
          });

          if (result.length >= CONF.maxItems) break;
        }
      } catch (e) { }
      if (result.length > 0) return result;
    }

    // 策略2: 通过 "You said" 文本定位
    const root = document.querySelector('main') || document.querySelector('[role="main"]') || document.body;
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
      acceptNode: function (node) {
        const t = (node.textContent || '').trim();
        return (t === 'You said' || t === 'You said:') ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT;
      }
    });

    const labelNodes = [];
    while (walker.nextNode()) {
      labelNodes.push(walker.currentNode);
    }

    for (const textNode of labelNodes) {
      let labelEl = textNode.parentElement;
      if (!labelEl || labelEl.closest('#sidenav-toc-container')) continue;

      let msgContainer = null;
      let cur = labelEl.parentElement;
      for (let depth = 0; depth < 6 && cur && cur !== document.body; depth++) {
        if (cur.offsetHeight > 30 && cur.offsetHeight < window.innerHeight * 0.7) {
          const textContent = getUserTextWithoutLabel(cur);
          if (textContent && textContent.length >= 1) {
            msgContainer = cur;
            break;
          }
        }
        cur = cur.parentElement;
      }

      if (!msgContainer || seen.has(msgContainer)) continue;
      seen.add(msgContainer);

      const text = getUserTextWithoutLabel(msgContainer);
      if (!text || text.length < 1) continue;

      const id = stableId(text);
      if (!msgContainer.id || msgContainer.id.startsWith(ID_PREFIX)) {
        msgContainer.id = id;
      }

      result.push({
        id: msgContainer.id,
        title: trunc(text, CONF.titleMax),
        selector: generateSelector(msgContainer) || `#${CSS.escape(msgContainer.id)}`
      });

      if (result.length >= CONF.maxItems) break;
    }

    if (result.length > 0) return result;

    // 策略3: 结构推断
    const mainArea = document.querySelector('main') || document.querySelector('[role="main"]');
    if (!mainArea) return result;

    const divs = mainArea.querySelectorAll('div');
    for (const div of divs) {
      if (div.closest('#sidenav-toc-container')) continue;
      const children = Array.from(div.children).filter(
        ch => ch.offsetHeight > 40 && !ch.matches('nav,header,footer,script,style')
      );
      if (children.length < 2 || children.length > 200) continue;

      const t1 = getUserText(children[0]);
      const t2 = getUserText(children[1]);
      if (!t1 || !t2 || t1.length > 500 || t2.length < 10) continue;

      for (let i = 0; i < children.length; i += 2) {
        const child = children[i];
        if (seen.has(child)) continue;
        seen.add(child);
        const text = getUserTextWithoutLabel(child);
        if (!text || text.length < 1) continue;

        const id = stableId(text);
        if (!child.id || child.id.startsWith(ID_PREFIX)) {
          child.id = id;
        }

        result.push({
          id: child.id,
          title: trunc(text, CONF.titleMax),
          selector: generateSelector(child) || `#${CSS.escape(child.id)}`
        });

        if (result.length >= CONF.maxItems) break;
      }
      if (result.length > 0) return result;
    }

    return result;
  }

  // ── Claude 扫描 (多策略加强版) ──────────────────────
  function scanClaude() {
    const result = [];
    const seen = new Set();
    const root = document.querySelector('main') || document.body;

    // 策略1：海网捕鱼。尝试所有已知的 Claude 用户消息特征
    const knownSelectors = [
      '[data-is-user="true"]',        // 常见的数据属性 (较老版本)
      '[data-testid="user-message"]', // 常见测试属性 (较新版本)
      '.font-user-message',           // 经典文本类名
      '[data-message-author="user"]'  // 备用兜底
    ];

    for (const sel of knownSelectors) {
      try {
        const els = root.querySelectorAll(sel);
        for (const el of els) {
          if (el.closest('#sidenav-toc-container')) continue;

          // 获取最外层的气泡容器作为点击跳转的锚点
          // Claude 现在的结构里，最外层通常是一个带有 group 类的 div
          const target = el.closest('.group') || el.closest('[data-is-user="true"]') || el;
          if (seen.has(target)) continue;
          seen.add(target);

          // 提取文本并清理
          let text = cleanText(el.textContent);

          // 清除 Claude 有时会带上的杂乱按钮文字 (比如 "Edit")
          text = text.replace(/^(Edit|Copy)\s*/i, '').trim();

          if (!text || text.length < 2) continue;

          const id = stableId(text);
          if (!target.id || target.id.startsWith(ID_PREFIX)) {
            target.id = id;
          }

          result.push({
            id: target.id,
            title: trunc(text, CONF.titleMax),
            rawText: text, // <--- 新增这行，把完整的文本存下来
            selector: generateSelector(target) || `#${CSS.escape(target.id)}`
          });

          if (result.length >= CONF.maxItems) break;
        }
      } catch (e) { }

      // 只要某一个策略抓到了数据，就直接返回，不往下试了
      if (result.length > 0) return result;
    }

    // 策略2：如果上面的选择器全军覆没 (Claude 又偷偷改版了)，开启暴力结构推断
    // Claude 的对话通常在 max-w-3xl 这样的固定宽度容器里，且用户消息没有复杂的 Markdown 格式
    if (result.length === 0) {
      const possibleUserTexts = root.querySelectorAll('.whitespace-pre-wrap');
      for (const textDiv of possibleUserTexts) {
        if (textDiv.closest('#sidenav-toc-container')) continue;
        // 通常助手回答会带一堆 p 标签和 pre 标签，用户提问比较纯粹
        if (textDiv.querySelector('pre, code')) continue;

        const target = textDiv.closest('.group') || textDiv;
        if (seen.has(target)) continue;
        seen.add(target);

        const text = cleanText(textDiv.textContent);
        if (!text || text.length < 5) continue; // 提问通常大于几个字

        const id = stableId(text);
        if (!target.id || target.id.startsWith(ID_PREFIX)) {
          target.id = id;
        }

        result.push({
          id: target.id,
          title: trunc(text, CONF.titleMax),
          selector: generateSelector(target) || `#${CSS.escape(target.id)}`
        });

        if (result.length >= CONF.maxItems) break;
      }
    }

    return result;
  }

  // ── 通义千问 扫描 ────────────────────
  // www.qianwen.com 使用 CSS Modules 哈希类名：
  //   用户消息: questionItem-{hash}
  //   助手消息: answerItem-{hash}
  //   内容区域: content-{hash}
  // 哈希值会随版本更新变化，因此使用 [class*="questionItem-"] 模式匹配

  function getQwenScanRoot() {
    return document.getElementById('ice-container')
      || document.querySelector('main')
      || document.querySelector('[role="main"]')
      || document.body;
  }

  function getClassNameText(el) {
    if (!el) return '';
    const cls = el.className;
    if (!cls) return '';
    if (typeof cls === 'string') return cls;
    if (typeof cls.baseVal === 'string') return cls.baseVal;
    return '';
  }

  function hasClassTokenPrefix(el, prefix) {
    const cls = getClassNameText(el);
    if (!cls) return false;
    return cls.split(/\s+/).some(token => token.startsWith(prefix));
  }

  function hasQwenUserHint(el) {
    if (!el) return false;
    if (el.matches?.('[data-role="user"],[data-message-role="user"],[data-type="question"]')) {
      return true;
    }
    const cls = getClassNameText(el).toLowerCase();
    return cls.includes('question') || cls.includes('user') || cls.includes('query') || cls.includes('prompt');
  }

  function hasQwenAssistantHint(el) {
    if (!el) return false;
    if (el.matches?.('[data-role="assistant"],[data-message-role="assistant"],[data-type="answer"]')) {
      return true;
    }
    const cls = getClassNameText(el).toLowerCase();
    return cls.includes('answer') || cls.includes('assistant') || cls.includes('response') || cls.includes('model');
  }

  function scanQwen() {
    const result = [];
    const seen = new Set();
    const root = getQwenScanRoot();

    // 策略1: CSS Modules 哈希类名模式匹配（www.qianwen.com 主站）
    // questionItem-{hash} 是用户消息的容器类
    const questionItems = root.querySelectorAll('[class*="questionItem-"]');
    for (const item of questionItems) {
      if (item.closest('#sidenav-toc-container')) continue;
      if (!hasClassTokenPrefix(item, 'questionItem-')) continue;
      if (hasClassTokenPrefix(item, 'answerItem-')) continue;
      if (seen.has(item)) continue;
      seen.add(item);

      // 尝试从 content-{hash} 子元素获取文本
      const contentEl = item.querySelector('[class*="content-"]');
      const text = contentEl ? cleanText(contentEl.textContent) : getUserText(item);
      if (!text || text.length < 2) continue;

      const id = stableId(text);
      if (!item.id || item.id.startsWith(ID_PREFIX)) {
        item.id = id;
      }

      result.push({
        id: item.id,
        title: trunc(text, CONF.titleMax),
        rawText: text, // <--- 新增这行，把完整的文本存下来
        selector: generateSelector(item) || `#${CSS.escape(item.id)}`
      });

      if (result.length >= CONF.maxItems) break;
    }

    if (result.length > 0) return result;

    // 策略2: chat.qwen.ai — Ant Design X Bubble 组件
    const userBubbles = root.querySelectorAll('.ant-bubble.ant-bubble-end');
    for (const bubble of userBubbles) {
      if (bubble.closest('#sidenav-toc-container')) continue;
      if (seen.has(bubble)) continue;
      seen.add(bubble);

      const contentEl = bubble.querySelector('.ant-bubble-content');
      const text = contentEl ? cleanText(contentEl.textContent) : getUserText(bubble);
      if (!text || text.length < 2) continue;

      const id = stableId(text);
      if (!bubble.id || bubble.id.startsWith(ID_PREFIX)) {
        bubble.id = id;
      }

      result.push({
        id: bubble.id,
        title: trunc(text, CONF.titleMax),
        selector: generateSelector(bubble) || `#${CSS.escape(bubble.id)}`
      });

      if (result.length >= CONF.maxItems) break;
    }

    if (result.length > 0) return result;

    // 策略3: data 属性匹配
    const dataSelectors = [
      '[data-role="user"]',
      '[data-message-role="user"]',
      '[data-type="question"]',
    ];

    for (const sel of dataSelectors) {
      try {
        const els = root.querySelectorAll(sel);
        for (const el of els) {
          if (el.closest('#sidenav-toc-container')) continue;
          if (seen.has(el)) continue;
          seen.add(el);

          const text = getUserText(el);
          if (!text || text.length < 2) continue;

          const id = stableId(text);
          if (!el.id || el.id.startsWith(ID_PREFIX)) {
            el.id = id;
          }

          result.push({
            id: el.id,
            title: trunc(text, CONF.titleMax),
            selector: generateSelector(el) || `#${CSS.escape(el.id)}`
          });

          if (result.length >= CONF.maxItems) break;
        }
      } catch (e) { }
      if (result.length > 0) return result;
    }

    // 策略4: 结构推断 — 在 #ice-container 中查找交替的问答对
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_ELEMENT, {
      acceptNode: (node) => node.tagName === 'DIV' ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_SKIP,
    });

    let checkedContainers = 0;
    while (walker.nextNode()) {
      const div = walker.currentNode;
      checkedContainers++;
      if (checkedContainers > CONF.qwenFallbackContainerLimit) break;

      if (div.closest('#sidenav-toc-container')) continue;
      const children = Array.from(div.children).filter(
        ch => ch.offsetHeight > 30 && !ch.matches('nav,header,footer,script,style')
      );
      // 至少2个子元素，呈现交替的问答结构
      if (children.length < 2 || children.length > CONF.qwenFallbackMaxChildren) continue;

      const t1 = getUserText(children[0]);
      const t2 = getUserText(children[1]);
      if (!t1 || !t2 || t1.length > 500 || t2.length < 10) continue;

      // 偶数索引 = 用户消息，奇数 = 助手回复
      let matched = 0;
      for (let i = 0; i < children.length; i += 2) {
        const child = children[i];
        const assistantPeer = children[i + 1] || null;

        if (!hasQwenUserHint(child)) continue;
        if (assistantPeer && !hasQwenAssistantHint(assistantPeer)) continue;

        if (seen.has(child)) continue;
        seen.add(child);
        const text = getUserText(child);
        if (!text || text.length < 2) continue;

        const id = stableId(text);
        if (!child.id || child.id.startsWith(ID_PREFIX)) {
          child.id = id;
        }

        result.push({
          id: child.id,
          title: trunc(text, CONF.titleMax),
          selector: generateSelector(child) || `#${CSS.escape(child.id)}`
        });
        matched++;

        if (result.length >= CONF.maxItems) break;
      }
      if (matched > 0) return result;
    }

    return result;
  }

  // ── DOM 构建 ──────────────────────────

  function buildUI() {
    const old = document.getElementById('sidenav-toc-container');
    if (old) old.remove();

    const c = document.createElement('div');
    c.id = 'sidenav-toc-container';
    c.setAttribute('role', 'navigation');
    c.setAttribute('aria-label', '对话导航');
    // 新增了 #sidenav-toc-search-wrapper
    c.innerHTML =
      '<div id="sidenav-toc-inner">' +
      '<div id="sidenav-toc-header">' +
      '<span id="sidenav-toc-header-title">提示词</span>' +
      '<span id="sidenav-toc-header-count"></span>' +
      '</div>' +
      '<div id="sidenav-toc-search-wrapper">' +
      '<input type="text" id="sidenav-toc-search" placeholder="搜索对话..." autocomplete="off" spellcheck="false">' +
      '</div>' +
      '<div id="sidenav-toc-list"></div>' +
      '</div>';
    return c;
  }

  function buildItem(item, idx) {
    const d = document.createElement('div');
    d.className = 'sn-item';
    d.dataset.idx = idx;
    d.dataset.targetId = item.id;
    d.dataset.selector = item.selector || '';
    d.dataset.rawText = item.rawText || item.title; // <--- 新增这行，把全文藏在 data-raw-text 属性里
    d.tabIndex = 0;
    d.title = item.title;

    const txt = document.createElement('span');
    txt.className = 'sn-label';
    txt.textContent = item.title;

    const bar = document.createElement('span');
    bar.className = 'sn-bar';

    d.appendChild(txt);
    d.appendChild(bar);
    return d;
  }

  // ── 渲染 ──────────────────────────────

  function render() {
    if (!enabled || rendering) return;
    rendering = true;

    try {
      if (container && !document.body.contains(container)) {
        container = null;
        expanded = false;
        animating = false;
      }

      const newItems = scan();

      // 比较变化（基于 ID 和 title）
      const changed = newItems.length !== items.length ||
        newItems.some((it, i) => !items[i] || it.id !== items[i].id || it.title !== items[i].title);

      if (!changed && isContainerAlive()) {
        updateActive();
        rendering = false;
        return;
      }

      // 调试日志：仅在项目数量变化时输出
      if (newItems.length !== items.length) {
        console.log(`[SideNav TOC] 项目数: ${items.length} → ${newItems.length}`);
      }

      items = newItems;

      if (!isContainerAlive()) {
        container = buildUI();
        document.body.appendChild(container);
        expanded = false;
        animating = false;
        bindHoverEvents();
        bindClickEvents();
        bindScrollEvents();
        bindSearchEvents();
      }

      const list = container.querySelector('#sidenav-toc-list');
      const cnt = container.querySelector('#sidenav-toc-header-count');

      while (list && list.firstChild) list.removeChild(list.firstChild);

      if (items.length === 0) {
        container.classList.add('sn-hidden');
        if (retryCount < CONF.maxRetries) {
          retryCount++;
          scheduleRetryRender();
        }
        rendering = false;
        return;
      }

      retryCount = 0;
      if (retryRenderTimer) {
        clearTimeout(retryRenderTimer);
        retryRenderTimer = null;
      }
      container.classList.remove('sn-hidden');
      if (cnt) cnt.textContent = items.length;

      const frag = document.createDocumentFragment();
      items.forEach((it, i) => frag.appendChild(buildItem(it, i)));
      if (list) list.appendChild(frag);

      // 重建列表后，重新计算高亮
      // 保存之前的 activeIdx，如果新列表中存在则尝试保持
      const prevActiveIdx = activeIdx;
      activeIdx = -1;  // 重置，让 updateActive 重新计算

      updateActive();

      // 如果 updateActive 后仍然没有高亮，强制设置第一个
      if (activeIdx < 0 && items.length > 0) {
        setActive(prevActiveIdx >= 0 && prevActiveIdx < items.length ? prevActiveIdx : 0, true);
      }
    } catch (e) {
      console.warn('[SideNav TOC] Render error:', e);
    }

    rendering = false;
  }

  // ── 交互事件 ──────────────────────────

  function bindHoverEvents() {
    if (!container) return;
    container.addEventListener('mouseenter', onMouseEnter);
    container.addEventListener('mouseleave', onMouseLeave);
    container.addEventListener('transitionend', onTransitionEnd);
  }

  function onMouseEnter() {
    if (collapseTimer) { clearTimeout(collapseTimer); collapseTimer = null; }
    if (expanded || animating) return;
    expandTimer = setTimeout(doExpand, CONF.expandDelay);
  }

  function onMouseLeave() {
    if (expandTimer) { clearTimeout(expandTimer); expandTimer = null; }
    if (!expanded) return;
    collapseTimer = setTimeout(doCollapse, CONF.collapseDelay);
  }

  function onTransitionEnd(e) {
    if (e.target === container && e.propertyName === 'width') {
      animating = false;
      if (animatingTimer) { clearTimeout(animatingTimer); animatingTimer = null; }
    }
  }

  // 设置动画锁，带超时自动解除
  function setAnimating(value) {
    animating = value;
    if (animatingTimer) { clearTimeout(animatingTimer); animatingTimer = null; }
    if (value) {
      animatingTimer = setTimeout(() => {
        animating = false;
        animatingTimer = null;
      }, CONF.animationTimeout);
    }
  }

  function doExpand() {
    expandTimer = null;
    if (expanded || !isContainerAlive()) return;
    expanded = true;
    setAnimating(true);
    container.classList.add('sn-expanded');
  }

  function doCollapse() {
    collapseTimer = null;
    if (!expanded || !isContainerAlive()) return;

    // ====== 新增：如果搜索框正在被使用，拒绝收起！ ======
    const searchInput = document.getElementById('sidenav-toc-search');
    if (searchInput && document.activeElement === searchInput) {
      return;
    }
    // ===================================================

    expanded = false;
    setAnimating(true);
    container.classList.remove('sn-expanded');
  }

  function bindClickEvents() {
    if (!container) return;

    container.addEventListener('click', (e) => {
      const itemEl = e.target.closest('.sn-item');
      if (!itemEl) return;

      const idx = parseInt(itemEl.dataset.idx, 10);
      const item = items[idx];
      if (!item) return;

      // 实时查找目标元素
      let targetEl = getItemElement(item);

      if (!targetEl) {
        // 目标不存在，尝试重新扫描
        render();
        // 再次尝试
        const newItem = items[idx];
        if (newItem) {
          targetEl = getItemElement(newItem);
        }
      }

      if (!targetEl) {
        console.warn('[SideNav TOC] Target element not found for:', item.id);
        return;
      }

      // 设置点击锁定，防止滚动过程中切换高亮
      clickLocked = true;
      clickLockedIdx = idx;
      if (clickLockTimer) clearTimeout(clickLockTimer);
      clickLockTimer = setTimeout(() => {
        clickLocked = false;
        clickLockedIdx = -1;
        clickLockTimer = null;
      }, CONF.clickLockDuration);

      setActive(idx, true);
      jumpTo(targetEl);

      // 高亮目标：找到各平台内最贴合消息内容的元素
      let highlightEl = targetEl;

      if (IS_CHATGPT) {
        // ChatGPT：用户消息内容在 [data-message-author-role="user"] 内部
        const userMsg = targetEl.querySelector('[data-message-author-role="user"]');
        if (userMsg) {
          const inner = userMsg.querySelector('.whitespace-pre-wrap')
            || userMsg.querySelector('[class*="markdown"]');
          highlightEl = inner || userMsg;
        }
      } else if (IS_GEMINI) {
        // Gemini：用户消息在 query-text / user-query 等元素内
        const inner = targetEl.querySelector('.query-text')
          || targetEl.querySelector('.user-query')
          || targetEl.querySelector('.query-content')
          || targetEl.querySelector('[data-message-author="user"]');
        if (inner) highlightEl = inner;
      } else if (IS_QWEN) {
        // 千问：用户消息是右对齐紧凑气泡，找到比容器窄的最内层文字元素
        const containerW = targetEl.offsetWidth;
        const descendants = targetEl.querySelectorAll('div, span, p');
        let best = null;
        let bestW = containerW;
        for (const d of descendants) {
          const w = d.offsetWidth;
          if (w > 20 && w < containerW * 0.85 && d.textContent.trim().length > 1) {
            if (w <= bestW) { best = d; bestW = w; }
          }
        }
        if (best) highlightEl = best;
      }

      // 应用高亮效果：淡蓝背景 + 柔和光晕 + 圆角
      highlightEl.style.transition = 'background-color 0.3s ease, box-shadow 0.3s ease';
      highlightEl.style.backgroundColor = 'rgba(66, 133, 244, 0.15)';
      highlightEl.style.boxShadow = '0 0 0 3px rgba(66, 133, 244, 0.12)';
      highlightEl.style.borderRadius = '10px';

      let highlightTimer = null;
      const clearHighlight = () => {
        if (highlightEl && document.body.contains(highlightEl)) {
          highlightEl.style.backgroundColor = '';
          highlightEl.style.boxShadow = '';
          setTimeout(() => {
            if (highlightEl && document.body.contains(highlightEl)) {
              highlightEl.style.transition = '';
            }
          }, 300);
        }
        // 移除监听器
        window.removeEventListener('scroll', onUserAction, true);
        window.removeEventListener('mousedown', onUserAction, true);
        window.removeEventListener('touchstart', onUserAction, true);
        window.removeEventListener('keydown', onUserAction, true);
        if (highlightTimer) {
          clearTimeout(highlightTimer);
          highlightTimer = null;
        }
      };

      const onUserAction = () => {
        clearHighlight();
      };

      // 监听用户操作，操作时立即取消高亮
      window.addEventListener('scroll', onUserAction, { capture: true, once: true });
      window.addEventListener('mousedown', onUserAction, { capture: true, once: true });
      window.addEventListener('touchstart', onUserAction, { capture: true, once: true });
      window.addEventListener('keydown', onUserAction, { capture: true, once: true });

      // 无操作时，1.8秒后自动消失
      highlightTimer = setTimeout(clearHighlight, 1800);
    });

    container.addEventListener('keydown', (e) => {
      const item = e.target.closest('.sn-item');
      if (!item) return;
      if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        item.click();
      } else if (e.key === 'ArrowDown') {
        e.preventDefault();
        const next = item.nextElementSibling;
        if (next && next.classList.contains('sn-item')) next.focus();
      } else if (e.key === 'ArrowUp') {
        e.preventDefault();
        const prev = item.previousElementSibling;
        if (prev && prev.classList.contains('sn-item')) prev.focus();
      }
    });
  }

  let rafId = null;  // requestAnimationFrame ID

  function bindScrollEvents() {
    if (scrollListenersBound) return;

    // 使用 RAF + throttle 组合，更流畅
    const rafUpdate = () => {
      rafId = null;
      updateActive();
    };

    const throttled = throttle(() => {
      if (rafId) return;
      rafId = requestAnimationFrame(rafUpdate);
    }, CONF.scrollThrottle);

    // 包装 cancel 方法，同时清理 throttle 和 RAF
    scrollHandler = throttled;
    const originalCancel = throttled.cancel;
    scrollHandler.cancel = () => {
      if (originalCancel) originalCancel();
      if (rafId) { cancelAnimationFrame(rafId); rafId = null; }
    };

    window.addEventListener('scroll', scrollHandler, { passive: true, capture: true });
    document.addEventListener('scroll', scrollHandler, { passive: true, capture: true });
    scrollListenersBound = true;
  }

  function unbindScrollEvents() {
    if (!scrollListenersBound || !scrollHandler) return;
    window.removeEventListener('scroll', scrollHandler, { capture: true });
    document.removeEventListener('scroll', scrollHandler, { capture: true });
    if (scrollHandler.cancel) scrollHandler.cancel();
    if (rafId) { cancelAnimationFrame(rafId); rafId = null; }
    scrollHandler = null;
    scrollListenersBound = false;
  }

  // 强制刷新高亮状态（确保始终有高亮）
  function forceRefreshActive() {
    if (!isContainerAlive() || !items.length) return;
    const allItems = container.querySelectorAll('.sn-item');
    if (!allItems.length) return;

    // 如果 activeIdx 无效，默认高亮第一个
    if (activeIdx < 0 || activeIdx >= allItems.length) {
      activeIdx = 0;
    }

    allItems.forEach((el, i) => {
      el.classList.toggle('sn-active', i === activeIdx);
    });
  }

  function setActive(idx, force = false) {
    if (!isContainerAlive()) return;

    const allItems = container.querySelectorAll('.sn-item');
    if (!allItems.length) return;

    // 确保 idx 有效
    if (idx < 0 || idx >= allItems.length) {
      idx = 0;  // 默认第一个
    }

    // 如果 idx 没变且不强制，检查 DOM 是否已正确设置
    if (idx === activeIdx && !force) {
      const currentActive = container.querySelector('.sn-item.sn-active');
      const expectedActive = allItems[idx];
      // 如果 DOM 状态正确，跳过
      if (currentActive === expectedActive) return;
    }

    activeIdx = idx;
    allItems.forEach((el, i) => {
      el.classList.toggle('sn-active', i === idx);
    });
  }

  function updateActive() {
    if (!items.length || !isContainerAlive()) return;

    const allItems = container.querySelectorAll('.sn-item');
    if (!allItems.length) return;

    // 如果点击锁定中，保持锁定的高亮状态
    if (clickLocked && clickLockedIdx >= 0 && clickLockedIdx < items.length) {
      // 只刷新 DOM 状态，不改变 activeIdx
      if (activeIdx !== clickLockedIdx) {
        setActive(clickLockedIdx, true);
      }
      return;
    }

    // 只有1条时，直接高亮第一个
    if (items.length === 1) {
      setActive(0, true);
      return;
    }

    let bestI = -1;
    let bestD = Infinity;
    let fallbackI = -1;
    let fallbackD = Infinity;
    const target = window.innerHeight * SCROLL_TARGET_RATIO;
    let foundCount = 0;

    // 记录当前激活项的距离（用于粘性判断）
    let currentActiveD = Infinity;
    let currentActiveInView = false;

    for (let i = 0; i < items.length; i++) {
      const el = getItemElement(items[i]);
      if (!el) continue;
      foundCount++;
      try {
        const rect = el.getBoundingClientRect();
        const d = Math.abs(rect.top - target);
        const inView = rect.top >= -100 && rect.bottom <= window.innerHeight + 100;

        // 记录当前激活项的状态
        if (i === activeIdx) {
          currentActiveD = d;
          currentActiveInView = inView;
        }

        // 优先选择在视口内的元素
        if (inView) {
          if (d < bestD) { bestD = d; bestI = i; }
        }
        // 同时记录最近的元素作为 fallback
        if (d < fallbackD) { fallbackD = d; fallbackI = i; }
      } catch (e) { }
    }

    // 如果大部分元素都找不到了，可能需要重新扫描
    if (foundCount < items.length * 0.5 && foundCount < items.length - 1) {
      scheduleRetryRender();
    }

    // 优先用视口内的，没有则用最近的
    let finalI = bestI !== -1 ? bestI : fallbackI;

    // 如果都找不到，保持之前的或默认第一个
    if (finalI === -1) {
      finalI = (activeIdx >= 0 && activeIdx < items.length) ? activeIdx : 0;
    }

    // 粘性逻辑：如果当前激活项仍在视口内，且新选项的优势不够明显，保持当前
    // 这防止相邻项因为微小位置差异而频繁切换
    const STICKY_THRESHOLD = 80; // 像素阈值，新项必须比当前项近这么多才切换
    if (activeIdx >= 0 && activeIdx < items.length && currentActiveInView) {
      const improvement = currentActiveD - bestD;
      if (improvement < STICKY_THRESHOLD) {
        // 优势不够明显，保持当前激活项
        finalI = activeIdx;
      }
    }

    setActive(finalI);
  }

  // ── SPA 路由监听 ──────────────────────

  function ensureRouteHook() {
    if (window[ROUTE_HOOK_FLAG]) return;

    try {
      const _push = history.pushState;
      const _replace = history.replaceState;

      history.pushState = function () {
        _push.apply(this, arguments);
        window.dispatchEvent(new Event(ROUTE_EVENT));
      };
      history.replaceState = function () {
        _replace.apply(this, arguments);
        window.dispatchEvent(new Event(ROUTE_EVENT));
      };

      window[ROUTE_HOOK_FLAG] = true;
    } catch (e) { }
  }

  function watchRoute() {
    if (routeWatchBound) return;
    routeWatchBound = true;

    ensureRouteHook();

    routeEventHandler = scheduleRouteCheck;
    popstateHandler = scheduleRouteCheck;
    window.addEventListener(ROUTE_EVENT, routeEventHandler);
    window.addEventListener('popstate', popstateHandler);

    routePollTimer = setInterval(() => {
      if (!enabled) return;
      if (location.href !== lastUrl) onRouteChange();
    }, 1000);
  }

  function unwatchRoute() {
    if (!routeWatchBound) return;
    routeWatchBound = false;

    if (routePollTimer) { clearInterval(routePollTimer); routePollTimer = null; }
    if (routeEventHandler) {
      window.removeEventListener(ROUTE_EVENT, routeEventHandler);
      routeEventHandler = null;
    }
    if (popstateHandler) {
      window.removeEventListener('popstate', popstateHandler);
      popstateHandler = null;
    }
    if (routeCheckTimer) { clearTimeout(routeCheckTimer); routeCheckTimer = null; }
  }

  function scheduleRouteCheck() {
    if (!enabled || !routeWatchBound) return;
    if (routeCheckTimer) clearTimeout(routeCheckTimer);
    routeCheckTimer = setTimeout(() => {
      routeCheckTimer = null;
      if (location.href !== lastUrl) onRouteChange();
    }, 80);
  }

  function onRouteChange() {
    lastUrl = location.href;

    clearAllTimers();
    clearElementCache();  // 清理元素缓存

    retryCount = 0;
    items = [];
    activeIdx = -1;
    expanded = false;
    animating = false;
    cachedScrollContainer = null;

    if (isContainerAlive()) {
      container.classList.remove('sn-expanded');
      const list = container.querySelector('#sidenav-toc-list');
      if (list) while (list.firstChild) list.removeChild(list.firstChild);
      container.classList.add('sn-hidden');
    }

    routeRenderTimer = setTimeout(() => {
      routeRenderTimer = null;
      render();
    }, CONF.routeDelay);
  }

  // ── DOM 变化监听 ──────────────────────

  function watchDOM() {
    if (observer) observer.disconnect();
    const rerender = debounce(render, CONF.observerDebounce);

    observer = new MutationObserver((muts) => {
      if (rendering) return;

      for (const m of muts) {
        if (m.target.id === 'sidenav-toc-container' ||
          m.target.id === 'sidenav-toc-list' ||
          m.target.id === 'sidenav-toc-inner' ||
          m.target.id === 'sidenav-toc-header') continue;
        if (m.target.closest?.('#sidenav-toc-container')) continue;

        if (m.type === 'childList' && (m.addedNodes.length || m.removedNodes.length)) {
          rerender();
          return;
        }
      }
    });

    observer.observe(document.body, { childList: true, subtree: true });
  }

  // ── 启动 ──────────────────────────────

  // 定期检查高亮状态是否正确
  function startActiveCheck() {
    if (activeCheckTimer) return;
    activeCheckTimer = setInterval(() => {
      if (!enabled || !isContainerAlive() || !items.length) return;

      const allItems = container.querySelectorAll('.sn-item');
      if (!allItems.length) return;

      const activeEl = container.querySelector('.sn-item.sn-active');

      // 情况1：没有任何高亮 - 强制设置一个
      if (!activeEl) {
        if (activeIdx >= 0 && activeIdx < allItems.length) {
          forceRefreshActive();
        } else {
          setActive(0, true);
        }
        return;
      }

      // 情况2：有高亮但位置不对
      if (activeIdx >= 0 && activeIdx < allItems.length) {
        if (activeEl !== allItems[activeIdx]) {
          forceRefreshActive();
        }
      }
    }, 2000);
  }

  function stopActiveCheck() {
    if (activeCheckTimer) {
      clearInterval(activeCheckTimer);
      activeCheckTimer = null;
    }
  }

  function bindGlobalEvents() {
    // 切回标签页时刷新高亮
    visibilityHandler = () => {
      if (!document.hidden && enabled && isContainerAlive()) {
        forceRefreshActive();
      }
    };
    document.addEventListener('visibilitychange', visibilityHandler);

    // 窗口获得焦点时也刷新一下
    focusHandler = () => {
      if (enabled && isContainerAlive()) {
        setTimeout(forceRefreshActive, 100);
      }
    };
    window.addEventListener('focus', focusHandler);
  }

  function unbindGlobalEvents() {
    if (visibilityHandler) {
      document.removeEventListener('visibilitychange', visibilityHandler);
      visibilityHandler = null;
    }
    if (focusHandler) {
      window.removeEventListener('focus', focusHandler);
      focusHandler = null;
    }
  }

  function boot() {
    setTimeout(() => {
      render();
      watchDOM();
      watchRoute();
      startActiveCheck();
      bindGlobalEvents();

      try {
        chrome?.runtime?.onMessage?.addListener((msg, _, reply) => {
          if (!msg || typeof msg !== 'object') return false;

          if (msg.action === 'toggle') {
            enabled ? disable() : enable();
            reply({ enabled });
            return false;
          } else if (msg.action === 'refresh') {
            retryCount = 0;
            items = [];
            cachedScrollContainer = null;
            activeIdx = -1;
            render();
            reply({ ok: true });
            return false;
          } else if (msg.action === 'getStatus') {
            reply({ enabled, itemCount: items.length });
            return false;
          }
          return false;
        });
      } catch (e) { }
    }, CONF.initDelay);
  }

  function disable() {
    enabled = false;
    clearAllTimers();
    stopActiveCheck();
    unwatchRoute();
    unbindScrollEvents();
    unbindGlobalEvents();
    if (isContainerAlive()) container.style.display = 'none';
    observer?.disconnect();
  }

  function enable() {
    enabled = true;
    if (isContainerAlive()) container.style.display = '';
    retryCount = 0;
    cachedScrollContainer = null;
    activeIdx = -1;
    render();
    watchDOM();
    watchRoute();
    bindScrollEvents();
    startActiveCheck();
    bindGlobalEvents();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }


  // ── 升级版：搜索功能事件绑定（防抖 + 全文搜索 + 焦点管理） ──
  function bindSearchEvents() {
    if (!container) return;
    const searchInput = container.querySelector('#sidenav-toc-search');
    if (!searchInput) return;

    // 1. 将原本直接执行的逻辑，用 debounce 包裹起来，延迟 666 毫秒
    const handleSearch = debounce(() => {
      const query = searchInput.value.trim().toLowerCase();
      const allItems = container.querySelectorAll('.sn-item');
      let visibleCount = 0;

      allItems.forEach(el => {
        // 核心改变：去拿咱们刚才存的未阉割版的全文进行比对！
        const fullText = (el.dataset.rawText || '').toLowerCase();

        if (fullText.includes(query)) {
          el.style.display = '';
          visibleCount++;
        } else {
          el.style.display = 'none';
        }
      });

      const cnt = container.querySelector('#sidenav-toc-header-count');
      if (cnt) {
        cnt.textContent = query ? `${visibleCount} / ${items.length}` : items.length;
      }

      updateActive();
    }, 666); // 666 毫秒的防抖黄金时间

    // 绑定防抖后的函数
    searchInput.addEventListener('input', handleSearch);

    searchInput.addEventListener('keydown', (e) => {
      e.stopPropagation(); // 阻止按键冒泡

      // 体验优化：按下 Esc 键清空搜索框并让其失去焦点
      if (e.key === 'Escape') {
        searchInput.value = '';
        handleSearch();
        searchInput.blur();
      }
    });

    // 2. 体验优化：当搜索框失去焦点时，如果鼠标其实早就移出侧边栏了，顺手把它收起
    searchInput.addEventListener('blur', () => {
      if (!container.matches(':hover')) {
        onMouseLeave();
      }
    });
  }


})();

