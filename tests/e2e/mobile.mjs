// End-to-end smoke test on a phone-sized viewport. Usage: node tests/e2e/mobile.mjs [baseUrl] [screenshotDir]
import { chromium } from 'playwright-core';
import { existsSync, mkdirSync } from 'node:fs';

const base = process.argv[2] ?? 'http://localhost:4173';
const shots = process.argv[3] ?? 'test-results';
mkdirSync(shots, { recursive: true });
const exe = ['/opt/pw-browsers/chromium', '/opt/pw-browsers/chromium-1194/chrome-linux/chrome'].find((p) => existsSync(p));
const browser = await chromium.launch({ executablePath: exe });
const ctx = await browser.newContext({ viewport: { width: 390, height: 844 }, deviceScaleFactor: 2, isMobile: true, hasTouch: true });
const page = await ctx.newPage();
const errors = [];
page.on('pageerror', (e) => errors.push(e.message));
page.on('console', (m) => m.type() === 'error' && errors.push(m.text()));

function check(cond, msg) {
  if (!cond) {
    console.error('FAIL:', msg);
    process.exitCode = 1;
  } else console.log('ok:', msg);
}
async function noHScroll(name) {
  const w = await page.evaluate(() => document.documentElement.scrollWidth - document.documentElement.clientWidth);
  check(w <= 1, `${name}: no horizontal page scroll (overflow ${w}px)`);
}

await page.goto(base + '/');
await page.screenshot({ path: `${shots}/home.png`, fullPage: true });
check(await page.getByText('Learn to prove things').isVisible(), 'home renders');
await noHScroll('home');

await page.goto(base + '/ide/');
await page.getByText('All checked ✓').first().waitFor({ timeout: 30000 });
check(true, 'IDE checks default theory without errors');
await page.screenshot({ path: `${shots}/ide.png` });
await noHScroll('ide');
// type a broken lemma and see an error
await page.locator('.cm-content').click();
await page.keyboard.press('Control+End');
await page.keyboard.press('ArrowUp');
await page.keyboard.press('Home');
await page.keyboard.type('lemma "rev xs = xs" by simp\n');
await page.getByText(/1 error/).first().waitFor({ timeout: 30000 });
check(true, 'IDE reports an error for a false lemma');
await page.screenshot({ path: `${shots}/ide-error.png` });
// abbreviation replacement
await page.keyboard.type('lemma "A ==> A" by simp\n');
const txt = await page.locator('.cm-content').innerText();
check(txt.includes('A ⟹ A'), 'ASCII ==> is replaced by ⟹');

await page.goto(base + '/practice/');
await page.screenshot({ path: `${shots}/practice.png`, fullPage: true });
await noHScroll('practice');

await page.goto(base + '/practice/itrev/');
await page.getByText('Not solved yet').waitFor({ timeout: 30000 });
check(true, 'exercise starter is not solved');
await page.getByRole('button', { name: 'Show solution' }).click();
await page.getByRole('button', { name: /Really replace/ }).click();
await page.getByText('Solved!').first().waitFor({ timeout: 30000 });
check(true, 'exercise solution is accepted');
await page.screenshot({ path: `${shots}/exercise.png`, fullPage: true });
await noHScroll('exercise');

await page.goto(base + '/learn/induction/');
await page.getByRole('button', { name: /Run & edit/ }).first().click();
await page.getByText('All checked ✓').first().waitFor({ timeout: 30000 });
check(true, 'lesson example runs');
await page.screenshot({ path: `${shots}/lesson.png`, fullPage: true });
await noHScroll('lesson');

await page.goto(base + '/reference/');
await noHScroll('reference');

check(errors.length === 0, 'no page errors: ' + errors.join(' | '));
await browser.close();
