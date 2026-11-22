import { execFileSync } from 'node:child_process';
import { copyFileSync, mkdirSync, mkdtempSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const { HOME, PATH, RUNNER_TEMP } = process.env;
const source = dirname(fileURLToPath(import.meta.url));
const client = join(mkdtempSync(join(RUNNER_TEMP, 'layer-sdk-')), 'lean-compile-checkpoint');
mkdirSync(client);
for (const name of ['package.json', 'package-lock.json', 'run.mjs']) {
  copyFileSync(join(source, name), join(client, name));
}
execFileSync('npm', ['ci', '--ignore-scripts', '--omit=dev', '--no-audit', '--no-fund'], {
  cwd: client, env: {HOME, PATH}, stdio: 'inherit', timeout: 120000
});
await import(pathToFileURL(join(client, 'run.mjs')).href);
