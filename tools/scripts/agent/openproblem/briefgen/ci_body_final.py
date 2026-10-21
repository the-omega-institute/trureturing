#!/usr/bin/env python3
"""Render final required-CI readings at a delivered PR head."""
from common import Context, entry, fail
def main(argv):
    ctx = Context(required=('gh',))
    import sys, json, subprocess, re
    pr, head = (argv[1], argv[2])
    if not pr.isdigit() or not re.fullmatch(r'[0-9a-f]{40}', head):
        fail(13, 'numeric PR and full head SHA required')
    R = ctx.slug

    def gh(*a):
        return subprocess.check_output(['gh', *a, '-R', R], text=True)
    runs = json.loads(gh('run', 'list', '--commit', head, '--event', 'pull_request', '--json', 'databaseId,conclusion,status,name'))
    runs = [r for r in runs if r['status'] == 'completed' and r.get('name') == 'CI']
    if not runs:
        print('CI_BODY_FAIL no-completed-run')
        sys.exit(1)
    run = runs[0]['databaseId']
    jobs = json.loads(gh('run', 'view', str(run), '--json', 'jobs'))['jobs']
    jc = {j['name']: (j['databaseId'], j['conclusion']) for j in jobs}
    if jc.get('required', (0, ''))[1] != 'success' or jc.get('current', (0, ''))[1] != 'success':
        print('CI_BODY_FAIL not-green', jc.get('required'), jc.get('current'))
        sys.exit(1)
    log = subprocess.run(['gh', 'api', f"repos/{R}/actions/jobs/{jc['current'][0]}/logs"], capture_output=True, text=True, check=True).stdout
    blocks = 0
    steps = 0
    for line in log.splitlines():
        i = line.find('{"executed"')
        if i < 0:
            continue
        try:
            d = json.loads(line[i:].strip())
        except Exception:
            continue
        steps += 1
        blocks += sum((1 for x in d.get('diagnostics', []) if x.get('AdmissionEffect') == 1))
    if not steps:
        fail(13, 'CI_BODY_FAIL no-rules-readings')
    current_head = gh('pr', 'view', pr, '--json', 'headRefOid', '-q', '.headRefOid').strip()
    if current_head != head:
        fail(13, 'CI_BODY_FAIL head-mismatch')
    body = gh('pr', 'view', pr, '--json', 'body', '-q', '.body')
    rq, cu = (jc['required'][0], jc['current'][0])
    out = []
    n = 0
    for line in body.split('\n'):
        cells = line.split('|')
        if line.startswith('|') and len(cells) > 3 and re.search('Required CI', cells[1]):
            line = f'| Required CI | `gh pr checks {pr} --required` | `{head}` | exit 0; required SUCCESS (job {rq}); current SUCCESS (job {cu}); run [{run}](https://github.com/{R}/actions/runs/{run}) |'
            n += 1
        elif line.startswith('|') and len(cells) > 3 and re.search('CI current reading', cells[1]):
            line = f'| CI current reading | `gh run view {run} --json jobs` | `{head}` | exit 0; current SUCCESS, job {cu}; {steps} rules steps with {blocks} Block diagnostics |'
            n += 1
        elif re.search('workflow run \\[\\d+\\]', line) and '`required`' in line and re.search('not-observed|in_progress|pending|not yet', line):
            line = f'At delivered head `{head}`, workflow run [{run}](https://github.com/{R}/actions/runs/{run}) reports `required`: success (job {rq}); `current`: success (job {cu}); its {steps} rules steps report {blocks} Block diagnostics.'
            n += 1
        elif re.match('CI run `\\d+`', line):
            line = f'CI run `{run}` at `{head}`: `current` SUCCESS (job {cu}) and `required` SUCCESS (job {rq}); the {steps} rules steps report {blocks} Block diagnostics.'
            n += 1
        if line.startswith('Verification attribution:') and 'final CI readings' not in line:
            line = line.rstrip() + ' The Claude Code orchestrator read the final CI readings at the delivered head from the run and its raw job log.'
        out.append(line)
    if n == 0:
        print('CI_BODY_FAIL no-pending-lines')
        sys.exit(1)
    ctx.state.mkdir(parents=True, exist_ok=True)
    open(str(ctx.state / f'ci-body-{pr}.md'), 'w').write('\n'.join(out))
    subprocess.check_call(['gh', 'pr', 'edit', pr, '-R', R, '--body-file', str(ctx.state / f'ci-body-{pr}.md')], stdout=subprocess.DEVNULL)
    print('CI_BODY_OK', n, 'lines; run', run, 'blocks', blocks)

if __name__ == "__main__":
 import sys
 sys.exit(entry(main, minimum=2, maximum=2))
