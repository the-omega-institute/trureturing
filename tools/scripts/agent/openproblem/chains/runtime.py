#!/usr/bin/env python3
"""Lane continuations composed from the canonical pipeline and brief generators."""
from pathlib import Path
import re
import subprocess
import sys

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS / 'briefgen'))
from common import Context, entry, fail, lane_spec, load, name, read, sha, uint


class Chain:
    def __init__(self, lane, tree):
        self.ctx = Context(required=('gh', 'make'))
        self.lane = name(lane)
        self.spec = lane_spec(self.ctx.scratch / 'lanes' / (lane + '.json'))
        if self.spec['lane'] != lane:
            fail(13, 'lane does not match spec')
        self.tree = self.tree_path(tree)
        if not self.tree.is_dir():
            fail(11, 'worktree missing: ' + str(self.tree))
        if self.tree != self.tree_path(self.spec['worktree']):
            fail(13, 'worktree does not match lane spec')
        self.briefs = self.ctx.scratch / 'briefs'
        self.logs = self.ctx.scratch / 'logs'
        self.logs.mkdir(parents=True, exist_ok=True)
        read(self.ctx.scratch / 'lanes' / (lane + '.target.md'))

    def tree_path(self, value):
        path = Path(value)
        return (path if path.is_absolute() else self.ctx.main / path).resolve()

    def brief(self, seat):
        return self.briefs / (name(seat) + '.md')

    def call(self, command, log=None):
        if log:
            with (self.logs / log).open('w') as out:
                result = subprocess.run([str(x) for x in command], cwd=self.ctx.main,
                                        stdout=out, stderr=subprocess.STDOUT)
        else:
            result = subprocess.run([str(x) for x in command], cwd=self.ctx.main)
        if result.returncode:
            fail(result.returncode if result.returncode > 0 else 16,
                 'chain dependency failed: ' + Path(command[1] if command[0] in ('bash', sys.executable) else command[0]).name +
                 (('; log=' + str(self.logs / log)) if log else ''))

    def python(self, tool, *args, log=None):
        self.call([sys.executable, TOOLS / tool, *args], log)

    def shell(self, tool, *args, log=None):
        self.call(['/bin/bash', TOOLS / tool, *args], log)

    def dispatch(self, seat, stage, brief=None):
        brief = brief or self.brief(seat)
        read(brief)
        log = seat + '.log'
        self.shell('pipeline/seat-wait.sh', self.ctx.prefix + name(seat), brief, self.tree, stage, '0', log=log)
        text = read(self.logs / log)
        # Runner output names a flight; DONE presets instead print its result path.
        flights = re.findall(r'^FLIGHT ([0-9a-f]{24})(?:\s|$)', text, re.M)
        if not flights:
            for line in text.splitlines():
                path = Path(line.strip())
                if path.name != 'result.json':
                    continue
                try:
                    path = path if path.is_absolute() else self.ctx.main / path
                    parts = path.resolve().relative_to(self.ctx.sshx).parts
                except (OSError, ValueError):
                    continue
                if (len(parts) == 3 and re.fullmatch(r'[0-9a-f]{24}', parts[0])
                        and re.fullmatch(r'attempt-[0-9]+', parts[1])):
                    flights.append(parts[0])
        if not flights:
            fail(13, 'dispatch supplied no result identity: ' + seat)
        result = self.ctx.result(flights[-1])
        payload = load(result)
        conclusion = payload.get('conclusion')
        if not isinstance(conclusion, dict):
            fail(13, 'result conclusion must be an object: ' + str(result))
        verdict = conclusion.get('verdict')
        if verdict is None and seat == 'implb-' + self.lane + '-r1':
            verdict = conclusion.get('status')
        if not isinstance(verdict, str) or not verdict:
            fail(13, 'result verdict missing: ' + str(result))
        print(seat, result, verdict, flush=True)
        return result, conclusion, verdict

    def accepts(self, verdict, *allowed):
        if verdict in allowed:
            return True
        print('CHAIN_STOP verdict=' + verdict, flush=True)
        return False

    def reviews(self, round_number):
        for role in ('architecture', 'quality', 'tests'):
            self.dispatch('review-' + self.lane + '-' + role + '-r' + str(round_number), 'review')

    def from_mirror(self, mirror):
        result, _, verdict = self.dispatch(mirror, 'review')
        if not self.accepts(verdict, 'approve'):
            return
        flight = result.parent.parent.name
        self.shell('briefgen/stageb_prep.sh', self.lane, 'quality', flight, log='stageb-prep-' + self.lane + '.log')
        seat = 'implb-' + self.lane + '-r1'
        head = self.briefs / (seat + '.head.md')
        if not head.is_file() or not head.stat().st_size:
            self.python('briefgen/implb_head.py', self.lane)
        self.brief(seat).write_text(read(head) + read(self.briefs / ('impl-op-w1-' + self.lane + '.stageB.filled.md')))
        _, conclusion, verdict = self.dispatch(seat, 'implementation')
        if not self.accepts(verdict, 'success'):
            return
        pr = conclusion.get('pr_number') or conclusion.get('pr')
        if isinstance(pr, dict):
            pr = pr.get('number')
        pr = str(uint(str(pr), 'PR'))
        self.postb(pr)
        self.reviews(1)

    def postb(self, pr):
        log = 'postb3-' + self.lane + '.log'
        self.shell('briefgen/postb3.sh', self.lane, pr, log=log)
        if not re.search(r'^READY(?:\s|$)', read(self.logs / log), re.M):
            fail(13, 'postb3 supplied no READY sentinel')
        head = sha(self.output('gh', 'pr', 'view', pr, '-R', self.ctx.slug, '--json', 'headRefOid', '-q', '.headRefOid'))
        self.python('briefgen/ci_body_final.py', pr, head)

    def output(self, *command):
        result = subprocess.run(command, cwd=self.ctx.main, text=True, capture_output=True)
        if result.returncode:
            fail(16, 'cannot read ' + ' '.join(command[:2]) + ': ' + result.stderr.strip())
        return result.stdout.strip()


def main(argv):
    mode, args = argv[1], argv[2:]
    bounds = {'stagea': (4, 4), 'from-mirror': (3, 3), 'rework': (7, 8), 'prep-and-chain': (4, 5),
              'postb-prepare': (3, 3), 'review-one': (3, 3)}
    if mode not in bounds or not bounds[mode][0] <= len(args) <= bounds[mode][1]:
        fail(10, 'invalid chain arguments; see README')
    if mode in ('postb-prepare', 'review-one'):
        lane, middle, tree = args
        if mode == 'postb-prepare': uint(middle, 'PR')
        elif middle not in ('architecture', 'quality', 'tests'): fail(13, 'invalid review role')
        chain = Chain(lane, tree)
        if mode == 'postb-prepare':
            chain.postb(middle)
            for role in ('architecture', 'quality', 'tests'):
                read(chain.brief('review-' + lane + '-' + role + '-r1'))
        else:
            chain.dispatch('review-' + lane + '-' + middle + '-r1', 'review')
        return
    if mode == 'prep-and-chain':
        kind, lane, tree, first = args[:4]
        if kind not in ('stagea', 'mirror') or len(args) != (5 if kind == 'stagea' else 4):
            fail(10, 'prep-and-chain TYPE LANE WORKTREE A [B]')
        chain = Chain(lane, tree)
        read(chain.brief(first))
        if kind == 'stagea': read(chain.brief(args[4]))
        chain.shell('pipeline/prep-lane-tree.sh', chain.tree, log='prep-' + lane + '.log')
        return main([argv[0], 'stagea' if kind == 'stagea' else 'from-mirror', lane, tree, *args[3:]])
    if mode in ('stagea', 'from-mirror'):
        lane, tree, first = args[:3]
        chain = Chain(lane, tree)
        if first != '-': read(chain.brief(first))
        mirror = args[3] if mode == 'stagea' else first
        read(chain.brief(mirror))
        if mode == 'stagea' and first != '-':
            _, _, verdict = chain.dispatch(first, 'implementation')
            if not chain.accepts(verdict, 'mirror-ready'):
                return
        chain.from_mirror(mirror)
        return
    lane, pr, round_number, tree, oldhead, rw, mw = args[:7]
    uint(pr, 'PR'); uint(round_number, 'round'); sha(oldhead); name(rw); name(mw)
    chain = Chain(lane, tree)
    seat = 'rework-' + lane + '-' + rw
    mirror = 'mirror-' + lane + '-' + mw
    resume = seat + 'b'
    read(chain.brief('mirror-check-' + lane + '-' + mw))
    read(chain.briefs / (resume + '.head.md'))
    if len(args) == 8:
        read(args[7])
        chain.python('briefgen/rework_brief.py', args[7])
        chain.brief(seat).write_text(read(chain.briefs / ('rework-' + lane + '.md')))
    read(chain.brief(seat))
    _, _, verdict = chain.dispatch(seat, 'implementation')
    if not chain.accepts(verdict, 'mirror-ready'):
        return
    fixhead = sha(chain.output('git', '-C', str(chain.tree), 'rev-parse', 'HEAD'))
    _, _, verdict = chain.dispatch(mirror, 'review', chain.brief('mirror-check-' + lane + '-' + mw))
    if not chain.accepts(verdict, 'approve'):
        return
    if chain.output('git', '-C', str(chain.tree), 'rev-parse', 'HEAD') != fixhead:
        fail(14, 'head moved during mirror review')
    chain.python('briefgen/rehead.py', chain.briefs / (resume + '.head.md'), chain.brief(seat),
                 chain.brief(resume), '0' * 40, fixhead, 'rework round')
    result, _, verdict = chain.dispatch(resume, 'implementation')
    if not chain.accepts(verdict, 'success', 'done'):
        return
    newhead = sha(chain.output('gh', 'pr', 'view', pr, '-R', chain.ctx.slug, '--json', 'headRefOid', '-q', '.headRefOid'))
    if newhead == oldhead:
        print('CHAIN_STOP unchanged PR head', flush=True)
        return
    chain.python('standing-check.py', pr, '--round', round_number)
    chain.python('gen_review.py', '--codex3', lane, pr, chain.spec['branch'], chain.tree,
                 result, chain.ctx.scratch / 'lanes' / (lane + '.target.md'), round_number,
                 log='genreview-' + lane + '-r' + round_number + '.log')
    chain.reviews(round_number)


if __name__ == '__main__':
    if '--selftest' in sys.argv[1:]:
        subprocess.check_call([sys.executable, str(Path(__file__).with_name('selftest.py')),
                               sys.argv[1] if len(sys.argv) == 3 else 'all'])
    else:
        sys.exit(entry(main, minimum=1))
