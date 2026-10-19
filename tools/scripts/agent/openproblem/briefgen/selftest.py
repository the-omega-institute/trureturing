#!/usr/bin/env python3
"""Hermetic golden cases and rejection cases for each brief entry point."""
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
DATA = HERE / 'testdata'

REGISTRATION_CI_READING = (
    'Report whether each Reg registration decodes at the delivered head from the scoped report, '
    'and read its `DTR-*` finding from the required CI `current` job of the pushed head '
    '(`gh run view <run-id> --log --job <current-job-id>`, the `DTR-` lines; report the run id '
    'and job id); until that reading exists the registration is pending. '
    'Never write `declared_validated` without that CI reading.')


def assert_dtr_source(text):
    for instruction in re.split(r'\n\s*\n|\n(?=\s*(?:[-*]|\d+\.)\s)', text):
        # Decoding and CI validation may share a bullet, but have distinct sources.
        for clause in re.split(r'(?<=[.;])\s+|\s+and\s+(?=(?:read|report)\b)',
                               instruction, flags=re.I):
            status = re.search(r'\b(?:DTR|declared_validated)\b|Reg registration state', clause)
            report = re.search(r'\b(?:the\s+(?:scoped\s+)?report|scoped report|Lean report|report command)\b'
                               r'|`[^`\n]*\breport[\w-]*[^`\n]*`'
                               r'|\bmake\s+lean-report(?:-scoped)?(?![\w-])', clause, re.I)
            assert not (status and report), \
                'DTR findings and declared_validated require the pushed delivery head CI current job reading'


def assert_unsafe_dtr_source(text):
    try:
        assert_dtr_source(text)
    except AssertionError:
        return
    raise AssertionError('unsafe DTR source accepted: ' + text)


def assert_scoped_builds(text, *, binding=False, all_commands=False):
    from common import BUILD_SCOPE
    if binding:
        assert text.count(BUILD_SCOPE) == 1, 'missing or repeated Build-scope block'
        text = text.replace(BUILD_SCOPE, '', 1)
    # Exempt only the command mention, never the rest of its line: prohibitions,
    # disclosure of an already-run gate, diagnostic descriptions and serialization.
    for reference in (
        r'(?:Do not|Never) run `make (?:lean|lean-report|test|gate)`',
        r'- the exact command `make gate BASE=<40-hex>`;',
        r'`make gate` reports `(?:describe red code=incomplete-library-locator|blueprint-namespace)`',
        r'Do not paste the `make gate` JSON',
        r'one `lake env lean`, `lake build` or `make lean …` invocation, never several in parallel',
    ):
        text = re.sub(reference, '', text)
    commands = r'lean(?:-report(?:-scoped)?)?'
    if all_commands:
        commands += r'|test|gate'
    for match in re.finditer(r'\bmake\s+(' + commands + r')(?![\w-])', text):
        tail = text[match.end():].split('`', 1)[0].split('\n', 1)[0]
        assert match[1] != 'lean-report', 'whole-library Lean report instruction'
        assert re.match(r'''\s+LEAN_TARGETS=(?:"[^"\n]+"|'[^'\n]+'|[^\s`"']+)''', tail), \
            'untargeted build instruction: ' + match[0] + tail


def build_scope_regressions():
    from common import BUILD_SCOPE
    ci_source = ('Read `DTR-Declared` from the pushed delivery head required CI '
                 '`current` job using `gh run view <run-id> --log --job <current-job-id>`.')
    assert_dtr_source(ci_source)
    assert_dtr_source(REGISTRATION_CI_READING)
    assert_dtr_source('Run `make lean-report-scoped LEAN_TARGETS="D5.Sample"`.')
    assert_dtr_source('- Run `make lean-report-scoped LEAN_TARGETS="D5.Sample"`.\n- ' + ci_source)
    for command in ('make lean-report-scoped LEAN_TARGETS="D5.Sample"', 'make lean-report',
                    'python3 report.py', 'custom-report --target D5.Sample'):
        for text in (f'Read the DTR finding for the target in `{command}`.',
                     f'For example `DTR-Unregistered` from `{command}`.',
                     f'Read `{command}`\nfor the target\'s `DTR-Declared` finding.',
                     f'Write `declared_validated` from `{command}`.'):
            assert_unsafe_dtr_source(text)
    for text in ('Read the `DTR-*` finding from the scoped report.',
                 'Write `declared_validated` from the scoped report.',
                 'Report the Reg registration state at the delivered head from the scoped report (decoded or not). '
                 'Never write `declared_validated` without the reading.'):
        assert_unsafe_dtr_source(text)
    assert_scoped_builds(BUILD_SCOPE, binding=True, all_commands=True)
    for text in ('', BUILD_SCOPE.replace('binding;', 'optional;'),
                 *(BUILD_SCOPE + '\n' + command for command in (
                     '`make lean`', '`make lean-report`', '`make test`',
                     '`make gate BASE=abc`', '`make lean LEAN_TARGETS=""`',
                     '`make lean-report-scoped`',
                     '`make lean-report LEAN_TARGETS="D5.Sample"`'))):
        try:
            assert_scoped_builds(text, binding=True, all_commands=True)
        except AssertionError:
            pass
        else:
            raise AssertionError('unsafe build instruction accepted: ' + text)
    references = (
        *(prefix + ' `make ' + command + '`.'
          for prefix in ('Do not run', 'Never run')
          for command in ('lean', 'lean-report', 'test', 'gate')),
        '- the exact command `make gate BASE=<40-hex>`;',
        '`make gate` reports `describe red code=incomplete-library-locator`.',
        '`make gate` reports `blueprint-namespace` if it is missing or different.',
        'Do not paste the `make gate` JSON or its inventories into the body.',
        'one `lake env lean`, `lake build` or `make lean …` invocation, never several in parallel',
    )
    for reference in references:
        assert_scoped_builds(reference, all_commands=True)
        for command in ('lean', 'lean-report', 'test', 'gate'):
            try:
                assert_scoped_builds(reference + ' Then run `make ' + command + '`.',
                                     all_commands=True)
            except AssertionError:
                pass
            else:
                raise AssertionError('reference hid unsafe instruction: ' + reference)
    blocks = sorted(path for path in (TOOLS / 'templates/blocks').rglob('*') if path.is_file())
    assert blocks, 'missing implementation/rework/continuation blocks'
    for path in [TOOLS / 'templates/impl-base-brief.md', *blocks]:
        template = path.read_text()
        try:
            assert_dtr_source(template)
            assert_scoped_builds(template, all_commands=True)
        except AssertionError as exc:
            raise AssertionError(str(path.relative_to(TOOLS)) + ': ' + str(exc)) from exc
        for command in ('lean', 'lean-report', 'test', 'gate'):
            try:
                assert_scoped_builds(template + '\n`make ' + command + '`', all_commands=True)
            except AssertionError:
                pass
            else:
                raise AssertionError('template regression accepted: ' + str(path) + ': ' + command)
    print('BUILD_SCOPE_REGRESSIONS template=targeted blocks=' + str(len(blocks)) +
          ' negative_controls=passed')


def head_generality_regressions(tool):
    with tempfile.TemporaryDirectory(prefix='header fixtures __tokens__ ') as tmp:
        root = Path(tmp); env = prepare(root)
        spec_path = root / 'scratch/lanes/sample.json'
        spec = json.loads(spec_path.read_text())
        spec['target_md'] = spec['target_md'].replace('generality: I', 'generality: G')
        spec_path.write_text(json.dumps(spec))
        source = root / 'tree' / (spec['module'] + '.lean')
        source.parent.mkdir(parents=True)

        def check(expected):
            result = subprocess.run(command(tool, root), cwd=root, env=env,
                                    capture_output=True, text=True)
            assert result.returncode == 0, (result.stdout, result.stderr)
            text = (root / 'scratch/briefs/implb-sample-r1.head.md').read_text()
            assert '`generality: ' + expected + '`' in text, text
            assert_scoped_builds(text, binding=True)

        for value in ('I', 'E', 'G'):
            source.write_text('/-\n  generality: ' + value + ' \t\n-/\n')
            check(value)
        source.unlink()
        check('G')
        spec['target_md'] = spec['target_md'].replace('`generality: G`', '')
        spec_path.write_text(json.dumps(spec))
        check('I')
    print('HEAD_GENERALITY_REGRESSIONS header=GIE fallback=target,default')


def stub(kind, args):
    data = json.loads((DATA / 'input.json').read_text())
    root = Path(os.environ['BRIEF_FIXTURE_ROOT'])
    head = data['head']
    if kind == 'git':
        if 'worktree' in args: print('worktree ' + str(root / 'main'))
        elif 'get-url' in args: print('https://github.com/' + os.environ.get('BRIEF_FIXTURE_SLUG', 'example/fixture') + '.git')
        elif 'rev-parse' in args: print('false' if '--is-bare-repository' in args else str(root / 'main') if '--show-toplevel' in args else head)
        elif 'ls-remote' in args: print(head + '\trefs/heads/lane/math/op-sample')
        elif 'diff' in args: print('A\tD5/S1/Fixtures/Sample.lean')
        elif 'grep' in args: print('2601.01234')
        elif any(x in args for x in ('fetch', 'status', 'merge-base')): pass
        else: raise RuntimeError('unexpected git call ' + repr(args))
    elif kind == 'make': print('PR_WATCH_RESULT outcome=green')
    elif args[:2] == ['pr', 'edit']:
        (root / 'capture.md').write_text(Path(args[args.index('--body-file') + 1]).read_text())
    elif args[:2] == ['pr', 'view']:
        fields = args[args.index('--json') + 1]
        if fields == 'headRefOid': print(os.environ.get('BRIEF_FIXTURE_PR_HEAD', head))
        elif fields == 'title': print('Synthetic fixture')
        elif fields == 'body': print(os.environ.get('BRIEF_FIXTURE_BODY', data['body']))
        else: print(json.dumps({'body':os.environ.get('BRIEF_FIXTURE_BODY', data['body']), 'headRefOid':head}))
    elif args[:2] == ['run', 'list']:
        print(json.dumps([{'databaseId': 7, 'status':'completed', 'conclusion':'success', 'name':'CI'}]))
    elif args[:2] == ['run', 'view']:
        print(json.dumps({'jobs':[{'name':n,'databaseId':i,'conclusion':os.environ.get('BRIEF_FIXTURE_CI', 'success')} for n,i in [('current',8),('required',9)]]}))
    elif args[:1] == ['api']:
        if os.environ.get('BRIEF_FIXTURE_API_FAIL'): sys.exit(41)
        if os.environ.get('BRIEF_FIXTURE_API_EMPTY'): return
        print('{"executed":true,"diagnostics":[{"AdmissionEffect":1}]}')
    elif args[:2] == ['issue', 'list']:
        if '--json' in args and '--jq' not in args: print('[]')
        elif any('preregistration' in a for a in args):
            print('#12345 Preregister synthetic question\n#12346 Open problem (preregistration): synthetic question\n'
                  '#12347 Open problem (preregistration): refute a synthetic conjecture (arXiv:2501.07269v2) at an explicit small case\n'
                  '#12348 Open problem (preregistration): answer a synthetic basis question of quant-ph/9601020 in every dimension\n'
                  '#12349 Open problem (preregistration): refute a synthetic journal conjecture (J. Synth. 2026, DOI 10.1000/xyz.123) on a forcing')
        else: print('#12345 Preregister synthetic question')
    else: raise RuntimeError('unexpected gh call ' + repr(args))


def prepare(root):
    data = json.loads((DATA / 'input.json').read_text())
    for name in ('scratch/briefs','scratch/lanes','scratch/logs','state','sshx','main','tree','bin'):
        (root / name).mkdir(parents=True,exist_ok=True)
    scratch = root / 'scratch'
    (scratch / 'briefs/goal-artifact.yaml').write_text('GoalArtifact:\n  normalized_goal: Synthetic fixture\n  revisions:\n    - Synthetic current rule\n')
    spec = dict(data['lane'], worktree=str(root / 'tree'))
    (scratch / 'lanes/sample.json').write_text(json.dumps(spec))
    (scratch / 'lanes/sample.target.md').write_text(spec['target_md'])
    (root / 'sshx' / ('a'*24) / 'attempt-1').mkdir(parents=True)
    (root / 'sshx' / ('a'*24) / 'attempt-1/result.json').write_text(json.dumps(data['mirror']))
    (scratch / 'logs/implb-sample-r1.log').write_text('FLIGHT ' + 'a'*24 + '\n')
    (scratch / 'briefs/impl-op-w1-sample.stageB.md').write_text('Before\n<<MIRROR_FIXES>>\nAfter\n')
    (scratch / 'briefs/search-exclusions.md').write_text(json.loads((DATA/'text.json').read_text())['exclusions']['source'])
    (root / 'excluded.md').write_text('Synthetic excluded question.')
    (root / 'standing.json').write_text(json.dumps(data['standing']))
    rework = dict(lane='sample',pr=12345,head=data['head'],worktree=str(root/'tree'),branch=spec['branch'],gid=spec['gid'],module=spec['module'],fixes='Synthetic fix.',standing_rows=data['standing']['rows'],tally_line=data['standing']['tally'],next_layout_line=data['standing']['next'],commit_source='Synthetic source',commit_builder='Synthetic builder',next_round=2)
    (scratch/'lanes/rework-sample.json').write_text(json.dumps(rework))
    (root/'base.md').write_text('**Public surface is deliberate.** Synthetic.\n\n**Imports are minimal** Synthetic.\n\n**Provenance is typed** Synthetic.\n\n')
    (root/'brief.md').write_text('Synthetic brief\n## Steps\nDo the work.\n')
    text_fixture=json.loads((DATA/'text.json').read_text())['rehead']
    (root/'head.md').write_text(text_fixture['head'])
    (root/'rest.md').write_text(text_fixture['rest'])
    (root/'door.md').write_text('make gate BASE="$(git rev-parse origin/dev^{commit})"\n')
    (root/'review.md').write_text('Synthetic review\nrevisions: []\n')
    for command in ('git','gh','make'):
        path=root/'bin'/command
        path.write_text('#!/bin/sh\nexec "'+sys.executable+'" "'+str(Path(__file__).resolve())+'" --stub '+command+' "$@"\n')
        path.chmod(0o755)
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(('OP_', 'BRIEF_FIXTURE_'))
           and key not in ('SSHX_HOME', 'REGEN', 'ORCH_NOTE', 'JF_FLIGHT', 'PYTHONPATH')}
    env.update(PATH=str(root/'bin')+os.pathsep+os.environ['PATH'],OP_SCRATCH=str(scratch),OP_STATE=str(root/'state'),SSHX_HOME=str(root/'sshx'),OP_NAME_PREFIX='fixture-',OP_PROVENANCE_MD='Synthetic provenance.\n',OP_SEARCH_WORKTREE=str(root/'tree'),OP_SEARCH_OUTPUT_DIR=str(root/'search'),OP_CODEX_EXCLUSIONS=str(root/'excluded.md'),BRIEF_FIXTURE_ROOT=str(root),REGEN='0',PYTHONWARNINGS='error::SyntaxWarning')
    return env


def command(tool, root, variant=None):
    scratch=root/'scratch'; stem=tool.stem
    prefix=['/bin/bash' if tool.suffix=='.sh' else sys.executable,str(tool)]
    triplet=['sample','12345','lane/math/op-sample',str(root/'tree'),'none',str(scratch/'lanes/sample.target.md')]
    args={
      'rehead':[str(root/x) for x in ('head.md','rest.md','out.md')]+['1'*40,'2'*40,'fixture'],
      'lane_brief':[str(scratch),str(scratch/'lanes/sample.json')],
      'implb_head':['sample'],
      'continuation_head':['sample','12345','r2','a'*24,str(root/'tree'),str(root/'out.md'),'D5.S1.Fixtures.Owner'],
      'rework_brief':[str(scratch/'lanes/rework-sample.json')],
      'fix_door_base':[str(root/'door.md')],
      'fix_review':[str(root/'review.md')],
      'exclusions_compact':[],
      'gen_stage_briefs':[str(scratch),'sample',str(root/'tree'),'lane/math/op-sample','D5/S1/Fixtures/Sample','quality'],
      'stages':['sample','quality'],
      'fill_mirror_fixes':[str(scratch),'sample',str(root/'sshx'/('a'*24)/'attempt-1/result.json')],
      'stageb_prep':['sample','quality','a'*24],
      'gen_review':triplet+['quality'],
      'review':triplet+['quality'],
      'postb3':['sample','12345'],
      'ci_body_final':['12345','1'*40],
      'standing_append':['12345',str(root/'standing.json')],
      'codex_search':['a','1',variant or 'quick']+(['2601'] if variant!='deep' else []),
      'render-search-brief':['fixture',str(root/'out.md'),'quick','2601'],
      'add_base_blocks':['--base',str(root/'base.md'),str(root/'brief.md')],
    }[stem]
    if stem=='gen_review' and variant=='codex3': args=['--codex3',*triplet,'1']
    if variant == 'defaults':
        if stem == 'gen_stage_briefs': args = ['--lane-spec', 'sample', 'quality']
        elif stem == 'fill_mirror_fixes': args = ['--prepare', 'sample', 'quality', 'a'*24]
    return prefix+args


def collect(root, before):
    output={}
    for path in root.rglob('*'):
        if path.is_file() and path.suffix in ('.md',):
            value=path.read_text()
            if before.get(str(path)) == value: continue
            try:
                assert_dtr_source(value)
            except AssertionError as exc:
                raise AssertionError(str(path.relative_to(root)) + ': ' + str(exc)) from exc
            for spelling in sorted({str(root),str(root.resolve())},key=len,reverse=True):
                value=value.replace(spelling,'<FIXTURE>')
            value=value.replace(str(TOOLS.parents[3]),'<REPOSITORY>')
            output[str(path.relative_to(root))]=hashlib.sha256(value.encode()).hexdigest()
    return output


def case(tool, variant=None):
    with tempfile.TemporaryDirectory(prefix='brief fixtures __tokens__ ') as tmp:
        root=Path(tmp)/'workspace __name__ __BRANCH__ with spaces'
        env=prepare(root)
        assert not any((root/'scratch/briefs'/name).exists()
                       for name in json.loads((DATA/'input.json').read_text())['blocks'])
        if variant == 'defaults':
            env.pop('REGEN')
            env.pop('OP_PROVENANCE_MD')
        if tool.stem == 'gen_stage_briefs' and variant != 'defaults':
            result=subprocess.run([sys.executable,str(HERE/'lane_brief.py'),str(root/'scratch'),str(root/'scratch/lanes/sample.json')],env=env,capture_output=True,text=True)
            assert result.returncode==0,result.stderr
        before={str(p):p.read_text() for p in root.rglob('*.md')}
        result=subprocess.run(command(tool,root,variant),cwd=root,env=env,capture_output=True,text=True)
        assert result.returncode==0,(tool,result.returncode,result.stdout[-1200:],result.stderr[-3000:])
        assert 'SyntaxWarning' not in result.stderr,(tool,result.stderr)
        if tool.name == 'render-search-brief.sh':
            listed = (root / 'out.md').read_text()
            assert '#12346 Open problem (preregistration): synthetic question' in listed, 'preregistration-titled issue missing'
            assert listed.count('#12345 Preregister synthetic question') == 1, 'issue matched by both queries listed twice'
            oracle = subprocess.run(['/bin/bash', str(tool), 'nyxid-oracle:fixture', str(root / 'oracle.md'), 'quick', '2601'],
                                    cwd=root, env=env, capture_output=True, text=True)
            assert oracle.returncode == 0, (oracle.returncode, oracle.stderr)
            compact = (root / 'oracle.md').read_text()
            assert '#12347 2501.07269\n' in compact, 'oracle brief does not name the issue by its arXiv identifier'
            assert '#12348 quant-ph/9601020' in compact, 'oracle brief drops a legacy arXiv identifier'
            assert '#12349 10.1000/xyz.123\n' in compact, 'oracle brief drops a DOI'
            assert 'refute a synthetic conjecture' not in compact, 'oracle brief keeps a full title that names an identifier'
            assert '#12345 Preregister synthetic question' in compact, 'oracle brief drops an issue without an identifier'
        if tool.stem in ('implb_head', 'rework_brief', 'gen_stage_briefs', 'stages'):
            path = ('implb-sample-r1.head.md' if tool.stem == 'implb_head' else
                    'rework-sample.md' if tool.stem == 'rework_brief' else
                    'impl-op-w1-sample.stageB.md')
            text = (root / 'scratch/briefs' / path).read_text()
            assert_scoped_builds(text, binding=True)
            assert_dtr_source(text)
            if tool.stem in ('gen_stage_briefs', 'stages'):
                stage_a = (root / 'scratch/briefs/impl-op-w1-sample.stageA.md').read_text()
                assert_scoped_builds(stage_a)
            if tool.stem == 'implb_head':
                from common import BUILD_SCOPE
                assert BUILD_SCOPE + '\n\n- **SDK host.**' in text
                assert REGISTRATION_CI_READING in text
                for source in ('the scoped report', '`make lean-report-scoped LEAN_TARGETS="D5.Sample"`',
                               '`python3 report.py`', '`custom-report --target D5.Sample`'):
                    for unsafe in (f'Read the `DTR-*` finding from {source}.',
                                   f'Write `declared_validated` from {source}.'):
                        assert_unsafe_dtr_source(text.replace(REGISTRATION_CI_READING, unsafe))
            if tool.stem == 'rework_brief':
                audit = (TOOLS / 'templates/blocks/escape-audit-block.md').read_text()
                assert text.count(audit) == 1, 'missing or repeated escape-audit block'
                assert '"pending CI reading"; never write `declared_validated` without the CI reading.' in text
                assert 'required CI `current` job: run `gh run view <run-id> --log --job <current-job-id>`' in text
        if variant == 'defaults':
            print('BRIEF_DEFAULTS tool='+tool.name+' exit='+str(result.returncode))
        outputs=collect(root,before)
        assert outputs,(tool,'no output')
        return outputs


def run(tool):
    tool=tool.resolve()
    if tool.stem in ('common', 'implb_head', 'lane_brief', 'rework_brief', 'gen_stage_briefs', 'stages'):
        build_scope_regressions()
    if tool.stem == 'implb_head':
        head_generality_regressions(tool)
    if tool.stem == 'common':
        from common import Context, BriefError, entry, name
        for error in (AssertionError(), ValueError(' '), KeyError(), IndexError(), TypeError(), AttributeError(), ValueError('invalid field')):
            def invalid(args):
                raise error
            diagnostic=io.StringIO()
            with contextlib.redirect_stderr(diagnostic):
                code=entry(invalid, argv=['brief-error'])
            assert code==13,(type(error).__name__,code)
            message=diagnostic.getvalue()
            assert message.startswith(f'BRIEF_INVALID_INPUT {type(error).__name__}: '),message
            assert (str(error).strip() or ' in invalid:') in message,message
        saved=dict(os.environ)
        try:
            with tempfile.TemporaryDirectory(prefix='context fixture __tokens__ ') as tmp:
                root=Path(tmp);os.environ.update(prepare(root))
                for number in (2,10):
                    path=root/'sshx'/('b'*24)/f'attempt-{number}'
                    path.mkdir(parents=True);(path/'result.json').write_text('{}')
                ctx=Context()
                assert ctx.result('b'*24).parent.name=='attempt-10'
                invalid=root/'sshx'/('b'*24)/'attempt-invalid/result.json'
                invalid.parent.mkdir(parents=True)
                invalid.write_text('{}')
                (root/'sshx'/('b'*24)/'attempt-99/result.json').mkdir(parents=True)
                assert ctx.result('b'*24).parent.name=='attempt-10'
                for flight, code in [('c'*24, 11), ('../escape', 13), ('A'*24, 13), ('a'*23, 13)]:
                    try: ctx.result(flight)
                    except BriefError as exc: assert exc.code==code
                    else: raise AssertionError('invalid or missing flight accepted')
                assert ctx.main==root/'main'
                for value in ('../escape','bad name',''):
                    try: name(value)
                    except BriefError as exc: assert exc.code==13
                    else: raise AssertionError('invalid name accepted')
                os.environ.pop('OP_SCRATCH')
                try: Context()
                except BriefError as exc: assert exc.code==11
                else: raise AssertionError('missing scratch accepted')
        finally:
            os.environ.clear();os.environ.update(saved)
        print('BRIEF_SELFTEST tool='+tool.name+' failed=0')
        return 0
    if tool.stem == 'purge_stale_fib':
        import zipfile
        with tempfile.TemporaryDirectory(prefix='cache fixture __tokens__ ') as tmp:
            directory=Path(tmp)/'.lake/build/lean-inspector/modules'
            directory.mkdir(parents=True)
            fixture=json.loads((DATA/'cache.json').read_text())
            for name, payload in fixture['archives'].items():
                with zipfile.ZipFile(directory/name,'w') as archive:
                    archive.writestr('raw-lean-report.json',json.dumps(payload))
            result=subprocess.run([sys.executable,str(tool),tmp,'--delete'],capture_output=True,text=True)
            assert result.returncode==0,result.stderr
            assert result.stdout==fixture['expected']
            assert sorted(p.name for p in directory.iterdir())==['current.zip']
        print('BRIEF_SELFTEST tool='+tool.name+' failed=0')
        return 0
    if tool.stem in ('gen_stage_briefs', 'gen_review'):
        import importlib.util
        from common import BriefError
        spec=importlib.util.spec_from_file_location('render_fixture',tool)
        module=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        if tool.stem == 'gen_stage_briefs':
            def render(template):
                return module.render_mirror(template, 'sample', 'tree __BRANCH__ with __name__',
                                            'lane/test', 'D5/Fixture')
            assert render('__LANE__ __WORKTREE__ __BRANCH__ __MODULE__ __init__') == \
                'sample tree __BRANCH__ with __name__ lane/test D5/Fixture __init__'
        else:
            values={'__ROLE__': 'architecture __TITLE__',
                    '__TITLE__': r'literal __UNKNOWN__ __ROLE__ __init__ \1',
                    '__WORKTREE__': 'tree __BRANCH__ with __name__'}
            def render(template):
                return module.render_review(template, values)
            assert render('__ROLE__|__TITLE__|__WORKTREE__|__init__') == \
                values['__ROLE__']+'|'+values['__TITLE__']+'|'+values['__WORKTREE__']+'|__init__'
        try:
            render('__UNKNOWN_2__')
        except BriefError as exc:
            assert exc.code==13 and '__UNKNOWN_2__' in exc.message,(exc.code,exc.message)
        else:
            raise AssertionError('unknown template token accepted')
    expected=json.loads((DATA/'golden.json').read_text())
    variants = (('codex3', None) if tool.stem == 'gen_review' else
                ('deep', 'quick') if tool.stem == 'codex_search' else
                (None, 'defaults') if tool.stem in ('gen_stage_briefs', 'fill_mirror_fixes', 'rework_brief') else
                (None,))
    for variant in variants:
        key=tool.name+(':'+variant if variant else '')
        got=case(tool,variant)
        assert got==expected[key],(key,got,expected[key])
    with tempfile.TemporaryDirectory(prefix='brief failures __tokens__ ') as tmp:
        root=Path(tmp);env=prepare(root)
        result=subprocess.run(['/bin/bash' if tool.suffix=='.sh' else sys.executable,str(tool),'--invalid-option'],cwd=root,env=env,capture_output=True,text=True)
        assert result.returncode in (10,11,13),(tool,result.returncode,result.stderr)
        def rejected(code):
            result=subprocess.run(command(tool,root),cwd=root,env=env,capture_output=True,text=True)
            assert result.returncode==code,(tool,result.returncode,result.stderr)
            assert not (root/'capture.md').exists(), 'rejected input edited the PR'
        if tool.stem=='add_base_blocks':
            result=subprocess.run([sys.executable,str(tool),'--base',str(root/'base.md')],cwd=root,env=env,capture_output=True,text=True)
            assert result.returncode==10,(result.returncode,result.stderr)
        elif tool.stem=='rehead':
            (root/'rest.md').unlink()
            original=(root/'head.md').read_text()
            rejected(11)
            assert (root/'head.md').read_text()==original
        elif tool.stem=='implb_head':
            import importlib.util
            import shlex
            spec=importlib.util.spec_from_file_location('implb_fixture',tool)
            module=importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            path=root/'repository with spaces/briefgen/purge_stale_fib.py'
            assert shlex.split(module.purge_command(path))[:2]==['python3',str(path)]
            (root/'scratch/lanes/sample.json').unlink()
            rejected(11)
        elif tool.stem=='rework_brief':
            for i in (1,2): (root/f'scratch/lanes/rework-sample-r{i}.json').write_text('{}')
            rejected(13)
            assert not (root/'scratch/briefs/rework-sample.md').exists()
        elif tool.stem=='standing_append':
            spec=json.loads((root/'standing.json').read_text())
            spec['tally']+=' The seats asked for a change.'
            (root/'standing.json').write_text(json.dumps(spec))
            rejected(13)
            spec=json.loads((DATA/'input.json').read_text())['standing']
            (root/'standing.json').write_text(json.dumps(spec))
            env['BRIEF_FIXTURE_BODY']='Round 1 review is pending.\n'+json.loads((DATA/'input.json').read_text())['body']
            rejected(13)
        elif tool.stem=='ci_body_final':
            env['BRIEF_FIXTURE_CI']='failure'
            rejected(1)
            env.pop('BRIEF_FIXTURE_CI')
            env['BRIEF_FIXTURE_API_FAIL']='1'
            rejected(16)
            env.pop('BRIEF_FIXTURE_API_FAIL')
            env['BRIEF_FIXTURE_API_EMPTY']='1'
            rejected(13)
            env.pop('BRIEF_FIXTURE_API_EMPTY')
            env['BRIEF_FIXTURE_PR_HEAD']='2'*40
            rejected(13)
        elif tool.stem in ('gen_stage_briefs','fill_mirror_fixes','lane_brief','implb_head'):
            if tool.stem in ('lane_brief','implb_head'):
                (root/'scratch/lanes/sample.json').unlink()
            elif tool.stem=='gen_stage_briefs':
                (root/'scratch/briefs/impl-op-w1-sample.md').write_text('No anchors.\n')
            else:
                (root/'scratch/briefs/impl-op-w1-sample.stageB.md').write_text('No placeholder.\n')
            rejected(11 if tool.stem in ('lane_brief','implb_head') else 13)
    print('BRIEF_SELFTEST tool='+tool.name+' failed=0')
    return 0


if __name__=='__main__':
    if sys.argv[1:2]==['--stub']:
        stub(sys.argv[2],sys.argv[3:])
    elif sys.argv[1:]==['--selftest']:
        for name in sorted({key.split(':')[0] for key in json.loads((DATA/'golden.json').read_text())} | {'common.py','purge_stale_fib.py'}):
            tool=HERE/name
            run(tool if tool.exists() else TOOLS/name)
    else:
        sys.exit(run(Path(sys.argv[1])))
