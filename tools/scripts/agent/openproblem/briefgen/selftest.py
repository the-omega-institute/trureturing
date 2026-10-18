#!/usr/bin/env python3
"""Hermetic golden cases and rejection cases for each brief entry point."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
DATA = HERE / 'testdata'


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
        print('[]' if '--json' in args and '--jq' not in args else '#12345 Preregister synthetic question')
    else: raise RuntimeError('unexpected gh call ' + repr(args))


def prepare(root):
    data = json.loads((DATA / 'input.json').read_text())
    for name in ('scratch/briefs','scratch/lanes','scratch/logs','state','sshx','main','tree','bin'):
        (root / name).mkdir(parents=True,exist_ok=True)
    scratch = root / 'scratch'
    for name in data['blocks']:
        (scratch / 'briefs' / name).write_text('\n## Synthetic block ' + name + '\nSynthetic rule.\n')
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
    env=dict(os.environ,PATH=str(root/'bin')+os.pathsep+os.environ['PATH'],OP_SCRATCH=str(scratch),OP_STATE=str(root/'state'),SSHX_HOME=str(root/'sshx'),OP_NAME_PREFIX='fixture-',OP_PROVENANCE_MD='Synthetic provenance.\n',OP_SEARCH_WORKTREE=str(root/'tree'),OP_SEARCH_OUTPUT_DIR=str(root/'search'),OP_CODEX_EXCLUSIONS=str(root/'excluded.md'),BRIEF_FIXTURE_ROOT=str(root),REGEN='0')
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
    return prefix+args


def collect(root, before):
    output={}
    for path in root.rglob('*'):
        if path.is_file() and path.suffix in ('.md',):
            value=path.read_text()
            if before.get(str(path)) == value: continue
            for spelling in sorted({str(root),str(root.resolve())},key=len,reverse=True):
                value=value.replace(spelling,'<FIXTURE>')
            value=value.replace(str(TOOLS.parents[3]),'<REPOSITORY>')
            output[str(path.relative_to(root))]=hashlib.sha256(value.encode()).hexdigest()
    return output


def case(tool, variant=None):
    with tempfile.TemporaryDirectory(prefix='brief fixtures ') as tmp:
        root=Path(tmp)
        env=prepare(root)
        if tool.stem in ('gen_stage_briefs','stages'):
            result=subprocess.run([sys.executable,str(HERE/'lane_brief.py'),str(root/'scratch'),str(root/'scratch/lanes/sample.json')],env=env,capture_output=True,text=True)
            assert result.returncode==0,result.stderr
        before={str(p):p.read_text() for p in root.rglob('*.md')}
        result=subprocess.run(command(tool,root,variant),cwd=root,env=env,capture_output=True,text=True)
        assert result.returncode==0,(tool,result.returncode,result.stdout[-1200:],result.stderr[-3000:])
        outputs=collect(root,before)
        assert outputs,(tool,'no output')
        return outputs


def run(tool):
    tool=tool.resolve()
    if tool.stem == 'common':
        from common import Context, BriefError, name
        saved=dict(os.environ)
        try:
            with tempfile.TemporaryDirectory(prefix='context fixture ') as tmp:
                root=Path(tmp);os.environ.update(prepare(root))
                for number in (2,10):
                    path=root/'sshx'/('b'*24)/f'attempt-{number}'
                    path.mkdir(parents=True);(path/'result.json').write_text('{}')
                ctx=Context()
                assert ctx.result('b'*24).parent.name=='attempt-10'
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
        with tempfile.TemporaryDirectory(prefix='cache fixture ') as tmp:
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
    expected=json.loads((DATA/'golden.json').read_text())
    variants=('codex3',None) if tool.stem=='gen_review' else ('deep','quick') if tool.stem=='codex_search' else (None,)
    for variant in variants:
        key=tool.name+(':'+variant if variant else '')
        got=case(tool,variant)
        assert got==expected[key],(key,got,expected[key])
    with tempfile.TemporaryDirectory(prefix='brief failures ') as tmp:
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
