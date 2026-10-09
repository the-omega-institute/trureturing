using System.Text;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void CanonicalMakeEntryRetainsRealHostActivityAndVerifiesControlledCapabilityStates()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var cli = Path.Combine(root, "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll");
        var result = TestProcessRunner.Run("python3", ["-c", EntryFixture, root, cli], root,
            TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    private const string EntryFixture = """
        import json, os, pathlib, shlex, shutil, signal, subprocess, sys, tempfile
        source, cli = map(pathlib.Path, sys.argv[1:])
        real_dotnet = shutil.which('dotnet')
        with tempfile.TemporaryDirectory(prefix='clean-lanes-entry-') as store:
            store = pathlib.Path(store).resolve()
            repo, lane, bin_dir = store/'repository', store/'lane', store/'bin'
            repo.mkdir(); bin_dir.mkdir()
            env = dict(os.environ, GIT_AUTHOR_DATE='1700000000 +0000', GIT_COMMITTER_DATE='1700000000 +0000')
            def git(*args, cwd=repo):
                return subprocess.run(['git', *args], cwd=cwd, env=env, check=True,
                                      capture_output=True, text=True).stdout.strip()
            git('init', '--initial-branch=dev')
            git('config', 'user.name', 'Entry Test'); git('config', 'user.email', 'test@example.invalid')
            (repo/'README.md').write_text('rebuildable checkout\n')
            git('add', '.'); git('-c', 'maintenance.auto=false', 'commit', '-m', 'baseline')
            tip = git('rev-parse', 'HEAD')
            git('worktree', 'add', '--detach', str(lane), tip)
            stream = ''.join('commit refs/heads/dev\ncommitter Test <test@example.invalid> 1700000000 +0000\ndata 1\nx\n'
                             + ('from '+tip+'\n' if i == 0 else '') + '\n' for i in range(300))
            subprocess.run(['git', 'fast-import', '--quiet', '--force'], cwd=repo, env=env,
                           input=stream, text=True, capture_output=True, check=True)
            git('init', '--bare', str(store/'remote.git'))
            git('remote', 'add', 'origin', str(store/'remote.git'))
            git('push', 'origin', 'dev')
            lock = 'worktree-init:'+'a'*32
            git('worktree', 'lock', '--reason', lock, str(lane))
            scripts = repo/'tools/scripts'; scripts.mkdir(parents=True)
            for name in ('clean-lanes.sh', 'host-cleanup.py'):
                shutil.copy(source/'tools/scripts'/name, scripts/name)
            shutil.copy(source/'tools/Makefile', repo/'tools/Makefile')
            shim = bin_dir/'dotnet'
            # Keep the real locked-worktree consumer while excluding unrelated global temp sweeps.
            shim.write_text('#!/bin/sh\nwhile [ "$1" != -- ]; do shift; done\nshift\nexec '
                            + shlex.quote(real_dotnet)+' '+shlex.quote(str(cli))+' "$@" --lanes-only\n')
            shim.chmod(0o700)
            env['PATH'] = str(bin_dir)+os.pathsep+env['PATH']
            env['CODEX_HOME'] = str(store/'codex')
            def command(force=False):
                return ['make', '--no-print-directory', '-C', str(repo/'tools'),
                                      'clean-lanes', 'BASE=dev', 'FORCE='+str(int(force))]
            def clean(force=False):
                run = subprocess.run(command(force), cwd=repo, env=env, capture_output=True, text=True)
                assert run.returncode == 0, (run.returncode, run.stdout, run.stderr)
                rows = [json.loads(line) for line in run.stdout.splitlines() if line.startswith('{')]
                return next(row for row in rows if row.get('path') == str(lane))
            reader = subprocess.Popen([sys.executable, '-c',
                                       'import sys; print("ready",flush=True); sys.stdin.read()'],
                                      cwd=lane, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
            try:
                assert reader.stdout.readline().strip() == 'ready'
                for force in (False, True):
                    row = clean(force)
                    assert row['reason'] in ('locked_activity', 'locked_activity_unknown'), row
                    assert row['action'] == 'skipped', row
                    assert lane.exists() and reader.poll() is None
                sample = subprocess.run([sys.executable, str(scripts/'host-cleanup.py'), 'active-paths'],
                                        cwd=repo, env=env, capture_output=True, text=True)
                if sample.returncode == 0:
                    assert str(lane) in json.loads(sample.stdout), sample.stdout
                print(json.dumps(dict(real_sampler_exit=sample.returncode,
                                      real_sampler_stderr=sample.stderr.strip(), retained=True)))
            finally:
                reader.communicate('')
            sampler = scripts/'host-cleanup.py'
            sampler.rename(scripts/'fixture-host-cleanup.py')
            # Supply complete or partial observations to the existing sampler command;
            # make, Bash argument forwarding, JSON decoding and cleanup stay real.
            sampler.write_text("import importlib.util, json, os, pathlib, subprocess, sys\n"
                "from unittest.mock import patch\n"
                "root=pathlib.Path(__file__).parent\n"
                "spec=importlib.util.spec_from_file_location('fixture_host',root/'fixture-host-cleanup.py')\n"
                "module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)\n"
                "def activity(codex, *scopes):\n"
                "    state=json.loads((root/'activity.json').read_text())\n"
                "    observed={pathlib.Path(p) for p in state['paths']}\n"
                "    if not state['complete']: raise OSError('incomplete controlled activity evidence')\n"
                "    return observed\n"
                "state=json.loads((root/'activity.json').read_text())\n"
                "if state.get('kind') == 'linux':\n"
                "    module.sys.platform='linux'\n"
                "    process=root/'proc'/str(state['pid']); descriptors=process/'fd'\n"
                "    iterdir, readlink=pathlib.Path.iterdir, os.readlink\n"
                "    def inventory(path):\n"
                "        if path == pathlib.Path('/proc'): return iter([process])\n"
                "        if path == descriptors:\n"
                "            if state['boundary']=='fd': raise FileNotFoundError('descriptor directory unavailable')\n"
                "            return iter([descriptors/str(i) for i in range(3)])\n"
                "        return iterdir(path)\n"
                "    def link(path):\n"
                "        if ((state['boundary']=='descriptor' and path==descriptors/str(state['position']))\n"
                "            or (state['boundary']=='cwd' and path==process/'cwd')):\n"
                "            error=FileNotFoundError if state['error']=='missing' else ProcessLookupError\n"
                "            raise error('observation disappeared')\n"
                "        return readlink(path)\n"
                "    ps=subprocess.CompletedProcess([],0,str(os.getuid())+' generic-reader\\n','')\n"
                "    patch.object(pathlib.Path,'iterdir',inventory).start()\n"
                "    patch.object(module.os,'readlink',link).start()\n"
                "    patch.object(module.subprocess,'run',return_value=ps).start()\n"
                "else: module.active_paths=activity\n"
                "sys.exit(module.main())\n")
            def activity(paths=(), complete=True):
                (scripts/'activity.json').write_text(json.dumps(dict(paths=list(map(str,paths)),complete=complete)))

            # Keep a native checkout handle open with cwd/argv outside the lane.
            # Only /proc and ps observations are simulated; the sampler, make,
            # Bash, CLI, native Git consumer and actual reader remain real.
            reader = subprocess.Popen([sys.executable, '-c',
                'import os,sys; handle=open(os.environ["ENTRY_READER_FILE"]); '
                'print("ready",flush=True); sys.stdin.read()'], cwd=repo,
                env=dict(env, ENTRY_READER_FILE=str(lane/'README.md')),
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
            try:
                assert reader.stdout.readline().strip() == 'ready'
                process = scripts/'proc'/str(reader.pid)
                (process/'fd').mkdir(parents=True)
                (process/'cwd').symlink_to(repo)
                for i in range(3):
                    (process/'fd'/str(i)).symlink_to(lane/'README.md' if i==2 else repo/'README.md')
                for boundary, position, error in [('descriptor',p,e) for p in (0,1)
                                                    for e in ('missing','exited')] + [('cwd',0,'missing'),('fd',0,'missing')]:
                    (scripts/'activity.json').write_text(json.dumps(dict(kind='linux',pid=reader.pid,
                        boundary=boundary,position=position,error=error)))
                    sample = subprocess.run([sys.executable,str(sampler),'active-paths'],
                        cwd=repo,env=env,capture_output=True,text=True)
                    expected = 'locked_activity' if boundary=='descriptor' else 'locked_activity_unknown'
                    observations = [(force,clean(force)) for force in (False,True)]
                    print(json.dumps(dict(linux_observations='simulated',boundary=boundary,
                        position=position,error=error,sampler_exit=sample.returncode,
                        target_observed=sample.returncode==0 and str(lane/'README.md') in json.loads(sample.stdout),
                        consumer_actions=[row['action'] for _,row in observations],
                        consumer_reasons=[row['reason'] for _,row in observations],
                        worktree_exists=lane.exists(),native_reader_alive=reader.poll() is None)),flush=True)
                    if boundary=='descriptor':
                        assert sample.returncode==0 and str(lane/'README.md') in json.loads(sample.stdout), sample
                    else:
                        assert sample.returncode!=0 and not sample.stdout, sample
                    for force,row in observations:
                        assert row['action']=='skipped' and row['reason']==expected, row
                        assert lane.exists() and reader.poll() is None
                        assert 'locked '+lock in git('worktree','list','--porcelain')
                    print(json.dumps(dict(linux_observations='simulated',boundary=boundary,
                        position=position,error=error,sampler_exit=sample.returncode,
                        consumer_reason=expected,preview_retained=True,force_retained=True,
                        native_reader_alive=reader.poll() is None)))
            finally:
                reader.communicate('')
            activity([lane])
            for force in (False, True):
                row = clean(force)
                assert row['reason'] == 'locked_activity' and row['action'] == 'skipped', row
                assert lane.exists()
            activity([repo], complete=False)
            for force in (False, True):
                row = clean(force)
                assert row['reason'] == 'locked_activity_unknown' and row['action'] == 'skipped', row
                assert lane.exists()
            saved = sampler.read_bytes(); sampler.unlink()
            for force in (False, True):
                row = clean(force)
                assert row['reason'] == 'locked_activity_unknown', row
                assert lane.exists()
            sampler.write_bytes(saved)
            activity()
            row = clean()
            assert row['action'] == 'would_remove' and row['reason'] == 'stale_initialization_lock', row
            assert lane.exists()

            # Pause at the native removal boundary, without mutating the lock. A
            # second invocation and interruption must retain the locked policy.
            real_git = shutil.which('git')
            ready, release = store/'ready', store/'release'
            os.mkfifo(ready); os.mkfifo(release)
            git_shim = bin_dir/'git'
            git_shim.write_text('#!'+sys.executable+'\nimport os, pathlib, sys\n'
                "if os.environ.get('ENTRY_PAUSE') and 'worktree' in sys.argv and 'remove' in sys.argv:\n"
                "    with open(os.environ['ENTRY_READY'],'w') as p: p.write('ready\\n')\n"
                "    with open(os.environ['ENTRY_RELEASE']) as p: p.read()\n"
                + 'os.execv('+repr(real_git)+', ['+repr(real_git)+']+sys.argv[1:])\n')
            git_shim.chmod(0o700)
            paused_env = dict(env, ENTRY_PAUSE='1', ENTRY_READY=str(ready), ENTRY_RELEASE=str(release))
            paused = subprocess.Popen(command(True), cwd=repo, env=paused_env, start_new_session=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                with ready.open() as pipe: assert pipe.read().strip() == 'ready'
                assert 'locked '+lock in git('worktree','list','--porcelain')
                (lane/'resumed.txt').write_text('unsaved resumed session\n')
                activity([lane])
                row = clean(True)
                assert row['action'] == 'skipped' and row['reason'] == 'locked_activity', row
                activity([repo], complete=False)
                row = clean(True)
                assert row['reason'] == 'locked_activity_unknown', row
                activity()
                row = clean(True)
                assert row['reason'] == 'locked_content', row
            finally:
                os.killpg(paused.pid, signal.SIGTERM)
                paused.communicate()
            assert paused.returncode != 0
            assert 'locked '+lock in git('worktree','list','--porcelain')
            row = clean(True)
            assert row['reason'] == 'locked_content' and (lane/'resumed.txt').exists(), row
            (lane/'resumed.txt').unlink()
            row = clean(True)
            assert row['action'] == 'removed' and not lane.exists(), row
            print('canonical entry: controlled active/partial/missing/idle; concurrent invocation and interruption retained')
        """;
}
