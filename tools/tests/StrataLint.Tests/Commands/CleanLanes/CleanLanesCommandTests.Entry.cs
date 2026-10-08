using System.Text;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void CanonicalMakeEntrySamplesRealActivityAndRetainsUnknownThenReclaimsIdleLockedTree()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var cli = Path.Combine(root, "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll");
        var result = TestProcessRunner.Run("python3", ["-c", EntryFixture, root, cli], root,
            TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    private const string EntryFixture = """
        import json, os, pathlib, shlex, shutil, subprocess, sys, tempfile
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
            def clean(force=False):
                run = subprocess.run(['make', '--no-print-directory', '-C', str(repo/'tools'),
                                      'clean-lanes', 'BASE=dev', 'FORCE='+str(int(force))],
                                     cwd=repo, env=env, capture_output=True, text=True)
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
                    assert row['reason'] == 'locked_activity', row
                    assert lane.exists() and reader.poll() is None
                print('canonical entry: active reader retained in preview and force')
            finally:
                reader.communicate('')
            sampler = scripts/'host-cleanup.py'
            saved = sampler.read_bytes(); sampler.unlink()
            for force in (False, True):
                row = clean(force)
                assert row['reason'] == 'locked_activity_unknown', row
                assert lane.exists()
            sampler.write_bytes(saved)
            row = clean()
            assert row['action'] == 'would_remove' and row['reason'] == 'stale_initialization_lock', row
            assert lane.exists()
            row = clean(True)
            assert row['action'] == 'removed' and not lane.exists(), row
            print('canonical entry: unknown retained; positively idle clean lock reclaimed')
        """;
}
