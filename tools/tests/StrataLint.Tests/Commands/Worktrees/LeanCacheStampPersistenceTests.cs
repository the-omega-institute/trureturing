using System.Globalization;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheStampPersistenceTests
{
    [Theory]
    [InlineData("complete", true, 0)]
    [InlineData("complete", true, 23)]
    [InlineData("dependency-only", true, 0)]
    [InlineData("project-corrupt", true, 0)]
    [InlineData("dependency-corrupt", false, 0)]
    [InlineData("dependency-matched-key-missing", false, 0)]
    [InlineData("dependency-matched-key-missing", false, 23)]
    [InlineData("project-matched-key-missing", true, 0)]
    [InlineData("transfer-miss", false, 0)]
    [InlineData("publication-failed", false, 0)]
    [InlineData("project-only", false, 0)]
    [InlineData("foreign-mathlib", false, 0)]
    [InlineData("foreign-platform", false, 0)]
    [InlineData("existing-mismatch", true, 0)]
    [InlineData("existing-platform", true, 0)]
    [InlineData("existing-corrupt", true, 0)]
    [InlineData("existing-mismatch-miss", false, 0)]
    [InlineData("existing-platform-miss", false, 0)]
    [InlineData("stamp-publication-failed", false, 0)]
    public void ActionsRestoreHandsDependencyIdentityToRealWriter(
        string scenario, bool dependencyAccepted, int producerExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PrivateReaderFixture();
        var repository = TestRepositoryLayout.FindRoot();
        var restore = TestProcessRunner.Run("python3", ["-B", "-c", """
            import json, os, pathlib, shutil, subprocess, sys
            sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / 'tools/scripts/worktree'))
            import lean_actions as actions
            root, scenario = pathlib.Path(sys.argv[2]), sys.argv[3]
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            os.environ.update(GITHUB_RUN_ID='17', GITHUB_RUN_ATTEMPT='2',
                GITHUB_EVENT_NAME='push', GITHUB_REF='refs/heads/dev',
                STRATALINT_CHECK_SUCCEEDED='true', STRATALINT_CACHE_WRITES='true',
                GITHUB_OUTPUT=str(root / 'outputs'), GITHUB_ENV=str(root / 'environment'))
            package = root / '.lake/packages/mathlib'
            for name, contents in [('Mathlib/Fixture.lean', 'def fixture := 0'),
                    ('.lake/build/lib/lean/Mathlib/Fixture.olean', 'cached module'),
                    ('.git/config', 'retained dependency identity')]:
                path = package / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents)
            keys = actions.actions_keys(root)
            # Actions extracts native build directories before this adapter runs.
            # This fixture exercises restoration and the real C# writer handoff,
            # without invoking the independent optional snapshot-save policy.
            stamp = root / '.lake/.stratalint-lean-cache-stamp.json'
            stamp.unlink()
            matched = {layer: keys[layer]['key'] for layer in actions.LAYERS}
            outcomes = {layer: 'success' for layer in actions.LAYERS}
            if scenario == 'dependency-only':
                matched['project'] = ''
                outcomes['project'] = 'skipped'
                shutil.rmtree(root / keys['project']['path'])
            if scenario in ('transfer-miss', 'project-only') or scenario.endswith('-miss'):
                matched['dependency'] = ''
                outcomes['dependency'] = 'skipped'
                shutil.rmtree(root / keys['dependency']['path'])
            if scenario.endswith('-corrupt') and not scenario.startswith('existing-'):
                layer = scenario.removesuffix('-corrupt')
                damaged = (package / '.lake/build/lib/lean/Mathlib/Fixture.olean' if layer == 'dependency'
                    else root / '.lake/build/lib/lean/Fixture.olean')
                damaged.write_text('partial damaged extraction')
                # Actions reports archive corruption; the adapter must discard
                # its incomplete directory while retaining the other layer.
                outcomes[layer] = 'failure'
            if scenario.endswith('-matched-key-missing'):
                matched[scenario.removesuffix('-matched-key-missing')] = ''
            if scenario == 'publication-failed': outcomes['dependency'] = 'failure'
            if scenario == 'foreign-mathlib':
                matched['dependency'] = matched['dependency'].replace('a' * 40, 'b' * 40)
            if scenario == 'foreign-platform':
                matched['dependency'] = matched['dependency'].replace(keys['arch'], 'foreign-arch')
            if scenario.startswith('existing-') or scenario == 'stamp-publication-failed':
                stamp.parent.mkdir(parents=True, exist_ok=True)
                if scenario.startswith(('existing-mismatch', 'existing-platform')):
                    stamp.write_text(json.dumps(dict(schema='stratalint-lean-cache-v2',
                        mathlib_revision='b' * 40 if scenario.startswith('existing-mismatch') else 'a' * 40,
                        os=keys['os'], arch='foreign' if scenario.startswith('existing-platform') else keys['arch'])))
                elif scenario == 'existing-corrupt': stamp.write_text('corrupt')
                else: stamp.mkdir()
            actions.restore(root, keys, matched, outcomes=outcomes)
            """, repository, fixture.Reader, scenario], repository,
            TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(restore.ExitCode == 0,
            Encoding.UTF8.GetString(restore.StandardOutput) + Encoding.UTF8.GetString(restore.StandardError));
        var lake = Path.Combine(fixture.Reader, ".lake");
        var restoreReceipts = Encoding.UTF8.GetString(restore.StandardOutput).Split('\n')
            .Where(line => line.StartsWith("LEAN_ACTIONS_CACHE ", StringComparison.Ordinal))
            .Select(line =>
            {
                using var receipt = JsonDocument.Parse(line["LEAN_ACTIONS_CACHE ".Length..]);
                return receipt.RootElement.Clone();
            }).ToDictionary(receipt => receipt.GetProperty("layer").GetString()!, StringComparer.Ordinal);
        var projectAccepted = scenario is not ("dependency-only" or "project-corrupt" or "project-matched-key-missing");
        Assert.Equal(dependencyAccepted ? "restored" : "miss", restoreReceipts["dependency"].GetProperty("status").GetString());
        Assert.Equal(projectAccepted ? "restored" : "miss", restoreReceipts["project"].GetProperty("status").GetString());
        Assert.Equal(dependencyAccepted, Directory.Exists(Path.Combine(lake, "packages")));
        Assert.Equal(projectAccepted, Directory.Exists(Path.Combine(lake, "build")));
        if (dependencyAccepted)
        {
            Assert.Equal("cached module", File.ReadAllText(Path.Combine(lake, "packages/mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean")));
            Assert.Equal("retained dependency identity", File.ReadAllText(Path.Combine(lake, "packages/mathlib/.git/config")));
        }
        if (projectAccepted)
            Assert.Equal("fixture output\n", File.ReadAllText(Path.Combine(lake, "build/lib/lean/Fixture.olean")));
        var beforeEnsure = LeanCacheStamp.Inspect(lake,
            LeanPinSet.TryReadWorktree(fixture.Reader, out _)!);
        File.WriteAllText(fixture.Lake, """
            #!/bin/sh
            set -eu
            printf '%s\n' "$*" >> calls
            if [ "$1" = exe ]; then
              mkdir -p .lake/packages/mathlib/Mathlib .lake/packages/mathlib/.lake/build/lib/lean/Mathlib
              printf 'def fixture := 0\n' > .lake/packages/mathlib/Mathlib/Fixture.lean
              printf 'compiled\n' > .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean
              exit 0
            fi
            printf 'producer ran\n'
            exit "$2"
            """ + "\n");
        var result = LeanCacheEnsureCommand.RunWithWriter(fixture.Reader,
            ["--", fixture.Lake, "build", producerExit.ToString(CultureInfo.InvariantCulture)],
            new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance,
            variable => variable == "STRATALINT_ACCEPT_COLD_BUILD" ? "1" : null);

        Assert.True(producerExit == result.ExitCode, result.Output + result.Error);
        Assert.Equal(producerExit == 0, result.Success);
        Assert.EndsWith("producer ran\n", result.Output, StringComparison.Ordinal);
        Assert.Equal(dependencyAccepted ? ["build " + producerExit] : new[] { "exe cache get", "build " + producerExit },
            File.ReadAllLines(Path.Combine(fixture.Reader, "calls")));
        Assert.Equal(dependencyAccepted, beforeEnsure.State == LeanCacheStampState.Match);
        if (scenario is "existing-mismatch-miss" or "existing-platform-miss")
            Assert.Equal(LeanCacheStampState.Mismatch, beforeEnsure.State);
        if (scenario == "stamp-publication-failed")
            Assert.Equal(LeanCacheStampState.Corrupt, beforeEnsure.State);
        Assert.Empty(Directory.GetFiles(lake, ".stratalint-lean-cache-stamp.*.tmp"));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(23)]
    public void CorruptStampPersistenceRunsProducerAndUsesItsVerdict(int producerExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PrivateReaderFixture();
        var root = fixture.Reader;
        var lake = Path.Combine(root, ".lake");
        File.Delete(LeanCacheStamp.PathFor(lake));
        Directory.CreateDirectory(LeanCacheStamp.PathFor(lake));
        var retained = Path.Combine(lake, "build", "retained");
        Directory.CreateDirectory(Path.GetDirectoryName(retained)!);
        File.WriteAllText(retained, "preserved");

        File.WriteAllText(fixture.Lake, "#!/bin/sh\nif [ \"$1\" = exe ]; then exit 0; fi\n"
            + "printf 'producer output\\n'; printf 'producer diagnostic\\n' >&2; exit \"$1\"\n");
        var result = LeanCacheEnsureCommand.RunWithWriter(root,
            ["--", fixture.Lake, producerExit.ToString(CultureInfo.InvariantCulture)],
            new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner());

        Assert.Equal(producerExit == 0, result.Success);
        Assert.EndsWith("producer output\n", result.Output, StringComparison.Ordinal);
        Assert.Equal("producer diagnostic\n", result.Error);
        Assert.Equal(producerExit, result.ExitCode);
        Assert.Equal("preserved", File.ReadAllText(retained));
        Assert.True(Directory.Exists(LeanCacheStamp.PathFor(lake)));
        Assert.Equal(LeanCacheStampState.Corrupt,
            LeanCacheStamp.Inspect(lake, LeanPinSet.TryReadWorktree(root, out _)!).State);
        using var receipt = JsonDocument.Parse(
            result.Output["LEAN_CACHE ".Length..result.Output.IndexOf('\n', StringComparison.Ordinal)]);
        Assert.Equal("degraded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Contains("stamp publication failed", receipt.RootElement.GetProperty("reason").GetString()!, StringComparison.Ordinal);
        using var released = LeanCacheWriterGuard.TryAcquire(lake);
        Assert.NotNull(released);
    }

    [Fact]
    public void MetadataAndToolchainBytesDoNotChangeTheMathlibStampPartition()
    {
        using var directory = new TemporaryDirectory();
        var original = LeanPinSet.Create(Encoding.UTF8.GetBytes("leanprover/lean4:v4.33.0\n"),
            Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest()));
        var changed = LeanPinSet.Create(Encoding.UTF8.GetBytes("leanprover/lean4:v4.34.0\n"),
            Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest() + " \n"));
        LeanCacheStamp.Write(directory.Path, original);

        Assert.True(original.SamePartition(changed));
        Assert.Equal(original.Sha256, changed.Sha256);
        Assert.False(original.HasSameBytes(changed));
        Assert.Equal(LeanCacheStampState.Match, LeanCacheStamp.Inspect(directory.Path, changed).State);
    }

    [Fact]
    public void MathlibRevisionChangeInvalidatesTheStampPartition()
    {
        using var directory = new TemporaryDirectory();
        var toolchain = Encoding.UTF8.GetBytes("leanprover/lean4:v4.33.0\n");
        var original = LeanPinSet.Create(toolchain, Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest()));
        var changed = LeanPinSet.Create(toolchain, Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest('f')));
        LeanCacheStamp.Write(directory.Path, original);

        Assert.False(original.SamePartition(changed));
        Assert.NotEqual(original.Sha256, changed.Sha256);
        Assert.Equal(LeanCacheStampState.Mismatch, LeanCacheStamp.Inspect(directory.Path, changed).State);
    }
}
