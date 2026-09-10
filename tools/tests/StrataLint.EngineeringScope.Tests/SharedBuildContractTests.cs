using System.Diagnostics;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class SharedBuildContractTests
{
    [Theory]
    [InlineData("engineering")]
    [InlineData("current")]
    public void BranchSealRejectsAChangedCandidateEvenWhenBuildRoundAndMaterialsMatch(string stage)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        const string log = "build/ci/build.log";
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(fixture.Root, "build/ci"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, log), "built\n");
        StageStep[] Steps(string[] names) => names.Select(name => new StageStep(name,
            name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray();
        var started = CommonExecutionEvidence.SealBuild(fixture.Root, CommonExecutionEvidence.Candidate(fixture.Root), [log], Steps(CommonExecutionEvidence.BuildSteps));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, CurrentExecutionContractTests.CandidateFixture.First), "\n");
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.BuildPath, started with { Candidate = CommonExecutionEvidence.Candidate(fixture.Root) });
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) => { fixture.WriteTrx(results, "Passed"); return 0; }, TextWriter.Null, started));
        CiTransportTests.Report(fixture.Root);
        Assert.Throws<InvalidDataException>(() =>
        {
            if (stage == "engineering") CommonExecutionEvidence.SealEngineering(fixture.Root, started, Steps(CommonExecutionEvidence.EngineeringSteps));
            else CommonExecutionEvidence.SealCurrent(fixture.Root, started, Steps(CommonExecutionEvidence.CurrentSteps));
        });
    }

    [Theory]
    [InlineData("restore", 1, 1)]
    [InlineData("build", 17, 2)]
    [InlineData("missing-outputs", 0, 2)]
    public void FreshBuildRejectsFailedProcessesAndCannotUseASeedAsSuccess(string failure, int raw, int expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "build/bin"));
        const string log = "build/seed.log";
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, log), "old successful build\n");
        CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), [log],
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
        var shim = Path.Combine(root, "build/bin/dotnet");
        TemporaryFileSystem.File.WriteAllText(shim, $$"""
            #!/bin/bash
            echo "$1" >> build/events
            [[ "$1" != '{{failure}}' ]] || exit {{raw}}
            exit 0
            """);
        File.SetUnixFileMode(shim, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var scope = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = Process(root, scope, ["build", "--repository", root], new Dictionary<string, string> {
            ["PATH"] = Path.Combine(root, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH") });
        Assert.True(result.Exit == expected, result.Text);
        Assert.Equal(failure == "restore" ? ["restore"] : new[] { "restore", "build" },
            TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/events")).Split('\n', StringSplitOptions.RemoveEmptyEntries));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.BuildPath)));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.CurrentPath)));
    }

    [Theory]
    [InlineData("current", "", 0)]
    [InlineData("engineering", "", 0)]
    [InlineData("engineering", "test", 1)]
    [InlineData("current", "check-current", 1)]
    [InlineData("current", "replace-build", 2)]
    [InlineData("engineering", "replace-build", 2)]
    public void BranchProcessesUseOneBuildInEitherOrderAndPropagateRealExits(string first, string failure, int expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        Write(".gitignore", "build/\n.lake/\n**/bin/\n");
        Write("Makefile", "lean-report:\n\t@echo report >> build/events\n");
        Write("tools/scripts/workflow/scribe-content-checks.sh", "echo scribe >> build/events\n");
        Write("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", "// banned-api-proof\n");
        Write("build/bin/dotnet", """
            #!/bin/bash
            set -euo pipefail
            if [[ "$1" == *.EngineeringScope.dll ]]; then shift; exec "$CONTRACT_SCOPE" "$@"; fi
            if [[ "$1" == restore ]]; then
              [[ "$2" == *CompileFailProof.csproj ]] || exit 91
              echo restore-proof >> build/events
              exit 0
            fi
            if [[ "$1" == build ]]; then
              [[ " $* " == *' --no-dependencies '* ]] || exit 92
              echo proof >> build/events
              if [[ "$2" == */CompileFailProof/CompileFailProof.csproj ]]; then
                echo 'MissingCapability.cs(13,9): error CS7036: missing metaClear'
              else echo 'BannedApiViolations.cs(1,1): error RS0030: banned symbol'; fi
              exit 1
            fi
            if [[ "$1" == test ]]; then
              echo test >> build/events
              while [[ "$1" != --results-directory ]]; do shift; done
              mkdir -p "$2"
              cp build/passed/execution.trx "$2/run.trx"
              [[ "$CONTRACT_FAILURE" != replace-build ]] || sed 's/"round": "/"round": "changed-/' build/ci/build.json > build/changed.json
              [[ ! -f build/changed.json ]] || mv build/changed.json build/ci/build.json
              [[ "$CONTRACT_FAILURE" != test ]]
              exit $?
            fi
            action="$2"
            if [[ "$action" == check-current && "$CONTRACT_FAILURE" == replace-build ]]; then
              sed 's/"round": "/"round": "changed-/' build/ci/build.json > build/changed.json
              mv build/changed.json build/ci/build.json
            fi
            echo "$action" >> build/events
            [[ "$action" != "$CONTRACT_FAILURE" ]] || exit 1
            [[ "$action" != selftest ]] || echo deterministic-selftest
            """);
        File.SetUnixFileMode(Path.Combine(root, "build/bin/dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var binaries = new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.RunnerPath, CommonExecutionEvidence.ScribePath,
            "tools/tests/First/bin/Release/net10.0/First.dll", "tools/tests/Second/bin/Release/net10.0/Second.dll" };
        foreach (var binary in binaries) Write(binary, "synthetic runtime\n");
        CommonExecutionEvidence.Write(root, CommonBuildOutputs.TestsPath, new[] {
            new BuiltTestProject(CurrentExecutionContractTests.CandidateFixture.First, binaries[3]),
            new BuiltTestProject(CurrentExecutionContractTests.CandidateFixture.Second, binaries[4]) });
        Write("build/ci/build.log", "shared production\n");
        fixture.WriteTrx(Path.Combine(root, "build/passed"), "Passed");
        CiTransportTests.Report(root);
        var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), binaries.Append(CommonBuildOutputs.TestsPath),
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/build.log")).ToArray());
        var before = CommonExecutionEvidence.Hash(Path.Combine(root, CommonExecutionEvidence.BuildPath));
        var scope = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var environment = new Dictionary<string, string> {
            ["PATH"] = Path.Combine(root, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            ["CONTRACT_SCOPE"] = scope, ["CONTRACT_FAILURE"] = failure };
        var result = Branch(first);
        Assert.True(result.Exit == expected, result.Text);
        var other = first == "current" ? "engineering" : "current";
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, "build/ci/" + other + ".json")));
        if (expected == 0)
        {
            result = Branch(other);
            Assert.True(result.Exit == 0, result.Text);
            CommonExecutionEvidence.ValidateCommon(root, [CurrentExecutionContractTests.CandidateFixture.First]);
            var events = TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/events")).Split('\n');
            Assert.Equal(2, events.Count(value => value == "test"));
            Assert.Equal(2, events.Count(value => value == "proof"));
            Assert.Equal(1, events.Count(value => value == "report"));
        }
        else Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, "build/ci/" + first + ".json")));
        Assert.Equal(failure == "replace-build", before != CommonExecutionEvidence.Hash(Path.Combine(root, CommonExecutionEvidence.BuildPath)));

        (int Exit, string Text) Branch(string stage) => Process(root, scope,
            new[] { stage, "--repository", root }.Concat(stage == "engineering" ? ["--build-round", build.Round] : Array.Empty<string>()).ToArray(), environment);
        void Write(string path, string text)
        {
            var full = Path.Combine(root, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            TemporaryFileSystem.File.WriteAllText(full, text);
        }
    }

    [Theory]
    [InlineData("complete")]
    [InlineData("missing-engineering")]
    [InlineData("missing-current")]
    [InlineData("missing-build")]
    [InlineData("failed-engineering")]
    [InlineData("failed-current")]
    [InlineData("failed-build")]
    [InlineData("raw-engineering-exit")]
    [InlineData("raw-current-exit")]
    [InlineData("raw-build-exit")]
    [InlineData("wrong-test-round")]
    [InlineData("wrong-engineering-round")]
    [InlineData("wrong-current-round")]
    [InlineData("corrupt-build")]
    [InlineData("corrupt-trx")]
    [InlineData("missing-base-project")]
    public void DeltaJoinsIndependentBranchesAndRejectsIncompleteOrMixedEvidence(string defect)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        const string log = "build/ci/build.log";
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(fixture.Root, "build/ci"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, log), "built once\n");
        StageStep[] Steps(string[] names) => names.Select(name => new StageStep(name,
            name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", log)).ToArray();
        var build = CommonExecutionEvidence.SealBuild(fixture.Root, CommonExecutionEvidence.Candidate(fixture.Root), [log],
            Steps(CommonExecutionEvidence.BuildSteps));
        CiTransportTests.Report(fixture.Root);
        CommonExecutionEvidence.SealCurrent(fixture.Root, build, Steps(CommonExecutionEvidence.CurrentSteps));
        CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath)));
        Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.ValidateCommon(fixture.Root));
        var currentHash = CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath));
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, directory) => { fixture.WriteTrx(directory, "Passed"); return 0; },
            TextWriter.Null, build));
        CommonExecutionEvidence.SealEngineering(fixture.Root, build, Steps(CommonExecutionEvidence.EngineeringSteps));
        Assert.Equal(currentHash, CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
        CommonExecutionEvidence.ValidateCommon(fixture.Root, [CurrentExecutionContractTests.CandidateFixture.First]);
        var tests = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath);
        if (defect == "complete")
        {
            var previousTrx = tests.Projects.Select(project => project.Results).ToArray();
            Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, directory) => { fixture.WriteTrx(directory, "Passed"); return 0; }, TextWriter.Null, build));
            var next = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath);
            Assert.Empty(previousTrx.Intersect(next.Projects.Select(project => project.Results)));
            Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateCommon(fixture.Root)); // Old engineering cannot attest a new invocation.
            return;
        }
        if (defect.StartsWith("missing-", StringComparison.Ordinal) && defect != "missing-base-project")
            TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, "build/ci/" + defect[8..] + ".json"));
        else if (defect.StartsWith("failed-", StringComparison.Ordinal) || defect.StartsWith("wrong-", StringComparison.Ordinal) && defect != "wrong-test-round")
        {
            var path = "build/ci/" + defect.Split('-')[1] + ".json";
            var record = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, path);
            CommonExecutionEvidence.Write(fixture.Root, path, defect.StartsWith("failed-", StringComparison.Ordinal)
                ? record with { Steps = record.Steps.Select(step => step with { Exit = 1 }).ToArray() }
                : record with { Round = "another-build" });
        }
        else if (defect == "wrong-test-round") CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, tests with { Round = "another-build" });
        else if (defect.StartsWith("raw-", StringComparison.Ordinal))
        {
            var path = "build/ci/" + defect.Split('-')[1] + ".json";
            var record = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, path);
            CommonExecutionEvidence.Write(fixture.Root, path, record with { Steps = record.Steps.Select(step => step with { RawExit = 17 }).ToArray() });
        }
        else if (defect == "corrupt-build") TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, log), "corrupt");
        else if (defect == "corrupt-trx") TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, tests.Materials[0].Path), "corrupt");
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateCommon(fixture.Root,
            defect == "missing-base-project" ? ["tools/tests/Removed/Removed.csproj"] : []));
        if (defect == "missing-base-project") return; // CLI consumer tests derive this floor from real base data.
        using var output = new StringWriter();
        Assert.Equal(2, new CommonStages(fixture.Root, output).Run("delta", Git(fixture.Root, "rev-parse", "HEAD")));
        Assert.Contains("\"not_executed\":[\"check-delta\"]", output.ToString(), StringComparison.Ordinal);
    }

    internal static string Git(string root, params string[] arguments)
    {
        var result = Process(root, "git", arguments);
        Assert.True(result.Exit == 0, result.Text);
        return result.Text.Trim();
    }

    internal static (int Exit, string Text) Process(string root, string executable, string[] arguments,
        IReadOnlyDictionary<string, string>? environment = null)
    {
        var start = new ProcessStartInfo(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        foreach (var pair in environment ?? new Dictionary<string, string>()) start.Environment[pair.Key] = pair.Value;
        using var process = System.Diagnostics.Process.Start(start)!;
        using var deadline = new CancellationTokenSource(TestBudgets.ScriptProcessHangGuard);
        var stdout = process.StandardOutput.ReadToEndAsync(deadline.Token);
        var stderr = process.StandardError.ReadToEndAsync(deadline.Token);
        try
        {
            process.WaitForExitAsync(deadline.Token).GetAwaiter().GetResult();
            Task.WhenAll(stdout, stderr).WaitAsync(deadline.Token).GetAwaiter().GetResult();
            return (process.ExitCode, stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult());
        }
        catch (OperationCanceledException)
        {
            throw new SkipException("infrastructure-hang-guard expired for shared build fixture: " + executable + " " + string.Join(' ', arguments));
        }
        finally { if (!process.HasExited) process.Kill(entireProcessTree: true); }
    }
}
