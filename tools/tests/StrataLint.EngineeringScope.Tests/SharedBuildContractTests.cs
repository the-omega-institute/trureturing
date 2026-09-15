using System.Diagnostics;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class SharedBuildContractTests(ITestOutputHelper output)
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
        var started = CommonExecutionEvidence.SealBuild(fixture.Root, CommonExecutionEvidence.Candidate(fixture.Root), fixture.Build().Materials.Select(material => material.Path).Append(log), Steps(CommonExecutionEvidence.BuildSteps));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, CurrentExecutionContractTests.CandidateFixture.First), "\n");
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.BuildPath, started with { Candidate = CommonExecutionEvidence.Candidate(fixture.Root) });
        Assert.Throws<InvalidDataException>(() => Program.RunCurrentTests(fixture.Root, (_, _) => throw new InvalidOperationException("must not run"), TextWriter.Null, started));
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
        Assert.Equal(failure == "restore" ? ["restore"] : failure == "build" ? ["restore", "build"]
                : new[] { "restore", "build", "restore", "build" },
            TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/events")).Split('\n', StringSplitOptions.RemoveEmptyEntries));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.BuildPath)));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.CurrentPath)));
    }

    [Theory]
    [InlineData("current", "", 0)]
    [InlineData("engineering", "", 0)]
    [InlineData("engineering", "test", 1)]
    [InlineData("engineering", "selftest", 1)]
    [InlineData("engineering", "selftest-mismatch", 2)]
    [InlineData("engineering", "capability-proof", 1)]
    [InlineData("current", "check-current", 1)]
    [InlineData("current", "replace-build", 2)]
    [InlineData("current", "missing-current-units", 2)]
    [InlineData("engineering", "replace-build", 2)]
    public void BranchProcessesUseOneBuildInEitherOrderAndPropagateRealExits(string first, string failure, int expected)
        => RunBranches(first, failure, expected, exportSeeds: true);

    [Theory]
    [InlineData("engineering")]
    [InlineData("current")]
    public void ReadOnlyBranchesPreserveRequiredTransportAndExplicitSeedExport(string first)
        => RunBranches(first, "", 0, exportSeeds: false);

    [Theory]
    [InlineData("current", "missing-current-units", 2)]
    [InlineData("current", "replace-build", 2)]
    [InlineData("engineering", "replace-build", 2)]
    [InlineData("engineering", "test", 1)]
    [InlineData("engineering", "capability-proof", 1)]
    public void ReadOnlyBranchesStillRejectInvalidRequiredEvidence(string first, string failure, int expected)
        => RunBranches(first, failure, expected, exportSeeds: false);

    [Theory]
    [InlineData("engineering", "automatic", true)]
    [InlineData("current", "automatic", true)]
    [InlineData("engineering", "automatic", false)]
    [InlineData("current", "automatic", false)]
    [InlineData("engineering", "deferred", true)]
    [InlineData("current", "deferred", true)]
    [InlineData("engineering", "deferred", false)]
    [InlineData("current", "deferred", false)]
    public void ExplicitSeedExportModePreservesRequiredEvidenceAndCanonicalExport(string first, string mode, bool cacheWrites)
        => RunBranches(first, "", 0, cacheWrites, mode);

    [Theory]
    [InlineData("current", "missing-current-units", 2)]
    [InlineData("current", "replace-build", 2)]
    [InlineData("engineering", "replace-build", 2)]
    [InlineData("engineering", "test", 1)]
    [InlineData("engineering", "capability-proof", 1)]
    public void DeferredSeedExportStillRejectsInvalidRequiredEvidence(string first, string failure, int expected)
        => RunBranches(first, failure, expected, exportSeeds: true, seedExport: "deferred");

    [Theory]
    [InlineData("value")]
    [InlineData("missing")]
    [InlineData("duplicate")]
    [InlineData("build")]
    [InlineData("delta")]
    public void InvalidSeedExportOptionFailsBeforeStageExecution(string defect)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var stage = defect is "build" or "delta" ? defect : "current";
        string[] options = defect switch
        {
            "value" => ["--seed-export", "unsupported"],
            "missing" => ["--seed-export"],
            "duplicate" => ["--seed-export", "automatic", "--seed-export", "deferred"],
            _ => ["--seed-export", "deferred"],
        };
        using var text = new StringWriter();
        Assert.Equal(2, Program.Run([stage, "--repository", fixture.Root, .. options], TestResultEvidence.Load, text, text));
        Assert.Contains("ENGINEERING_TEST_PLAN_FAILED", text.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("STAGE_PROCESS ", text.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/" + stage + "-result.json")));
    }

    private void RunBranches(string first, string failure, int expected, bool exportSeeds, string? seedExport = null)
    {
        if (OperatingSystem.IsWindows()) return;
        var automaticExport = exportSeeds && seedExport != "deferred";
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        Write(".gitignore", "build/\n.lake/\n**/bin/\n");
        Write("Makefile", "lean-report:\n\t@echo report >> build/events\n");
        Write("tools/scripts/workflow/scribe-content-checks.sh", "echo scribe >> build/events\n");
        fixture.RegisterProofs();
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
                [[ "$CONTRACT_FAILURE" != capability-proof ]] || exit 1
                echo 'MissingCapability.cs(13,9): error CS7036: missing metaClear'
              else echo 'BannedApiViolations.cs(1,1): error RS0030: banned symbol'; fi
              exit 1
            fi
            if [[ "$1" == test ]]; then
              [[ "${LEAN_NUM_THREADS:-unset}" == 7 ]] || exit 95
              echo test >> build/events
              assembly="$2"
              source=build/passed/execution.trx
              [[ "$CONTRACT_FAILURE" != test ]] || source=build/failed/execution.trx
              while [[ "$1" != --results-directory ]]; do shift; done
              mkdir -p "$2"
              if [[ "$assembly" == *Second.dll ]]; then sed 's/First.dll/Second.dll/g' "$source" > "$2/run.trx"
              else cp "$source" "$2/run.trx"; fi
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
            if [[ "$action" == check-current && "$CONTRACT_FAILURE" != missing-current-units ]]; then
              cp build/prepared-current-checks.json build/ci/current-checks.json
            fi
            echo "$action" >> build/events
            [[ "$action" != "$CONTRACT_FAILURE" ]] || exit 1
            [[ "$action" != selftest ]] || echo "SELFTEST PASS"
            if [[ "$action" == selftest && "$CONTRACT_FAILURE" == selftest-mismatch ]]; then
              wc -l < build/events
            fi
            """);
        File.SetUnixFileMode(Path.Combine(root, "build/bin/dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var binaries = new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.RunnerPath, CommonExecutionEvidence.ScribePath,
            "tools/tests/First/bin/Release/net10.0/First.dll", "tools/tests/Second/bin/Release/net10.0/Second.dll", CommonExecutionEvidence.LeanProducerPath };
        foreach (var binary in binaries) Write(binary, "synthetic runtime\n");
        CommonExecutionEvidence.Write(root, CommonBuildOutputs.TestsPath, new[] {
            new BuiltTestProject(CurrentExecutionContractTests.CandidateFixture.First, binaries[3]),
            new BuiltTestProject(CurrentExecutionContractTests.CandidateFixture.Second, binaries[4]) });
        Write("build/ci/build.log", "shared production\n");
        fixture.WriteTrx(Path.Combine(root, "build/passed"), "Passed");
        fixture.WriteTrx(Path.Combine(root, "build/failed"), "Failed");
        CiTransportTests.Report(root);
        if (!automaticExport)
        {
            fixture.Track();
            Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "required branch fixture");
        }
        var build = CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), binaries.Append(CommonBuildOutputs.TestsPath),
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/build.log")).ToArray());
        // The CLI fixture supplies a unit manifest produced by the native common
        // owner. A shell success without this material must fail, even with an old
        // same-round result present when the branch starts.
        CheckEvidenceFixture.Seal(root, "current", build);
        File.Copy(Path.Combine(root, CommonExecutionEvidence.ChecksPath("current")), Path.Combine(root, "build/prepared-current-checks.json"));
        var before = CommonExecutionEvidence.Hash(Path.Combine(root, CommonExecutionEvidence.BuildPath));
        var scope = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var environment = new Dictionary<string, string> {
            ["PATH"] = Path.Combine(root, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            ["CONTRACT_SCOPE"] = scope, ["CONTRACT_FAILURE"] = failure, ["LEAN_NUM_THREADS"] = "7" };
        if (!exportSeeds) environment["STRATALINT_CACHE_WRITES"] = "false";
        var result = Branch(first);
        Assert.True(result.Exit == expected, result.Text);
        if (!automaticExport) AssertNoOptionalSeeds();
        var other = first == "current" ? "engineering" : "current";
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, "build/ci/" + other + ".json")));
        if (expected == 0)
        {
            AssertAutomaticSeed(first, result.Text);
            result = Branch(other);
            Assert.True(result.Exit == 0, result.Text);
            AssertAutomaticSeed(other, result.Text);
            var accepted = CommonExecutionEvidence.ValidateCommon(root, [CurrentExecutionContractTests.CandidateFixture.First]);
            Assert.Equal(build.Candidate, accepted.Current.Candidate);
            Assert.Equal(build.Round, accepted.Current.Round);
            Assert.Equal(CommonExecutionEvidence.CurrentSteps, accepted.Current.Steps.Select(step => step.Name));
            Assert.All(accepted.Current.Steps, step => Assert.Equal((0, 0, "executed"), (step.RawExit, step.Exit, step.Status)));
            var events = TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/events")).Split('\n');
            Assert.Equal(2, events.Count(value => value == "test"));
            Assert.Equal(2, events.Count(value => value == "proof"));
            Assert.Equal(2, events.Count(value => value == "selftest"));
            Assert.Equal(1, events.Count(value => value == "report"));
            var fresh = EngineeringSummary("fresh");
            Assert.Equal("completed", fresh.GetProperty("status").GetString());
            Assert.Empty(fresh.GetProperty("not_executed").EnumerateArray());
            Assert.Empty(fresh.GetProperty("not_required").EnumerateArray());
            AssertUnits(fresh, ["executed", "executed", "executed"]);
            foreach (var proof in fresh.GetProperty("steps").EnumerateArray().Where(step => step.GetProperty("name").GetString()!.EndsWith("proof", StringComparison.Ordinal)))
            {
                Assert.Equal(1, proof.GetProperty("raw_exit").GetInt32());
                Assert.Equal(0, proof.GetProperty("exit").GetInt32());
            }
            var initial = CommonExecutionEvidence.ValidateTests(root);
            if (!automaticExport)
            {
                Assert.False(fresh.GetProperty("test_seed_saved").GetBoolean());
                AssertNoOptionalSeeds();
                var commit = Git(root, "rev-parse", "HEAD");
                foreach (var stage in new[] { "engineering", "current" })
                {
                    Transport(stage);
                    AssertNoOptionalSeeds();
                }
                CommonExecutionEvidence.ValidateCommon(root, [CurrentExecutionContractTests.CandidateFixture.First]);
                // Explicit writer commands remain available without implicit stage export.
                foreach (var stage in new[] { "engineering", "current" })
                {
                    Transport(stage + "-seed");
                    CommonExecutionEvidence.ValidateCheckSeedBundle(root, stage);
                }

                void Transport(string stage)
                {
                    var arguments = new[] { "--repository", root, "--stage", stage,
                        "--commit", commit, "--run-id", "17", "--run-attempt", "2" };
                    var packed = Process(root, scope, new[] { "transport-pack" }.Concat(arguments)
                        .Concat(["--archive", Path.Combine(root, "build", stage + ".tgz")]).ToArray(), environment);
                    Assert.True(packed.Exit == 0, packed.Text);
                    Assert.Equal(stage.EndsWith("-seed", StringComparison.Ordinal) ? 1 : 0,
                        packed.Text.Split('\n').Count(line => line.StartsWith("COMMON_CHECK_SEED_SAVED ", StringComparison.Ordinal)));
                    Assert.Equal(stage == "engineering-seed" ? 1 : 0,
                        packed.Text.Split('\n').Count(line => line == "ENGINEERING_TEST_SEED_SAVED"));
                    var verified = Process(root, scope, new[] { "transport-verify" }.Concat(arguments).ToArray(), environment);
                    Assert.True(verified.Exit == 0, verified.Text);
                }
            }
            Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestSeedPath, "tests.json")));
            var seedFiles = !automaticExport ? SeedFiles() : [];
            var again = Branch("engineering");
            Assert.True(again.Exit == 0, again.Text);
            var summary = EngineeringSummary("warm");
            Assert.Equal(0, summary.GetProperty("test_projects_executed").GetInt32());
            Assert.Equal(2, summary.GetProperty("test_projects_reused").GetInt32());
            Assert.Equal(automaticExport, summary.GetProperty("test_seed_saved").GetBoolean());
            if (!automaticExport)
            {
                Assert.DoesNotContain("ENGINEERING_TEST_SEED_SAVED", again.Text, StringComparison.Ordinal);
                Assert.DoesNotContain("COMMON_CHECK_SEED_SAVED", again.Text, StringComparison.Ordinal);
                Assert.Equal(seedFiles, SeedFiles());
            }
            Assert.Empty(summary.GetProperty("not_executed").EnumerateArray());
            Assert.Empty(summary.GetProperty("not_required").EnumerateArray());
            AssertUnits(summary, ["reused", "reused", "reused"]);
            Assert.Equal(fresh.GetProperty("check_units").EnumerateArray().Select(unit => unit.GetProperty("execution_round").GetString()),
                summary.GetProperty("check_units").EnumerateArray().Select(unit => unit.GetProperty("execution_round").GetString()));
            Assert.Equal(fresh.GetProperty("check_units").EnumerateArray().Select(unit => unit.GetProperty("execution_candidate").GetString()),
                summary.GetProperty("check_units").EnumerateArray().Select(unit => unit.GetProperty("execution_candidate").GetString()));
            Assert.Equal(initial.Projects.Select(row => row with { Status = "reused" }), CommonExecutionEvidence.ValidateTests(root).Projects);
            Assert.Equal(2, TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/events")).Split('\n').Count(value => value == "test"));
            Assert.Equal(events, TemporaryFileSystem.File.ReadAllText(Path.Combine(root, "build/events")).Split('\n'));
            if (!automaticExport)
            {
                // The CLI fixture uses the native unit owner to prepare reused
                // evidence; invoking any unit's work here is a test failure.
                var checks = CommonExecutionEvidence.BeginChecks(root, "current", build, TextWriter.Null);
                foreach (var id in checks.Ids)
                    checks.Run(id, () => throw new InvalidOperationException("restored current unit must reuse: " + id));
                Assert.All(checks.Seal().Units, unit => Assert.Equal("reused", unit.Status));
                File.Copy(Path.Combine(root, CommonExecutionEvidence.ChecksPath("current")),
                    Path.Combine(root, "build/prepared-current-checks.json"), overwrite: true);
                var current = Branch("current");
                Assert.True(current.Exit == 0, current.Text);
                Assert.DoesNotContain("COMMON_CHECK_SEED_SAVED", current.Text, StringComparison.Ordinal);
                Assert.DoesNotContain("CURRENT_FINALIZE phase=seed-export", current.Text, StringComparison.Ordinal);
                Assert.Equal(seedFiles, SeedFiles());
                var currentEvidence = CommonExecutionEvidence.ValidateCommon(root,
                    [CurrentExecutionContractTests.CandidateFixture.First]).Current;
                Assert.All(currentEvidence.Steps.Where(step => step.Name is "scribe" or "filemap" or "check-current"),
                    step => Assert.Equal("reused", step.Status));
                Assert.Equal(events.Where(value => value.Length != 0).Concat(["report", "check-current"]),
                    File.ReadAllLines(Path.Combine(root, "build/events")));
                // An old successful seed never substitutes for the current
                // required evidence at an explicit snapshot/export boundary.
                File.AppendAllText(Path.Combine(root, CommonExecutionEvidence.ReportPath), "corrupt required report");
                var failedArchive = Path.Combine(root, "build/failed-current-seed.tgz");
                var failedExport = Process(root, scope, ["transport-pack", "--repository", root, "--stage", "current-seed",
                    "--commit", Git(root, "rev-parse", "HEAD"), "--run-id", "17", "--run-attempt", "2", "--archive", failedArchive], environment);
                Assert.Equal(2, failedExport.Exit);
                Assert.DoesNotContain("status=packed", failedExport.Text, StringComparison.Ordinal);
                Assert.DoesNotContain("COMMON_CHECK_SEED_SAVED", failedExport.Text, StringComparison.Ordinal);
                Assert.False(File.Exists(failedArchive));
                Assert.Equal(seedFiles, SeedFiles());
            }
        }
        else
        {
            using var failedSummary = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "build/ci/" + first + "-result.json")));
            Assert.Equal("failed", failedSummary.RootElement.GetProperty("status").GetString());
            Assert.Equal(expected, failedSummary.RootElement.GetProperty("exit").GetInt32());
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, "build/ci/" + first + ".json")));
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestSeedPath, "tests.json")));
            if (first == "engineering" && failure != "replace-build")
            {
                var summary = EngineeringSummary("failed-" + failure);
                Assert.Equal("failed", summary.GetProperty("status").GetString());
                Assert.Equal(expected, summary.GetProperty("exit").GetInt32());
                Assert.Null(summary.GetProperty("engineering_evidence").GetString());
                Assert.Empty(summary.GetProperty("not_required").EnumerateArray());
                Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.ChecksPath("engineering"))));
                var unreached = failure == "test" ? new[] { "selftest-pair", "capability-proof", "banned-api-proof" }
                    : failure == "capability-proof" ? ["banned-api-proof"] : ["capability-proof", "banned-api-proof"];
                Assert.Equal(unreached, summary.GetProperty("not_executed").EnumerateArray().Select(value => value.GetString()));
                AssertUnits(summary, failure == "test" ? ["not-executed", "not-executed", "not-executed"]
                    : failure == "capability-proof" ? ["executed", "failed", "not-executed"] : ["failed", "not-executed", "not-executed"]);
                if (failure == "test")
                {
                    var step = Assert.Single(summary.GetProperty("steps").EnumerateArray());
                    Assert.Equal("tests", step.GetProperty("name").GetString());
                    Assert.Equal(1, step.GetProperty("raw_exit").GetInt32());
                    Assert.Equal(1, step.GetProperty("exit").GetInt32());
                    Assert.Equal("failed", step.GetProperty("status").GetString());
                    Assert.Equal(new[] { "test", "test" }, File.ReadAllLines(Path.Combine(root, "build/events")));
                }
                if (failure == "selftest-mismatch")
                    Assert.All(summary.GetProperty("steps").EnumerateArray(), step => Assert.Equal(0, step.GetProperty("raw_exit").GetInt32()));
            }
        }
        Assert.Equal(failure == "replace-build", before != CommonExecutionEvidence.Hash(Path.Combine(root, CommonExecutionEvidence.BuildPath)));

        void AssertAutomaticSeed(string stage, string text)
        {
            Assert.Equal(automaticExport ? 1 : 0,
                text.Split('\n').Count(line => line == "COMMON_CHECK_SEED_SAVED stage=" + stage));
            if (automaticExport) CommonExecutionEvidence.ValidateCheckSeedBundle(root, stage);
        }

        void AssertNoOptionalSeeds()
        {
            Assert.False(Directory.Exists(Path.Combine(root, CommonExecutionEvidence.TestSeedPath)));
            foreach (var stage in new[] { "engineering", "current" })
            {
                Assert.False(Directory.Exists(Path.Combine(root, CommonExecutionEvidence.CheckSeedPath(stage))));
                Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.BundleListPath(stage + "-seed"))));
            }
        }

        (string Path, string Hash)[] SeedFiles() => new[] { CommonExecutionEvidence.TestSeedPath,
                CommonExecutionEvidence.CheckSeedPath("engineering"), CommonExecutionEvidence.CheckSeedPath("current") }
            .SelectMany(path => Directory.EnumerateFiles(Path.Combine(root, path), "*", SearchOption.AllDirectories))
            .Concat(new[] { "engineering", "current" }.Select(stage =>
                Path.Combine(root, CommonExecutionEvidence.BundleListPath(stage + "-seed"))))
            .Order(StringComparer.Ordinal)
            .Select(path => (Path.GetRelativePath(root, path), CommonExecutionEvidence.Hash(path))).ToArray();

        JsonElement EngineeringSummary(string phase)
        {
            var json = File.ReadAllText(Path.Combine(root, "build/ci/engineering-result.json"));
            output.WriteLine("COMMON_ENGINEERING_SUMMARY phase=" + phase + " " + json);
            using var document = JsonDocument.Parse(json);
            return document.RootElement.Clone();
        }
        static void AssertUnits(JsonElement summary, string[] statuses)
        {
            var units = summary.GetProperty("check_units").EnumerateArray().ToArray();
            Assert.Equal(new[] { "selftest-pair", "capability-proof", "banned-api-proof" }, units.Select(unit => unit.GetProperty("id").GetString()));
            Assert.Equal(statuses, units.Select(unit => unit.GetProperty("status").GetString()));
        }
        (int Exit, string Text) Branch(string stage) => Process(root, scope,
            new[] { stage, "--repository", root }.Concat(stage == "engineering" ? ["--build-round", build.Round] : Array.Empty<string>())
                .Concat(seedExport is null ? [] : new[] { "--seed-export", seedExport }).ToArray(), environment);
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
        var build = CommonExecutionEvidence.SealBuild(fixture.Root, CommonExecutionEvidence.Candidate(fixture.Root), fixture.Build().Materials.Select(material => material.Path).Append(log),
            Steps(CommonExecutionEvidence.BuildSteps));
        CiTransportTests.Report(fixture.Root);
        CheckEvidenceFixture.Seal(fixture.Root, "current", build);
        CommonExecutionEvidence.SealCurrent(fixture.Root, build, Steps(CommonExecutionEvidence.CurrentSteps));
        CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath)));
        Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.ValidateCommon(fixture.Root));
        var currentHash = CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath));
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, directory) => { fixture.WriteTrx(directory, "Passed"); return 0; },
            TextWriter.Null, build));
        CheckEvidenceFixture.Seal(fixture.Root, "engineering", build);
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
        IReadOnlyDictionary<string, string>? environment = null, TimeSpan? hangGuard = null)
    {
        var start = new ProcessStartInfo(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        // Keep synthetic fixture processes independent from the outer GitHub
        // workflow's candidate identity. Individual tests opt in explicitly.
        start.Environment["GITHUB_EVENT_NAME"] = "";
        start.Environment["CANDIDATE_SHA"] = "";
        start.Environment["CI_WORKFLOW_INPUTS"] = "null";
        start.Environment.Remove("STRATALINT_CACHE_WRITES");
        foreach (var pair in environment ?? new Dictionary<string, string>()) start.Environment[pair.Key] = pair.Value;
        using var process = System.Diagnostics.Process.Start(start)!;
        using var deadline = new CancellationTokenSource(hangGuard ?? TestBudgets.ScriptProcessHangGuard);
        using var cleanup = new CancellationTokenSource();
        var stdoutText = new System.Text.StringBuilder();
        var stderrText = new System.Text.StringBuilder();
        var stdout = Drain(process.StandardOutput, stdoutText);
        var stderr = Drain(process.StandardError, stderrText);
        var phase = "child-exit";
        var expired = false;
        try
        {
            process.WaitForExitAsync(deadline.Token).GetAwaiter().GetResult();
            phase = "output-drain";
            Task.WhenAll(stdout, stderr).WaitAsync(deadline.Token).GetAwaiter().GetResult();
            return (process.ExitCode, stdoutText.ToString() + stderrText);
        }
        catch (OperationCanceledException)
        {
            expired = true;
            throw new SkipException("infrastructure-hang-guard expired for shared build fixture: " + executable + " " + string.Join(' ', arguments)
                + "; phase=" + phase);
        }
        finally
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            cleanup.CancelAfter(TestBudgets.ScriptProcessHangGuard);
            try { Task.WhenAll(process.WaitForExitAsync(cleanup.Token), stdout, stderr).GetAwaiter().GetResult(); }
            catch (OperationCanceledException) when (expired) { } // Preserve the original guard phase after draining retained bytes.
            finally
            {
                if (Environment.GetEnvironmentVariable("JUDGE_SEED_EVIDENCE") is { Length: > 0 } evidence)
                {
                    Directory.CreateDirectory(evidence);
                    var path = Path.Combine(evidence, "process-" + process.Id + "-" + Guid.NewGuid().ToString("N"));
                    File.WriteAllText(path + ".json", System.Text.Json.JsonSerializer.Serialize(new {
                        executable, arguments, working_directory = root, phase, guard_expired = expired,
                        child_exit = process.HasExited ? (int?)process.ExitCode : null }));
                    File.WriteAllText(path + ".stdout.log", stdoutText.ToString());
                    File.WriteAllText(path + ".stderr.log", stderrText.ToString());
                }
            }
        }

        async Task Drain(StreamReader reader, System.Text.StringBuilder text)
        {
            var buffer = new char[4096];
            int count;
            while ((count = await reader.ReadAsync(buffer.AsMemory(), cleanup.Token).ConfigureAwait(false)) != 0)
                text.Append(buffer, 0, count);
        }
    }
}
