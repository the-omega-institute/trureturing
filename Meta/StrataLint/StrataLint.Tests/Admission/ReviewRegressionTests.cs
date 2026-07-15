using System.Diagnostics;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReviewRegressionTests
{
    [Fact]
    public void Cf1TopologyReportsBootstrapNotActiveWhenDefaultBranchLacksWorkflow()
    {
        using var remote = new TemporaryDirectory();
        using var repository = new TemporaryDirectory();
        InitializeRemoteDefaultBranch(remote.Path, repository.Path, installWorkflow: false);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { "topology" },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(3, exitCode);
        Assert.Contains(
            "BOOTSTRAP-NOT-ACTIVE:baseline gate 尚未注入 dev,当前非机器门控态,须人类可信注入(D5-T0017)",
            console.Output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("STEADY-STATE-ACTIVE", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void Cf1TopologyReportsSteadyStateWhenDefaultBranchContainsWorkflow()
    {
        using var remote = new TemporaryDirectory();
        using var repository = new TemporaryDirectory();
        InitializeRemoteDefaultBranch(remote.Path, repository.Path, installWorkflow: true);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { "topology" },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains(
            "STEADY-STATE-ACTIVE:dev-baseline workflow 已注入 dev;required_status_checks/enforce_admins 仍须外部核验(D5-T0017)",
            console.Output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("BOOTSTRAP-NOT-ACTIVE", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void Cf1BootstrapTicketCannotDisappearFromProtectedBackfillInventory()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"].Replace(
            "  - case_id: D5-T0017\n    gid: D5/X_Frontier/RequiredChecks\n",
            string.Empty,
            StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(
            evaluation.Diagnostics,
            diagnostic => diagnostic.Message.Contains("D5-T0017", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsTicketWhoseTargetDoesNotDeclareItsCase()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.HeartsDraftPath] = fixture.Files[RuleFixture.HeartsDraftPath].Replace(
            "TASK D5-T0018 ",
            "TASK D5-T0099 ",
            StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(
            evaluation.Diagnostics,
            diagnostic => diagnostic.Message.Contains(
                "ticket D5-T0018 target does not declare TASK D5-T0018",
                StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsFrontierTaskMissingFromTicketIndex()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.HeartsDraftPath] += "\n/-- TASK D5-T0099 -/\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(
            evaluation.Diagnostics,
            diagnostic => diagnostic.Message.Contains(
                "frontier TASK cases are missing from ticket_index: D5-T0099",
                StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016AcceptsTheNeutralSyntheticDigestionLedger()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl016AcceptsCurrentRepositoryTicketDeclarations()
    {
        var repositoryRoot = FindRepositoryRoot();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var path in Directory.EnumerateFiles(
                     Path.Combine(repositoryRoot, "D5", "X_Frontier"),
                     "*.lean",
                     SearchOption.TopDirectoryOnly))
        {
            var repoPath = Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
            fixture.Files[repoPath] = File.ReadAllText(path, Encoding.UTF8);
            fixture.Reports.TryAdd(repoPath, new LeanFileReport([], []));
        }

        // The digestion projection consumes Lean truth, so this synthetic managed file carries its report.
        fixture.Files["D5/X_Frontier/DownwardImportTail.lean"] = """
            /- GID: D5/X_Frontier/DownwardImportTail
               generality: E
               mirror-B: none(waiver:test-fixture)
               mirror-E: none(waiver:test-fixture)
               anchors: []
               digest: SL-016 downward-import regression fixture. -/
            import D5.S3.Weil.FourierLaplace
            def downwardImportTail : Unit := ()
            """;
        fixture.Reports["D5/X_Frontier/DownwardImportTail.lean"] = new LeanFileReport(
            ["D5.S3.Weil.FourierLaplace"],
            []);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.BuildForRuleCompatibility());

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl016RejectsHandwrittenDigestionStatusThatDisagreesWithDerivation()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        const string expected = "          migration: partial\n          truth: closed";
        const string falseProjection = "          migration: absorbed\n          truth: closed";
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"].Replace(
            expected,
            falseProjection,
            StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsFormattedFingerprintThatDisagreesWithSourceSpan()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var document = BackfillInventoryLoader.Load(fixture.Files["Meta/BACKFILL.yaml"]);
        var fingerprint = document.RequireDigestionEntries()[0].Fingerprints.RawSha256;
        var replacement = fingerprint[..^1] + (fingerprint[^1] == '0' ? '1' : '0');
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"].Replace(
            fingerprint,
            replacement,
            StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("fingerprint", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void Sl016RejectsDuplicateSourceIdEvenWhenTheLaterSourceHasNoEntries()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        const string duplicate =
            "  - source_id: fixture-source\n"
            + "    path: docs/CONTRIBUTING.md\n"
            + "    atomizer: none\n"
            + "    entries: []\n"
            + "ticket_index:\n";
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"].Replace(
            "ticket_index:\n",
            duplicate,
            StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("duplicate source_id", StringComparison.Ordinal));
        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("must contain at least one atomic entry", StringComparison.Ordinal));
    }

    [Fact]
    public void Cf2RenameReportsBothProtectedOldPathAndNewPath()
    {
        using var repository = new TemporaryDirectory();
        RunGit(repository.Path, "init");
        RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        var oldPath = Path.Combine(repository.Path, "Meta", "StrataLint", "Gate.txt");
        Directory.CreateDirectory(
            Path.GetDirectoryName(oldPath)
                ?? throw new InvalidOperationException("protected fixture path has no parent"));
        File.WriteAllText(oldPath, "protected\n", new UTF8Encoding(false));
        RunGit(repository.Path, "add", ".");
        RunGit(repository.Path, "commit", "-m", "baseline");
        var baseline = RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        Directory.CreateDirectory(Path.Combine(repository.Path, "notes"));
        RunGit(repository.Path, "mv", "Meta/StrataLint/Gate.txt", "notes/Gate.txt");

        var prepared = new GitRepositoryGateway(repository.Path).Prepare(baseline);

        Assert.Contains(prepared.Changes.Paths, path => path.Value == "Meta/StrataLint/Gate.txt");
        Assert.Contains(prepared.Changes.Paths, path => path.Value == "notes/Gate.txt");
        var review = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(
            BootstrapGate.Evaluate(prepared.Changes));
        Assert.Contains(review.ChangeSet.Paths, path => path.Value == "Meta/StrataLint/Gate.txt");
    }

    [Theory]
    [InlineData("Evidence/D5/S0/Carrier/Probe.result.toml")]
    [InlineData("Evidence/D5/S0/Carrier/Probe.spec.json")]
    public void Cf3ReversePathValidationRejectsRegistryUnknownKindOrSelector(string path)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = "{}\n";
        var context = fixture.BuildForRuleCompatibility();

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context));
        var diagnostic = Assert.Single(completed.Capability.Diagnostics, item => item.Path == path);
        Assert.Equal(RuleId.CreateKnown(15), diagnostic.RuleId);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);

        var policy = AcceptedPolicy(TestRegistry.Canonical);
        var canonical = RepositoryCanonicalizer.Validate(context.Current, policy);
        Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(canonical);
    }

    [Fact]
    public void Cf4Sl019ScansResidualScalarAfterAValidEmbeddedObject()
    {
        var fixture = new RuleFixture();
        const string path = "Evidence/D5/S0/Carrier/Mixed.run.json";
        fixture.Files[path] = "{\"payload\": \"prefix {\\\"note\\\":\\\"ok\\\"} anomaly tail\"}\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), fixture.Build());

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Path == path);
        Assert.Contains("unknown anomaly-bearing schema at $.payload", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("extension-table/6.38\u2032", false)]
    [InlineData("unresolved tension", true)]
    public void Sl019DistinguishesExtensionLocatorFromTensionSignal(
        string value,
        bool expectsDiagnostic)
    {
        var fixture = new RuleFixture();
        const string path = "Evidence/D5/S0/Carrier/Locator.run.json";
        fixture.Files[path] = "{\"ast_path\":\"" + value + "\"}\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), fixture.Build());

        Assert.Equal(
            expectsDiagnostic,
            evaluation.Diagnostics.Any(item => item.Path == path));
    }

    [Theory]
    [InlineData(
        "Evidence/D5/S0/Carrier/Canonical.run.json",
        "{\"alpha\": 1, \"omega\": 2}\n",
        "{\"alpha\":1,\"omega\":2}\n")]
    [InlineData(
        "Evidence/D5/S0/Carrier/Canonical.run.yaml",
        "alpha: 1\nomega: 2\n",
        "alpha:  1\nomega: 2\n")]
    public void Cf5CanonicalizationComparesRawStructuredBytes(
        string path,
        string canonicalBytes,
        string noncanonicalBytes)
    {
        var fixture = new RuleFixture();
        var policy = AcceptedPolicy(TestRegistry.Canonical);
        fixture.Files[path] = canonicalBytes;
        var canonicalSnapshot = fixture.BuildForRuleCompatibility().Current;
        Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(canonicalSnapshot, policy));

        fixture.Files[path] = noncanonicalBytes;
        var noncanonicalSnapshot = fixture.BuildForRuleCompatibility().Current;
        var rejected = RepositoryCanonicalizer.Validate(noncanonicalSnapshot, policy);

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(rejected);
        Assert.Contains("canonical", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void Cf6ProductionRouteRejectsDomainMissingFromDomainsYaml()
    {
        using var repository = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(repository.Path, "Meta"));
        File.WriteAllText(
            Path.Combine(repository.Path, "Meta", "registry.yaml"),
            TestRegistry.Canonical,
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "Meta", "domains.yaml"),
            "domains:\n  Conventions:\n    stratum: S0\n    definition: Fixture.\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "manifest.json"),
            "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\",\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"tag\":\"\",\"theory\":\"D5\"}\n",
            new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            repository.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.False(result.Success);
        Assert.Contains("controlled domain", result.Error, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void Cf7UnknownLeanAxiomIsSl020BlockInsteadOfInfrastructureFailure()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var baselineReport = LeanAxiomReport.Create(fixture.BaselineReports);
        fixture.SetRingDeclaration("invented", "theorem", "unregistered.axiom");
        var currentReport = LeanAxiomReport.Create(fixture.Reports);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.BlueprintPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));
        var candidateReportPath = Path.Combine(temporary.Path, "candidate.json");
        var baselineReportPath = Path.Combine(temporary.Path, "baseline.json");
        File.WriteAllBytes(
            candidateReportPath,
            RawLeanReportArtifact.Write(
                Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                    SnapshotDecoder.Decode(Snapshot(fixture.Files))).Snapshot,
                currentReport).AsSpan());
        File.WriteAllBytes(
            baselineReportPath,
            RawLeanReportArtifact.Write(
                Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                    SnapshotDecoder.Decode(Snapshot(fixture.Baseline))).Snapshot,
                baselineReport).AsSpan());

        var outcome = environment.Check(new[]
        {
            "--candidate-lean-report", candidateReportPath,
            "--baseline-lean-report", baselineReportPath,
        });

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics,
            item => item.RuleId == RuleId.CreateKnown(20)
                && item.Message.Contains("unregistered.axiom", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Fact]
    public void Cf8ClosedWorldShapeFailuresKeepSl000DiagnosticCode()
    {
        Assert.True(RuleId.TryCreate("SL-000", out var sl000));
        var fixture = new RuleFixture();
        fixture.Files["rogue.txt"] = "unknown\n";

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.BuildForRuleCompatibility()));

        var diagnostic = Assert.Single(completed.Capability.Diagnostics, item => item.Path == "rogue.txt");
        Assert.Equal(sl000, diagnostic.RuleId);
        Assert.Equal("unknown top-level artifact", diagnostic.Message);
    }

    [Fact]
    public void Cf9BackfillProtectedPathMembershipComesFromRegistry()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var source = Assert.Single(BackfillInventoryLoader
            .Load(fixture.Files["Meta/BACKFILL.yaml"])
            .RequireDigestionSources());
        var registryWithoutSource = TestRegistry.Canonical.Replace(
            $"  - \"{source.SourcePath}\"\n",
            string.Empty,
            StringComparison.Ordinal);
        var policy = AcceptedPolicy(registryWithoutSource);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build(policy));

        Assert.Contains(
            evaluation.Diagnostics,
            item => item.Message.Contains(
                $"source {source.SourceId} has an invalid governance path",
                StringComparison.Ordinal));
        var enginePath = Directory.EnumerateFiles(
            Path.Combine(FindRepositoryRoot(), "Meta", "StrataLint", "StrataLint.Engine"),
            "BackfillInventoryRule.cs",
            SearchOption.AllDirectories).Single();
        var engineSource = File.ReadAllText(enginePath, Encoding.UTF8);
        Assert.DoesNotContain(source.SourcePath, engineSource, StringComparison.Ordinal);
    }

    [Fact]
    public void Cf10WorkflowSeparatesLeanInspectionFromDotnetAdmission()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(
            Path.Combine(root, ".github", "workflows", "ci.yml"),
            Encoding.UTF8);
        var gate = File.ReadAllText(
            Path.Combine(root, ".github", "scripts", "harness-gate.sh"),
            Encoding.UTF8);
        var producer = File.ReadAllText(
            Path.Combine(root, "Meta", "StrataLint", "lean-inspector", "inspect.sh"),
            Encoding.UTF8);
        var inspectJob = workflow[
            workflow.IndexOf("  lean-inspect:", StringComparison.Ordinal)..workflow.IndexOf("  baseline-admission:", StringComparison.Ordinal)];
        var baselineJob = workflow[workflow.IndexOf("  baseline-admission:", StringComparison.Ordinal)..];

        Assert.Contains("exe cache get", producer, StringComparison.Ordinal);
        Assert.Contains("build", producer, StringComparison.Ordinal);
        Assert.Contains("env", producer, StringComparison.Ordinal);
        Assert.Contains("lean", producer, StringComparison.Ordinal);
        Assert.Contains("--run", producer, StringComparison.Ordinal);
        Assert.Contains("stdout.log", producer, StringComparison.Ordinal);
        Assert.Contains("stderr.log", producer, StringComparison.Ordinal);
        Assert.Contains("cat", producer, StringComparison.Ordinal);
        Assert.DoesNotContain("tail -", producer, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("actions/upload-artifact", inspectJob, StringComparison.Ordinal);
        Assert.Contains("candidate-lean-report.json", inspectJob, StringComparison.Ordinal);
        Assert.Contains("baseline-lean-report.json", inspectJob, StringComparison.Ordinal);

        Assert.Contains("needs: lean-inspect", baselineJob, StringComparison.Ordinal);
        Assert.Contains("actions/download-artifact", baselineJob, StringComparison.Ordinal);
        Assert.Contains("harness-gate.sh", baselineJob, StringComparison.Ordinal);
        Assert.Contains("baseline/.github/scripts/harness-gate.sh", baselineJob, StringComparison.Ordinal);
        Assert.DoesNotContain("baseline-admission.sh", baselineJob, StringComparison.Ordinal);
        Assert.Contains("--candidate", baselineJob, StringComparison.Ordinal);
        Assert.Contains("--judge-root", baselineJob, StringComparison.Ordinal);
        Assert.Contains("--base", baselineJob, StringComparison.Ordinal);
        Assert.Contains("--candidate-lean-report", baselineJob, StringComparison.Ordinal);
        Assert.Contains("--baseline-lean-report", baselineJob, StringComparison.Ordinal);
        Assert.DoesNotContain("--legacy-bootstrap", baselineJob, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet build", baselineJob, StringComparison.Ordinal);
        Assert.DoesNotContain(" selftest", baselineJob, StringComparison.Ordinal);
        Assert.DoesNotContain(".lake", baselineJob, StringComparison.Ordinal);
        Assert.DoesNotContain("elan", baselineJob, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("lake build", baselineJob, StringComparison.Ordinal);

        Assert.Contains("set -euo pipefail", gate, StringComparison.Ordinal);
        Assert.Contains("check --protected-base", gate, StringComparison.Ordinal);
        Assert.Contains("--candidate-lean-report", gate, StringComparison.Ordinal);
        Assert.Contains("--baseline-lean-report", gate, StringComparison.Ordinal);
        Assert.DoesNotContain("--legacy-bootstrap", gate, StringComparison.Ordinal);
        Assert.Contains("verify-conservative", gate, StringComparison.Ordinal);
        Assert.True(Count(gate, " selftest") >= 2, "selftest must run twice in the shared gate");
        Assert.Contains("cmp", gate, StringComparison.Ordinal);
        Assert.DoesNotContain("LAKE", gate, StringComparison.Ordinal);
        Assert.DoesNotContain("elan", gate, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("tail -", workflow, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("Tail(", workflow + gate + producer, StringComparison.Ordinal);
    }

}
