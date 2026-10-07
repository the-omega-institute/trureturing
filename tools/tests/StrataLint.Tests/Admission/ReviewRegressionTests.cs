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
    public void Cf2RenameReportsBothProtectedOldPathAndNewPath()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        TestGit.Run(repository.Path, "config", "user.email", "stratalint@example.invalid");
        TestGit.Run(repository.Path, "config", "user.name", "StrataLint Tests");
        var oldPath = Path.Combine(repository.Path, "tools", "Gate.txt");
        Directory.CreateDirectory(
            Path.GetDirectoryName(oldPath)
                ?? throw new InvalidOperationException("protected fixture path has no parent"));
        File.WriteAllText(oldPath, "protected\n", new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "baseline");
        var baseline = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        Directory.CreateDirectory(Path.Combine(repository.Path, "notes"));
        TestGit.Run(repository.Path, "mv", "tools/Gate.txt", "notes/Gate.txt");

        var prepared = new GitRepositoryGateway(repository.Path).Prepare(baseline);

        Assert.Contains(prepared.Changes.Paths, path => path.Value == "tools/Gate.txt");
        Assert.Contains(prepared.Changes.Paths, path => path.Value == "notes/Gate.txt");
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "tools/Gate.txt"
            && change.Kind == RawChangeKind.Deleted);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "notes/Gate.txt"
            && change.Kind == RawChangeKind.Added);
        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(
            BootstrapGate.Evaluate(prepared.Changes));
        Assert.Contains(verification.ChangeSet.Paths, path => path.Value == "tools/Gate.txt");
    }

    [Fact]
    public void Cf2MultipleCopiesFromOneSourceProduceOneSourceChange()
    {
        using var repository = new TemporaryDirectory();
        TestGit.Run(repository.Path, "init");
        TestGit.Run(repository.Path, "config", "user.email", "stratalint@example.invalid");
        TestGit.Run(repository.Path, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(
            Path.Combine(repository.Path, "source.txt"),
            "copy source\n",
            new UTF8Encoding(false));
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "baseline");
        var baseline = TestGit.Run(repository.Path, "rev-parse", "HEAD").Trim();
        File.Copy(
            Path.Combine(repository.Path, "source.txt"),
            Path.Combine(repository.Path, "copy-one.txt"));
        File.Copy(
            Path.Combine(repository.Path, "source.txt"),
            Path.Combine(repository.Path, "copy-two.txt"));
        TestGit.Run(repository.Path, "add", ".");
        TestGit.Run(repository.Path, "commit", "-m", "candidate");

        var prepared = new GitRepositoryGateway(repository.Path).Prepare(baseline);

        var source = Assert.Single(
            prepared.Changes.Entries,
            change => change.Path.Value == "source.txt");
        Assert.Equal(RawChangeKind.Copied, source.Kind);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "copy-one.txt" && change.Kind == RawChangeKind.Added);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "copy-two.txt" && change.Kind == RawChangeKind.Added);
    }

    [Theory]
    [InlineData("Evidence/D5/S0/Carrier/Probe.result.toml")]
    [InlineData("Evidence/D5/S0/Carrier/Probe.spec.json")]
    public void Cf3ReversePathValidationRejectsRegistryUnknownKindOrSelector(string path)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = "{}\n";
        var context = fixture.Build(RawChangeSet.Create([path]));

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context));
        var diagnostic = Assert.Single(completed.Capability.Diagnostics, item => item.Path == path);
        Assert.Equal(RuleId.CreateKnown(15), diagnostic.RuleId);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);

        var policy = AcceptedPolicy(TestFileMap.Canonical);
        var canonical = RepositoryCanonicalizer.Validate(context.Current, policy);
        Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(canonical);
    }

    [Fact]
    public void Cf4Sl019ScansResidualScalarAfterAValidEmbeddedObject()
    {
        var fixture = new RuleFixture();
        const string path = "Evidence/D5/S0/Carrier/Mixed.run.json";
        fixture.Files[path] = "{\"payload\": \"prefix {\\\"note\\\":\\\"ok\\\"} anomaly tail\"}\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Path == path);
        Assert.Contains("unknown anomaly-bearing schema at $.payload", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Evidence/D5/S0/Carrier/Field.run.json", "{\"subject\":\"failure/report\"}")]
    [InlineData("Evidence/D5/S0/Carrier/Field.run.json", "{\"status\":\"failure/open\"}")]
    [InlineData("Evidence/D5/S0/Carrier/Field.run.json", "{\"note\":\"anomaly/v1\"}")]
    public void Sl019ReportsAnomalyResidueInStructuredEvidence(
        string path,
        string content)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = content + "\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.Contains(
            evaluation.Diagnostics,
            item => item.Path == path && item.Message.Contains(
                "unknown anomaly-bearing schema", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl019AcceptsInventoryCoverageAndScribeGidsWhoseSubjectIsNamedAfterAFailure()
    {
        var fixture = new RuleFixture();
        const string path = "Meta/Digestion/backfill/interface-v1/absorbed-closed/probe.yaml";
        const string gid =
            "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure"
            + ".lookup_copy_zero_loss_and_nonanticipating_failure";
        fixture.Files[path] = "cas_ref: sha256:00\n"
            + "coverage_gids:\n"
            + "  - gid: " + gid + "\n"
            + "    target_statement_id: sha256:00\n"
            + "receipts:\n"
            + "  scribe:\n"
            + "    - gid: " + gid + "\n"
            + "      definition_sha256: sha256:00\n"
            + "      emission_sha256: sha256:00\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.DoesNotContain(
            evaluation.Diagnostics,
            item => item.Path == path && item.Message.Contains(
                "anomaly-bearing", StringComparison.Ordinal));
    }

    public static TheoryData<string> InvalidInventoryGidSlots => new()
    {
        "coverage_" + "gids:\n  - unresolved failure without case\n",
        "receipts:\n  coverage:\n    - gid: FiniteFailure\n",
        "receipts:\n  coverage:\n    - gid: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.lookup_copy_zero_loss_and_nonanticipating_failure\n",
        "failure_gids:\n  - D5/S0/Carrier/ProbeFailure.failure_probe\n",
        "outer:\n  coverage_" + "gids:\n    - D5/S0/Carrier/ProbeFailure.failure_probe\n",
    };

    [Theory]
    [MemberData(nameof(InvalidInventoryGidSlots))]
    public void Sl019LeavesAuxiliaryInventoryResiduesToTargetCommands(string body)
    {
        var fixture = new RuleFixture();
        const string path = "Meta/Digestion/backfill/interface-v1/absorbed-closed/rogue.yaml";
        fixture.Files[path] = "cas_ref: sha256:00\n" + body;

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.DoesNotContain(
            evaluation.Diagnostics,
            item => item.Path == path && item.Message.Contains(
                "anomaly-bearing", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl019RejectsAValidGidInInventorySlotsOutsideACanonicalInventoryPath()
    {
        var fixture = new RuleFixture();
        const string path = "Evidence/D5/S0/Carrier/Inventory.run.json";
        fixture.Files[path] =
            "{\"coverage_" + "gids\":[\"D5/S0/Carrier/ProbeFailure.failure_probe\"]}\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.Contains(
            evaluation.Diagnostics,
            item => item.Path == path && item.Message.Contains(
                "anomaly-bearing", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl019SkipsAuxiliaryDigestionRecordStrings()
    {
        var fixture = new RuleFixture();
        const string path = "Meta/Digestion/backfill/interface-v1/residual-open/record.yaml";
        fixture.Files[path] = "subject: 'row/failure\"kind\":x'\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.DoesNotContain(
            evaluation.Diagnostics,
            item => item.Path == path && item.Message.Contains(
                "unknown anomaly-bearing schema at $.subject", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("extension-table/6.38\u2032", false)]
    [InlineData("row/adaptive-submodularity-failure-witness", true)]
    [InlineData("unresolved tension", true)]
    public void Sl019DistinguishesExtensionLocatorFromTensionSignal(
        string value,
        bool expectsDiagnostic)
    {
        var fixture = new RuleFixture();
        const string path = "Evidence/D5/S0/Carrier/Signal.run.json";
        fixture.Files[path] = "{\"subject\":\"" + value + "\"}\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

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
        var policy = AcceptedPolicy(TestFileMap.Canonical);
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
            Path.Combine(repository.Path, "Meta", "FILEMAP.toml"),
            TestFileMap.Canonical,
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
        ProductionEnvironmentTests.InstallDefaultAdmissionPlaneFileMap(fixture);
        fixture.SetRingDeclaration("invented", "theorem", "unregistered.axiom");
        var currentReport = LeanAxiomReport.Create(fixture.Reports);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.RingPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));
        var candidateReportPath = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReportPath,
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(Snapshot(fixture.Files))).Snapshot,
            currentReport);
        var outcome = environment.Check(new[]
        {
            "--candidate-lean-report", candidateReportPath,
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
            RuleCatalog.Default.Execute(
                fixture.Build(RawChangeSet.Create(["rogue.txt"]))));

        var diagnostic = Assert.Single(completed.Capability.Diagnostics, item => item.Path == "rogue.txt");
        Assert.Equal(sl000, diagnostic.RuleId);
        Assert.Equal("path must match exactly one FILEMAP entry; matches=0", diagnostic.Message);
    }

}
