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
    public void Sl016RejectsCasBackedLiveReceiptWithoutItsSourceVolume()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes(
            RuleFixture.FixtureDigestionSource));
        fixture.Files[RuleFixture.FixtureBackfillSourcePath] = fixture.Files[
                RuleFixture.FixtureBackfillSourcePath]
            .Replace(
                $"atomizer = \"{AtomizerRegistry.NoAtomizerId}\"",
                $"atomizer = \"{SyntheticNumberedAtomizer.Id}\"",
                StringComparison.Ordinal);
        fixture.Files[captured.RelativePath] = RuleFixture.FixtureDigestionSource;
        fixture.Files.Remove(RuleFixture.FixtureDigestionSourcePath);
        Assert.Equal(
            captured.Reference,
            Assert.Single(BackfillInventoryLoader.Load(
                fixture.Build().Current).RequireDigestionEntries()).CasRef);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("source path is dangling", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016StillRejectsMissingNoAtomizerSourceAfterCasMigration()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files.Remove(RuleFixture.FixtureDigestionSourcePath);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic => diagnostic.Message.Contains(
            $"source path is dangling: {RuleFixture.FixtureDigestionSourcePath}",
            StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsReceiptWithoutCasRefAtLoaderBoundary()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[
                RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                $"cas_ref: {RuleFixture.FixtureCasReference}\n",
                string.Empty,
                StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic => diagnostic.Message.Contains(
            "source fixture-source entry keys are not canonical",
            StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016AdmissionAndReportFreeShareInvalidSourceIdValidation()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var source = fixture.Files[RuleFixture.FixtureBackfillSourcePath]
            .Replace("source_id = \"fixture-source\"", "source_id = \"INVALID\"", StringComparison.Ordinal);
        var atom = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        fixture.Files.Remove(RuleFixture.FixtureBackfillSourcePath);
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        var invalidSourcePath = RuleFixture.FixtureBackfillSourcePath.Replace(
            "/fixture-source/",
            "/INVALID/",
            StringComparison.Ordinal);
        var invalidAtomPath = RuleFixture.FixtureBackfillAtomPath.Replace(
            "/fixture-source/",
            "/INVALID/",
            StringComparison.Ordinal);
        fixture.Files[invalidSourcePath] = source;
        fixture.Files[invalidAtomPath] = atom;

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build(RawChangeSet.Create([
                RuleFixture.FixtureBackfillSourcePath,
                RuleFixture.FixtureBackfillAtomPath,
                invalidSourcePath,
                invalidAtomPath,
            ])));

        Assert.Contains(evaluation.Diagnostics, diagnostic => diagnostic.Message.Contains(
            "invalid source_id: INVALID",
            StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsDeletingABaselineCasBlob()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files.Remove(RuleFixture.FixtureCasPath);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic => diagnostic.Message.Contains(
            $"baseline CAS blob was deleted: {RuleFixture.FixtureCasPath}",
            StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsHandwrittenDigestionStatusThatDisagreesWithDerivation()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var atom = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        fixture.Files[$"{BackfillInventoryLoader.RootPath}fixture-source/absorbed-closed/fixture-atom.yaml"] = atom;

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsFormattedFingerprintThatDisagreesWithSourceSpan()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var document = BackfillInventoryLoader.Load(fixture.Build().Current);
        var fingerprint = document.RequireDigestionEntries()[0].Fingerprints.RawSha256;
        var replacement = fingerprint[..^1] + (fingerprint[^1] == '0' ? '1' : '0');
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[
                RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                fingerprint,
                replacement,
                StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("CAS blob is missing", StringComparison.Ordinal)
            && diagnostic.Message.Contains(replacement["sha256:".Length..], StringComparison.Ordinal));
    }

    [Fact]
    public void Sl016RejectsSourceIdThatDoesNotMatchItsDirectory()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[$"{BackfillInventoryLoader.RootPath}different-directory/source.toml"] =
            fixture.Files[RuleFixture.FixtureBackfillSourcePath];

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build());

        Assert.Contains(evaluation.Diagnostics, diagnostic =>
            diagnostic.Message.Contains("source metadata path disagrees with source_id", StringComparison.Ordinal));
    }

    [Fact]
    public void Cf2RenameReportsBothProtectedOldPathAndNewPath()
    {
        using var repository = new TemporaryDirectory();
        RunGit(repository.Path, "init");
        RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        var oldPath = Path.Combine(repository.Path, "tools", "Gate.txt");
        Directory.CreateDirectory(
            Path.GetDirectoryName(oldPath)
                ?? throw new InvalidOperationException("protected fixture path has no parent"));
        File.WriteAllText(oldPath, "protected\n", new UTF8Encoding(false));
        RunGit(repository.Path, "add", ".");
        RunGit(repository.Path, "commit", "-m", "baseline");
        var baseline = RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        Directory.CreateDirectory(Path.Combine(repository.Path, "notes"));
        RunGit(repository.Path, "mv", "tools/Gate.txt", "notes/Gate.txt");

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
        RunGit(repository.Path, "init");
        RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(
            Path.Combine(repository.Path, "source.txt"),
            "copy source\n",
            new UTF8Encoding(false));
        RunGit(repository.Path, "add", ".");
        RunGit(repository.Path, "commit", "-m", "baseline");
        var baseline = RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        File.Copy(
            Path.Combine(repository.Path, "source.txt"),
            Path.Combine(repository.Path, "copy-one.txt"));
        File.Copy(
            Path.Combine(repository.Path, "source.txt"),
            Path.Combine(repository.Path, "copy-two.txt"));
        RunGit(repository.Path, "add", ".");
        RunGit(repository.Path, "commit", "-m", "candidate");

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

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Path == path);
        Assert.Contains("unknown anomaly-bearing schema at $.payload", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "subject: failure")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "subject: anomaly")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "subject: unresolved tension")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "subject: row//failure")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "status: failure")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "payload: tension")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "payload: failure/report")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "x.subject: failure/report")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/atom.yaml", "outer:\n  subject: failure/report")]
    [InlineData("Meta/Digestion/backfill/interface-v1/not-a-state/rogue.yaml", "subject: failure/report")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/deep/rogue.yaml", "subject: anomaly/v1")]
    [InlineData("Meta/Digestion/backfill/interface-v1/residual-open/rogue.yml", "subject: failure/open")]
    [InlineData("Evidence/D5/S0/Carrier/Field.run.json", "{\"subject\":\"failure/report\"}")]
    [InlineData("Evidence/D5/S0/Carrier/Field.run.json", "{\"status\":\"failure/open\"}")]
    [InlineData("Evidence/D5/S0/Carrier/Field.run.json", "{\"note\":\"anomaly/v1\"}")]
    public void Sl019ReportsEveryResidueOutsideADeclaredDigestionAddress(
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
    public void Sl019AcceptsInventoryCoverageAndReceiptGidsWhoseSubjectIsNamedAfterAFailure()
    {
        var fixture = new RuleFixture();
        const string path = "Meta/Digestion/backfill/interface-v1/absorbed-closed/probe.yaml";
        const string gid =
            "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure"
            + ".lookup_copy_zero_loss_and_nonanticipating_failure";
        fixture.Files[path] = "cas_ref: sha256:00\n"
            + "coverage_gids:\n  - " + gid + "\n"
            + "receipts:\n"
            + "  coverage:\n"
            + "    - gid: " + gid + "\n"
            + "      source_sha256: sha256:00\n"
            + "      target_statement_id: sha256:00\n"
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

    [Theory]
    [InlineData("coverage_gids:\n  - unresolved failure without case\n")]
    [InlineData("receipts:\n  coverage:\n    - gid: FiniteFailure\n")]
    [InlineData("failure_gids:\n  - D5/S0/Carrier/ProbeFailure.failure_probe\n")]
    [InlineData("outer:\n  coverage_gids:\n    - D5/S0/Carrier/ProbeFailure.failure_probe\n")]
    public void Sl019RejectsAnomalyResiduesOutsideTheDeclaredInventoryGidSlots(string body)
    {
        var fixture = new RuleFixture();
        const string path = "Meta/Digestion/backfill/interface-v1/absorbed-closed/rogue.yaml";
        fixture.Files[path] = "cas_ref: sha256:00\n" + body;

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.Contains(
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
            "{\"coverage_gids\":[\"D5/S0/Carrier/ProbeFailure.failure_probe\"]}\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.Contains(
            evaluation.Diagnostics,
            item => item.Path == path && item.Message.Contains(
                "anomaly-bearing", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl019StillReportsADigestionAddressWhoseResidueCarriesASerializedRecordKey()
    {
        var fixture = new RuleFixture();
        const string path = "Meta/Digestion/backfill/interface-v1/residual-open/record.yaml";
        fixture.Files[path] = "subject: 'row/failure\"kind\":x'\n";

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));

        Assert.Contains(
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
        Assert.Equal("unknown top-level artifact", diagnostic.Message);
    }

    [Fact]
    public void FormalizationReceiptResidenceIsClosedWorldCanonical()
    {
        Assert.True(RuleId.TryCreate("SL-000", out var sl000));
        var canonical =
            "Meta/Digestion/formalizations/sample-residual-"
            + new string('a', 64) + ".v1.json";
        var fixture = new RuleFixture();
        fixture.Files[canonical] = "{}\n";
        fixture.Files["Meta/Digestion/formalizations/BAD.v1.json"] = "{}\n";

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(
                fixture.Build(RawChangeSet.Create(["Meta/Digestion/formalizations/BAD.v1.json"]))));

        Assert.DoesNotContain(
            completed.Capability.Diagnostics,
            item => item.Path == canonical && item.RuleId == sl000);
        var rejected = Assert.Single(
            completed.Capability.Diagnostics,
            item => item.Path == "Meta/Digestion/formalizations/BAD.v1.json");
        Assert.Equal(sl000, rejected.RuleId);
        Assert.Equal("unknown Meta artifact", rejected.Message);
    }

    [Fact]
    public void Cf9BackfillProtectedPathMembershipComesFromRegistry()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var source = Assert.Single(BackfillInventoryLoader
            .Load(fixture.Build().Current)
            .RequireDigestionSources());
        var registryWithoutSource = TestRegistry.Canonical.Replace(
            $"  - \"{source.SourcePath}\"\n",
            string.Empty,
            StringComparison.Ordinal);
        var policy = AcceptedPolicy(registryWithoutSource);

        var evaluation = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), fixture.Build(policy));

        // Registering a new theory volume hits this before anything else, so the verdict
        // has to name the file and field that fix it, not only what is wrong.
        var diagnostic = Assert.Single(
            evaluation.Diagnostics,
            item => item.Message.Contains(
                $"source {source.SourceId} has an invalid governance path",
                StringComparison.Ordinal));
        Assert.Contains(source.SourcePath, diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("Meta/registry.yaml", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("governance_documents", diagnostic.Message, StringComparison.Ordinal);
        var enginePath = Directory.EnumerateFiles(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "StrataLint.Engine"),
            "BackfillInventoryRule.cs",
            SearchOption.AllDirectories).Single();
        var engineSource = File.ReadAllText(enginePath, Encoding.UTF8);
        Assert.DoesNotContain(source.SourcePath, engineSource, StringComparison.Ordinal);

        // The CAS pass rehashes every tracked blob. SL-016 admission used to run it twice on the
        // same tree: once in this rule and once inside the alignment pass it calls. The second run
        // could only reproduce the first one's verdict, so the first result is threaded down the
        // chain instead. DigestionCasStoreTests keeps pinning what the pass itself rejects; this
        // pins the shape of the chain that carries its result.
        //
        // These assertions live inside this test because Cf9 already reads
        // BackfillInventoryRule.cs, so they extend a read that is already paid for. Unknown
        // repository-read debt is now charged to the candidate that introduces a method identity
        // after its fork point; the repository-wide tolerance net remains separate.
        var casChainSource = engineSource
            + File.ReadAllText(
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "StrataLint.Engine", "Digestion", "DigestionLedgerAligner.cs"),
                Encoding.UTF8)
            + File.ReadAllText(
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "StrataLint.Engine", "Digestion", "Evaluation", "DigestionStatusEvaluator.cs"),
                Encoding.UTF8);
        Assert.Equal(1, Count(casChainSource, "var casEvaluation = DigestionCasStore.Evaluate("));
        Assert.DoesNotContain("var cas = DigestionCasStore.Evaluate(", casChainSource, StringComparison.Ordinal);
        Assert.Equal(2, Count(casChainSource, "casEvaluation: casEvaluation"));
    }

}
