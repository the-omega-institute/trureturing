using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void DigestStatusUnrelatedDeltaDoesNotReplayHistoricalCoverageReceipt()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment(
            RawChangeSet.Create(["notes/r16-unrelated.txt"]));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("coverage-receipt-mismatch", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusChangedTargetStillValidatesHistoricalCoverageReceipt()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment(
            RawChangeSet.Create(["D5/S0/Carrier/BackfillTarget.lean"]));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusImplementationChangeStillValidatesHistoricalCoverageReceipt()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment(
            RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.cs"]));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusWithoutBaseUnrelatedDeltaDoesNotReplayHistoricalCoverageReceipt()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment(
            RawChangeSet.Create(["notes/r17-unrelated-coverage.txt"]));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("coverage-receipt-mismatch", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusWithoutBaseChangedTargetStillValidatesHistoricalCoverageReceipt()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment(
            RawChangeSet.Create(["D5/S0/Carrier/BackfillTarget.lean"]));

        var result = environment.DigestStatus(["--json"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusWithoutBaseImplementationChangeStillValidatesHistoricalCoverageReceipt()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment(
            RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.cs"]));

        var result = environment.DigestStatus(["--json"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReportsCasSeenAcrossNormalizedSourceRewrite()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var ledgerBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\r\n\r\n**定理 1.1(Test)**。claim。\r\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, ledgerBytes, DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[RuleFixture.FixtureBackfillSourcePath] =
            $"source_id = \"fixture-source\"\n"
            + $"path = \"{RuleFixture.FixtureDigestionSourcePath}\"\n"
            + $"atomizer = \"{atomizerId}\"\n"
            + "genre_registry_check = \"collected\"\n"
            + "unregistered_genres = []\n";
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        fixture.Files[$"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/normalized-receipt.yaml"] = $$"""
            ast_path: {{atom.AstPath}}
            fingerprints:
              raw_sha256: {{atom.Fingerprints.RawSha256}}
              normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
            cas_ref: {{captured.Reference}}
            coverage_gids: []
            receipts:
              coverage: []
              scribe: []
              unresolved_subitems: []
              chain_atoms: []
              tail_authorization: null
            """;
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"alignment\": \"seen\"", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("normalized-seen-not-deletable", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"deletable\": false", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReadsTheDirectoryFormDigestionLedger()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"entries_total\": 1", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"atom_id\": \"fixture-atom\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReportsEveryEntryAndZeroCurrentlyDeletable()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"entries_total\": 1", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"deletable_now\": 0", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"atom_id\": \"fixture-atom\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"code\": \"boundary-not-reproducible\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusResidualSummaryUsesMachineDerivedUnresolvedSubitemGaps()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[
                RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                "  unresolved_subitems: []",
                "  unresolved_subitems:\n    - zeta-residual\n    - alpha-residual",
                StringComparison.Ordinal);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--residual-summary"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("- unresolved_subitems: 2", result.Output, StringComparison.Ordinal);
        Assert.Contains("- mother_residual_atom_ids: 1", result.Output, StringComparison.Ordinal);
        Assert.Contains("- `fixture-atom` (2)", result.Output, StringComparison.Ordinal);
        Assert.True(
            result.Output.IndexOf("`alpha-residual`", StringComparison.Ordinal)
                < result.Output.IndexOf("`zeta-residual`", StringComparison.Ordinal));
        Assert.DoesNotContain("boundary-not-reproducible", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReportsHistoricalCasReceiptAsStaleAndCurrentReceiptAsSeen()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var baselineLedger = IngestLedger(atomizerId, oldAtom);
        var baselineDocument = baselineLedger;
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var planningSnapshot = Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [TheoryAtomizerDataLoader.DataPath] = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes),
            [RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes),
            [oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan()),
        }));
        var plan = DigestionIngestor.Plan(baselineDocument, planningSnapshot, baselineDocument);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, plan.Document);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baselineLedger);
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        fixture.Baseline[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        foreach (var item in plan.CasObjects)
        {
            fixture.Files[item.RelativePath] = Encoding.UTF8.GetString(item.Bytes.AsSpan());
        }

        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var entries = json.RootElement.GetProperty("entries").EnumerateArray().ToArray();
        var historical = Assert.Single(
            entries,
            static entry => entry.GetProperty("atom_id").GetString() == "old-receipt");
        var current = Assert.Single(
            entries,
            static entry => entry.GetProperty("atom_id").GetString() != "old-receipt");
        Assert.Equal("stale", historical.GetProperty("alignment").GetString());
        Assert.Equal("seen", current.GetProperty("alignment").GetString());
        Assert.Contains(
            historical.GetProperty("gaps").EnumerateArray(),
            static gap => gap.GetProperty("code").GetString() == "stale-receipt-not-deletable");
    }

    [Fact]
    public void DigestStatusDiffDoesNotRequireBaselineGenreProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        DowngradeBaselineGenreMarkerSchema(fixture);
        var environment = DigestStatusEnvironment(fixture);

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void DigestStatusUnrelatedDeltaDoesNotValidateDiscardedBaselineGenreProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Baseline[RuleFixture.FixtureBackfillSourcePath] = fixture.Baseline[
                RuleFixture.FixtureBackfillSourcePath]
            .Replace(
                "genre_registry_check = \"no-registry\"",
                "genre_registry_check = \"invalid-historical-value\"",
                StringComparison.Ordinal);
        var environment = DigestStatusEnvironment(
            fixture,
            RawChangeSet.Create(["notes/r17-unrelated-genre.txt"]));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void DigestStatusChangedSourceMetadataStillValidatesCandidateGenreProjection()
    {
        var fixture = CandidateFixtureWithInvalidGenreProjection();
        var environment = DigestStatusEnvironment(
            fixture,
            RawChangeSet.Create([RuleFixture.FixtureBackfillSourcePath]));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("invalid genre_registry_check", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusImplementationChangeStillValidatesCandidateGenreProjection()
    {
        var fixture = CandidateFixtureWithInvalidGenreProjection();
        var environment = DigestStatusEnvironment(
            fixture,
            RawChangeSet.Create(
            ["tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryLoader.Parsing.cs"]));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("invalid genre_registry_check", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void FormalizeCandidatesDiffDoesNotRequireBaselineGenreProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        DowngradeBaselineGenreMarkerSchema(fixture);
        var environment = DigestStatusEnvironment(fixture);

        var result = environment.DigestStatus(["--formalize-candidates", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void ResidualShardDiffDoesNotRequireBaselineGenreProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        DowngradeBaselineGenreMarkerSchema(fixture);
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));

        var shards = DigestStatusCommand.RenderShards(
            repository,
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty),
            "baseline");

        Assert.Contains("Generated/echo-residuals/fixture-source.md", shards.Keys);
    }

    [Fact]
    public void R15DigestStatusScopesCommittedProjectedStatusReplayToDeltaAndImplementation()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var atom = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        var statusPath = $"{BackfillInventoryLoader.RootPath}fixture-source/absorbed-closed/fixture-atom.yaml";
        fixture.Files[statusPath] = atom;

        var unrelated = RunDigestStatus(fixture, RawChangeSet.Create(["notes/r15-unrelated.txt"]));
        var candidate = RunDigestStatus(fixture, RawChangeSet.Create([statusPath]));
        var implementation = RunDigestStatus(
            fixture,
            RawChangeSet.Create(["tools/StrataLint.Engine/Rules/RuleEngine.cs"]));

        Assert.True(unrelated.Success, unrelated.Error);
        Assert.False(candidate.Success);
        Assert.Contains("handwritten status", candidate.Error, StringComparison.Ordinal);
        Assert.False(implementation.Success);
        Assert.Contains("handwritten status", implementation.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void R15DigestStatusScopesCommittedCasRehashToDeltaAndImplementation()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureCasPath] = "tampered committed bytes";

        var unrelated = RunDigestStatus(fixture, RawChangeSet.Create(["notes/r15-unrelated.txt"]));
        var candidate = RunDigestStatus(
            fixture,
            RawChangeSet.Create([RuleFixture.FixtureCasPath]));
        var implementation = RunDigestStatus(
            fixture,
            RawChangeSet.Create(["tools/StrataLint.Engine/Rules/RuleEngine.cs"]));

        Assert.True(unrelated.Success, unrelated.Error);
        Assert.False(candidate.Success);
        Assert.Contains("CAS blob hash mismatch", candidate.Error, StringComparison.Ordinal);
        Assert.False(implementation.Success);
        Assert.Contains("CAS blob hash mismatch", implementation.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusFailsClosedWhenScribeVerificationFails()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(null));

        var result = environment.DigestStatus(Array.Empty<string>());

        Assert.False(result.Success);
        Assert.Contains("Scribe emission verification failed", result.Error, StringComparison.Ordinal);
    }

    private static ProductionCliEnvironment DigestStatusEnvironment(
        RuleFixture fixture,
        RawChangeSet? changes = null) => new(
        "/repo",
        new FakeRepositoryGateway(
            changes ?? RawChangeSet.Create(Array.Empty<string>()),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline)),
        new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
        new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

    private static ProductionCliEnvironment DigestStatusHistoricalCoverageEnvironment(
        RawChangeSet changes)
    {
        const string gid = "D5/S0/Carrier/BackfillTarget";
        const string targetPath = gid + ".lean";
        const string absorbedPath =
            "Meta/Digestion/backfill/fixture-source/absorbed-closed/fixture-atom.yaml";
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Baseline[targetPath] = fixture.Files[targetPath];
        fixture.ForkPoint[targetPath] = fixture.Files[targetPath];
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(gid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(gid);
        const string definition = "fixture definition\n";
        const string emission = "# Fixture emission\n";
        var definitionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(definition)).RawSha256;
        var emissionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(emission)).RawSha256;
        var atom = fixture.Files[RuleFixture.FixtureBackfillAtomPath]
            .Replace(
                "coverage: []",
                "coverage:\n"
                + $"    - gid: {gid}\n"
                + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
                + "      target_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000",
                StringComparison.Ordinal)
            .Replace(
                "scribe: []",
                "scribe:\n"
                + $"    - gid: {gid}\n"
                + $"      definition_sha256: {definitionSha256}\n"
                + $"      emission_sha256: {emissionSha256}",
                StringComparison.Ordinal);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files.Remove(RuleFixture.FixtureBackfillAtomPath);
            files[absorbedPath] = atom;
            files[definitionPath] = definition;
            files[emissionPath] = emission;
        }

        var verified = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                gid,
                definitionPath,
                definitionSha256,
                emissionPath,
                emissionSha256),
        ]);
        return new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                changes,
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(verified));
    }

    private static CommandResult RunDigestStatus(RuleFixture fixture, RawChangeSet changes) =>
        new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(changes, Snapshot(fixture.Files), null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty))
        .DigestStatus(Array.Empty<string>());

    private static void DowngradeBaselineGenreMarkerSchema(RuleFixture fixture)
    {
        fixture.Baseline[RuleFixture.FixtureBackfillSourcePath] = fixture.Baseline[
                RuleFixture.FixtureBackfillSourcePath]
            .Replace("genre_registry_check = \"no-registry\"\n", string.Empty, StringComparison.Ordinal)
            .Replace("unregistered_genres = []\n", string.Empty, StringComparison.Ordinal);
    }

    private static RuleFixture CandidateFixtureWithInvalidGenreProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureBackfillSourcePath] = fixture.Files[
                RuleFixture.FixtureBackfillSourcePath]
            .Replace(
                "genre_registry_check = \"no-registry\"",
                "genre_registry_check = \"invalid-candidate-value\"",
                StringComparison.Ordinal);
        return fixture;
    }

    // align-scribe 多对事务(#3297)的专项测试:存量 mismatch 互为否决,修复须单事务。
    [Theory]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignScribeReceiptRepairsTargetAndMismatchedSiblingInOneTransaction(
        string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.probe"),
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(materialized, mismatchCode));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(
        [
            "--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
            "--atom-id", "receipt-gap-sibling", "--gid", inputs.Gid,
            "--base", "baseline",
        ]);

        Assert.True(result.Success, result.Error);
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            inputs.Gid[..inputs.Gid.LastIndexOf('.')], out var verified));
        var after = BackfillInventoryLoader.LoadRoot(temporary.Path);
        foreach (var atomId in new[] { CoverWorld.DefaultAtomId, "receipt-gap-sibling" })
        {
            var entry = Assert.Single(
                after.RequireDigestionEntries(),
                item => item.AtomId == atomId);
            var receipt = Assert.Single(entry.Receipts.Scribe);
            Assert.Equal(verified.DefinitionSha256, receipt.DefinitionSha256);
            Assert.Equal(verified.EmissionSha256, receipt.EmissionSha256);
            Assert.Contains(
                $"atom_id={atomId} gid={inputs.Gid}",
                result.Output,
                StringComparison.Ordinal);
        }
    }

    [Fact]
    public void AlignScribeReceiptStillRejectsBatchWhenACoverageReceiptMismatchRemains()
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.probe"),
        });
        var inputs = DirectoryInputs(
            WithSiblingReceiptMismatch(materialized, "coverage-receipt-mismatch"));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(
        [
            "--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
            "--atom-id", "receipt-gap-sibling", "--gid", inputs.Gid,
            "--base", "baseline",
        ]);

        Assert.False(result.Success);
        Assert.Contains("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    public static TheoryData<string[]> UnpairedOrDuplicatePairArguments => new()
    {
        new[] { "--atom-id", "a", "--gid", "g", "--atom-id", "b", "--base", "rev" },
        new[] { "--atom-id", "a", "--atom-id", "b", "--gid", "g", "--base", "rev" },
        new[] { "--gid", "g", "--atom-id", "a", "--base", "rev" },
        new[] { "--atom-id", "a", "--gid", "g", "--atom-id", "a", "--gid", "g", "--base", "rev" },
    };

    [Theory]
    [MemberData(nameof(UnpairedOrDuplicatePairArguments))]
    public void AlignScribeReceiptRejectsUnpairedOrDuplicatePairArguments(string[] arguments)
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var inputs = DirectoryInputs(materialized);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(arguments);

        Assert.False(result.Success);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }
}
