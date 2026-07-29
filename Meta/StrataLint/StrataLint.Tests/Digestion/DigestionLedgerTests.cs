using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void CasBackedLegacyBoundaryDoesNotContributeSourceOrBoundaryGaps()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var yaml = LedgerYaml(
            atom,
            migration: "partial",
            truth: "open",
            coverageReceipts: "[]",
            scribeReceipts: "[]");
        var document = BackfillInventoryLoader.Load(yaml);
        var snapshot = Snapshot((captured.RelativePath, captured.Bytes.ToArray()));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            document,
            snapshot,
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.DoesNotContain(status.Gaps, static gap =>
            gap.Code == "source-missing" || gap.Code.Contains("boundary", StringComparison.Ordinal));
    }

    [Fact]
    public void CasBackedNoAtomizerBoundaryStillRequiresItsSpecificationSource()
    {
        var source = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            source.Length,
            ImmutableArray.CreateRange(source),
            DigestionFingerprint.Compute(source),
            ImmutableArray<DigestionContext>.Empty);
        var captured = DigestionCasStore.Capture(source);
        var yaml = LedgerYaml(
                atom,
                migration: "partial",
                truth: "open",
                coverageReceipts: "[]",
                scribeReceipts: "[]")
            .Replace(
                $"atomizer: {AtomizerRegistry.GictId}",
                $"atomizer: {AtomizerRegistry.NoAtomizerId}",
                StringComparison.Ordinal);
        var document = BackfillInventoryLoader.Load(yaml);
        var snapshot = Snapshot((captured.RelativePath, captured.Bytes.ToArray()));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            document,
            snapshot,
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.LegacyBoundary, status.Alignment);
        Assert.Contains(status.Gaps, static gap => gap.Code == "source-missing");
    }

    [Fact]
    public void IngestRebindsCasBackedNoAtomizerBoundaryAndRemainsByteIdempotent()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        var ledgerText = LedgerYaml(
                atom,
                migration: "partial",
                truth: "open",
                coverageReceipts: "[]",
                scribeReceipts: "[]")
            .Replace(
                $"atomizer: {AtomizerRegistry.GictId}",
                $"atomizer: {AtomizerRegistry.NoAtomizerId}",
                StringComparison.Ordinal);
        var ledger = BackfillInventoryLoader.Load(ledgerText);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));

        var migratedEntry = Assert.Single(migrated.RequireDigestionEntries());
        Assert.NotNull(migratedEntry.Boundary);
        Assert.Equal(atom.Fingerprints.RawSha256, migratedEntry.CasRef);
        Assert.Empty(first.CasObjects);

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(
                ("docs/source.md", sourceBytes),
                CasFile(atom)),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceAndRemainsByteIdempotent()
    {
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。first。\n\n**定理 1.2(B)**。second。\n");
        var atoms = AtomizerRegistry.Atomize(atomizerId, sourceBytes).Claims;
        var ledger = BackfillInventoryLoader.Load(EmptyLedger(atomizerId));

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes)),
            ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));
        var entries = Assert.Single(first.Document.RequireDigestionSources()).Entries;

        Assert.Equal(atoms.Length, first.ResidualOpenAdded);
        Assert.Equal(atoms.Length, entries.Length);
        Assert.Equal(atoms.Length, first.CasObjects.Length);
        Assert.Empty(first.Fallbacks);
        Assert.All(entries, static entry =>
        {
            Assert.Null(entry.Boundary);
            Assert.Equal(entry.Fingerprints.RawSha256, entry.CasRef);
            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Receipts.Coverage);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        });
        Assert.All(first.CasObjects, item => Assert.Contains(
            atoms,
            atom => atom.Fingerprints.RawSha256 == item.Reference
                && atom.RawBytes.AsSpan().SequenceEqual(item.Bytes.AsSpan())));

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceWithCoarseFallback()
    {
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**未知 1.1(A)**。free-form source。\n");
        var ledger = BackfillInventoryLoader.Load(EmptyLedger(atomizerId));

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes)),
            ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));

        var fallback = Assert.Single(first.Fallbacks);
        Assert.Equal("source", fallback.SourceId);
        Assert.Equal(1, first.ResidualOpenAdded);
        var coarse = Assert.Single(first.Document.RequireDigestionEntries());
        Assert.Equal("coarse/source", coarse.AstPath);
        Assert.Equal(DigestionMigrationState.Residual, coarse.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, coarse.ProjectedStatus.Truth);
        var captured = Assert.Single(first.CasObjects);
        Assert.Equal(coarse.Fingerprints.RawSha256, coarse.CasRef);
        Assert.Equal(sourceBytes, captured.Bytes.ToArray());

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void LoaderReadsOnlySchemaThreeAtomicEntries()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var yaml = LedgerYaml(
            atom,
            migration: "partial",
            truth: "open",
            coverageReceipts: "[]",
            scribeReceipts: "[]");

        var document = BackfillInventoryLoader.Load(yaml);
        var entry = Assert.Single(document.RequireDigestionEntries());

        Assert.Equal(3, document.Root["schema_version"]);
        Assert.Equal("gict-1.1", entry.AtomId);
        Assert.Equal("theorem/1.1", entry.AstPath);
        Assert.NotNull(entry.Boundary);
        Assert.Equal(["D5/X_Frontier/Probe"], document.RequireReferencedGids().ToArray());
    }

    [Fact]
    public void LegacyAnchorDispositionSchemaHasNoCompatibilityReader()
    {
        const string legacy = """
            schema_version: 2
            inventory: m0-protected-v1
            sources:
              - id: GICT-v3.6
                path: docs/source.md
                entries:
                  - anchor: old
                    disposition: D5/X_Frontier/Probe
            ticket_index: []
            """;

        var error = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(legacy));

        Assert.Contains("schema_version 3", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DerivationRejectsHandwrittenStatusThatClaimsMoreThanReceiptsProve()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            ("D5/X_Frontier/Probe.lean", Encoding.UTF8.GetBytes(Lean("D5/X_Frontier/Probe"))));
        var lean = AcceptedLean("D5/X_Frontier/Probe.lean");
        var yaml = LedgerYaml(
            atom,
            migration: "absorbed",
            truth: "closed",
            coverageReceipts: "[]",
            scribeReceipts: "[]");

        var evaluation = DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            lean);
        var status = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionMigrationState.Partial, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "coverage-receipt-missing");
        Assert.Contains(evaluation.Findings, finding =>
            finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void ReproducibleExtractionWithoutSemanticTargetRemainsResidual()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var yaml = LedgerYaml(
                atom,
                migration: "residual",
                truth: "open",
                coverageReceipts: "[]",
                scribeReceipts: "[]")
            .Replace(
                "        coverage_gids:\n          - D5/X_Frontier/Probe",
                "        coverage_gids: []",
                StringComparison.Ordinal);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            Snapshot(("docs/source.md", source), CasFile(atom)),
            AcceptedLean(Array.Empty<string>())).Entries);

        Assert.Equal(DigestionMigrationState.Residual, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.Contains(status.Gaps, gap => gap.Code == "coverage-gid-missing");
    }

    [Fact]
    public void StructuralRawSeenReplacesTheBoundaryPrerequisite()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var yaml = StructuralLedgerYaml(atom);
        var document = BackfillInventoryLoader.Load(yaml);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            document,
            Snapshot(("docs/source.md", source), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.DoesNotContain(status.Gaps, gap => gap.Code.Contains("boundary", StringComparison.Ordinal));
        Assert.DoesNotContain(status.Gaps, gap => gap.Code == "normalized-seen-not-deletable");
    }

    [Fact]
    public void CasReceiptRemainsSeenAcrossNormalizedSourceRewrite()
    {
        var ledgerBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(Test)**。claim。\r\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(ledgerBytes).Claims);
        var document = BackfillInventoryLoader.Load(StructuralLedgerYaml(atom));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            document,
            Snapshot(("docs/source.md", currentBytes), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.False(status.Deletable);
        Assert.DoesNotContain(status.Gaps, gap => gap.Code == "normalized-seen-not-deletable");
    }

    [Fact]
    public void SelfAuthoredScribeAttestationCannotProveEmissionPassed()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var target = Encoding.UTF8.GetBytes(Lean("D5/S0/Carrier/Probe"));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var targetHash = DigestionFingerprint.Compute(target).RawSha256;
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var coverage = $$"""
            - gid: D5/S0/Carrier/Probe
              source_sha256: {{atom.Fingerprints.RawSha256}}
              target_sha256: {{targetHash}}
            """;
        var scribe = $$"""
            - gid: D5/S0/Carrier/Probe
              definition_sha256: {{definitionHash}}
              emission_sha256: {{emissionHash}}
            """;
        var scribeAttestation = ScribeEmissionAttestation.Write(
        [
            new ScribeEmissionRecord(
                "D5/S0/Carrier/Probe",
                "Blueprint/D5/S0/Carrier/Probe.scribe.cs",
                definitionHash,
                "Blueprint/D5/S0/Carrier/Probe.md",
                emissionHash),
        ]).ToArray();
        var yaml = LedgerYaml(
            atom,
            migration: "absorbed",
            truth: "closed",
            coverageReceipts: coverage,
            scribeReceipts: scribe,
            coverageGid: "D5/S0/Carrier/Probe");
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            ("D5/S0/Carrier/Probe.lean", target),
            ("Blueprint/D5/S0/Carrier/Probe.scribe.cs", definition),
            ("Blueprint/D5/S0/Carrier/Probe.md", emission),
            (ScribeEmissionAttestation.RelativePath, scribeAttestation));
        var lean = AcceptedLean("D5/S0/Carrier/Probe.lean");

        var evaluation = DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            lean);
        var status = Assert.Single(evaluation.Entries);

        Assert.False(status.Deletable);
        Assert.Equal(DigestionMigrationState.Partial, status.DerivedStatus.Migration);
        Assert.Contains(status.Gaps, gap => gap.Code == "scribe-emission-unverified");
        Assert.Contains(evaluation.Findings, finding =>
            finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void MatchingScribeFileHashesWithoutEmitterAttestationFailClosed()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var target = Encoding.UTF8.GetBytes(Lean("D5/S0/Carrier/Probe"));
        var definition = Encoding.UTF8.GetBytes("arbitrary definition bytes\n");
        var emission = Encoding.UTF8.GetBytes("arbitrary emission bytes\n");
        var coverage = $$"""
            - gid: D5/S0/Carrier/Probe
              source_sha256: {{atom.Fingerprints.RawSha256}}
              target_sha256: {{DigestionFingerprint.Compute(target).RawSha256}}
            """;
        var scribe = $$"""
            - gid: D5/S0/Carrier/Probe
              definition_sha256: {{DigestionFingerprint.Compute(definition).RawSha256}}
              emission_sha256: {{DigestionFingerprint.Compute(emission).RawSha256}}
            """;
        var yaml = LedgerYaml(
            atom,
            migration: "absorbed",
            truth: "closed",
            coverageReceipts: coverage,
            scribeReceipts: scribe,
            coverageGid: "D5/S0/Carrier/Probe");
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            ("D5/S0/Carrier/Probe.lean", target),
            ("Blueprint/D5/S0/Carrier/Probe.scribe.cs", definition),
            ("Blueprint/D5/S0/Carrier/Probe.md", emission));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            AcceptedLean("D5/S0/Carrier/Probe.lean")).Entries);

        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "scribe-emission-unverified");
    }

    [Fact]
    public void DeclarationCoverageUsesItsContainingModuleScribeAttestation()
    {
        const string declarationGid = "D5/S0/Carrier/Probe.probe";
        var status = EvaluateDeclarationCoverage(declarationGid, [declarationGid]);

        Assert.Equal(DigestionMigrationState.Absorbed, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, status.DerivedStatus.Truth);
        Assert.True(status.Deletable);
        Assert.Empty(status.Gaps);
    }

    [Fact]
    public void DeclarationCoverageRejectsSelectorMissingFromLeanReport()
    {
        const string declarationGid = "D5/S0/Carrier/Probe.missing";
        var status = EvaluateDeclarationCoverage(declarationGid, [declarationGid]);

        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "target-declaration-missing");
    }

    [Fact]
    public void DeclarationCoverageRejectsRealDeclarationAbsentFromScribeDocument()
    {
        var status = EvaluateDeclarationCoverage("D5/S0/Carrier/Probe.probe", []);

        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "scribe-declaration-reference-missing");
    }

    [Fact]
    public void TailCannotAppearBeforeAbsorptionAndExternalAuthorizationReceipt()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var targetPath = "D5/X_Assumptions/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean("D5/X_Assumptions/Probe"));
        var snapshot = Snapshot(("docs/source.md", source), CasFile(atom), (targetPath, target));
        var report = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("tailProbe", "axiom", "True", ["tailProbe"])]);
        var lean = AcceptedLean((targetPath, report));
        var yaml = LedgerYaml(
            atom,
            migration: "partial",
            truth: "open",
            coverageReceipts: "[]",
            scribeReceipts: "[]",
            coverageGid: "D5/X_Assumptions/Probe");

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            lean).Entries);

        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.Contains(status.Gaps, gap => gap.Code == "tail-authorization-missing");
        Assert.DoesNotContain("partial-tail", status.Render(), StringComparison.Ordinal);
    }

    [Fact]
    public void ArbitraryHashedRepositoryFileCannotAuthorizeTailDeletion()
    {
        var arbitraryAuthorization = Encoding.UTF8.GetBytes("repository readme\n");
        var status = EvaluateCompleteTail("README.md", arbitraryAuthorization);

        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "tail-authorization-invalid");
    }

    [Fact]
    public void CanonicalAtomAndGidBoundAuthorizationPermitsAbsorbedTail()
    {
        const string atomId = "gict-1.1";
        const string gid = "D5/X_Assumptions/Probe";
        var authorization = TailAuthorizationArtifact.Write(atomId, [gid]).ToArray();

        var status = EvaluateCompleteTail(
            TailAuthorizationArtifact.PathFor(atomId),
            authorization);

        Assert.Equal(DigestionMigrationState.Absorbed, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Tail, status.DerivedStatus.Truth);
        Assert.True(status.Deletable);
        Assert.Empty(status.Gaps);
    }

    [Fact]
    public void SourceWithoutAdapterStillRejectsAValidlyFormattedButFalseRawFingerprint()
    {
        var source = Encoding.UTF8.GetBytes("# manual source\n\nclaim\n");
        var syntheticAtom = new DigestionAtom(
            "manual/claim",
            0,
            source.Length,
            ImmutableArray.CreateRange(source),
            DigestionFingerprint.Compute(source),
            ImmutableArray<DigestionContext>.Empty);
        var yaml = LedgerYaml(
                syntheticAtom,
                migration: "partial",
                truth: "open",
                coverageReceipts: "[]",
                scribeReceipts: "[]")
            .Replace(
                $"atomizer: {AtomizerRegistry.GictId}",
                $"atomizer: {AtomizerRegistry.NoAtomizerId}",
                StringComparison.Ordinal)
            .Replace(
                syntheticAtom.Fingerprints.RawSha256,
                "sha256:" + new string('0', 64),
                StringComparison.Ordinal);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(syntheticAtom),
            ("D5/X_Frontier/Probe.lean", Encoding.UTF8.GetBytes(Lean("D5/X_Frontier/Probe"))));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            AcceptedLean("D5/X_Frontier/Probe.lean"));

        Assert.Contains(evaluation.Findings, finding =>
            finding.Contains("fingerprint", StringComparison.OrdinalIgnoreCase));
    }

    private static DigestionEntryEvaluation EvaluateDeclarationCoverage(
        string declarationGid,
        IEnumerable<string> describedDeclarations)
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        const string moduleGid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(moduleGid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var record = new ScribeEmissionRecord(
            moduleGid,
            ScribeEmissionAttestation.DefinitionPath(moduleGid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(moduleGid),
            emissionHash);
        var coverage = $$"""
            - gid: {{declarationGid}}
              source_sha256: {{atom.Fingerprints.RawSha256}}
              target_sha256: {{DigestionFingerprint.Compute(target).RawSha256}}
            """;
        var scribe = $$"""
            - gid: {{declarationGid}}
              definition_sha256: {{definitionHash}}
              emission_sha256: {{emissionHash}}
            """;
        var yaml = LedgerYaml(
            atom,
            migration: "absorbed",
            truth: "closed",
            coverageReceipts: coverage,
            scribeReceipts: scribe,
            coverageGid: declarationGid);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(moduleGid), definition),
            (ScribeEmissionAttestation.EmissionPath(moduleGid), emission),
            (ScribeEmissionAttestation.RelativePath,
                ScribeEmissionAttestation.Write([record]).ToArray()));

        return Assert.Single(DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record], describedDeclarations)).Entries);
    }

    private static DigestionEntryEvaluation EvaluateCompleteTail(
        string authorizationPath,
        byte[] authorization)
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        const string gid = "D5/X_Assumptions/Probe";
        const string targetPath = "D5/X_Assumptions/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var coverage = $$"""
            - gid: {{gid}}
              source_sha256: {{atom.Fingerprints.RawSha256}}
              target_sha256: {{DigestionFingerprint.Compute(target).RawSha256}}
            """;
        var scribe = $$"""
            - gid: {{gid}}
              definition_sha256: {{definitionHash}}
              emission_sha256: {{emissionHash}}
            """;
        var yaml = LedgerYaml(
                atom,
                migration: "absorbed",
                truth: "tail",
                coverageReceipts: coverage,
                scribeReceipts: scribe,
                coverageGid: gid)
            .Replace(
                "tail_authorization: null",
                $"tail_authorization:\n            path: {authorizationPath}\n            sha256: {DigestionFingerprint.Compute(authorization).RawSha256}",
                StringComparison.Ordinal);
        var attestation = ScribeEmissionAttestation.Write(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]).ToArray();
        var report = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("tailProbe", "axiom", "True", ["tailProbe"])]);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(gid), definition),
            (ScribeEmissionAttestation.EmissionPath(gid), emission),
            (ScribeEmissionAttestation.RelativePath, attestation),
            (authorizationPath, authorization));

        var verifiedEmissions = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]);
        return Assert.Single(DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            AcceptedLean((targetPath, report)),
            verifiedEmissions).Entries);
    }

    private static string LedgerYaml(
        DigestionAtom atom,
        string migration,
        string truth,
        string coverageReceipts,
        string scribeReceipts,
        string coverageGid = "D5/X_Frontier/Probe") => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: {{AtomizerRegistry.GictId}}
            path: docs/source.md
            atomizer: {{AtomizerRegistry.GictId}}
            entries:
              - atom_id: gict-1.1
                boundary:
                  ast_path: {{atom.AstPath}}
                  start_byte: {{atom.StartByte}}
                  end_byte: {{atom.EndByte}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{atom.Fingerprints.RawSha256}}
                coverage_gids:
                  - {{coverageGid}}
                receipts:
        {{ReceiptList("coverage", coverageReceipts, 10)}}
        {{ReceiptList("scribe", scribeReceipts, 10)}}
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: {{migration}}
                  truth: {{truth}}
        ticket_index: []
        """;

    private static string StructuralLedgerYaml(DigestionAtom atom) =>
        LedgerYaml(
                atom,
                migration: "residual",
                truth: "open",
                coverageReceipts: "[]",
                scribeReceipts: "[]")
            .Replace(
                $"    atomizer: {AtomizerRegistry.GictId}\n    entries:",
                $"    atomizer: {AtomizerRegistry.GictId}\n    acknowledged_stale: []\n    entries:",
                StringComparison.Ordinal)
            .Replace(
                $"        boundary:\n"
                + $"          ast_path: {atom.AstPath}\n"
                + $"          start_byte: {atom.StartByte}\n"
                + $"          end_byte: {atom.EndByte}\n",
                $"        ast_path: {atom.AstPath}\n",
                StringComparison.Ordinal)
            .Replace(
                "        coverage_gids:\n          - D5/X_Frontier/Probe",
                "        coverage_gids: []",
                StringComparison.Ordinal);

    private static (BackfillInventoryDocument Ledger, DigestionCasObject Captured)
        CasBackedNoAtomizerLedger(byte[] receiptBytes)
    {
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            receiptBytes.Length,
            ImmutableArray.CreateRange(receiptBytes),
            DigestionFingerprint.Compute(receiptBytes),
            ImmutableArray<DigestionContext>.Empty);
        var yaml = LedgerYaml(
                atom,
                migration: "partial",
                truth: "open",
                coverageReceipts: "[]",
                scribeReceipts: "[]")
            .Replace(
                $"atomizer: {AtomizerRegistry.GictId}",
                $"atomizer: {AtomizerRegistry.NoAtomizerId}",
                StringComparison.Ordinal);
        return (BackfillInventoryLoader.Load(yaml), DigestionCasStore.Capture(receiptBytes));
    }
}
