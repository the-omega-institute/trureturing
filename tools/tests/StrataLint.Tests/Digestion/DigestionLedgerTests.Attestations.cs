using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void SelfAuthoredScribeAttestationCannotProveEmissionPassed()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var target = Encoding.UTF8.GetBytes(Lean("D5/S0/Carrier/Probe"));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var scribeAttestation = ScribeEmissionAttestation.Write(
        [
            new ScribeEmissionRecord(
                "D5/S0/Carrier/Probe",
                "Blueprint/D5/S0/Carrier/Probe.scribe.cs",
                definitionHash,
                "Blueprint/D5/S0/Carrier/Probe.md",
                emissionHash),
        ]).ToArray();
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            "D5/S0/Carrier/Probe",
            new DigestionCoverageReceipt(
                "D5/S0/Carrier/Probe",
                atom.Fingerprints.RawSha256,
                TestModuleStatementId),
            new DigestionScribeReceipt(
                "D5/S0/Carrier/Probe",
                definitionHash,
                emissionHash));
        var snapshot = Snapshot([
            ("docs/source.md", source),
            CasFile(atom),
            ("D5/S0/Carrier/Probe.lean", target),
            ("Blueprint/D5/S0/Carrier/Probe.scribe.cs", definition),
            ("Blueprint/D5/S0/Carrier/Probe.md", emission),
            (ScribeEmissionAttestation.RelativePath, scribeAttestation),
            .. FrozenLedgerFiles("D5/S0/Carrier/Probe.lean", "probe"),
        ]);
        var lean = AcceptedLean("D5/S0/Carrier/Probe.lean");

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
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
    public void MatchingScribeFileHashesWithoutProducerCapabilityFailClosed()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var target = Encoding.UTF8.GetBytes(Lean("D5/S0/Carrier/Probe"));
        var definition = Encoding.UTF8.GetBytes("arbitrary definition bytes\n");
        var emission = Encoding.UTF8.GetBytes("arbitrary emission bytes\n");
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            "D5/S0/Carrier/Probe",
            new DigestionCoverageReceipt(
                "D5/S0/Carrier/Probe",
                atom.Fingerprints.RawSha256,
                TestModuleStatementId),
            new DigestionScribeReceipt(
                "D5/S0/Carrier/Probe",
                DigestionFingerprint.Compute(definition).RawSha256,
                DigestionFingerprint.Compute(emission).RawSha256));
        var snapshot = Snapshot([
            ("docs/source.md", source),
            CasFile(atom),
            ("D5/S0/Carrier/Probe.lean", target),
            ("Blueprint/D5/S0/Carrier/Probe.scribe.cs", definition),
            ("Blueprint/D5/S0/Carrier/Probe.md", emission),
            .. FrozenLedgerFiles("D5/S0/Carrier/Probe.lean", "probe"),
        ]);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            snapshot,
            AcceptedLean("D5/S0/Carrier/Probe.lean")).Entries);

        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "scribe-emission-unverified");
    }

    [Fact]
    public void DeclarationCoverageUsesItsProducerCurrentModuleRecord()
    {
        const string declarationGid = "D5/S0/Carrier/Probe.probe";
        var status = EvaluateDeclarationCoverage(declarationGid, [declarationGid]);

        Assert.Equal(DigestionMigrationState.Absorbed, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, status.DerivedStatus.Truth);
        Assert.True(status.Deletable);
        Assert.Empty(status.Gaps);
    }

    [Fact]
    public void ProducerCurrentEmissionMakesCommittedMarkdownOptional()
    {
        const string declarationGid = "D5/S0/Carrier/Probe.probe";
        var status = EvaluateDeclarationCoverage(
            declarationGid,
            [declarationGid],
            includeCommittedEmission: false);

        Assert.Equal(DigestionMigrationState.Absorbed, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, status.DerivedStatus.Truth);
        Assert.True(status.Deletable);
        Assert.Empty(status.Gaps);
        Assert.NotEmpty(status.Entry.Receipts.Scribe);
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
    public void CandidateDeltaDoesNotPromoteBaselinePartialWithStaleScribeReceipts()
    {
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("current scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# Current emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var staleDefinitionHash = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("stale scribe definition\n")).RawSha256;
        var staleEmissionHash = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("# Stale emitted narrative\n")).RawSha256;
        var document = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                TestModuleStatementId),
            new DigestionScribeReceipt(gid, staleDefinitionHash, staleEmissionHash));
        var record = new ScribeEmissionRecord(
            gid,
            ScribeEmissionAttestation.DefinitionPath(gid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(gid),
            emissionHash);
        var snapshot = Snapshot([
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (record.DefinitionPath, definition),
            (record.EmissionPath, emission),
            .. FrozenLedgerFiles(targetPath, "probe"),
        ]);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: document,
            baselineSnapshot: snapshot);
        var status = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionMigrationState.Partial, status.DerivedStatus.Migration);
        Assert.Contains(status.Gaps, static gap => gap.Code == "scribe-definition-mismatch");
        Assert.Contains(status.Gaps, static gap => gap.Code == "scribe-emission-mismatch");
        Assert.DoesNotContain(evaluation.Findings, static finding =>
            finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void TailCannotAppearBeforeAbsorptionAndExternalAuthorizationReceipt()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var targetPath = "D5/X_Assumptions/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean("D5/X_Assumptions/Probe"));
        var snapshot = Snapshot(("docs/source.md", source), CasFile(atom), (targetPath, target));
        var report = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("tailProbe", "axiom", "True", ["tailProbe"])]);
        var lean = AcceptedLean((targetPath, report));
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            "D5/X_Assumptions/Probe");

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
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
    public void TrustedTailAuthorizationBytesAndRecordedHashAreNotReplayed()
    {
        const string atomId = "gict-1.1";
        const string gid = "D5/X_Assumptions/Probe";
        var canonical = TailAuthorizationArtifact.Write(atomId, [gid]);
        var noncanonical = Encoding.UTF8.GetBytes(
            Encoding.UTF8.GetString(canonical.AsSpan()).Replace("\": ", "\":", StringComparison.Ordinal));

        var status = EvaluateCompleteTail(
            TailAuthorizationArtifact.PathFor(atomId),
            noncanonical,
            "sha256:" + new string('0', 64));

        Assert.Equal(DigestionTruthState.Tail, status.DerivedStatus.Truth);
        Assert.True(status.Deletable);
        Assert.Empty(status.Gaps);
    }

    [Fact]
    public void TailAuthorizationWriteGateRejectsChangedBytesThatMismatchReceiptHash()
    {
        const string atomId = "gict-1.1";
        const string gid = "D5/X_Assumptions/Probe";
        var path = TailAuthorizationArtifact.PathFor(atomId);
        var authorization = TailAuthorizationArtifact.Write(atomId, [gid]).ToArray();

        var status = EvaluateCompleteTail(
            path,
            authorization,
            "sha256:" + new string('0', 64),
            RawChangeSet.Create([path]));

        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.Contains(status.Gaps, gap => gap.Code == "tail-authorization-invalid");
    }

    [Fact]
    public void TailAuthorizationWriteGateRejectsChangedNoncanonicalBytes()
    {
        const string atomId = "gict-1.1";
        const string gid = "D5/X_Assumptions/Probe";
        var path = TailAuthorizationArtifact.PathFor(atomId);
        var canonical = TailAuthorizationArtifact.Write(atomId, [gid]);
        var noncanonical = Encoding.UTF8.GetBytes(
            Encoding.UTF8.GetString(canonical.AsSpan()).Replace("\": ", "\":", StringComparison.Ordinal));

        var status = EvaluateCompleteTail(
            path,
            noncanonical,
            DigestionFingerprint.Compute(noncanonical).RawSha256,
            RawChangeSet.Create([path]));

        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.Contains(status.Gaps, gap => gap.Code == "tail-authorization-invalid");
    }

    [Fact]
    public void TailAuthorizationSelectionBindingStillRejectsADifferentGid()
    {
        const string atomId = "gict-1.1";
        var authorization = TailAuthorizationArtifact.Write(
            atomId,
            ["D5/X_Assumptions/Different"]);

        var status = EvaluateCompleteTail(
            TailAuthorizationArtifact.PathFor(atomId),
            authorization.ToArray());

        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "tail-authorization-invalid");
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
        var ledger = Ledger(
            syntheticAtom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            atomizer: AtomizerRegistry.NoAtomizerId);
        var ledgerSource = Assert.Single(ledger.RequireDigestionSources());
        var ledgerEntry = Assert.Single(ledgerSource.Entries);
        var falseFingerprint = "sha256:" + new string('0', 64);
        ledger = ledger.WithDigestionSources(
        [
            ledgerSource with
            {
                Entries =
                [
                    ledgerEntry with
                    {
                        Fingerprints = new DigestionFingerprints(falseFingerprint, falseFingerprint),
                        CasRef = falseFingerprint,
                    },
                ],
            },
        ]);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(syntheticAtom),
            ("D5/X_Frontier/Probe.lean", Encoding.UTF8.GetBytes(Lean("D5/X_Frontier/Probe"))));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            snapshot,
            AcceptedLean("D5/X_Frontier/Probe.lean"));

        Assert.Contains(evaluation.Findings, finding =>
            finding.Contains("fingerprint", StringComparison.OrdinalIgnoreCase));
    }

}
