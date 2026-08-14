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
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
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
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
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

}
