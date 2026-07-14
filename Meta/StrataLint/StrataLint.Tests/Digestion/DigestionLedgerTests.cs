using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionLedgerTests
{
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
        Assert.Equal("theorem/1.1", entry.Boundary.AstPath);
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
            Snapshot(("docs/source.md", source)),
            AcceptedLean(Array.Empty<string>())).Entries);

        Assert.Equal(DigestionMigrationState.Residual, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.Contains(status.Gaps, gap => gap.Code == "coverage-gid-missing");
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
    public void TailCannotAppearBeforeAbsorptionAndExternalAuthorizationReceipt()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var targetPath = "D5/X_Assumptions/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean("D5/X_Assumptions/Probe"));
        var snapshot = Snapshot(("docs/source.md", source), (targetPath, target));
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
            ("D5/X_Frontier/Probe.lean", Encoding.UTF8.GetBytes(Lean("D5/X_Frontier/Probe"))));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(yaml),
            snapshot,
            AcceptedLean("D5/X_Frontier/Probe.lean"));

        Assert.Contains(evaluation.Findings, finding =>
            finding.Contains("fingerprint", StringComparison.OrdinalIgnoreCase));
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

    private static string ReceiptList(string key, string value, int spaces) => value == "[]"
        ? new string(' ', spaces) + key + ": []"
        : new string(' ', spaces) + key + ":\n" + Indent(value, spaces + 2);

    private static string Indent(string value, int spaces) => string.Join(
        '\n',
        value.Split('\n').Select(line => new string(' ', spaces) + line));

    private static RepositorySnapshot Snapshot(params (string Path, byte[] Bytes)[] files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(file => new RawRepositoryEntry(
            file.Path,
            ImmutableArray.CreateRange(file.Bytes))));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static AcceptedLeanClosure AcceptedLean(params string[] paths) => AcceptedLean(
        paths.Select(path => (path, new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("probe", "theorem", "True", ImmutableArray<string>.Empty)]))).ToArray());

    private static AcceptedLeanClosure AcceptedLean(params (string Path, LeanFileReport Report)[] reports) =>
        AcceptedLeanClosure.Create(LeanAxiomReport.Create(reports.ToDictionary(
            static item => item.Path,
            static item => item.Report,
            StringComparer.Ordinal)));

    private static string Lean(string gid) => $$"""
        /- GID: {{gid}}
           generality: G
           mirror-B: none(waiver:test)
           mirror-E: none(waiver:test)
           anchors: []
           digest: Digestion test fixture. -/
        theorem probe : True := by trivial
        """;
}
