using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionFidelityAttestationTests
{
    [Fact]
    public void CanonicalAttestationRoundTripsAndVerifiesCompoundAtomAndTheoremKeys()
    {
        var fixture = FidelityFixture.Create(
            "pzg-residual-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-"
            + "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");

        var loaded = DigestionFidelityAttestation.Load(fixture.Snapshot, fixture.Path);
        var evaluation = DigestionFidelityAttestationChecker.Verify(
            fixture.Snapshot,
            fixture.Inputs.Report,
            fixture.Path);

        Assert.Equal(fixture.Attestation.AtomId, loaded.AtomId);
        Assert.Equal(fixture.Attestation.TheoremGid, loaded.TheoremGid);
        Assert.Equal(fixture.Attestation.SourceSha256, loaded.SourceSha256);
        Assert.Equal(fixture.Attestation.DeclarationSha256, loaded.DeclarationSha256);
        Assert.Equal(fixture.Attestation.Clauses.ToArray(), loaded.Clauses.ToArray());
        Assert.Equal(fixture.Attestation.ClauseMap.ToArray(), loaded.ClauseMap.ToArray());
        Assert.Equal(fixture.Attestation.GraderTraps.ToArray(), loaded.GraderTraps.ToArray());
        Assert.Equal(fixture.Attestation.AttestationSha256, loaded.AttestationSha256);
        Assert.Equal(
            DigestionFidelityAttestation.Write(loaded).ToArray(),
            fixture.Bytes.ToArray());
        Assert.Equal(2, evaluation.ClauseCount);
        Assert.Equal(1, evaluation.UndischargedCount);
        Assert.Equal(1, evaluation.FailedGraderTrapCount);
        Assert.Contains(fixture.Attestation.AtomId, fixture.Path, StringComparison.Ordinal);
        Assert.Contains(fixture.Attestation.TheoremGid, fixture.Path, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("unknown-root-key")]
    [InlineData("missing-root-key")]
    [InlineData("wrong-schema")]
    [InlineData("malformed-attestation-hash")]
    [InlineData("malformed-source-hash")]
    [InlineData("malformed-declaration-hash")]
    [InlineData("unknown-clause-key")]
    [InlineData("missing-clause-key")]
    [InlineData("malformed-clause-hash")]
    [InlineData("malformed-clause-span")]
    [InlineData("duplicate-clause-key")]
    [InlineData("missing-clause-map-entry")]
    [InlineData("unknown-clause-map-entry")]
    [InlineData("discharged-without-gid")]
    [InlineData("undischarged-with-gid")]
    [InlineData("invalid-clause-status")]
    [InlineData("missing-grader-trap")]
    [InlineData("unknown-grader-trap")]
    [InlineData("duplicate-grader-trap")]
    [InlineData("invalid-grader-result")]
    public void LoaderRejectsEveryMalformedClosedSchemaShape(string malformedShape)
    {
        var fixture = FidelityFixture.Create();
        var root = JsonNode.Parse(fixture.Bytes.AsSpan())!.AsObject();
        Mutate(root, malformedShape);
        var malformed = StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(root));
        var snapshot = FidelityFixture.Replace(fixture.Snapshot, fixture.Path, malformed);

        Assert.Throws<FormatException>(() =>
            DigestionFidelityAttestation.Load(snapshot, fixture.Path));
    }

    [Fact]
    public void LoaderRejectsNoncanonicalJsonAndMalformedJson()
    {
        var fixture = FidelityFixture.Create();
        var noncanonical = ImmutableArray.CreateRange(
            Encoding.UTF8.GetBytes(Encoding.UTF8.GetString(fixture.Bytes.AsSpan()).Replace(
                "{\"atom_id\"",
                "{ \"atom_id\"",
                StringComparison.Ordinal)));
        var malformed = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{\"atom_id\":\n"));

        Assert.Throws<FormatException>(() => DigestionFidelityAttestation.Load(
            FidelityFixture.Replace(fixture.Snapshot, fixture.Path, noncanonical),
            fixture.Path));
        Assert.Throws<FormatException>(() => DigestionFidelityAttestation.Load(
            FidelityFixture.Replace(fixture.Snapshot, fixture.Path, malformed),
            fixture.Path));
    }

    [Fact]
    public void LoaderRejectsAPathThatDropsPartOfACompoundAtomIdOrChangesTheTheoremGid()
    {
        var fixture = FidelityFixture.Create(
            "pzg-residual-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-"
            + "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
        var shortened = DigestionFidelityAttestation.RootPath
            + "pzg-residual-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa/"
            + fixture.Attestation.TheoremGid
            + DigestionFidelityAttestation.PathSuffix;
        var otherGid = DigestionFidelityAttestation.RootPath
            + fixture.Attestation.AtomId
            + "/D5/S0/Carrier/Probe.other"
            + DigestionFidelityAttestation.PathSuffix;

        Assert.Throws<FormatException>(() =>
            DigestionFidelityAttestation.Load(fixture.Snapshot, shortened));
        Assert.Throws<FormatException>(() =>
            DigestionFidelityAttestation.Load(fixture.Snapshot, otherGid));
    }

    [Fact]
    public void CheckerRejectsAtomAbsentFromTheLiveLedger()
    {
        var fixture = FidelityFixture.Create(attestationAtomId: "absent-atom");

        var exception = Assert.Throws<FormatException>(() =>
            DigestionFidelityAttestationChecker.Verify(
                fixture.Snapshot,
                fixture.Inputs.Report,
                fixture.Path));

        Assert.Contains("absent from the ledger", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckerRejectsAnAtomThatIsAmbiguousInTheLiveLedger()
    {
        var fixture = FidelityFixture.Create(duplicateLedgerAtom: true);

        Assert.Throws<FormatException>(() =>
            DigestionFidelityAttestationChecker.Verify(
                fixture.Snapshot,
                fixture.Inputs.Report,
                fixture.Path));
    }

    [Fact]
    public void CheckerRejectsSourceHashOrCasReferentDrift()
    {
        var sourceMismatch = FidelityFixture.Create(sourceSha256: Hash('a'));
        var missingCas = FidelityFixture.Create(removeCasBlob: true);

        Assert.Throws<FormatException>(() => DigestionFidelityAttestationChecker.Verify(
            sourceMismatch.Snapshot,
            sourceMismatch.Inputs.Report,
            sourceMismatch.Path));
        Assert.Throws<FormatException>(() => DigestionFidelityAttestationChecker.Verify(
            missingCas.Snapshot,
            missingCas.Inputs.Report,
            missingCas.Path));
    }

    [Fact]
    public void CheckerRejectsDeclarationHashDriftOrAMissingTheoremGid()
    {
        var hashMismatch = FidelityFixture.Create(declarationSha256: Hash('b'));
        var missingTheorem = FidelityFixture.Create(
            theoremGid: "D5/S0/Carrier/Probe.missing");

        Assert.Throws<FormatException>(() => DigestionFidelityAttestationChecker.Verify(
            hashMismatch.Snapshot,
            hashMismatch.Inputs.Report,
            hashMismatch.Path));
        Assert.Throws<FormatException>(() => DigestionFidelityAttestationChecker.Verify(
            missingTheorem.Snapshot,
            missingTheorem.Inputs.Report,
            missingTheorem.Path));
    }

    [Fact]
    public void CheckerRejectsEveryNamedClauseGidThatDoesNotExist()
    {
        var fixture = FidelityFixture.Create(
            dischargedGid: "D5/S0/Carrier/Probe.missing");

        var exception = Assert.Throws<FormatException>(() =>
            DigestionFidelityAttestationChecker.Verify(
                fixture.Snapshot,
                fixture.Inputs.Report,
                fixture.Path));

        Assert.Contains("D5/S0/Carrier/Probe.missing", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckerRejectsClauseSpanAndHashThatDoNotMatchThePinnedSource()
    {
        var hashMismatch = FidelityFixture.Create(firstClauseSha256: Hash('c'));
        var spanMismatch = FidelityFixture.Create(firstClauseEndByte: int.MaxValue);

        Assert.Throws<FormatException>(() => DigestionFidelityAttestationChecker.Verify(
            hashMismatch.Snapshot,
            hashMismatch.Inputs.Report,
            hashMismatch.Path));
        Assert.Throws<FormatException>(() => DigestionFidelityAttestationChecker.Verify(
            spanMismatch.Snapshot,
            spanMismatch.Inputs.Report,
            spanMismatch.Path));
    }

    [Fact]
    public void CliCommandIsRunnableAsAnExplicitCiStepAndFailsClosed()
    {
        var fixture = FidelityFixture.Create();
        var environment = new ProductionCliEnvironment(
            "/synthetic",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                FidelityFixture.Raw(fixture.Snapshot),
                FidelityFixture.Raw(fixture.Snapshot)),
            new FakeLeanReportSource(fixture.Inputs.Report));

        var validConsole = new CapturingConsole();
        var validExit = CliApplication.Run(
            ["check-fidelity-attestation", "--attestation", fixture.Path],
            environment,
            validConsole);
        var invalidConsole = new CapturingConsole();
        var invalidExit = CliApplication.Run(
            ["check-fidelity-attestation", "--attestation", fixture.Path + ".missing"],
            environment,
            invalidConsole);

        Assert.Equal(0, validExit);
        Assert.Contains("FIDELITY_ATTESTATION_VALID", validConsole.Output, StringComparison.Ordinal);
        Assert.Contains("undischarged=1", validConsole.Output, StringComparison.Ordinal);
        Assert.Contains("failed_grader_traps=1", validConsole.Output, StringComparison.Ordinal);
        Assert.Equal(2, invalidExit);
        Assert.Contains(
            "FIDELITY_ATTESTATION_INVALID",
            invalidConsole.Error,
            StringComparison.Ordinal);
    }

    private static void Mutate(JsonObject root, string malformedShape)
    {
        var clauses = root["clauses"]!.AsArray();
        var clauseMap = root["clause_map"]!.AsArray();
        var graderTraps = root["grader_traps"]!.AsArray();
        switch (malformedShape)
        {
            case "unknown-root-key": root["unknown"] = true; break;
            case "missing-root-key": root.Remove("atom_id"); break;
            case "wrong-schema": root["schema"] = "digestion-fidelity-attestation-v0"; break;
            case "malformed-attestation-hash": root["attestation_sha256"] = "sha256:ABC"; break;
            case "malformed-source-hash": root["source_sha256"] = "sha256:ABC"; break;
            case "malformed-declaration-hash": root["declaration_sha256"] = "sha256:ABC"; break;
            case "unknown-clause-key": clauses[0]!["unknown"] = true; break;
            case "missing-clause-key": clauses[0]!.AsObject().Remove("key"); break;
            case "malformed-clause-hash": clauses[0]!["clause_sha256"] = "sha256:ABC"; break;
            case "malformed-clause-span": clauses[0]!["start_byte"] = "zero"; break;
            case "duplicate-clause-key": clauses[1]!["key"] = clauses[0]!["key"]!.GetValue<string>(); break;
            case "missing-clause-map-entry": clauseMap.RemoveAt(1); break;
            case "unknown-clause-map-entry": clauseMap[0]!["clause_key"] = "clause-999"; break;
            case "discharged-without-gid": clauseMap[0]!.AsObject().Remove("gid"); break;
            case "undischarged-with-gid": clauseMap[1]!["gid"] = "D5/S0/Carrier/Probe.probe"; break;
            case "invalid-clause-status": clauseMap[0]!["status"] = "partial"; break;
            case "missing-grader-trap": graderTraps.RemoveAt(0); break;
            case "unknown-grader-trap": graderTraps[0]!["trap"] = "unknown-trap"; break;
            case "duplicate-grader-trap": graderTraps[1]!["trap"] = graderTraps[0]!["trap"]!.GetValue<string>(); break;
            case "invalid-grader-result": graderTraps[0]!["result"] = "unknown"; break;
            default: throw new InvalidOperationException("unknown malformed fixture");
        }
    }

    private static string Hash(char value) => "sha256:" + new string(value, 64);

    private sealed class CapturingConsole : ICliConsole
    {
        private readonly StringBuilder output = new();
        private readonly StringBuilder error = new();

        internal string Output => output.ToString();

        internal string Error => error.ToString();

        public void WriteOutput(string value) => output.Append(value);

        public void WriteError(string value) => error.Append(value);
    }

    private sealed record FidelityFixture(
        CoverInputs Inputs,
        DigestionFidelityAttestation Attestation,
        string Path,
        ImmutableArray<byte> Bytes,
        RepositorySnapshot Snapshot)
    {
        internal static FidelityFixture Create(
            string ledgerAtomId = CoverWorld.DefaultAtomId,
            string? attestationAtomId = null,
            string? theoremGid = null,
            string? sourceSha256 = null,
            string? declarationSha256 = null,
            string? dischargedGid = null,
            string? firstClauseSha256 = null,
            int? firstClauseEndByte = null,
            bool removeCasBlob = false,
            bool duplicateLedgerAtom = false)
        {
            var spec = new CoverSpec
            {
                AtomId = ledgerAtomId,
                OtherAtomBinding = duplicateLedgerAtom
                    ? (ledgerAtomId, "D5/S0/Carrier/Probe.other")
                    : null,
            };
            var inputs = spec.Materialize();
            var cas = Assert.Single(inputs.Files, pair =>
                pair.Key.StartsWith(DigestionCasStore.RootPath, StringComparison.Ordinal));
            var sourceBytes = Encoding.UTF8.GetBytes(cas.Value);
            var split = Math.Max(1, sourceBytes.Length / 2);
            var effectiveTheoremGid = theoremGid ?? inputs.Gid;
            var effectiveSourceSha256 = sourceSha256
                ?? DigestionFingerprint.Compute(sourceBytes).RawSha256;
            var effectiveDeclarationSha256 = declarationSha256
                ?? DeclarationSha256(inputs.Report, inputs.Gid);
            var clauses = ImmutableArray.Create(
                new DigestionFidelityClause(
                    "clause-001",
                    0,
                    firstClauseEndByte ?? split,
                    firstClauseSha256
                        ?? DigestionFingerprint.Compute(sourceBytes.AsSpan(0, split)).RawSha256),
                new DigestionFidelityClause(
                    "clause-002",
                    split,
                    sourceBytes.Length,
                    DigestionFingerprint.Compute(sourceBytes.AsSpan(split)).RawSha256));
            var clauseMap = ImmutableArray.Create(
                new DigestionFidelityClauseMapEntry(
                    "clause-001",
                    DigestionFidelityClauseStatus.Discharged,
                    dischargedGid ?? inputs.Gid),
                new DigestionFidelityClauseMapEntry(
                    "clause-002",
                    DigestionFidelityClauseStatus.Undischarged,
                    null));
            var graderTraps = DigestionFidelityAttestation.RequiredGraderTraps
                .Select((trap, index) => new DigestionFidelityGraderTrap(
                    trap,
                    index == 0
                        ? DigestionFidelityGraderResult.Fail
                        : DigestionFidelityGraderResult.Pass))
                .ToImmutableArray();
            var attestation = DigestionFidelityAttestation.Create(
                attestationAtomId ?? ledgerAtomId,
                effectiveTheoremGid,
                effectiveSourceSha256,
                effectiveDeclarationSha256,
                clauses,
                clauseMap,
                graderTraps);
            var path = DigestionFidelityAttestation.PathFor(
                attestation.AtomId,
                attestation.TheoremGid);
            var bytes = DigestionFidelityAttestation.Write(attestation);
            var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
            {
                [path] = Encoding.UTF8.GetString(bytes.AsSpan()),
            };
            if (removeCasBlob)
            {
                files.Remove(cas.Key);
            }

            var snapshot = Decode(CoverWorld.Raw(files));
            return new FidelityFixture(inputs, attestation, path, bytes, snapshot);
        }

        internal static RepositorySnapshot Replace(
            RepositorySnapshot snapshot,
            string path,
            ImmutableArray<byte> bytes)
        {
            var entries = snapshot.Files.Values
                .Where(file => !string.Equals(file.Path.Value, path, StringComparison.Ordinal))
                .Select(file => new RawRepositoryEntry(file.Path.Value, file.RawBytes))
                .Append(new RawRepositoryEntry(path, bytes));
            return Decode(RawRepositorySnapshot.Create(entries));
        }

        internal static RawRepositorySnapshot Raw(RepositorySnapshot snapshot) =>
            RawRepositorySnapshot.Create(snapshot.Files.Values.Select(file =>
                new RawRepositoryEntry(file.Path.Value, file.RawBytes)));

        private static string DeclarationSha256(LeanAxiomReport report, string gidText)
        {
            Assert.True(Gid.TryParse(gidText, out var gid));
            var file = report.Files[gid!.Path];
            var declaration = Assert.Single(file.Declarations);
            return Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
                gid.Path,
                new LeanFileReport([], [declaration]))).StatementId.Value;
        }

        private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }
}
