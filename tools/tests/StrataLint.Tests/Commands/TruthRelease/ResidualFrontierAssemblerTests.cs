using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed class ResidualFrontierAssemblerTests
{
    private const int AcknowledgedStaleCount = 55;
    private const string SourceId = "formal-concept-dynamics";
    private const string SourcePath = "docs/formal-concept-dynamics.md";
    private const string TargetGid = "D5/S0/Carrier/ResidualFrontierProbe";
    private const string TargetPath = TargetGid + ".lean";

    [Fact]
    public void ProducerUsesSettledLedgerAsBaselineForEveryAtom()
    {
        var fixture = CreateFixture();
        var canonical = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            fixture.Document,
            fixture.Snapshot,
            fixture.Lean,
            fixture.VerifiedScribeEmissions,
            baselineDocument: fixture.Document,
            truthStates: fixture.TruthStates);

        Assert.Empty(canonical.Findings);
        var acknowledged = canonical.Entries
            .Where(entry => fixture.AcknowledgedStale.Contains(entry.Entry.AtomId))
            .ToArray();
        Assert.Equal(AcknowledgedStaleCount, acknowledged.Length);
        Assert.All(acknowledged, static entry => Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            entry.DerivedStatus));
        Assert.Equal(
            fixture.ExpectedControlStatuses,
            canonical.Entries
                .Where(entry => !fixture.AcknowledgedStale.Contains(entry.Entry.AtomId))
                .ToDictionary(
                    static entry => entry.Entry.AtomId,
                    static entry => entry.DerivedStatus,
                    StringComparer.Ordinal));

        var actual = ResidualFrontierAssembler.Assemble(
            fixture.Snapshot,
            fixture.Lean,
            fixture.Lean.Report,
            new FakeScribeEmissionVerifier(fixture.VerifiedScribeEmissions),
            fixture.TruthStates);
        var expected = Encoding.UTF8.GetBytes(
            EchoResidualBlock.Render(DigestResidualSummary.Render(canonical)));

        Assert.Equal(expected, actual.ToArray());
    }

    private static Fixture CreateFixture()
    {
        var targetStatementId = FrozenStatementReceiptTestData.Id('a');
        var definition = Encoding.UTF8.GetBytes("residual frontier Scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# Residual frontier emission\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var verifiedRecord = new ScribeEmissionRecord(
            TargetGid,
            ScribeEmissionAttestation.DefinitionPath(TargetGid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(TargetGid),
            emissionHash);
        var verifiedScribeEmissions = VerifiedScribeEmissions.Create([verifiedRecord]);
        var entries = ImmutableArray.CreateBuilder<DigestionLedgerEntry>();
        var acknowledgedStale = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var casFiles = new List<(string Path, byte[] Bytes)>();

        for (var index = 0; index < AcknowledgedStaleCount; index++)
        {
            var atom = Atom($"acknowledged stale atom {index:D2}\n");
            var atomId = $"acknowledged-stale-{index:D2}";
            acknowledgedStale.Add(atomId);
            entries.Add(CompleteEntry(atom, atomId, targetStatementId, definitionHash, emissionHash));
            casFiles.Add(CasFile(atom));
        }

        var stableAbsorbed = Atom("stable absorbed atom\n");
        entries.Add(CompleteEntry(
            stableAbsorbed,
            "stable-absorbed",
            targetStatementId,
            definitionHash,
            emissionHash));
        casFiles.Add(CasFile(stableAbsorbed));

        var stablePartial = Atom("stable partial atom\n");
        entries.Add(Entry(
            stablePartial,
            "stable-partial",
            AtomizerRegistry.NoAtomizerId,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed,
            [TargetGid],
            sourceId: SourceId,
            sourcePath: SourcePath));
        casFiles.Add(CasFile(stablePartial));

        var stableResidual = Atom("stable residual atom\n");
        entries.Add(Entry(
            stableResidual,
            "stable-residual",
            AtomizerRegistry.NoAtomizerId,
            DigestionMigrationState.Residual,
            DigestionTruthState.Open,
            sourceId: SourceId,
            sourcePath: SourcePath));
        casFiles.Add(CasFile(stableResidual));

        var document = Document(
            AtomizerRegistry.NoAtomizerId,
            entries.ToImmutable(),
            SourceId,
            SourcePath,
            GenreRegistryCheck.NoGenreRegistry,
            ImmutableArray.CreateRange<string>(acknowledgedStale));
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [SourcePath] = "formal concept dynamics source\n",
            [TargetPath] = Lean(TargetGid),
            [verifiedRecord.DefinitionPath] = Encoding.UTF8.GetString(definition),
            [verifiedRecord.EmissionPath] = Encoding.UTF8.GetString(emission),
        };
        foreach (var (path, bytes) in casFiles)
        {
            files[path] = Encoding.UTF8.GetString(bytes);
        }
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(TargetPath, targetStatementId, []));
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        var snapshot = Snapshot(files.Select(static file =>
            (file.Key, Encoding.UTF8.GetBytes(file.Value))).ToArray());
        var lean = AcceptedLean(TargetPath);
        var truthStates = new Dictionary<RepoPath, TruthState>
        {
            [RepoPath.CreateKnown(TargetPath)] = TruthState.Closed,
        };

        return new Fixture(
            document,
            snapshot,
            lean,
            verifiedScribeEmissions,
            truthStates,
            acknowledgedStale.ToImmutable(),
            new Dictionary<string, DigestionStatus>(StringComparer.Ordinal)
            {
                ["stable-absorbed"] = new(
                    DigestionMigrationState.Absorbed,
                    DigestionTruthState.Closed),
                ["stable-partial"] = new(
                    DigestionMigrationState.Partial,
                    DigestionTruthState.Closed),
                ["stable-residual"] = new(
                    DigestionMigrationState.Residual,
                    DigestionTruthState.Open),
            });
    }

    private static DigestionLedgerEntry CompleteEntry(
        DigestionAtom atom,
        string atomId,
        string targetStatementId,
        string definitionHash,
        string emissionHash) => Entry(
        atom,
        atomId,
        AtomizerRegistry.NoAtomizerId,
        DigestionMigrationState.Absorbed,
        DigestionTruthState.Closed,
        [TargetGid],
        new DigestionReceipts(
            [new DigestionCoverageReceipt(TargetGid, atom.Fingerprints.RawSha256, targetStatementId)],
            [new DigestionScribeReceipt(TargetGid, definitionHash, emissionHash)],
            [],
            [],
            null),
        SourceId,
        SourcePath);

    private static DigestionAtom Atom(string text)
    {
        var bytes = Encoding.UTF8.GetBytes(text);
        return new DigestionAtom(
            0,
            bytes.Length,
            ImmutableArray.CreateRange(bytes),
            DigestionFingerprint.Compute(bytes),
            []);
    }

    private sealed record Fixture(
        BackfillInventoryDocument Document,
        RepositorySnapshot Snapshot,
        AcceptedLeanClosure Lean,
        VerifiedScribeEmissions VerifiedScribeEmissions,
        IReadOnlyDictionary<RepoPath, TruthState> TruthStates,
        ImmutableHashSet<string> AcknowledgedStale,
        IReadOnlyDictionary<string, DigestionStatus> ExpectedControlStatuses);
}
