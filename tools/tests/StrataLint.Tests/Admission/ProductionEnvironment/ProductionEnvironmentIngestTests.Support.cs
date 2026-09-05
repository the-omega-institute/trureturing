using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static BackfillInventoryDocument IngestLedger(string atomizerId, DigestionAtom atom) =>
        BuildIngestLedger(atomizerId, atom);

    private static BackfillInventoryDocument MapOnlyEntry(
        BackfillInventoryDocument document,
        Func<DigestionLedgerEntry, DigestionLedgerEntry> map)
    {
        var source = Assert.Single(document.RequireDigestionSources());
        return document.WithDigestionSources(
        [
            source with { Entries = [map(Assert.Single(source.Entries))] },
        ]);
    }

    private static void AssertByteIdenticalGenericChainIngestRejected(string? chainAtomId)
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var atomId = AtomId(atom);
        chainAtomId ??= atomId;
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallDirectoryLedger(fixture, atomizerId, atom);
        var atomPath = DirectoryAtomPath(atomId, "residual-open");
        var atomText = fixture.Files[atomPath].Replace(
            "  unresolved_subitems: []",
            $"  unresolved_subitems: []\n  chain_atoms:\n    - {chainAtomId}",
            StringComparison.Ordinal);
        fixture.Files[atomPath] = atomText;
        fixture.Baseline[atomPath] = atomText;
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var outputPath = Path.Combine(
            temporary.Path,
            atomPath.Replace('/', Path.DirectorySeparatorChar));
        var unchangedWriteTime = new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc);
        File.SetLastWriteTimeUtc(outputPath, unchangedWriteTime);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(
            $"INGEST_INVALID ingest clause chain parent {atomId} lacks verified clause-plan proof: "
                + $"entry {atomId} malformed clause chain: parent CAS blob has no clause plan",
            result.Error,
            StringComparison.Ordinal);
        Assert.Equal(atomText, TemporaryFileSystem.File.ReadAllText(outputPath));
        Assert.Equal(unchangedWriteTime, File.GetLastWriteTimeUtc(outputPath));
    }

    private static void InstallDirectoryLedger(
        RuleFixture fixture,
        string atomizerId,
        DigestionAtom atom) =>
        InstallProjectedLedger(fixture, IngestLedger(atomizerId, atom), atom);

    private static void InstallProjectedLedger(
        RuleFixture fixture,
        BackfillInventoryDocument ledger,
        DigestionAtom? existingAtom)
    {
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            DirectoryLedgerTestSupport.ReplaceWithProjection(files, ledger);
        }

        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        if (existingAtom is null)
        {
            return;
        }

        var captured = DigestionCasStore.Capture(existingAtom.RawBytes.AsSpan());
        var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[captured.RelativePath] = text;
        fixture.Baseline[captured.RelativePath] = text;
    }

    private static string DirectoryAtomPath(string atomId, string state) =>
        $"{BackfillInventoryLoader.RootPath}fixture-source/{state}/{atomId}.yaml";

    private static string DirectoryAtomPath(string sourceId, string atomId, string state) =>
        $"{BackfillInventoryLoader.RootPath}{sourceId}/{state}/{atomId}.yaml";

    private static string AtomId(DigestionAtom atom) =>
        atom.Fingerprints.RawSha256["sha256:".Length..];

    private static string DirectoryAtom(DigestionAtom atom) => $$"""
        fingerprints:
          raw_sha256: {{atom.Fingerprints.RawSha256}}
          normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
        cas_ref: {{atom.Fingerprints.RawSha256}}
        coverage_gids: []
        receipts:
          scribe: []
          unresolved_subitems: []
        """;

    private static void WriteDirectoryLedger(
        string repositoryRoot,
        IReadOnlyDictionary<string, string> files)
    {
        foreach (var (path, text) in files.Where(static pair =>
                     BackfillInventoryLoader.IsCanonicalPath(pair.Key)))
        {
            var outputPath = Path.Combine(
                repositoryRoot,
                path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
            File.WriteAllText(outputPath, text, new UTF8Encoding(false));
        }
    }

    private static BackfillInventoryDocument BuildIngestLedger(
        string atomizerId,
        DigestionAtom atom)
    {
        var entry = DigestionTestSupport.Entry(
            atom,
            AtomId(atom),
            atomizerId,
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath);
        return DigestionTestSupport.Document(
            atomizerId,
            [entry],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            atomizerId == AtomizerRegistry.NoAtomizerId
                ? GenreRegistryCheck.NoGenreRegistry
                : GenreRegistryCheck.Collected([]));
    }

    /// <summary>
    /// SL-003 的 conservative-unknown 判据按<b>语法</b>识别 receiver:对临时夹具变量路径的
    /// File.ReadAllText 会被记为 VariablePath。这里的包装让该读取显式归属于临时文件系统,
    /// 与 TruthReleaseBundleWriterTests 的同形处置一致。
    /// </summary>
    private static class TemporaryFileSystem
    {
        internal static class File
        {
            internal static string ReadAllText(string path) => System.IO.File.ReadAllText(path);
        }
    }
}
