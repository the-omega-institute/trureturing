using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class MaterializedRepositorySnapshotClosureTests
{
    [Fact]
    public void OutsideReadClosureProbeIsNotMaterializedAndDoesNotChangeVerifiedScribeEmissions()
    {
        var retained = RawRepositoryEntry.FromText(
            "D5/S0/Carrier/Probe.lean",
            "theorem probe : True := by trivial\n");
        var baseline = Snapshot(retained);
        var withOutsideFiles = Snapshot(
            retained,
            RawRepositoryEntry.FromText("outside/read-closure-probe.txt", "outside\n"),
            RawRepositoryEntry.FromText(
                "tools/Generated/scribe-emissions.v1.json",
                "generated output must not be read\n"));

        var baselineCapability = VerifyVisibleInputs(baseline);
        var probedCapability = VerifyVisibleInputs(withOutsideFiles);

        Assert.Equal(CapabilityBytes(baselineCapability), CapabilityBytes(probedCapability));
    }

    [Theory]
    [InlineData("Blueprint/D5/S0/Carrier/Probe.scribe.cs", false)]
    [InlineData("Golden/Projection/statement-projection-pilot-v1.json", false)]
    [InlineData("Golden/Projection/statement-projection-expansion-v1.json", false)]
    [InlineData("Meta/BACKFILL.yaml", false)]
    [InlineData("Meta/Digestion/backfill/probe/source.toml", false)]
    [InlineData("D5/S0/Carrier/Probe.lean", false)]
    [InlineData("Library/notes/probe.md", false)]
    [InlineData("Problems/probe.md", false)]
    [InlineData("Golden/Frozen/state/S0/Carrier/Probe.lean.json", true)]
    public void MaterializesEveryReaderOwnedInputPartition(string expectedPath, bool withProblemPool)
    {
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(expectedPath, "reader input\n"),
        };
        if (withProblemPool)
        {
            entries.Add(RawRepositoryEntry.FromText("Problems/.keep", string.Empty));
        }

        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            Assert.True(File.Exists(FullPath(root, expectedPath)), expectedPath);
            return VerifiedScribeEmissions.Empty;
        });

        verifier.Verify(Snapshot(entries.ToArray()), EmptyReport(), RawChangeSet.Create([]));
    }

    [Theory]
    [InlineData("Blueprint/D5/S0/Carrier/Probe.md")]
    [InlineData("Evidence/D5/S0/Carrier/Probe.result.json")]
    [InlineData("Chronicle/2026/09/05-probe.md")]
    [InlineData("Papers/recipes/D5-P001.yaml")]
    [InlineData("Papers/frozen/D5-P001/manifest.sha256")]
    public void DynamicGidAddressTargetsRemainVisible(string expectedPath)
    {
        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            Assert.True(File.Exists(FullPath(root, expectedPath)), expectedPath);
            return VerifiedScribeEmissions.Empty;
        });

        verifier.Verify(
            Snapshot(RawRepositoryEntry.FromText(expectedPath, "GID target\n")),
            EmptyReport(),
            RawChangeSet.Create([]));
    }

    [Fact]
    public void EmptyAndMissingReaderDirectoriesKeepTheirExistenceState()
    {
        VerifyDirectoryState(Snapshot(), expected: false);
        VerifyDirectoryState(
            Snapshot(
                RawRepositoryEntry.FromText("Library/empty/.keep", string.Empty),
                RawRepositoryEntry.FromText("Problems/.keep", string.Empty),
                RawRepositoryEntry.FromText(
                    "Meta/Digestion/backfill/empty/.keep",
                    string.Empty)),
            expected: true);
    }

    private static VerifiedScribeEmissions VerifyVisibleInputs(RepositorySnapshot snapshot)
    {
        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            Assert.False(File.Exists(FullPath(root, "outside/read-closure-probe.txt")));
            Assert.False(File.Exists(FullPath(
                root,
                "tools/Generated/scribe-emissions.v1.json")));
            var visiblePaths = Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
                .Order(StringComparer.Ordinal);
            var digest = Sha256(string.Join("\n", visiblePaths));
            return VerifiedScribeEmissions.Create(
            [
                new ScribeEmissionRecord(
                    "D5/S0/Carrier/Probe",
                    "Blueprint/D5/S0/Carrier/Probe.scribe.cs",
                    digest,
                    "Blueprint/D5/S0/Carrier/Probe.md",
                    digest),
            ]);
        });
        return verifier.Verify(snapshot, EmptyReport(), RawChangeSet.Create([]));
    }

    private static void VerifyDirectoryState(RepositorySnapshot snapshot, bool expected)
    {
        var verifier = new ProductionScribeEmissionVerifier((root, _) =>
        {
            Assert.Equal(expected, Directory.Exists(FullPath(root, "Library")));
            Assert.Equal(expected, Directory.Exists(FullPath(root, "Problems")));
            Assert.Equal(expected, Directory.Exists(FullPath(
                root,
                "Meta/Digestion/backfill")));
            return VerifiedScribeEmissions.Empty;
        });
        verifier.Verify(snapshot, EmptyReport(), RawChangeSet.Create([]));
    }

    private static byte[] CapabilityBytes(VerifiedScribeEmissions capability)
    {
        Assert.True(capability.TryGet("D5/S0/Carrier/Probe", out var record));
        return JsonSerializer.SerializeToUtf8Bytes(record);
    }

    private static LeanAxiomReport EmptyReport() => LeanAxiomReport.Create(
        new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));

    private static RepositorySnapshot Snapshot(params RawRepositoryEntry[] entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;

    private static string FullPath(string root, string path) => Path.Combine(
        root,
        path.Replace('/', Path.DirectorySeparatorChar));

    private static string Sha256(string value) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(value)));
}
