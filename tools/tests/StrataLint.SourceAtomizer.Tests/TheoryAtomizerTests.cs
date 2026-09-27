using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.TheoryAtomizerAssertions;

namespace StrataLint.SourceAtomizer.Tests;

public sealed class TheoryAtomizerTests
{
    private const string FourthProductionSource =
        "docs/develop/theory/INTERFACE_PAPER.md";

    private const string InterfacePhilosophySource =
        "docs/develop/theory/INTERFACE_PHILOSOPHY.md";

    [Fact]
    public void InterfacePaperDialectPreservesDuplicateBlocksAsDistinctOccurrences()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, FourthProductionSource));

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.PzgId,
            bytes,
            DigestionTestSupport.Rules);

        var duplicateContent = document.Claims
            .GroupBy(static atom => atom.Fingerprints.RawSha256, StringComparer.Ordinal)
            .Where(static group => group.Count() > 1)
            .ToArray();
        Assert.Equal(2, duplicateContent.Length);
        Assert.All(duplicateContent, static group => Assert.Equal(2, group.Count()));
    }

    [Fact]
    public void InterfacePhilosophyTheorem612IncludesBothContinuationLines()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, InterfacePhilosophySource));

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var atom = ClaimContaining(document, "**定理 6.12");
        var rawText = Encoding.UTF8.GetString(atom.RawBytes.AsSpan());

        Assert.Contains(
            "  −k_min − O(log Q) ≤ log(|C_Q(R)| / |F_Q|) ≤ −K(y|x) + O(log Q)。",
            rawText,
            StringComparison.Ordinal);
        Assert.Contains(
            "(iii)[证纲] 对定理 6.6 之构造记录可加强选取",
            rawText,
            StringComparison.Ordinal);
        Assert.DoesNotContain("**案卷 6.12.1", rawText, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionSourcesHaveStableAtomizationClassificationsAndFingerprints()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, FourthProductionSource));

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.PzgId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Equal(37, document.Claims.Length);
        Assert.Equal(35, document.Claims.Select(static atom => atom.Fingerprints.RawSha256)
            .Distinct(StringComparer.Ordinal).Count());

        var landing = ClaimContaining(document, "**引理 3.1(");
        var escape = ClaimContaining(document, "**定理 3.4(");
        Assert.Equal(
            "sha256:9d52e41b062f81b1ce93cf241bf4ef9806f6e6de3fe9d6d10b5dc2de6d1f929a",
            landing.Fingerprints.RawSha256);
        Assert.Equal(
            "sha256:c0a63f4cbbe848e456ae1f847150de6bf63e59a5295bf711230af4bbb4860cab",
            escape.Fingerprints.RawSha256);
        Assert.Contains("*证明。*", Encoding.UTF8.GetString(landing.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.Contains("*证明。*", Encoding.UTF8.GetString(escape.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.DoesNotContain("隐藏独立性", Encoding.UTF8.GetString(escape.RawBytes.AsSpan()), StringComparison.Ordinal);

        const string sourceId = "periodic-tree-registry";
        const string sourcePath = "docs/develop/theory/PERIODIC_TREE_registry.jsonl";
        var sourceRoot = $"{BackfillInventoryLoader.RootPath}{sourceId}/";
        var sourceBytes = File.ReadAllBytes(Path.Combine(root, sourcePath));
        var casPath = DigestionCasStore.RootPath
            + DigestionFingerprint.ComputeOpaque(sourceBytes).RawSha256["sha256:".Length..];
        var relativePaths = Directory
            .EnumerateFiles(Path.Combine(root, sourceRoot), "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'))
            .Append(sourcePath)
            .Append(TheoryAtomizerDataLoader.DataPath)
            .Append(casPath)
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        var raw = RawRepositorySnapshot.Create(relativePaths.Select(path => new RawRepositoryEntry(
            path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path)))))
            .Append(RawRepositoryEntry.FromText(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest())));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var source = Assert.Single(BackfillInventoryLoader.Load(snapshot).RequireDigestionSources());
        Assert.Equal(AtomizerRegistry.PeriodicTreeId, source.Atomizer);
        Assert.True(AtomizerRegistry.IsRegistered(source.Atomizer));
        var registryDocument = AtomizerRegistry.Atomize(
            source.Atomizer,
            sourceBytes,
            DigestionTestSupport.Rules);
        var registryAtom = Assert.Single(registryDocument.Claims);
        AssertContentIdentity(registryAtom);
        Assert.Equal(DigestionFingerprint.ComputeOpaque(sourceBytes), registryAtom.Fingerprints);
        Assert.Equal(sourceBytes, registryAtom.RawBytes.ToArray());
        Assert.Equal(sourceBytes, registryDocument.Reassemble().ToArray());
        var environment = new ProductionCliEnvironment(
            root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null),
            new FakeLeanReportSource(LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>(StringComparer.Ordinal))),
            new FakeScribeEmissionVerifier(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["digest-status", "--formalize-candidates"],
            environment,
            console);

        Assert.True(exitCode == 0, $"exit={exitCode}: {console.Error}");
        Assert.DoesNotContain(
            "atomizer recognition is incomplete or empty",
            console.Output,
            StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }
}
