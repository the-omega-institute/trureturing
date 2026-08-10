using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DagEmitterTests
{
    private static readonly TruthGraphProvenance Provenance = new(
        "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");

    [Fact]
    public void EmitWritesTheCanonicalProjectionWhenTheArtifactIsAbsent()
    {
        WithRoot(root =>
        {
            var dag = Build();
            var output = new StringWriter();

            var exit = DagEmitter.Emit(root, dag, Provenance, check: false, output, TextWriter.Null);

            Assert.Equal(0, exit);
            var written = File.ReadAllBytes(Path.Combine(root, DagEmitter.RelativePath));
            Assert.True(written.AsSpan().SequenceEqual(CanonicalDagWriter.Write(dag).AsSpan()));
            var truthGraph = File.ReadAllBytes(Path.Combine(root, DagEmitter.TruthGraphRelativePath));
            Assert.True(truthGraph.AsSpan().SequenceEqual(
                TruthGraphJsonWriter.Write(TruthGraphExportModel.Create(dag, Provenance)).AsSpan()));
            Assert.Contains(DagEmitter.RelativePath, output.ToString(), StringComparison.Ordinal);
        });
    }

    [Fact]
    public void CheckReportsAnAbsentArtifactAsOutOfDateWithoutWritingIt()
    {
        WithRoot(root =>
        {
            var error = new StringWriter();

            var exit = DagEmitter.Emit(root, Build(), Provenance, check: true, TextWriter.Null, error);

            Assert.Equal(1, exit);
            Assert.False(File.Exists(Path.Combine(root, DagEmitter.RelativePath)));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        });
    }

    [Fact]
    public void CheckAcceptsAnArtifactThatAlreadyMatches()
    {
        WithRoot(root =>
        {
            var dag = Build();
            Assert.Equal(0, DagEmitter.Emit(root, dag, Provenance, check: false, TextWriter.Null, TextWriter.Null));

            var exit = DagEmitter.Emit(root, dag, Provenance, check: true, TextWriter.Null, TextWriter.Null);

            Assert.Equal(0, exit);
        });
    }

    [Fact]
    public void CheckRefusesAStaleArtifactAndLeavesItUntouched()
    {
        WithRoot(root =>
        {
            var path = Path.Combine(root, DagEmitter.RelativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            var stale = Encoding.UTF8.GetBytes("# Truth DAG\n\nstale\n");
            File.WriteAllBytes(path, stale);

            var exit = DagEmitter.Emit(root, Build(), Provenance, check: true, TextWriter.Null, TextWriter.Null);

            Assert.Equal(1, exit);
            Assert.True(File.ReadAllBytes(path).AsSpan().SequenceEqual(stale));
        });
    }

    [Fact]
    public void EmitReplacesAStaleArtifact()
    {
        WithRoot(root =>
        {
            var path = Path.Combine(root, DagEmitter.RelativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, Encoding.UTF8.GetBytes("stale\n"));
            var dag = Build();

            var exit = DagEmitter.Emit(root, dag, Provenance, check: false, TextWriter.Null, TextWriter.Null);

            Assert.Equal(0, exit);
            Assert.True(File.ReadAllBytes(path).AsSpan()
                .SequenceEqual(CanonicalDagWriter.Write(dag).AsSpan()));
        });
    }

    [Fact]
    public void MarkdownProjectionDoesNotReadTheDocumentProjection()
    {
        var firstProjection = DocumentGraphExportProjection.Empty;
        var secondProjection = new DocumentGraphExportProjection(
            new DocumentGraphSection(
                [new DocumentGraphNode("Blueprint/D5/S0/Carrier/Delta.md", "D5/S0/Carrier/Delta", "receipt-free")],
                [],
                [],
                []),
            new TruthGraphJoinsSection([]));
        WithRoot(firstRoot => WithRoot(secondRoot =>
        {
            var dag = Build();
            Assert.Equal(0, DagEmitter.Emit(
                firstRoot, dag, Provenance, check: false, TextWriter.Null, TextWriter.Null, firstProjection));
            Assert.Equal(0, DagEmitter.Emit(
                secondRoot, dag, Provenance, check: false, TextWriter.Null, TextWriter.Null, secondProjection));

            Assert.True(File.ReadAllBytes(Path.Combine(firstRoot, DagEmitter.RelativePath)).AsSpan()
                .SequenceEqual(File.ReadAllBytes(Path.Combine(secondRoot, DagEmitter.RelativePath))));
            Assert.False(File.ReadAllBytes(Path.Combine(firstRoot, DagEmitter.TruthGraphRelativePath)).AsSpan()
                .SequenceEqual(File.ReadAllBytes(Path.Combine(secondRoot, DagEmitter.TruthGraphRelativePath))));
        }));
    }

    [Fact]
    public void TheProjectionIsDeclaredInTheGeneratedArtifactInventory()
    {
        // FileMapPolicy cross-checks this inventory against Meta/FILEMAP.toml, so an artifact that
        // ships without an entry is an ungoverned generated file.
        var artifact = Assert.Single(
            GeneratedArtifactInventory.All.Where(static item => item.Path == DagEmitter.RelativePath));

        Assert.Equal(nameof(DagEmitter), artifact.Producer);

        var truthArtifact = Assert.Single(
            GeneratedArtifactInventory.All.Where(static item => item.Path == DagEmitter.TruthGraphRelativePath));
        Assert.Equal(nameof(DagEmitter), truthArtifact.Producer);
    }

    private static void WithRoot(Action<string> body)
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-dag-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        try
        {
            body(root);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    private static AcyclicTruthDag Build()
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["D5/S0/Carrier/Delta.lean"] = "def delta : Nat := 0\n",
            ["D5/S0/Carrier/Epsilon.lean"] = "def epsilon : Nat := 0\n",
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            ["D5/S0/Carrier/Delta.lean"] = new(
                ImmutableArray<string>.Empty,
                ImmutableArray<LeanDeclaration>.Empty),
            ["D5/S0/Carrier/Epsilon.lean"] = new(
                ["D5.S0.Carrier.Delta"],
                ImmutableArray<LeanDeclaration>.Empty),
        };
        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        return Assert.IsType<DagBuildOutcome.Accepted>(
            AcyclicTruthDag.Build(snapshot, closure)).Capability;
    }
}
