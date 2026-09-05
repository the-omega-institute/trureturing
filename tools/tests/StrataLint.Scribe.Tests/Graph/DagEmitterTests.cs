using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using Trureturing.Truth;

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
            var written = TemporaryFileSystem.File.ReadAllBytes(Path.Combine(root, DagEmitter.RelativePath));
            Assert.True(written.AsSpan().SequenceEqual(CanonicalDagWriter.Write(dag).AsSpan()));
            var truthGraph = TemporaryFileSystem.File.ReadAllBytes(Path.Combine(root, DagEmitter.TruthGraphRelativePath));
            Assert.True(truthGraph.AsSpan().SequenceEqual(
                TruthGraphJsonWriter.Write(TruthGraphModelBuilder.Create(dag, Provenance)).AsSpan()));
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
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, DagEmitter.RelativePath)));
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
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            var stale = Encoding.UTF8.GetBytes("# Truth DAG\n\nstale\n");
            TemporaryFileSystem.File.WriteAllBytes(path, stale);

            var exit = DagEmitter.Emit(root, Build(), Provenance, check: true, TextWriter.Null, TextWriter.Null);

            Assert.Equal(1, exit);
            Assert.True(TemporaryFileSystem.File.ReadAllBytes(path).AsSpan().SequenceEqual(stale));
        });
    }

    [Fact]
    public void EmitReplacesAStaleArtifact()
    {
        WithRoot(root =>
        {
            var path = Path.Combine(root, DagEmitter.RelativePath);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            TemporaryFileSystem.File.WriteAllBytes(path, Encoding.UTF8.GetBytes("stale\n"));
            var dag = Build();

            var exit = DagEmitter.Emit(root, dag, Provenance, check: false, TextWriter.Null, TextWriter.Null);

            Assert.Equal(0, exit);
            Assert.True(TemporaryFileSystem.File.ReadAllBytes(path).AsSpan()
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

            Assert.True(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(firstRoot, DagEmitter.RelativePath)).AsSpan()
                .SequenceEqual(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(secondRoot, DagEmitter.RelativePath))));
            Assert.False(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(firstRoot, DagEmitter.TruthGraphRelativePath)).AsSpan()
                .SequenceEqual(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(secondRoot, DagEmitter.TruthGraphRelativePath))));
        }));
    }

    private static void WithRoot(Action<string> body)
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-dag-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        try
        {
            body(root);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    private static TruthDagProjection Build()
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
        return TruthDagProjectionAssembler.Build(snapshot, closure);
    }
}
