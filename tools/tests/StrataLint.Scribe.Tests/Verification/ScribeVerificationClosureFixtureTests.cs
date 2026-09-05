using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeVerificationClosureFixtureTests
{
    [Fact]
    public void FilteredAndUnfilteredRepositoryFixturesProduceByteIdenticalCapabilities()
    {
        var repositoryRoot = RepositoryAccessor
            .Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation)
            .Root.FullPath;
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            GitRepositorySnapshotReader.ReadCurrent(repositoryRoot))).Snapshot;
        var report = LeanReportFixture.ForDocuments(
            DocumentDefinitions.All.Select(static definition => definition.Document));
        var unfilteredError = new StringWriter();
        var unfiltered = ScribeEmitter.Verify(repositoryRoot, unfilteredError, report);
        Assert.NotNull(unfiltered);
        Assert.Equal(string.Empty, unfilteredError.ToString());

        var hasProblemPool = snapshot.Files.Keys.Any(static path =>
            path.Value.StartsWith("Problems/", StringComparison.Ordinal));
        using var filtered = Materialize(
            snapshot,
            path => IsExpectedVerificationInput(path.Value, hasProblemPool));
        var filteredError = new StringWriter();
        var filteredCapability = ScribeEmitter.Verify(filtered.Path, filteredError, report);

        Assert.NotNull(filteredCapability);
        Assert.Equal(string.Empty, filteredError.ToString());
        Assert.Equal(
            CapabilityBytes(unfiltered!, report),
            CapabilityBytes(filteredCapability!, report));
    }

    private static byte[] CapabilityBytes(
        VerifiedScribeEmissions capability,
        LeanAxiomReport report)
    {
        var records = DocumentDefinitions.All
            .Select(definition => capability.TryGet(
                definition.Document.Header.Gid.Value,
                out var record) ? record : null)
            .Where(static record => record is not null)
            .OrderBy(static record => record!.Gid, StringComparer.Ordinal)
            .ToArray();
        var references = report.Files
            .SelectMany(static file => file.Value.Declarations.Select(declaration =>
                file.Key.Value[..^".lean".Length]
                + "."
                + declaration.Name[(declaration.Name.LastIndexOf('.') + 1)..]))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .Select(reference => new
            {
                Reference = reference,
                Present = capability.ReferencesDeclaration(reference),
            })
            .ToArray();
        return JsonSerializer.SerializeToUtf8Bytes(new
        {
            Records = records,
            References = references,
            Latex = capability.DescribeLatexRecords,
        });
    }

    private static MaterializedFixture Materialize(
        RepositorySnapshot snapshot,
        Func<RepoPath, bool> include)
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-closure-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        try
        {
            foreach (var (path, file) in snapshot.Files.Where(item => include(item.Key)))
            {
                var destination = Path.Combine(
                    root,
                    path.Value.Replace('/', Path.DirectorySeparatorChar));
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.WriteAllBytes(destination, file.RawBytes.AsSpan());
            }

            return new MaterializedFixture(root);
        }
        catch
        {
            Directory.Delete(root, recursive: true);
            throw;
        }
    }

    private static bool IsExpectedVerificationInput(string path, bool hasProblemPool) =>
        path.StartsWith("Blueprint/D5/", StringComparison.Ordinal)
        || path.StartsWith("Evidence/D5/", StringComparison.Ordinal)
        || path.StartsWith("Chronicle/", StringComparison.Ordinal)
        || path.StartsWith("Library/", StringComparison.Ordinal)
        || path.StartsWith("Papers/recipes/", StringComparison.Ordinal)
        || path.StartsWith("Papers/frozen/", StringComparison.Ordinal)
        || path.StartsWith("Problems/", StringComparison.Ordinal)
        || path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal)
        || path.StartsWith("D5/", StringComparison.Ordinal)
            && path.EndsWith(".lean", StringComparison.Ordinal)
        || path == "Meta/BACKFILL.yaml"
        || path is "Golden/Projection/statement-projection-pilot-v1.json"
            or "Golden/Projection/statement-projection-expansion-v1.json"
        || hasProblemPool
            && path.StartsWith("Golden/Frozen/state/", StringComparison.Ordinal);

    private sealed class MaterializedFixture(string path) : IDisposable
    {
        internal string Path { get; } = path;

        public void Dispose() => Directory.Delete(Path, recursive: true);
    }
}
