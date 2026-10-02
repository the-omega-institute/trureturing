using System.Collections.Immutable;

namespace StrataLint.Scribe;

public sealed record ScribeResourceScriptPackResult(
    ScribeResourcePackManifest? Manifest,
    ImmutableArray<string> ExecutedPaths,
    ImmutableArray<string> ReusedPaths,
    ImmutableArray<ScribeScriptFailure> Failures)
{
    public string? ReuseSkippedReason { get; init; }
}

/// <summary>Produces resource packs from scripts, with reuse only from an explicitly supplied pack.</summary>
public static class ScribeResourceScriptPacker
{
    public static ScribeResourceScriptPackResult Write(string repositoryRoot, string outputPath, string? reuseFrom = null) =>
        WriteCore(repositoryRoot, outputPath, reuseFrom, ScribeScriptSemantics.ResourceSemanticVersion,
            ScribeResourcePackExecutionEnvironment.Current);

    internal static ScribeResourceScriptPackResult WriteCore(string repositoryRoot, string outputPath,
        string? reuseFrom, int semanticVersion)
        => WriteCore(repositoryRoot, outputPath, reuseFrom, semanticVersion,
            ScribeResourcePackExecutionEnvironment.Current);

    internal static ScribeResourceScriptPackResult WriteCore(string repositoryRoot, string outputPath,
        string? reuseFrom, int semanticVersion, ScribeResourcePackExecutionEnvironment executionEnvironment)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(outputPath);
        var root = Path.GetFullPath(repositoryRoot);
        var reuse = reuseFrom is null ? null : ScribeResourcePack.Open(reuseFrom);
        // Validate resource shapes even for entries that the current tree no longer selects.
        if (reuse is not null) foreach (var definition in reuse.ReadAll()) _ = definition;
        var environmentDifferences = reuse?.Manifest.ExecutionEnvironment.Differences(executionEnvironment)
            .ToImmutableArray() ?? [];
        var priorEntries = environmentDifferences.IsEmpty
            ? reuse?.Manifest.Entries.ToDictionary(
                entry => "Blueprint/" + entry.Gid + ".scribe.cs", StringComparer.Ordinal)
            : null;
        var paths = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
            .Order(StringComparer.Ordinal).ToImmutableArray();
        return StatementProjectionFixtureLoader.WithFreshRepositoryRoot(root, () =>
        {
            var execute = ImmutableArray.CreateBuilder<string>();
            var reused = ImmutableArray.CreateBuilder<string>();
            var failures = ImmutableArray.CreateBuilder<ScribeScriptFailure>();
            var inputs = new Dictionary<string, string>(StringComparer.Ordinal);
            var resources = new List<(string Gid, string InputKey, byte[] Bytes, ImmutableArray<ScribeProjectionRead> ReadSet)>();
            foreach (var path in paths)
            {
                var input = ScribeScriptInputs.Read(root, path, semanticVersion);
                if (input.Failure is { } failure)
                {
                    failures.Add(failure.RelativePath == path ? failure : failure with
                    {
                        RelativePath = path, Message = failure.ToString(),
                    });
                    continue;
                }
                inputs.Add(path, input.Key!);
                if (priorEntries is not null && priorEntries.TryGetValue(path, out var entry)
                    && entry.InputKey == input.Key && ReadsMatch(entry.ReadSet))
                {
                    resources.Add((entry.Gid, input.Key!, reuse!.EncodedBytes(entry.Gid).ToArray(), entry.ReadSet));
                    reused.Add(path);
                }
                else execute.Add(path);
            }
            foreach (var result in ScribeScriptHost.ExecuteBatch(root, execute))
            {
                if (!result.IsSuccess)
                {
                    var failure = result.Failure!;
                    failures.Add(failure.RelativePath == result.RelativePath ? failure : failure with
                    {
                        RelativePath = result.RelativePath, Message = failure.ToString(),
                    });
                }
                else resources.Add((result.Definition!.Document.Header.Gid.Value, inputs[result.RelativePath],
                    ScribeResourceCodec.Encode(result.Definition), result.ReadSet));
            }
            var errors = failures.OrderBy(failure => failure.RelativePath, StringComparer.Ordinal).ToImmutableArray();
            var manifest = errors.IsEmpty
                ? ScribeResourcePack.WriteEncoded(outputPath, resources, executionEnvironment)
                : null;
            return new ScribeResourceScriptPackResult(manifest, execute.ToImmutable(), reused.ToImmutable(), errors)
            {
                ReuseSkippedReason = environmentDifferences.IsEmpty
                    ? null
                    : string.Join(",", environmentDifferences),
            };
        });
    }

    private static bool ReadsMatch(ImmutableArray<ScribeProjectionRead> reads)
    {
        foreach (var read in reads)
        {
            StatementAssessment current;
            try { current = StatementSource.Evaluate(LeanDeclarationRef.Create(read.Declaration)); }
            catch (Exception exception) when (exception is not OutOfMemoryException) { return false; }
            if (ScribeResourcePack.Digest(ScribeResourceCodec.EncodeAssessment(current)) != read.Sha256) return false;
        }
        return true;
    }
}
