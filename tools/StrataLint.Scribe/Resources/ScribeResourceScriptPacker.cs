using System.Collections.Immutable;

namespace StrataLint.Scribe;

public sealed record ScribeResourceScriptPackResult(
    ScribeResourcePackManifest? Manifest,
    ImmutableArray<ScribeScriptFailure> Failures);

/// <summary>Executes every Blueprint script and writes its canonical resource definition.</summary>
public static class ScribeResourceScriptPacker
{
    public static ScribeResourceScriptPackResult Write(string repositoryRoot, string outputPath)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(outputPath);
        var root = Path.GetFullPath(repositoryRoot);
        var paths = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
            .Order(StringComparer.Ordinal).ToImmutableArray();
        return StatementProjectionFixtureLoader.WithFreshRepositoryRoot(root, () =>
        {
            var results = ScribeScriptHost.ExecuteBatch(root, paths);
            var failures = results.Where(result => !result.IsSuccess).Select(result =>
            {
                var failure = result.Failure!;
                return failure.RelativePath == result.RelativePath ? failure : failure with
                {
                    RelativePath = result.RelativePath, Message = failure.ToString(),
                };
            }).ToImmutableArray();
            if (!failures.IsEmpty)
            {
                return new ScribeResourceScriptPackResult(null, failures);
            }
            var manifest = ScribeResourcePack.Write(outputPath, results.Select(result => result.Definition!));
            return new ScribeResourceScriptPackResult(manifest, failures);
        });
    }
}
