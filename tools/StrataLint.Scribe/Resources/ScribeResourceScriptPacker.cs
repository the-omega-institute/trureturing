using System.Collections.Immutable;

namespace StrataLint.Scribe;

public sealed record ScribeResourceScriptPackResult(
    ScribeResourcePackManifest? Manifest,
    ImmutableArray<string> ExecutedPaths,
    ImmutableArray<string> ReusedPaths,
    ImmutableArray<ScribeScriptFailure> Failures);

/// <summary>Produces resource packs from scripts, with reuse only from an explicitly supplied pack.</summary>
public static class ScribeResourceScriptPacker
{
    public static ScribeResourceScriptPackResult Write(string repositoryRoot, string outputPath, string? reuseFrom = null) =>
        WriteCore(repositoryRoot, outputPath, reuseFrom, ScribeScriptSemantics.ResourceSemanticVersion);

    internal static ScribeResourceScriptPackResult WriteCore(string repositoryRoot, string outputPath,
        string? reuseFrom, int semanticVersion)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(outputPath);
        var root = Path.GetFullPath(repositoryRoot);
        var reuse = reuseFrom is null ? null : ScribeResourcePack.Open(reuseFrom);
        // Validate resource shapes even for entries that the current tree no longer selects.
        var prior = reuse?.ReadAll().ToDictionary(definition => definition.SourcePath, StringComparer.Ordinal);
        var priorEntries = reuse?.Manifest.Entries.ToDictionary(
            entry => "Blueprint/" + entry.Gid + ".scribe.cs", StringComparer.Ordinal);
        var paths = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
            .Order(StringComparer.Ordinal).ToImmutableArray();
        return StatementProjectionFixtureLoader.WithFreshRepositoryRoot(root, () =>
        {
            var execute = ImmutableArray.CreateBuilder<string>();
            var reused = ImmutableArray.CreateBuilder<string>();
            var failures = ImmutableArray.CreateBuilder<ScribeScriptFailure>();
            var inputs = new Dictionary<string, string>(StringComparer.Ordinal);
            var resources = new List<(string Gid, string InputKey, byte[] Bytes)>();
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
                    && entry.InputKey == input.Key && AssessmentsMatch(prior![path]))
                {
                    resources.Add((entry.Gid, input.Key!, reuse!.EncodedBytes(entry.Gid).ToArray()));
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
                    ScribeResourceCodec.Encode(result.Definition)));
            }
            var errors = failures.OrderBy(failure => failure.RelativePath, StringComparer.Ordinal).ToImmutableArray();
            var manifest = errors.IsEmpty ? ScribeResourcePack.WriteEncoded(outputPath, resources) : null;
            return new ScribeResourceScriptPackResult(manifest, execute.ToImmutable(), reused.ToImmutable(), errors);
        });
    }

    private static bool AssessmentsMatch(DocumentDefinition definition)
    {
        foreach (var describe in Descriptions(definition.Document.Content))
        {
            if (describe.StatementAssessment is not { } recorded
                || describe.KindSource is not DescribeKindSource.ReportDerived derived) continue;
            StatementAssessment current;
            try { current = StatementSource.Evaluate(LeanDeclarationRef.Create(derived.Handle.Value)); }
            catch (Exception exception) when (exception is not OutOfMemoryException) { return false; }
            if (!ScribeResourceCodec.EncodeAssessment(recorded).AsSpan()
                .SequenceEqual(ScribeResourceCodec.EncodeAssessment(current))) return false;
        }
        return true;
    }

    private static IEnumerable<DocumentBlock.Describe> Descriptions(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (block is DocumentBlock.Describe description) yield return description;
            if (nested is not null)
                foreach (var item in Descriptions(nested)) yield return item;
        }
    }
}
