using System.Collections.Immutable;

namespace StrataLint.Scribe;

internal sealed record GeneratedArtifactIdentity(
    string Path,
    string Producer,
    string ArtifactId = "none");

internal static class GeneratedArtifactInventory
{
    internal static ImmutableArray<GeneratedArtifactIdentity> All { get; } = Build();

    private static ImmutableArray<GeneratedArtifactIdentity> Build()
    {
        var artifacts = DocumentDefinitions.All
            .Select(static definition => new GeneratedArtifactIdentity(
                definition.RelativePath.Value,
                nameof(ScribeEmitter)))
            .Concat(
            [
                new GeneratedArtifactIdentity(
                    CanonicalValuesWriter.RelativePath,
                    nameof(ValuesEmitter),
                    "A-VALUES"),
                new GeneratedArtifactIdentity(
                    DagEmitter.RelativePath,
                    nameof(DagEmitter),
                    "A-DAG"),
                new GeneratedArtifactIdentity(
                    DagEmitter.TruthGraphRelativePath,
                    nameof(DagEmitter),
                    "A-TRUTH"),
                new GeneratedArtifactIdentity(
                    FileMapEmitter.RelativePath,
                    nameof(FileMapEmitter),
                    "A-FILEMAP"),
                new GeneratedArtifactIdentity(
                    ScribeEmitter.AttestationRelativePath,
                    nameof(ScribeEmitter),
                    "A-SCRIBE"),
            ])
            .OrderBy(static artifact => artifact.Path, StringComparer.Ordinal)
            .ToImmutableArray();
        if (artifacts.Select(static artifact => artifact.Path)
            .Distinct(StringComparer.Ordinal).Count() != artifacts.Length)
        {
            throw new InvalidOperationException("Generated artifact inventory contains duplicate paths.");
        }

        return artifacts;
    }
}
