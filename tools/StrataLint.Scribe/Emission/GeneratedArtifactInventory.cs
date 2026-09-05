using System.Collections.Immutable;
using Trureturing.Truth;

namespace StrataLint.Scribe;

internal sealed record GeneratedArtifactIdentity(
    string Path,
    string Producer,
    string ArtifactId = "none");

internal static class GeneratedArtifactInventory
{
    internal static ImmutableArray<GeneratedArtifactIdentity> Create(
        IEnumerable<DocumentDefinition> definitions)
    {
        ArgumentNullException.ThrowIfNull(definitions);
        return Create(definitions.Select(static definition => definition.RelativePath.Value));
    }

    internal static ImmutableArray<GeneratedArtifactIdentity> Create(
        IEnumerable<string> documentPaths)
    {
        ArgumentNullException.ThrowIfNull(documentPaths);
        var artifacts = documentPaths
            .Select(static path => new GeneratedArtifactIdentity(
                path,
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
                    "Generated/truth-export.v1.json",
                    TruthExportModel.ProducerName,
                    "A-TRUTHEXPORT"),
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
