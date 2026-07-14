using System.Collections.Immutable;

namespace StrataLint.Scribe;

internal sealed record GeneratedArtifactIdentity(
    string Path,
    string Producer,
    string VerifiedBy);

internal static class GeneratedArtifactInventory
{
    internal static ImmutableArray<GeneratedArtifactIdentity> All { get; } = Build();

    private static ImmutableArray<GeneratedArtifactIdentity> Build()
    {
        var artifacts = DocumentDefinitions.All
            .Select(static definition => new GeneratedArtifactIdentity(
                definition.RelativePath.Value,
                nameof(ScribeEmitter),
                "emit-check"))
            .Concat(
            [
                new GeneratedArtifactIdentity(
                    CanonicalAnchorCatalogWriter.RelativePath,
                    nameof(AnchorCatalogEmitter),
                    "emit-check"),
                new GeneratedArtifactIdentity(
                    CanonicalValuesWriter.RelativePath,
                    nameof(ValuesEmitter),
                    "emit-check"),
                new GeneratedArtifactIdentity(
                    FileMapEmitter.RelativePath,
                    nameof(FileMapEmitter),
                    "emit-check"),
                new GeneratedArtifactIdentity(
                    ScribeEmitter.AttestationRelativePath,
                    nameof(ScribeEmitter),
                    "emit-check"),
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
