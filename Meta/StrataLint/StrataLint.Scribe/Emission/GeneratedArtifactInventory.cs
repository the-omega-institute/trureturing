using System.Collections.Immutable;

namespace StrataLint.Scribe;

internal sealed record GeneratedArtifactIdentity(
    string Path,
    string Producer,
    string VerifiedBy,
    string ArtifactId = "none");

internal static class GeneratedArtifactInventory
{
    internal const string EchoResidualSummaryPath = "Generated/echo-residual-summary.md";

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
                    "emit-check",
                    "A-ANCHOR"),
                new GeneratedArtifactIdentity(
                    CanonicalValuesWriter.RelativePath,
                    nameof(ValuesEmitter),
                    "emit-check",
                    "A-VALUES"),
                new GeneratedArtifactIdentity(
                    DagEmitter.RelativePath,
                    nameof(DagEmitter),
                    "emit-check",
                    "A-DAG"),
                new GeneratedArtifactIdentity(
                    DagEmitter.TruthGraphRelativePath,
                    nameof(DagEmitter),
                    "emit-check",
                    "A-TRUTH"),
                new GeneratedArtifactIdentity(
                    EchoResidualSummaryPath,
                    "EchoVerifyCommand",
                    "emit-check",
                    "A-ECHO"),
                new GeneratedArtifactIdentity(
                    FileMapEmitter.RelativePath,
                    nameof(FileMapEmitter),
                    "emit-check",
                    "A-FILEMAP"),
                new GeneratedArtifactIdentity(
                    ScribeEmitter.AttestationRelativePath,
                    nameof(ScribeEmitter),
                    "emit-check",
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
