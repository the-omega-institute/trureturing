using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe.Definitions;

public sealed record PilotDocument(ScribeDocument Document)
{
    public RepoPath RelativePath => Document.Header.MirrorBlueprint.Path;
}

public static class PilotDocuments
{
    public static ImmutableArray<PilotDocument> All { get; } =
    [
        new(PhaseBasicDocument.Create()),
        new(ScaleEmbeddingDocument.Create()),
        new(ScaleLogDocument.Create()),
    ];
}
