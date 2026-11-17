using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SixBoundarySideCountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private helpers consumed by the actual six-boundary side-gap theorem.",
        H("Actual degree slices and short paths"),
        Blocks(Paragraph(Text("Private helpers retain actual left roots and the actual degree-zero through degree-three right slices. Existing GirthSliceCounting.one_three_paths_card_le_rectangle supplies the path injection. Reindexing real paths gives 3e+2 sum_R d(d-1) at most eo. Exact incidence counts reduce small left cardinalities to zero, one, eleven or twelve; a local root count gives fifteen distinct right endpoints if all three first neighbors have degree three. The eleven and twelve degree spectra and the unique deficient left label are derived without a minimum-degree assumption on R."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting"))
        ]));
}
