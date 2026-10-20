using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class DeformedJucysMurphyCutsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal rotation displacement supplies every positive ordered native cut.",
        H("Native Rotation Cuts and Their Occurrences"),
        Blocks(Paragraph(Text("The cut proof follows the actual product rotation and its exact "
            + "period. Conjugating equal-charge vertices at displacement d splits a component "
            + "with r identity edges into d and r-d, for every 0<d<r. The proof excludes the "
            + "other charge sheet and proves the reverse identity-partner orientation gives the "
            + "same complete type. The rotation powers identify the r actual edge occurrences "
            + "bijectively, so the two orientations give coefficient r/2 on the positive ordered "
            + "cut sum. Equal cuts, adjacent cuts, repeated parts, partner degeneracies and "
            + "the empty cut range at r=1 are all retained. The exact counted row feeds "
            + "native_row in the canonical Row owner, where its public statement is described.")))));
}
