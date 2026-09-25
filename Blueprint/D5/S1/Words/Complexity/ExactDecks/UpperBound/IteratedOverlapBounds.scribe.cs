using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.UpperBound;

internal sealed class ExactDecksUpperBoundIteratedOverlapBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterated infiltrations isolate their maximal-length ordinary shuffles.",
        H("IteratedOverlapBounds"),
        Blocks(
            Paragraph(Text(
                "The infiltration product and its top-degree shuffle stratum are classical and "
                + "are also used in the cited source. The list-valued definitions retain one "
                + "entry per alignment, so coincident output words remain repeated. The final "
                + "unconditional recovery theorem is the repository bridge used by the exact "
                + "asymptotic upper injection.")))));

}
