using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationArrays;

internal sealed class EtiennePrefixCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted binary matrices with bounded top-left rectangle sums.",
        H("Etienne's width-two prefix matrices"),
        Blocks(
            Paragraph(Text("The objects are actual functions from Fin n to Fin 2 to Bool. "
                + "Rows are lexicographically nondecreasing in the order 00,01,10,11. "
                + "The left column word is lexicographically at most the right column word, "
                + "with zero before one. Repeated rows and equal columns are retained.")),
            Paragraph(Text("For every nonempty top-left i by j rectangle, twice its number "
                + "of ones is at most i*j. Both widths one and two are required. "
                + "The function a is the cardinality of this literal matrix subtype, "
                + "independently of a proposed formula.")),
            Paragraph(Text("A sorted matrix has four consecutive blocks 00,01,10,11. "
                + "The cuts p,q,r count ranks strictly below one, two and three. "
                + "The strict sublevel sets of a monotone word are initial segments, "
                + "so the three sizes reconstruct every entry at its original position.")),
            Paragraph(Text("The full cardinality formula remains an unresolved mathematical "
                + "statement here; the definitions alone do not establish it.")))));
}
