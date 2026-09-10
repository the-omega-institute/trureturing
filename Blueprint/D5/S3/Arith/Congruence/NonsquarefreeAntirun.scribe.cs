using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class NonsquarefreeAntirunDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full intervals of nonsquarefree numbers with successive gaps greater than one have at most nine entries.",
        H("The sharp bound for nonsquarefree antiruns"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonsquarefree-antirun-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/NonsquarefreeAntirun.antirun_length_le_nine"),
                H("Every nonsquarefree antirun has length at most nine"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/wiseman2024antiruns")),
                Blocks(
                    Paragraph(Text(
                        "FullNonsquarefreeInterval requires a strictly increasing list, "
                        + "nonsquarefreeness of every entry, and membership of every nonsquarefree "
                        + "number between any two entries. Thus the list occupies consecutive "
                        + "positions in the increasing enumeration. The antirun need not be maximal.")),
                    Paragraph(Text(
                        "Multiples of four and nine force adjacent pairs at offsets 8 and 9, "
                        + "and at offsets 27 and 28, in every block of 36 integers. A full antirun "
                        + "cannot cross either pair. Ten entries separated by at least two need "
                        + "a span of at least 18. The only remaining interval has offsets 9 through "
                        + "27, forcing the second entry to have offset 11. Fullness also requires "
                        + "the multiple of four at offset 12, contradicting the gap condition.")),
                    Paragraph(Text(
                        "The private theorem nine_term_witness verifies the full interval "
                        + "6345, 6348, 6350, 6352, 6354, 6356, 6358, 6360, 6363, including "
                        + "all intervening numbers and every gap. Its length is nine, so the bound "
                        + "is attained."))),
                DescribeRole.Theorem))));
}
