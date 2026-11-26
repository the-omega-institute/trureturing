using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalRankThreeLocalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pencil of the retained baseline determines the common derivative. The original fixed-unit word and the literal coordinate heights supply the remaining hypotheses.",
        H("The original prime-cube Dixon triple"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-original-nonzero-dixon-rank-three"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRankThreeLocal.original_nonzero_dixon_rank_three"),
                H("The original nonzero Dixon local calculation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The original slope V1/R1 and the common word ratio are lifted from the prime-cube ring. The derivative parameter is calculated at the chosen actual baseline modulo p. The original Dixon divisibility and height give exact valuation five, and the coordinate kernel theorem then supplies saturation and the discriminant dichotomy for the actual rows. The physical-coordinate transform and norm ideals enter later in the endpoint proof."))), DescribeRole.Theorem))));
}
