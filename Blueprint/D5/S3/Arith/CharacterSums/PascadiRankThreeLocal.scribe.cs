using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiRankThreeLocalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The surviving term of the Dixon determinant modulo the sixth prime power supplies a unit three-column minor and controls both discriminant strata.",
        H("The coordinate kernel of a nonzero Dixon triple"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-rankthreekernel"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.RankThreeKernel"),
                H("Primitive coordinate kernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The original three quadratic cofactors are one common multiple of a primitive polynomial. The leading cofactor is a unit modulo p. The integer discriminant factor, its real height, the two strata, and the ramified derivative gap are kept in the same statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-nonzero-dixon-rank-three"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiRankThreeLocal.nonzero_dixon_rank_three"),
                H("Saturation and the two discriminant strata"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The constant and linear columns after translation and common-parameter subtraction are divisible by the third and first powers of p. In the original Dixon determinant only one term of degree five survives modulo the sixth power. Its factors give the unit minor and exclude the simultaneous fourth-power value and second-power derivative divisibilities. The original coordinate heights give the bound 23328 (I J)^4 / p^2 for the discriminant factor."))), DescribeRole.Theorem))));
}
