using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class FiniteFieldQuadraticCharacterSumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef LidlNiederreiter =
        LibraryNoteRef.Create("D5/L/ArithSums/lidlniederreiter1997finitefields");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shifted quadratic character sum over an odd finite field is -1 away from the singular parameter.",
        H("Shifted Quadratic Character Sum over a Finite Field"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shifted-quadratic-character-sum-is-minus-one"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FiniteFieldQuadraticCharacterSum.quadraticChar_shift_square_sum"),
                H("The shifted quadratic character sum is minus one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("F"), Comma, Sp, F.Id("a"), Comma, Sp,
                    F.Id("ringChar"), Open, F.Id("F"), Close, Neq, D(2), Sp,
                    Land, Sp, F.Id("a"), Neq, D(0), Sp, Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("x"), InMacro, Sp, F.Id("F")), Sp,
                    Operatorname, Grp(F.Id("quadraticChar")), Open, F.Id("F"), Close,
                    Open, F.Id("x"), Caret, Grp(D(2)), Minus, F.Id("a"), Close,
                    Eq, Minus, D(1), Dot))),
                AssessedProvenance.FromLiterature(LidlNiederreiter),
                Blocks(
                    Paragraph(Text(
                        "For a finite field of odd characteristic and a nonzero shift a, the quadratic character of x squared minus a sums to minus one over all x. The proof counts the conic y squared equals x squared minus a.")),
                    Paragraph(Text(
                        "The change of variables u equals x minus y and v equals x plus y is invertible exactly because the characteristic is not two. The equation becomes uv equals a, which has one point for every nonzero u. The hypothesis a nonzero excludes the singular boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shifted-square-conic-has-q-minus-one-points"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FiniteFieldQuadraticCharacterSum.conic_card_eq_card_field_sub_one"),
                H("The shifted-square conic has q minus one points"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("F"), Comma, Sp, F.Id("a"), Comma, Sp,
                    F.Id("ringChar"), Open, F.Id("F"), Close, Neq, D(2), Sp,
                    Land, Sp, F.Id("a"), Neq, D(0), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("Conic")), Open, F.Id("F"),
                    Comma, Sp, F.Id("a"), Close, Close,
                    Eq, F.Id("card"), Open, F.Id("F"), Close, Minus, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This helper is the finite point-counting statement used by the character-sum theorem. Its proof factors the conic through the hyperbola uv equals a and then through the nonzero elements of F."))),
                DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/ArithUnits/FiniteFieldTwoSquares"))]));
}
