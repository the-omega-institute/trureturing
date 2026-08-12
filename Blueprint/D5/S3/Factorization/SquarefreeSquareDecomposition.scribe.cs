using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class SquarefreeSquareDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squarefree-times-square factorization of a positive integer is unique.",
        H("Uniqueness of the Squarefree-Square Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("squarefree-square-decomposition-unique"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/SquarefreeSquareDecomposition.bcs_square_squarefree_unique"),
                H("The squarefree-times-square factorization is unique"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Squarefree")), Sp, F.Id("a"), Underscore, D(1), Comma, Sp,
                    Operatorname, Grp(F.Id("Squarefree")), Sp, F.Id("a"), Underscore, D(2), Comma, Sp,
                    F.Id("b"), Underscore, D(1), Sp, Neq, Sp, D(0), Comma, Sp,
                    F.Id("b"), Underscore, D(1), Caret, Grp(D(2)), F.Id("a"), Underscore, D(1), Sp,
                    Eq, Sp, F.Id("b"), Underscore, D(2), Caret, Grp(D(2)), F.Id("a"), Underscore, D(2), RowBreak,
                    Rightarrow, Sp, F.Id("a"), Underscore, D(1), Sp, Eq, Sp, F.Id("a"), Underscore, D(2), Sp,
                    Land, Sp, F.Id("b"), Underscore, D(1), Sp, Eq, Sp, F.Id("b"), Underscore, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every positive integer's factorization as a squarefree number times a perfect square is "
                        + "unique. If b1^2 * a1 = b2^2 * a2 with a1 and a2 squarefree and b1 not zero, then the "
                        + "squarefree parts agree (a1 = a2) and the square roots agree (b1 = b2). The hypothesis "
                        + "b1 not zero (equivalently n not zero) is essential: n = 0 leaves the squarefree part "
                        + "unconstrained.")),
                    Paragraph(Text(
                        "The proof is prime by prime. The p-adic valuation of n = b^2 * a is v_p(n) = 2 v_p(b) + "
                        + "v_p(a), and squarefreeness bounds v_p(a) <= 1. Two values in {0,1} that leave the same "
                        + "residue modulo 2 (as forced by the common v_p(n)) are equal, so v_p(a1) = v_p(a2) at "
                        + "every prime; hence a1 = a2 by equality of factorizations. Cancelling the common "
                        + "squarefree part gives b1^2 = b2^2, and squaring is injective on the naturals, so "
                        + "b1 = b2.")),
                    Paragraph(Text(
                        "Mathlib supplies only the existence of the squarefree-times-square decomposition "
                        + "(Nat.sq_mul_squarefree), not the uniqueness recorded here, so this is a genuine "
                        + "addition. It is the uniqueness half of the BCS decomposition, part P1 of the source's "
                        + "three-part arithmetic-statistics theorem; the existence half, the k-free ladder (P2), "
                        + "and the Mobius / reciprocal-zeta identity (P3) are not covered."))),
                DescribeRole.Theorem
            )),
        []));
}
