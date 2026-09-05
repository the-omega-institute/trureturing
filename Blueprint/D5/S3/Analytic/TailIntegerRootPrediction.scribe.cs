using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class TailIntegerRootPredictionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/TailIntegerRootPrediction.tail_integer_roots_are_exact";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The row-eight and row-ten tail polynomials have exactly the predicted integer roots.",
        H("Exact Integer Roots of Two Golden Tail Rows"),
        Blocks(Describe.Lean(
            DescribeId.Create("row-eight-and-row-ten-tail-roots-are-exact"),
            DeclarationHandle.Create(Declaration),
            H("The two predicted tail roots are unique"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a row with only its first two principal parts present, the tail "
                        + "specializes to P1 times choose(b,0) plus P2 times choose(b+1,1). "
                        + "The displayed row-eight values P1 = 42 and P2 = -1/2 therefore "
                        + "give a zero exactly at b = 83. The row-ten values P1 = 336 and "
                        + "P2 = -8 give a zero exactly at b = 41.")),
                Paragraph(Text(
                    "The proof uses Mathlib's Nat.choose_zero_right and "
                        + "Nat.choose_one_right to reduce both binomial-basis expressions "
                        + "to affine rational equations. Exact cast transport and linear "
                        + "arithmetic prove both directions, so the two displayed values are "
                        + "roots and no other natural-number arguments are roots.")),
                Paragraph(Text(
                    "This theorem formalizes only the source atom's two tail-polynomial root "
                        + "predictions. It does not assert the separate bridge from a tail root "
                        + "to an e-table coefficient, the all-order principal-part formula, "
                        + "the finite-part cancellations, or the empirical onset law.")),
                Paragraph(Text(
                    "Repository, digestion, digest, git-history, generalized theorem-shape, "
                        + "and in-flight searches found no existing declaration for either "
                        + "root. The escape witness is the public equivalence itself: the two "
                        + "source-specific rational cancellations compute new exact and unique "
                        + "natural roots rather than projecting a frozen theorem."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("b");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula tailEight = new Formula.Subscript(F.Id("T"), D(8));
        Formula tailTen = new Formula.Subscript(F.Id("T"), D(1, 0));

        return Disp(Seq(
            Open, Forall, Sp, b, Sp, InMacro, Sp, naturals, Comma, Esc,
            tailEight, Open, b, Close, Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            b, Sp, Eq, Sp, D(8, 3), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, b, Sp, InMacro, Sp, naturals, Comma, Esc,
            tailTen, Open, b, Close, Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            b, Sp, Eq, Sp, D(4, 1), Close, Dot));
    }
}
