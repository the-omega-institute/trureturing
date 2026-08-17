using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class RightHalfReflectionCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var half = new Formula.Fraction(Num(1), Num(2));
        var reflected = Seq(
            F.Id("P"), Open, D(1), Minus, F.Id("x"), Close,
            Sp, Leftrightarrow, Sp, F.Id("P"), Open, F.Id("x"), Close);
        var fixedPoint = Seq(
            F.Id("P"), Open, F.Id("x"), Close, Sp, Rightarrow, Sp,
            F.Id("x"), Sp, Eq, Sp, half);
        var rightFixedPoint = Seq(
            F.Id("P"), Open, F.Id("x"), Close, Sp, Rightarrow, Sp,
            half, Sp, Le, Sp, F.Id("x"), Sp, Rightarrow, Sp,
            F.Id("x"), Sp, Eq, Sp, half);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Reflection symmetry reduces a fixed-point claim to the right half.",
            H("Right-Half Reflection Criterion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("reflection-symmetric-right-half-criterion"),
                    DeclarationHandle.Create(
                        "D5/S3/Zeros/Symmetry/RightHalfReflectionCriterion."
                        + "reflection_symmetric_right_half_iff"),
                    H("Reflection symmetry makes the right-half criterion sufficient"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("K"), Comma, Esc,
                        reflected, Close, Sp, Rightarrow, Sp,
                        Open,
                        Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("K"), Comma, Esc,
                        fixedPoint, Close,
                        Sp, Leftrightarrow, Sp,
                        Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("K"), Comma, Esc,
                        rightFixedPoint, Close,
                        Close, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let K be a linearly ordered field and P a predicate invariant under "
                            + "reflection x maps to one minus x. The global claim that every P-point "
                            + "equals one half is equivalent to its restriction to P-points at or "
                            + "to the right of one half. A point left of one half reflects to the "
                            + "right, where the restricted hypothesis fixes it; reflecting back "
                            + "then fixes the original point.")),
                        Paragraph(Text(
                            "This closes only the symmetry-reduction sentence in the source clause. "
                            + "It does not assert the zeta functional equation, a zero-free region, "
                            + "the Riemann hypothesis, or any numerical window certificate."))),
                    DescribeRole.Theorem)),
            []));
    }
}
