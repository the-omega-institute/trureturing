using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class GeometricNumeratorParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A geometric numerator cancels the quadratic denominator exactly at even capacities.",
        H("Geometric Numerator Parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geometric-numerator-divisible-iff-even"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/GeometricNumeratorParity."
                    + "geometric_numerator_divisible_iff_even"),
                H("The quadratic denominator divides exactly at even capacities"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("cap"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Open, F.Id("X"), Caret, Grp(D(2)), Minus, D(1), Close,
                    Sp, Mid, Sp,
                    Open, F.Id("X"), Caret, Grp(F.Id("cap")), Minus, D(1), Close,
                    Sp, Iff, Sp,
                    Operatorname, Grp(F.Id("Even")), Open, F.Id("cap"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the integer polynomial X^cap-1, the factor X^2-1 cancels exactly "
                        + "when cap is even. In the forward direction, evaluating a claimed "
                        + "divisibility at X=-1 forces (-1)^cap=1 and hence even parity. In the "
                        + "reverse direction, even parity gives 2 divides cap, so Mathlib's "
                        + "generic power-difference divisibility theorem applies directly.")),
                    Paragraph(Text(
                        "This closes only clause (ii) of source theorem 6.53: the parity criterion "
                        + "for cancellation of the geometric numerator by the quadratic "
                        + "denominator. It does not close the fiber bijection, the row-tail residue "
                        + "identification, the generating-function coefficient formula, or the "
                        + "subsequent numerical predictions in the same atom.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no exact biconditional. The "
                        + "proof reuses dvd_pow_sub_one_of_dvd, Polynomial.eval_dvd, and "
                        + "neg_one_pow_eq_one_iff_even. An external GitHub and Loogle domain search "
                        + "through NyxID and Tavily found no exact match."))),
                DescribeRole.Theorem))));
}
