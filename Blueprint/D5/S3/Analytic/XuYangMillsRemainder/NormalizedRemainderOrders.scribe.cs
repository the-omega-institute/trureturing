using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class NormalizedRemainderOrdersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Mills normalization and complete classification.",
        H("Normalized exponential remainder orders"),
        Blocks(
            Proof("normalized-remainder-integral", "normalized_exp_remainder",
                "The exact normalized Taylor remainder integral",
                "For every natural r and y>0, the signed remainder divided by y^(r+1) "
                + "equals the integral of (1-s)^r exp(-sy) over [0,1], divided by r!. "
                + "The original remainder and its normalization are retained."),
            Proof("remainder-upper-multiplier", "exp_remainder_ratio_strict_anti",
                "Strictly decreasing upper normalized remainder",
                "Write E_k(y) = (-1)^k (exp(-y) - sum_{j<k} (-y)^j/j!). "
                + "For every k >= 1, E_k(y)/y^k strictly decreases on y > 0. "
                + "The proof uses the existing public ExpRemainderDifferences.R with k=r+1, "
                + "then the pinned Mathlib Taylor integral theorem gives "
                + "E_k(y)/y^k = integral_0^1 (1-s)^(k-1) exp(-sy) ds / (k-1)!. "
                + "Strict integral comparison at s=1/2 proves the multiplier order."),
            Proof("remainder-lower-multiplier", "exp_remainder_ratio_strict_mono",
                "Strictly increasing lower normalized remainder",
                "For every k >= 1, E_k(y)/y^(k-1) strictly increases on y > 0. "
                + "Changing variables in the same Taylor integral gives "
                + "E_k(y)/y^(k-1) = integral_0^y (1-q/y)^(k-1) exp(-q) dq / (k-1)!. "
                + "Increasing y increases the integrand on the old interval and adds a strictly "
                + "positive interval. This includes k=1."))));

    private static DocumentBlock Proof(string id, string name, string title, string narrative) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(
                "D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders." + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))),
            DescribeRole.Theorem);
}
