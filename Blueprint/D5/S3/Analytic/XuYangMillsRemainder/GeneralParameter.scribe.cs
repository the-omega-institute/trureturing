using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.XuYangMillsRemainder;

internal sealed class GeneralParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original general-parameter Mills target, Gaussian regularity, origin asymptotic and exponential remainder multiplier orders.",
        H("General-parameter Mills remainder classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("f-normalization"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.F"),
                H("Original signed remainder normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "F n a x is the original signed remainder (-1)^n * D n x a, "
                    + "where D is imported from the frozen Xu-Yang Mills source and retains "
                    + "the Gaussian Mills ratio, Gamma coefficients, and finite truncation.")))),
            Describe.Lean(
                DescribeId.Create("theorem-21-target"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter.theorem21"),
                H("Theorem 2.1 target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every n >= 2 and real a, the positive global-sign predicate is "
                        + "equivalent to complete monotonicity and to a <= theta (n-2); "
                        + "the negative global-sign predicate is equivalent to complete "
                        + "monotonicity of -F and to a >= theta (n-1), with both endpoints "
                        + "included. The proposition is retained as the exact source target.")),
                    Paragraph(Text(
                        "The proposition states two separate equivalences in each chain: "
                        + "global sign iff complete monotonicity, and complete monotonicity iff "
                        + "the sharp parameter bound. It is a target definition, not an asserted theorem. "
                        + "The general-a coefficient identity, exact Laplace representation, "
                        + "weighted-moment comparison, infinity asymptotic and both classification "
                        + "chains remain open."))),
                DescribeRole.Definition),
            Proof("regularity-and-origin", "regularity_and_origin",
                "Gaussian regularity and the original origin asymptotic",
                "For every n >= 2 and every real a, the original F n a is C-infinity on x > 0, "
                + "and x^(2n) F n a x tends to -u n a (a-2) as x decreases to zero. "
                + "The Gaussian tail equals its value at zero minus its interval primitive. "
                + "The fundamental theorem of calculus gives smoothness of that primitive. "
                + "After multiplying the finite remainder by x^(2n), every lower truncation "
                + "term vanishes at zero and only the original nth Gamma coefficient remains."),
            Proof("positive-origin-obstruction", "positive_cm_necessary",
                "Necessary coefficient sign for the positive branch",
                "If the original F n a is completely monotone, then u n a (a-2) <= 0. "
                + "The proof consumes the zeroth derivative sign and the concrete origin limit. "
                + "The stronger hypothesis that F is globally nonnegative alone suffices, "
                + "as established by positive_sign_necessary. Translating this coefficient sign "
                + "to a <= theta (n-2) still requires the general-a coefficient identity."),
            Proof("negative-origin-obstruction", "negative_cm_necessary",
                "Origin obstruction for the negative branch",
                "If -F n a is completely monotone, or merely globally nonnegative, "
                + "then u n a (a-2) >= 0. This is the obstruction at the origin; "
                + "it does not establish the required infinity obstruction u (n+1) a (a-2) >= 0 "
                + "or the sharp negative-branch threshold theta (n-1)."),
            Proof("remainder-upper-multiplier", "exp_remainder_ratio_strictAnti",
                "Strictly decreasing upper normalized remainder",
                "Write E_k(y) = (-1)^k (exp(-y) - sum_{j<k} (-y)^j/j!). "
                + "For every k >= 1, E_k(y)/y^k strictly decreases on y > 0. "
                + "The proof uses the existing public ExpRemainderDifferences.R with k=r+1, "
                + "then the pinned Mathlib Taylor integral theorem gives "
                + "E_k(y)/y^k = integral_0^1 (1-s)^(k-1) exp(-sy) ds / (k-1)!. "
                + "Strict integral comparison at s=1/2 proves the multiplier order."),
            Proof("remainder-lower-multiplier", "exp_remainder_ratio_strictMono",
                "Strictly increasing lower normalized remainder",
                "For every k >= 1, E_k(y)/y^(k-1) strictly increases on y > 0. "
                + "Changing variables in the same Taylor integral gives "
                + "E_k(y)/y^(k-1) = integral_0^y (1-q/y)^(k-1) exp(-q) dq / (k-1)!. "
                + "Increasing y increases the integrand on the old interval and adds a strictly "
                + "positive interval. This includes k=1. These two multiplier orders are the "
                + "inputs required for the source's weighted-moment comparison; that comparison "
                + "and its application to the signed Mills kernel are not asserted here."))));

    private static DocumentBlock Proof(string id, string name, string title, string narrative) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(
                "D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter." + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))),
            DescribeRole.Theorem);
}
