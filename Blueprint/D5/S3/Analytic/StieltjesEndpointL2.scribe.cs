using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class StieltjesEndpointL2Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/StieltjesEndpointL2";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pointwise L2 cap controls the integral against the singular Stieltjes weight.",
        H("Stieltjes endpoint L2 estimate"),
        Blocks(
            Item("l2Norm", "Interval L2 norm of a real profile",
                "The quantity L_b(q) is the square root of the integral of q(t)^2 from zero to b.",
                DescribeRole.Definition),
            Item("stieltjesWeight", "Stieltjes weight",
                "The weight w(t) is the reciprocal of the real square root of t(1+t).",
                DescribeRole.Definition),
            Item("integral_div_sqrt_le_of_pos", "The endpoint split",
                "Let b>0 and M≥1, with q continuous and nonnegative on [0,b]. If q(t)≤M L_b(q)/sqrt(b) "
                + "throughout [0,b], the integral of q(t)/sqrt(t) is at most "
                + "(2+sqrt(2 log M)) L_b(q). Split at s=b/M^2. The cap and the integral of 1/sqrt(t) "
                + "give the first piece a bound of 2 L_b(q). On [s,b], Cauchy–Schwarz gives the second "
                + "piece a bound of sqrt(2 log M) L_b(q) since the squared weight integrates to log(b/s)."),
            Item("integral_stieltjes_mul_norm_le", "Weighted norm profile",
                "Let F be continuous on [0,b] with values in a normed additive commutative group, where b>0 "
                + "and M≥1. If q(t)=norm(F(t)) satisfies q(t)≤M L_b(q)/sqrt(b) there, w(t)q(t) is interval "
                + "integrable and its integral is at most (2+sqrt(2 log M)) L_b(q). "
                + "On the nonnegative ray the Stieltjes weight is bounded above by 1/sqrt(t)."),
            Item("norm_integral_stieltjes_smul_le", "Norm of the Stieltjes integral",
                "Under the same continuity and cap hypotheses in a complete real normed space, "
                + "w(t) times F(t) is interval integrable and the norm of its Bochner integral is at most "
                + "(2+sqrt(2 log M)) L_b(norm(F)). This includes Hilbert-space profiles "
                + "of the kind used for the short-interval residual in sharp Gibbs recovery."),
            Item("polynomial_norm_le_cap", "Degree controls the pointwise cap",
                "For a natural d and a complex polynomial p of degree below d in WithBot(Nat), at every "
                + "real x in [0,1], norm(p(x))≤(1+d^2) L_1(norm(p)). Evaluation embeds the real input "
                + "in the complex numbers. The fundamental theorem of calculus bounds each difference "
                + "p(x)−p(y) by the integral of norm(p'). Averaging in y and applying Cauchy–Schwarz and "
                + "the canonical complex-polynomial derivative energy estimate gives the cap. "
                + "The degree condition includes p=0 when d=0."),
            Item("integral_stieltjes_polynomial_norm_le", "Complex-polynomial Stieltjes bound",
                "For a natural d and a complex polynomial p of degree below d in WithBot(Nat), "
                + "w(t) norm(p(t)) is interval integrable on [0,1]. Its integral there is at most "
                + "(2+sqrt(2 log(1+d^2))) L_1(norm(p)). The degree cap supplies M=1+d^2 in the endpoint "
                + "bound, so the logarithm depends on degree through a polynomial in d."))));

    private static DocumentBlock Item(string name, string title, string explanation,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);
}
