using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class BetaIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta moments and integral formulas for the Kummer function.",
        H("Beta integral representation"), Blocks(
            Describe.Lean(DescribeId.Create("kummer-real-beta-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta"),
                H("Real beta moments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real p and q, the integral over the unit interval of t raised to p minus one times one minus t raised to q minus one equals Gamma(p) Gamma(q) divided by Gamma(p+q). The complex beta identity transfers to this real integral because both bases are nonnegative on the integration interval."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kummer-beta-integrability"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta"),
                H("Integrable beta weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive shape parameters, the real beta weight is integrable over the unit interval. This follows by taking the real part of the convergent complex beta integrand."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kummer-gamma-pochhammer"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer"),
                H("Gamma shifts and rising factorials"), StatementSource.FromAuthor(Disp(All("s", F.Id("Real"), Implies(Lt(Num(0), F.Id("s")), All("n", F.Id("Nat"), Equal(App(Qualified("Real", "Gamma"), Add(F.Id("s"), F.Id("n"))), Multiply(App(Qualified("Polynomial", "eval"), F.Id("s"), Call("ascPochhammer", F.Id("Real"), F.Id("n"))), App(Qualified("Real", "Gamma"), F.Id("s"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive real s and natural n, Real.Gamma(s+n) equals the evaluation of ascPochhammer Real n at s times Real.Gamma(s). Division by the positive Real.Gamma(s) supplies the Gamma ratio used by KarpZhangGamma.Kernel.binomialGamma_sum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kummer-beta-representation"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/BetaIntegral.kummer_eq_betaIntegral"),
                H("The beta representation of Kummer's function"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When zero is less than s and s is less than c, Kummer's function M(s;c;x) is the integral of exp(xt) against the beta weight t^(s-1)(1-t)^(c-s-1), multiplied by Gamma(c)/(Gamma(s) Gamma(c-s)). The exponential series is integrated term by term. The terms in absolute value are bounded by the beta weight multiplied by |x|^n/n!, whose sum is integrable. The Gamma and ascending Pochhammer identity identifies each resulting beta moment with the defining Kummer coefficient."))),
                DescribeRole.Theorem))));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
}
