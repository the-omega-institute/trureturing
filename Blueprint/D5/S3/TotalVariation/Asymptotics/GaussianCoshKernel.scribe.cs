using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class GaussianCoshKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Gaussian positive-part cosh integral has a uniform local expansion on every positive compact interval.",
        H("A uniform Gaussian-cosh local kernel"),
        Blocks(
            Paragraph(Text("Write phi for the existing standard normal density, with the exact normalization"),
                Math(Disp(All("u", R, Seq(PhiAt(I("u")), Eq,
                    Fr(Call("exp", Seq(Minus, Fr(Pow(I("u"), D(2)), D(2)))),
                        Seq(Sqrt, Grp(D(2), Pi)))))))),
            Paragraph(Text("Use the following kernel, with the positive part taken before integration:"),
                Math(Disp(All("q", R, All("d", R, All("u", R,
                    Seq(Call("K", I("q"), I("d"), I("u")), Eq,
                        PhiAt(I("u")), Cdot, Sp, Clip(I("q"), I("d"), I("u"))))))))),
            Describe.Lean(
                DescribeId.Create("gaussian-cosh-integral"),
                DeclarationHandle.Create(Prefix + "gaussianCoshIntegral"),
                H("The actual clipped Gaussian integral"),
                StatementSource.FromAuthor(Disp(All("q", R, All("d", R,
                    Seq(Call("J", I("q"), I("d")), Eq, Int, Underscore, Grp(R), Sp,
                        Call("K", I("q"), I("d"), I("u")), Sp, I("du")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral uses Lebesgue measure on the whole real line. "
                    + "Its integrand is bounded by exp(d) times the standard normal density, so it is "
                    + "integrable for every real q and d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("all-parameter-integrability"),
                DeclarationHandle.Create(Prefix + "kernel_integrable"),
                H("Integrability for every real parameter"),
                StatementSource.FromAuthor(Disp(All("q", R, All("d", R,
                    Call("Integrable", Call("K", I("q"), I("d"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonnegative clipped integrand is at most exp(d) "
                    + "times the standard normal density. This gives integrability without "
                    + "any sign or smallness restriction on either real parameter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-uniform-remainder"),
                DeclarationHandle.Create(Prefix + "gaussian_cosh_uniform_remainder"),
                H("The exact coefficient and a uniform fifth-half-power remainder"),
                StatementSource.FromAuthor(UniformFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every fixed positive lower endpoint, one choice is delta=1/4 "
                        + "and C=4 phi(0)(5+2/lo^2)/lo. The same constants work for every q in the "
                        + "closed interval, including a singleton interval. The theorem also allows "
                        + "an upper endpoint below the lower endpoint, in which case the interval is empty.")),
                    Paragraph(Text("Compare the clipped kernel with phi(0) times the positive part "
                        + "of d-(qu)^2/2. For d at most 1/4, both vanish outside the interval "
                        + "|u| at most 2 sqrt(d)/q. The cosh series gives cosh(x) at least 1+x^2/2. "
                        + "The upper bound cosh(x) at most exp(x^2/2), combined with the quadratic "
                        + "exponential remainder, bounds the clipped-kernel discrepancy by 5d^2.")),
                    Paragraph(Text("The density changes by at most phi(0)u^2/2 from its value at zero. "
                        + "On the common interval, u^2 is at most 4d/lo^2. Thus the weighted integrand "
                        + "error is at most phi(0)(5+2/lo^2)d^2. Its integration interval has length "
                        + "4 sqrt(d)/q. The exact integral of the leading clipped parabola is "
                        + "4 sqrt(2)d^(3/2)/(3q), giving the stated coefficient and remainder.")),
                    Paragraph(Text("This is the local-kernel estimate in equation 14.5 of the "
                        + "categorical decision blindness theory, strengthened to arbitrary positive "
                        + "compact intervals. It does not assert a Bayes-risk identity or either complete "
                        + "crossover theorem. The powers are real powers and d is strictly positive."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Zeros/Jensen/FactorialJensenKernelBound"))]));

    private static Formula I(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(I("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(I(name), [.. args]);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula PhiAt(Formula x) => Seq(Varphi, Open, x, Close);
    private static Formula Clip(Formula q, Formula d, Formula u) =>
        Seq(Max, Grp(OpenBrace,
            Call("exp", d), Minus, Call("cosh", Seq(q, Cdot, Sp, u)), Comma, D(0), CloseBrace));
    private static Formula UniformFormula()
    {
        Formula lo = I("lo"), hi = I("hi"), q = I("q"), d = I("d"), c = I("C");
        Formula coefficient = Fr(Seq(D(4), Sqrt, Grp(D(2)), PhiAt(D(0))), Seq(D(3), Cdot, Sp, q));
        Formula error = new Formula.Absolute(Seq(Call("J", q, d), Minus,
            coefficient, Cdot, Sp, Pow(d, Fr(D(3), D(2)))));
        Formula conclusion = Seq(Call("Integrable", Call("K", q, d)), Land, Sp,
            error, Le, Sp, c, Cdot, Sp, Pow(d, Fr(D(5), D(2))));
        Formula parameters = All("q", R, Seq(q, InMacro, Sp,
            OpenBracket, lo, Comma, hi, CloseBracket, Rightarrow, Sp,
            All("d", R, Seq(D(0), Lt, Sp, d, Land, Sp, d, Le, Sp, I("delta"), Rightarrow, Sp, conclusion))));
        return Disp(All("lo", R, All("hi", R, Seq(D(0), Lt, Sp, lo, Rightarrow, Sp,
            Ex("delta", R, Ex("C", R, Seq(D(0), Lt, Sp, I("delta"), Land, Sp,
                D(0), Le, Sp, c, Land, Sp, parameters)))))));
    }
}
