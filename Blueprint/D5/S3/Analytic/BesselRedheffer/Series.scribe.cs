using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRedheffer;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergence and differential identities of the normalized Bessel series.",
        H("The normalized Bessel series"), Blocks(
            FormulaEntry("bessel-coeff", "coeff", "The normalized coefficients",
                All("b", R, All("n", N, Eqn(Call("coeff", V("b"), V("n")),
                    Fr(D(1), Mul(Call("Nat.factorial", V("n")), Poch(V("b"), V("n"))))))),
                "The coefficient is the reciprocal of the factorial times the rising factorial.",
                DescribeRole.Definition),
            FormulaEntry("bessel-coeff-succ", "coeff_succ", "The coefficient recurrence",
                All("b", R, Imp(Pos(V("b")), All("n", N,
                    Eqn(Call("coeff", V("b"), Add(V("n"), D(1))),
                        Mul(Fr(Fr(D(1), Add(V("b"), V("n"))), Add(V("n"), D(1))),
                            Call("coeff", V("b"), V("n"))))))),
                "For a positive lower parameter, the rising-factorial and factorial recurrences determine the next coefficient."),
            FormulaEntry("bessel-norm-series", "summable_norm_series", "Absolute convergence at every argument",
                All("b", R, Imp(Pos(V("b")), All("t", R,
                    Call("Summable", Seq(V("n"), Colon, Sp, N, Mapsto, Sp,
                        new Formula.Norm(Mul(Call("coeff", V("b"), V("n")),
                            new Formula.Power(V("t"), V("n"))))))))),
                "For a positive lower parameter and every real t, the weighted coefficient series is absolutely summable."),
            Entry("bessel-summable", "summable_nbessel", "Absolute convergence",
                "For order nu greater than -1 and every real argument x, the defining series converges absolutely. The ratio of successive coefficient magnitudes is 1/((nu+1+n)(n+1)); multiplying by any fixed argument still gives a sequence tending to zero."),
            Entry("bessel-zero", "nbessel_zero", "The value at the origin",
                "For every real order nu the value at zero is one, since only the constant term contributes."),
            Entry("bessel-derivative", "hasDerivAt_nbessel", "Differentiation raises the order",
                "For nu greater than -1, the derivative at every real x is -x/(2(nu+1)) times the normalized Bessel function of order nu+1. The auxiliary series in t=-x squared/4 has derivative equal to the series with its lower parameter raised by one, divided by the original lower parameter. On a bounded interval the differentiated series has an absolutely summable uniform majorant."),
            Entry("bessel-continuous", "continuous_nbessel", "Continuity",
                "For nu greater than -1, the normalized Bessel function is continuous on the real line."),
            Entry("bessel-near-zero", "nbessel_pos_near_zero", "Positivity near zero",
                "For nu greater than -1 the normalized series is positive in a neighbourhood of zero, since it is continuous and its value at zero is one."),
            Entry("bessel-contiguous", "nbessel_contiguous", "Three consecutive orders",
                "For nu greater than -1, the series of order nu equals the series of order nu+1 minus x squared divided by 4(nu+1)(nu+2) times the series of order nu+2. The rising factorial recurrence gives the coefficient identity and absolute convergence permits summation."),
            Entry("bessel-second-derivative", "hasDerivAt_nbessel_deriv", "A second derivative",
                "For nu greater than -1, the derivative of -x/(2(nu+1)) times the series of order nu+1 is -1/(2(nu+1)) times that series plus x squared divided by 4(nu+1)(nu+2) times the series of order nu+2."),
            Entry("bessel-equation", "nbessel_ode", "The normalized Bessel equation",
                "The second derivative multiplied by x, plus the first derivative multiplied by 2nu+1, plus x times the normalized series, vanishes for every real x and every nu greater than -1. Substituting the shifted-series derivative formulas reduces the identity to the relation between three consecutive orders."))));

    private static DocumentBlock FormulaEntry(string id, string name, string title, Formula statement,
        string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/Series." + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        return new Formula.Apply(Seq(Operatorname, Sp, Grp([.. parts])), [.. args]);
    }
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Pos(Formula a) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Poch(Formula b, Formula n) =>
        Call("Polynomial.eval", b, Call("ascPochhammer", R, n));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/Series." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
