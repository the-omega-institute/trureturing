using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class SignedCompleteWindowExponentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact signed power-window growth for the complete Mangoldt tail",
        H("The logarithmic exponent at the zeta zero abscissa"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-mass"),
                DeclarationHandle.Create(Module + "signedMass"),
                H("Signed weighted window mass"),
                StatementSource.FromAuthor(F.Disp(MassDefinition())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real e, b and Y, M(e,b,Y) is the oriented interval integral from Y to Y^b. "
                    + "The complete Chebyshev tail Q(x) is the integral of (ψ(t)−t)/t² from x to infinity, "
                    + "with every prime power counted in ψ. The signs e=1 and e=−1 select "
                    + "the positive and negative parts of −Q respectively."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-mass-window-upper"),
                DeclarationHandle.Create(Module + "signedMass_le_of_window_bound"),
                H("Mass bound from a one-sided window estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Y > 2, b > 1, θ ≥ 1/2 and C ≥ 0, assume eU(x) ≤ Cx^θ throughout [Y,Y^b]. The pointwise bound "
                    + "bounds its positive part because the power majorant is nonnegative. "
                    + "The identity −Q(x)=U(x)/x bounds the density by C Y^(b(θ−1/2))/x. "
                    + "Integrating the reciprocal gives (b−1) log Y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-mass-exact-power-integral"),
                DeclarationHandle.Create(Module + "signed_interval_mass_le_of_positive_loss"),
                H("Exact power integral on arbitrary closed intervals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 2 < A ≤ B, κ > 0 and C ≥ 0, assume eU(x) ≤ Cx^(1/2+κ) throughout [A,B]. The signed density is at most "
                    + "Cx^(κ−1). Integrating this density on the same endpoints gives "
                    + "(C/κ)(B^κ−A^κ)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cofinal-signed-window-abscissa"),
                DeclarationHandle.Create(Module + "zeroAbscissa_le_iff_frequently_window_bound"),
                H("A fixed one-sided exponent determines a zero bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For b > 1, θ ≥ 1/2 and e = 1 or e = −1, Θ ≤ θ holds exactly when some fixed C ≥ 0 bounds eU(x) by Cx^θ on arbitrarily late whole windows [Y,Y^b]. "
                    + "If Θ≤θ, the absolute zero expansion yields a single constant on every late window. "
                    + "If Θ>θ, choose an exponent strictly between b(θ−1/2) and b(Θ−1/2). "
                    + "The eventual mass lower bound has this exponent while the local estimate "
                    + "bounds the mass on cofinally many windows by C(b−1)Y^(b(θ−1/2)) log Y. "
                    + "The strict exponent gap absorbs the logarithm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-window-log-growth"),
                DeclarationHandle.Create(Module + "tendsto_log_one_add_signedMass"),
                H("Exact exponent for either sign"),
                StatementSource.FromAuthor(F.Disp(Exponent())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Θ be zeroAbscissa, the supremum of the real parts of the nontrivial zeta zeros. "
                        + "Reflection gives Θ≥1/2. Fix any real b>1 and either sign e=1 or e=−1. "
                        + "Set p=b(Θ−1/2). The logarithmic growth of 1+M(e,b,Y) has limit p "
                        + "as the real window start Y tends to infinity.")),
                    Paragraph(Text(
                        "Absolute summability of the actual zero coefficients and the bounded remainder "
                        + "in RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le give "
                        + "|U(x)|≤C x^Θ for x≥1, even when Θ is unattained. "
                        + "The identity ZeroAbscissaPower.primitive_eq_negative_tail gives −Q(x)=U(x)/x "
                        + "for x≥2. On [Y,Y^b] the density is therefore at most C Y^p/x. "
                        + "Integration yields M(e,b,Y)≤C(b−1)Y^p log Y for both signs "
                        + "with the same constant and threshold.")),
                    Paragraph(Text(
                        "For Θ>1/2 and any real a<p, choose a nontrivial zero with real part β>1/2 "
                        + "and b(β−1/2)>a by the defining supremum. "
                        + "PrimeWindowPoleGrowth.off_line_zero_forces_signed_complete_window_mass "
                        + "applied with ε=b(β−1/2)−a gives Y^a≤M(e,b,Y) on every sufficiently late "
                        + "window, simultaneously for both signs.")),
                    Paragraph(Text(
                        "The upper bound contributes only a logarithmic factor beyond Y^p, "
                        + "and log(log Y)/log Y tends to zero. The lower bound holds for "
                        + "every exponent strictly below p when p>0. At p=0, nonnegativity of "
                        + "the mass supplies the lower limit. Together these estimates give the exact limit."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula MassDefinition()
    {
        var e = F.Id("e");
        var b = F.Id("b");
        var y = F.Id("Y");
        var x = F.Id("x");
        var integrand = new Formula.Fraction(
            Call("max", Multiply(e, F.Seq(F.Minus, Call("Q", x))), F.D(0)),
            F.Seq(F.Sqrt, F.Grp(x)));
        var integral = F.Seq(F.Int, F.Underscore, F.Grp(y), F.Caret, F.Grp(new Formula.Power(y, b)),
            F.Sp, integrand, F.Sp, F.Id("d"), x);
        return All("e", All("b", All("Y", Eq(Call("M", e, b, y), integral))));
    }

    private static Formula Exponent()
    {
        var e = F.Id("e");
        var b = F.Id("b");
        var y = F.Id("Y");
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var p = Multiply(b, F.Seq(F.Open, Subtract(F.Id("Theta"), half), F.Close));
        var sign = new Formula.Logic(Eq(e, F.D(1)), FormulaLogicOperator.Or,
            Eq(e, F.Seq(F.Minus, F.D(1))));
        var ratio = new Formula.Fraction(Call("log", Add(F.D(1), Call("M", e, b, y))), Call("log", y));
        var function = F.Seq(F.Open, F.LambdaLower, F.Sp, y, F.Colon, Real,
            F.Sp, F.Mapsto, F.Sp, ratio, F.Close);
        var limit = Call("Tendsto", function, F.Id("atTop"), Call("nhds", p));
        return All("b", All("e", Implies(Lt(F.D(1), b), Implies(sign, limit))));
    }
}
