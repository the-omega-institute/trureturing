using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class CompleteLowHWeightedSpectralMeanDocument : IScribeDocumentDefinition
{
    private static Formula Real => Seq(Mathbb, Grp(StrataLint.Scribe.FormulaDsl.Id("R")));

    private static Formula CallF(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula AddF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula MulF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Pow(Formula value, long exponent) =>
        new Formula.Power(value, Num(exponent));

    private static Formula Neg(Formula value) =>
        new Formula.Binary(Num(0), FormulaBinaryOperator.Subtract, value);

    private static Formula Exp(Formula value) => CallF("exp", value);

    private static Formula Bound()
    {
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        var gamma = StrataLint.Scribe.DefinitionDsl.Id("gamma");
        var dSquared = Pow(CallF("D", gamma), 2);
        var shell = MulF(Num(2400000), Exp(Neg(MulF(Num(83), m))));
        var positive = Num(2400);
        var negative = MulF(Num(384), Exp(Neg(MulF(Num(28), m))));
        return MulF(MulF(m, dSquared), AddF(AddF(shell, positive), negative));
    }

    private static Formula Statement()
    {
        var z = StrataLint.Scribe.DefinitionDsl.Id("Z");
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        var gamma = StrataLint.Scribe.DefinitionDsl.Id("gamma");
        var integrable = CallF("IntegrableOn", CallF("lowHIntegrand", z, m, gamma),
            CallF("Ioi", Num(1)));
        var estimate = Le(CallF("norm", CallF("lowHMean", z, m, gamma)), Bound());
        return All("Z", CallF("CompleteZeroFamily"),
            All("m", Real,
                All("gamma", Real,
                    Imp(CallF("LowHCertificates", z, m, gamma), And(integrable, estimate)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full countable low-height mean is bounded by a decaying shell term and two explicit extensions.",
        H("Complete Low-Height Weighted Spectral Mean"),
        Blocks(
            Paragraph(Text(
                "The complete Gaussian mean identity reduces the physical integral on y > 1 to "
                + "the all-index full-line mean and two signed extension integrals. This source bounds "
                + "the divided cubic numerator after division by the actual nonzero resolvent denominator. "
                + "For t = abs(Im(rho)) > 10, it obtains a core constant 2, then the paper's constant 20; "
                + "neither imaginary sign is selected.")),
            Paragraph(Text(
                "The h integral uses 3*(1+h) on [0,2], whose integral is 12. Thus core 20 gives the "
                + "integrated coefficient 240, while core 2 gives 24 and absolute summability of the "
                + "complex shell norms. The shell count gives 10000*exp(-100*m); multiplying by "
                + "exp(17*m) yields the complete 2400000*exp(-83*m) term.")),
            Paragraph(Text(
                "The positive extension keeps y in (0,1]. For the negative extension, the Gaussian "
                + "tilt has center 12*m, variance 2*m and factor exp(-28*m). Its central second and "
                + "fourth moments are 2*m and 12*m^2, giving the coefficient 384. These bounds apply "
                + "to repeated zeros in the complete natural-index family.")),
            Paragraph(Text(
                "For every real m >= 1 and gamma > 10, the additional scalar consequence is "
                + "24*m*(gamma+10)^2*(10000*exp(-100*m))*exp(17*m) <= "
                + "m*(gamma+10)^2*(2400000*exp(-83*m)). The exponential addition law first makes "
                + "the left side exactly m*(gamma+10)^2*(240000*exp(-83*m)); nonnegativity of "
                + "m and (gamma+10)^2 then gives the stated relaxation. This consequence is "
                + "exposition of an existing application, with an anonymous transient exact check; "
                + "it has no retained named declaration or theorem Describe. The proof of the "
                + "full mean bound instead uses shell_exp_constant240, the exact identity with "
                + "coefficient 240, through complete_real_line_mean_bound.")),
            Describe.Lean(
                DescribeId.Create("complete-low-h-weighted-mean-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/CompleteLowHWeightedSpectralMean.complete_low_h_weighted_mean_bound"),
                H("Complete multiplicity-preserving weighted mean"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary complete indexed family, the LowHCertificates hypothesis is exactly "
                        + "m >= 1 and gamma > 10. The conclusion first gives IntegrableOn over y in (1,infinity), "
                        + "then bounds the norm of lowHMean by "
                        + "m*(gamma+10)^2*(2400000*exp(-83*m) + 2400 + 384*exp(-28*m)).")),
                    Paragraph(Text(
                        "The proof retains the full h interval [0,2] with weight 1+h and integral 4, the "
                        + "Gaussian center 16*m and denominator 4*m, physical coefficient 3, all natural-index "
                        + "multiplicities, and both imaginary signs. The shell path supplies 20, the h integral "
                        + "supplies 4, and the physical coefficient supplies 3; the named extensions supply 2400 "
                        + "and 384*exp(-28*m), while the shell decay is 2400000*exp(-83*m). No finite or "
                        + "truncated replacement, assumed final bound, critical-line premise, Robin conclusion, "
                        + "QGP conclusion, or RH conclusion is part of this declaration."))))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean"))]));
}
