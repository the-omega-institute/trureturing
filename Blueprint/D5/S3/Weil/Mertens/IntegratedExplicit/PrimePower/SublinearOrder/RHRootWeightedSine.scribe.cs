using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHRootWeightedSineDocument : IScribeDocumentDefinition
{
    internal const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted sine approximation to the RH root signal",
        H("The inclusive positive-ordinate cutoff"),
        Blocks(
            Paragraph(Text("Under Mathlib's Riemann hypothesis, each distinct positive ordinate γ "
                + "identifies a unique zero. Write mγ for its analytic multiplicity. "
                + "The weight is wγ = mγ γ/(1/4 + γ²). For 0 < γ ≤ T the sum of these weights "
                + "is W(T) and the sum of wγ sin(γv) is S(T,v). Write P(T) for the real supremum "
                + "of S(T,v) over real v. "), Ref("D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum")),
            Describe.Lean(DescribeId.Create("harmonic-mass-limit"),
                DeclarationHandle.Create(Owner + ".harmonic_mass_limit"),
                H("Harmonic mass"), StatementSource.FromAuthor(MassStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At t = 1/T the signed quarter-phase sine slope has the "
                    + "known leading term t log²(T)/(2π). Its Taylor approximation equals "
                    + "2t W(T) and differs from the slope by at most a constant times "
                    + "t(1 + log T). The count through the inclusive cutoff controls the "
                    + "quadratic Taylor error and the inverse-square tail controls the rest. "),
                    Ref("D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness"),
                    Text(" "), Ref("D5/S3/Weil/Mertens/ZeroAbscissaPower"))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted-sine-sup-bounds"),
                DeclarationHandle.Create(Owner + ".weighted_sine_sup_bounds"),
                H("Bounds for the real supremum"),
                StatementSource.FromAuthor(F.Disp(Imp(Id("RH"), All("T",
                    And(Le(Num(0), Call("P", Id("T"))), Le(Call("P", Id("T")), Call("W", Id("T")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The value at zero is zero. Each sine has absolute value "
                    + "bounded by one and each weight is nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("root-signal-weighted-sine-return"),
                DeclarationHandle.Create(Owner + ".root_signal_weighted_sine_return"),
                H("Uniform upper bound and cofinal signed lower bound"),
                StatementSource.FromAuthor(ReturnStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For real r > 1 use s(r) = 1/2 − 1/(2r), and let R(r,u) be the "
                        + "centered normalized root signal. The difference Δ(r,h,u) is "
                        + "R(r,u+h) − R(r,u). Write B(r,h) = (2h/s(r)) P(r/h) and "
                        + "E(C,h) = C h log(1/h).")),
                    Paragraph(Text("The coefficient correction multiplied by the ordinate is "
                        + "absolutely summable, so the correction contributes at most order h. "
                        + "The Taylor bound for the leading coefficients is uniform in phase. "
                        + "Pairing conjugate occurrences gives the approximation "
                        + "(2h/s(r)) S(r/h,u/r), with analytic multiplicities retained. "),
                        Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement")),
                    Paragraph(Text("Oddness makes the supremum of the absolute polynomial "
                        + "equal to its signed supremum. Each real orbit point is a cluster "
                        + "point at arbitrarily late times. The finite polynomial is a continuous "
                        + "readout of the occurrence phases, so every strict lower threshold "
                        + "below B(r,h) − E(C,h) has a sufficiently late signed return. "),
                        Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster"))),
                DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Reals, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Reals, body);

    private static Formula MassStatement()
    {
        var t = Id("T");
        var mass = new Formula.Fraction(Call("W", t), new Formula.Power(Call("log", t), Num(2)));
        var coefficient = new Formula.Fraction(Num(1), Multiply(Num(4), F.Pi));
        var function = F.Seq(F.Open, F.LambdaLower, F.Sp, t, F.Sp, F.Mapsto, F.Sp, mass, F.Close);
        return F.Disp(Imp(Id("RH"), Call("Tendsto", function, Id("atTop"), Call("nhds", coefficient))));
    }

    private static Formula ReturnStatement()
    {
        var r = Id("r");
        var h = Id("h");
        var u = Id("u");
        var b = Id("b");
        var c = Id("C");
        var lead = Call("B", r, h);
        var error = Call("E", c, h);
        var delta = Call("Delta", r, h, u);
        var upper = All("u", Le(new Formula.Absolute(delta), Add(lead, error)));
        var lower = All("U", All("b", Imp(Lt(b, Subtract(lead, error)),
            Exists("u", And(Le(Id("U"), u), Lt(b, delta))))));
        var range = And(Lt(Num(0), h), Le(h, new Formula.Fraction(Num(1), Call("exp", Num(1)))));
        var bound = All("h", Imp(range, And(upper, lower)));
        return F.Disp(Imp(Id("RH"), All("r", Imp(Lt(Num(1), r),
            Exists("C", And(Le(Num(0), c), bound))))));
    }
}
