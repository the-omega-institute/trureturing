using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumCriticalMissingWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shifted critical cutoff gives a strict missing window at the endpoint mass fraction.",
        H("Missing Windows at the Critical Mass Fraction"),
        Blocks(
            Paragraph(Text(
                "For a locally finite positive spectrum S and weights w, use the same "
                + "inclusive cutoff for the mass and the sine score. In each formula, Eventually "
                + "means that the indicated real variable is sufficiently large. "),
                Ref("D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff")),
            Describe.Lean(
                DescribeId.Create("has-log-squared-mass"),
                DeclarationHandle.Create(Owner + ".HasLogSquaredMass"),
                H("Squared-logarithmic mass with a linear logarithmic error"),
                StatementSource.FromAuthor(MassCondition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient is positive. The error constant is independent of the cutoff."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("has-small-square-tail"),
                DeclarationHandle.Create(Owner + ".HasSmallSquareTail"),
                H("Uniform smallness of the square tail"),
                StatementSource.FromAuthor(TailCondition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The lower cutoff may depend on η. The bound then holds uniformly "
                    + "over every upper cutoff and includes every ordinate in (X,T]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("eventual-critical-missing-window"),
                DeclarationHandle.Create(Owner + ".eventual_critical_missing_window"),
                H("Arbitrarily late closed windows below the critical mass fraction"),
                StatementSource.FromAuthor(Window()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write W for the mass function, L = log T and X = exp(−K)T^β. "
                        + "Choose K = (C(β+β²)+4)/(2aβ), where a and C are the coefficient "
                        + "and error constant in the mass hypothesis. Expanding log X = βL − K "
                        + "gives β²W(T) − W(X) > 3L eventually. Nonnegative weights on the head "
                        + "then imply positive total mass.")),
                    Paragraph(Text(
                        "In score time, use length exp(T^β)/r, threshold L and mesh h = 1/T². "
                        + "The tail slope is bounded by TW(T), so the mesh allowance is "
                        + "at most W(T)/T < L eventually. The grid has at most exp(2T^β) "
                        + "nodes because exp(T^β)/T² grows without bound.")),
                    Paragraph(Text(
                        "Apply the uniform square-tail bound at that same X with "
                        + "η = exp(−K)/(8β²). Since 0 ≤ log X ≤ βL eventually, "
                        + "the variance bound V ≤ L²/(8T^β) follows. For V > 0, the product "
                        + "of the grid count and the one-node tail bound is at most "
                        + "exp(−2T^β) < 1. The finite theorem also handles V = 0. "),
                        Ref("D5/S3/Fourier/Concentration/FiniteSineMissingWindow"
                            + ".exists_arbitrarily_late_missing_window")),
                    Paragraph(Text(
                        "Restrict rational linear independence to the finite cutoff. "
                        + "The head mass, threshold and mesh allowance fit strictly below β²W(T) − log T, "
                        + "so the finite orbit theorem gives a closed score-time window starting "
                        + "above A/r. Multiplying the endpoints by r gives the asserted "
                        + "window starting above A.")),
                    Paragraph(Text(
                        "For actual ζ, assume RH and rational linear independence of the distinct "
                        + "positive ordinates. Use the analytic-multiplicity weight "
                        + "wγ = mγ γ/(1/4 + γ²) at each ordinate γ ≤ T. The squared-logarithmic "
                        + "mass error in "), Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/"
                        + "SublinearOrder/RHRootWeightedSine"),
                        Text(" gives a = 1/(4π) in the mass hypothesis.")),
                    Paragraph(Text(
                        "The required small square tail follows from mγ = o(log γ). To see "
                        + "this bound in the existing zeta estimates, fix ε > 0 and put "
                        + "s = exp(−4/ε)/2. For a zero ρ = 1/2 + iγ, center a radius-1/4 "
                        + "disk at c = ρ + s/4 and use g(z) = ζ(c + z/4)/ζ(c). The same "
                        + "multiplicity occurs at z = −s. On |z| ≤ 1/2, linear ζ growth "
                        + "and the reciprocal estimate at c give |g(z)| ≤ Cγ², with C "
                        + "independent of γ. The finite-disk Jensen bound gives "
                        + "mγ ≤ log(Cγ²)/log((1/2)/s) ≤ ε log γ for all sufficiently "
                        + "large γ, since the denominator is 4/ε. Goldston and Gonek, "
                        + "Corollary 1 (9), DOI 10.1112/blms/bdm032, give the stronger "
                        + "order log γ/log log γ.")),
                    Paragraph(Text(
                        "The count bound N(Y) = O(Y log Y) gives a bound O(log² X/X) "
                        + "for the sum of mγ log γ/γ² over γ > X. On each (2^k X, 2^(k+1) X] "
                        + "bound the count and logarithm by the upper endpoint and the square "
                        + "denominator by the lower endpoint. The resulting geometric series "
                        + "with a quadratic factor in k converges. Since wγ² ≤ mγ²/γ² and "
                        + "mγ/log γ tends to zero, the squared-weight tail is o(log² X/X) "
                        + "uniformly over every finite upper cutoff. The theorem therefore gives "
                        + "actual ζ windows with deficit strictly greater than 1 − β² + log(T)/W(T) at every point. "
                        + "The proof uses rational independence for the finite orbit step."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("has-logarithmic-square-tail"),
                DeclarationHandle.Create(Owner + ".HasLogarithmicSquareTail"),
                H("A uniform logarithmic square-tail bound"),
                StatementSource.FromAuthor(TailCondition(logarithmic: true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One positive constant bounds the squared weights on (X,T] for every "
                    + "finite upper cutoff T ≥ X once X is sufficiently large."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("eventual-logarithmic-missing-window"),
                DeclarationHandle.Create(Owner + ".eventual_logarithmic_missing_window"),
                H("A logarithmic gain in the waiting exponent"),
                StatementSource.FromAuthor(Window(logarithmic: true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the shifted cutoff X = exp(−K)T^β and write L = log T. "
                        + "The same head estimate gives β²W(T) − W(X) > 3L, and the "
                        + "mesh 1/T² costs less than L because the slope is at most TW(T). "
                        + "Nonnegative head mass gives W(T) > 0 eventually.")),
                    Paragraph(Text(
                        "For the square-tail constant C, put D = Cβ exp(K). "
                        + "Using log X = βL − K gives V ≤ DL/T^β. When V is positive, "
                        + "the one-node tail bound at threshold L is at most "
                        + "exp(−T^βL/(2D)). Choose c = 1/(4D) and E = cT^βL.")),
                    Paragraph(Text(
                        "In score time the interval has length exp(E)/r. The grid count "
                        + "is at most exp(E)(1 + 1/r)T² for T ≥ 1. Its logarithm is "
                        + "at most E + 2L + log(1 + 1/r) < 2E eventually. The grid "
                        + "count times the one-node bound is then strictly less than one. "
                        + "The finite theorem also allows zero variance. "),
                        Ref("D5/S3/Fourier/Concentration/FiniteSineMissingWindow"
                            + ".exists_arbitrarily_late_missing_window")),
                    Paragraph(Text(
                        "The head, threshold and mesh allowance fit below β²W(T) − L. "
                        + "Rational linear independence restricts to the finite cutoff. "
                        + "The orbit supplies a closed score-time interval starting above A/r, "
                        + "and scaling by r gives the stated interval."))),
                DescribeRole.Theorem))));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Spectrum => F.Id("Spectrum");
    private static Formula Weights => Seq(Call("index", F.Id("S")), Sp, To, Sp, Reals);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula ExistsReal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Reals, body);

    private static Formula Eventually(Formula variable, Formula body) =>
        Call("Eventually", Seq(Open, variable, Sp, Mapsto, Sp, body, Close), F.Id("atTop"));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Square(Formula body) => new Formula.Power(body, D(2));

    private static Formula Mass(Formula t) => Call("mass", F.Id("S"), F.Id("w"), t);

    private static Formula OverSpectrum(Formula body) =>
        Disp(All("S", Spectrum, All("w", Weights, body)));

    private static Formula MassCondition()
    {
        var y = F.Id("Y");
        var a = F.Id("a");
        var c = F.Id("C");
        var log = Call("log", y);
        var error = new Formula.Absolute(Subtract(Mass(y), Multiply(a, Square(log))));
        var bound = AtMost(error, Multiply(c, Seq(Open, Add(D(1), log), Close)));
        return OverSpectrum(Iff(Call("HasLogSquaredMass", F.Id("S"), F.Id("w")),
            ExistsReal("a", ExistsReal("C",
                And(Less(D(0), a), And(AtMost(D(0), c), Eventually(y, bound)))))));
    }

    private static Formula TailCondition(bool logarithmic = false)
    {
        var x = F.Id("X");
        var t = F.Id("T");
        var constant = F.Id(logarithmic ? "C" : "eta");
        var j = F.Id("j");
        var cut = Seq(Call("cut", F.Id("S"), t), Sp, Setminus, Sp, Call("cut", F.Id("S"), x));
        var sum = Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, cut), Sp, Square(Call("w", j)));
        var log = Call("log", x);
        var bound = AtMost(sum, new Formula.Fraction(Multiply(constant, logarithmic ? log : Square(log)), x));
        var uniform = Eventually(x, All("T", Reals, Implies(AtMost(x, t), bound)));
        return OverSpectrum(Iff(Call(TailName(logarithmic), F.Id("S"), F.Id("w")),
            logarithmic
                ? ExistsReal("C", And(Less(D(0), constant), uniform))
                : All("eta", Reals, Implies(Less(D(0), constant), uniform))));
    }

    private static string TailName(bool logarithmic) =>
        logarithmic ? "HasLogarithmicSquareTail" : "HasSmallSquareTail";

    private static Formula Window(bool logarithmic = false)
    {
        var t = F.Id("T");
        var a = F.Id("a");
        var b = F.Id("beta");
        var r = F.Id("r");
        var c = F.Id("c");
        var s = F.Id("S");
        var w = F.Id("w");
        var u = F.Id("u");
        var nonnegative = All("j", Call("index", s), AtMost(D(0), Call("w", F.Id("j"))));
        var independent = Call("LinearIndependent", Seq(Mathbb, Grp(F.Id("Q"))), Call("gamma", s));
        var conditions = And(nonnegative, And(independent,
            And(Call("HasLogSquaredMass", s, w), And(Call(TailName(logarithmic), s, w),
                And(Less(D(0), r), And(Less(D(0), b), Less(b, D(1))))))));
        var power = new Formula.Power(t, b);
        var exponent = logarithmic ? Multiply(Multiply(c, power), Call("log", t)) : power;
        var interval = Seq(OpenBracket, a, Comma, Add(a, Call("exp", exponent)), CloseBracket);
        var strict = Less(Call("sine", s, w, t, new Formula.Fraction(u, r)),
            Subtract(Multiply(Square(b), Mass(t)), Call("log", t)));
        var windows = All("A", Reals, ExistsReal("a",
            And(Less(F.Id("A"), a), All("u", interval, strict))));
        var eventual = Eventually(t, And(Less(D(0), Mass(t)), windows));
        var conclusion = logarithmic ? ExistsReal("c", And(Less(D(0), c), eventual)) : eventual;
        return OverSpectrum(All("r", Reals, All("beta", Reals, Implies(conditions, conclusion))));
    }
}
