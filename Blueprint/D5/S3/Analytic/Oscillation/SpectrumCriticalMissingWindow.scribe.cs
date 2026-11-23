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
                StatementSource.FromAuthor(Endpoint()),
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
                        + "The head mass, threshold and mesh allowance fit strictly below β²W(T), "
                        + "so the finite orbit theorem gives a closed score-time window starting "
                        + "above A/r. Multiplying the endpoints by r gives the asserted "
                        + "window starting above A."))),
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

    private static Formula TailCondition()
    {
        var x = F.Id("X");
        var t = F.Id("T");
        var eta = F.Id("eta");
        var j = F.Id("j");
        var cut = Seq(Call("cut", F.Id("S"), t), Sp, Setminus, Sp, Call("cut", F.Id("S"), x));
        var sum = Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, cut), Sp, Square(Call("w", j)));
        var bound = AtMost(sum, new Formula.Fraction(Multiply(eta, Square(Call("log", x))), x));
        return OverSpectrum(Iff(Call("HasSmallSquareTail", F.Id("S"), F.Id("w")),
            All("eta", Reals, Implies(Less(D(0), eta),
                Eventually(x, All("T", Reals, Implies(AtMost(x, t), bound)))))));
    }

    private static Formula Endpoint()
    {
        var t = F.Id("T");
        var a = F.Id("a");
        var b = F.Id("beta");
        var r = F.Id("r");
        var s = F.Id("S");
        var w = F.Id("w");
        var u = F.Id("u");
        var nonnegative = All("j", Call("index", s), AtMost(D(0), Call("w", F.Id("j"))));
        var independent = Call("LinearIndependent", Seq(Mathbb, Grp(F.Id("Q"))), Call("gamma", s));
        var conditions = And(nonnegative, And(independent,
            And(Call("HasLogSquaredMass", s, w), And(Call("HasSmallSquareTail", s, w),
                And(Less(D(0), r), And(Less(D(0), b), Less(b, D(1))))))));
        var interval = Seq(OpenBracket, a, Comma, Add(a, Call("exp", new Formula.Power(t, b))),
            CloseBracket);
        var strict = Less(Call("sine", s, w, t, new Formula.Fraction(u, r)), Multiply(Square(b), Mass(t)));
        var windows = All("A", Reals, ExistsReal("a",
            And(Less(F.Id("A"), a), All("u", interval, strict))));
        return OverSpectrum(All("r", Reals, All("beta", Reals, Implies(conditions,
            Eventually(t, And(Less(D(0), Mass(t)), windows))))));
    }
}
