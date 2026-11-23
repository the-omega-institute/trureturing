using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumThreeBandRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumThreeBandRecurrence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short-window averaging improves the loss bound for weighted sine recurrence.",
        H("Three-band averaging after a low-frequency hit"),
        Blocks(
            Paragraph(Text("Let I index a locally finite positive spectrum and let w(j) be its "
                + "weights. Write W(T) for the sum of the weights at frequencies γ(j) ≤ T "
                + "and S(T,v) for the sum of w(j) sin(γ(j)v) over the same indices. "
                + "Eventually refers to the indicated real variable tending to positive infinity. "),
                Ref("D5/S3/Analytic/Oscillation/OrdinateCounting")),
            Describe.Lean(
                DescribeId.Create("eventual-sine-three-band-recurrence"),
                DeclarationHandle.Create(Owner + ".eventual_sine_three_band_recurrence"),
                H("Uniform recurrence from low-frequency hits"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix r, β > 0 and put m = min(β,1). Assume the weights "
                        + "are nonnegative and that W(T^p)/W(T) tends to q(p) for every 0 < p < 1, "
                        + "with q continuous at m. For every tolerance e > 0 and all sufficiently "
                        + "large X, assume W(X) > 0 and that each interval of length exp(X) "
                        + "contains a point b with head loss 1 − S(X,b/r)/W(X) < e.")),
                    Paragraph(Text("Choose 0 < α < κ < ν < m and e > 0 so that "
                        + "1 + q(ν) − 2q(α) + e q(α) < ε. Continuity at m and the strict slack "
                        + "above 1 − q(m) permit this choice. For X = T^α, Y = T^ν and h = T^(−κ), "
                        + "start at the head hit b and apply the local point bound on [b,b+h]. "
                        + "It controls the score using head drift hX/r, the middle band mass "
                        + "W(Y) − W(X), and the tail factor 2r/(hY). "),
                        Ref("D5/S3/Fourier/HarmonicScoreLocalAverage")),
                    Paragraph(Text("After division by W(T), the head drift and tail errors tend "
                        + "to zero because α < κ < ν and the mass ratios have finite limits. "
                        + "The resulting upper bound on normalized loss tends to "
                        + "1 + q(ν) − 2q(α) + e q(α). Since α < β, eventually exp(X) + h "
                        + "is at most exp(T^β). The eventual bounds are independent of a.")),
                    Paragraph(Text("For the actual positive zeta ordinates under RH and "
                        + "Lamzouri's Conjecture 1.1 (Effective LI), use weights mγ γ/(1/4 + γ²), "
                        + "where mγ is the analytic multiplicity at γ. Effective LI supplies "
                        + "separation on each fixed coefficient box because the zero count "
                        + "eventually exceeds its bound. The distinct mode count is O(X log X). "
                        + "The weighted cutoff recurrence with exponent 1 then gives the head "
                        + "hits for every e > 0. The harmonic mass satisfies "
                        + "W(T)/log²(T) → 1/(4π), so q(p) = p². Thus for r, β > 0 and "
                        + "ε > 1 − min(β,1)², every interval of length exp(T^β) contains "
                        + "a point with normalized loss below ε for all sufficiently large T. "),
                        Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine")),
                    Paragraph(Text("A singleton spectrum at frequency one with weight one "
                        + "has q(p) = 1. Its sine reaches one in every interval of length "
                        + "at least 2πr, so it satisfies the head-hit premise for each r > 0."))),
                DescribeRole.Theorem))));

    private static Formula RealType => F.Seq(F.Mathbb, F.Grp(Id("R")));
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula W(Formula cutoff) => Call("W", cutoff);
    private static Formula Lambda(Formula x, Formula body) =>
        F.Seq(F.Open, x, F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula Eventually(Formula x, Formula body) =>
        Call("Eventually", Lambda(x, body), Id("atTop"));

    private static Formula WindowHit(Formula cutoff, Formula windowLength, Formula tolerance)
    {
        var a = Id("a");
        var u = Id("u");
        var endpoint = Add(a, windowLength);
        var window = F.Seq(F.OpenBracket, a, F.Comma, F.Sp, endpoint, F.CloseBracket);
        var loss = Subtract(Num(1), Div(Call("S", cutoff, Div(u, Id("r"))), W(cutoff)));
        var hit = All("a", RealType, Exists("u", RealType, And(In(u, window), Lt(loss, tolerance))));
        return Eventually(cutoff, And(Lt(Num(0), W(cutoff)), hit));
    }

    private static Formula Statement()
    {
        var r = Id("r");
        var beta = Id("beta");
        var epsilon = Id("varepsilon");
        var e = Id("e");
        var t = Id("T");
        var x = Id("X");
        var p = Id("p");
        var j = Id("j");
        var q = Id("q");
        var nonnegative = All("j", Id("I"), Le(Num(0), Call("w", j)));
        var m = Call("min", beta, Num(1));
        var ratio = Call("Tendsto", Lambda(t, Div(W(Power(t, p)), W(t))),
            Id("atTop"), Call("nhds", Call("q", p)));
        var ratios = All("p", RealType, Imp(And(Lt(Num(0), p), Lt(p, Num(1))), ratio));
        var head = All("e", RealType, Imp(Lt(Num(0), e), WindowHit(x, Call("exp", x), e)));
        var parameterDomain = And(Lt(Num(0), r), Lt(Num(0), beta));
        var limitHypotheses = And(Call("ContinuousAt", q, m), ratios);
        var lossThreshold = Lt(Subtract(Num(1), Call("q", m)), epsilon);
        var hypotheses = And(parameterDomain, And(limitHypotheses, And(head, lossThreshold)));
        var conclusion = WindowHit(t, Call("exp", Power(t, beta)), epsilon);
        return F.Disp(Imp(nonnegative, All("q", F.Seq(RealType, F.To, RealType),
            All("r", RealType, All("beta", RealType, All("varepsilon", RealType,
                Imp(hypotheses, conclusion)))))));
    }
}
