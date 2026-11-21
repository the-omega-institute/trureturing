using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeGrowingWidthRateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeGrowingWidthRate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmic error in the cumulative prime-tail mass",
        H("Cumulative prime-tail phase error"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-tail-cumulative-error-log-order"),
            DeclarationHandle.Create(Module + "prime_tail_cumulative_error_log_order"),
            H("Two-sided logarithmic order at the critical spectral gap"),
            StatementSource.FromAuthor(Disp(CumulativeBound())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
            Blocks(
                Paragraph(Text(
                    "Let Qθ(x) be the integral of (θ(u)−u)/u² over u>x in Zhao's equation (14). "
                    + "Write N(a,B) for the integral of max(−Qθ(x),0)/√x from a to B. "
                    + "Let β=Re ρ for the stated zero and put p=β−1/2. The simultaneous "
                    + "phase orbit φ uses the actual zero occurrences with multiplicity. "
                    + "The integral I∞ uses the line at β and the weight exp(−ps) on past lags s>0.")),
                Paragraph(Text(
                    "In log time u, let q(u)=exp((1−β)u)Qθ(exp u) and let F(u) be the β-line profile "
                    + "at φ(u) and lag zero. After subtracting the β-line, the remaining root-scaled "
                    + "spectral sum is bounded in norm by the sum of the coefficient norms. "
                    + "The complete-tail correction is O(exp(−u)) before root scaling, and the "
                    + "root-scaled prime-power correction tends to 2. The signed residual "
                    + "exp(pu)(q(u)−F(u)) is bounded in absolute value and is eventually at most −1.")),
                Paragraph(Text(
                    "Choose W one unit above the critical width. The weighted negative-part "
                    + "integral is nonnegative on the compact phase closure. A zero there would "
                    + "give a zero cluster value for normalized arithmetic mass and force its "
                    + "lower limit to vanish. Continuity gives a positive minimum. Because the "
                    + "weight is at most one, the unweighted negative part of F has at least "
                    + "that much integral on every interval of length W.")),
                Paragraph(Text(
                    "The root-scaled difference of negative parts D(u) is eventually nonnegative "
                    + "and bounded. When F(u)≤0 it is at least 1. If F⁻≤M, this implies "
                    + "D≥F⁻/(M+1), so each full late interval of width W contributes uniformly "
                    + "positive mass. Summing adjacent intervals up to log B gives a linear "
                    + "lower bound up to a constant. Boundedness gives the linear upper bound.")),
                Paragraph(Text(
                    "The fixed-window substitution identifies the truncated discrepancy with "
                    + "the integral of D from log 2 to log B. The initial segment has fixed mass. "
                    + "After multiplication by B^p, the omitted phase tail beyond log B−log 2 "
                    + "is bounded by a constant as well. The inequalities follow by absorbing "
                    + "both constants at a sufficiently large real endpoint."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-tail-window-error-of-lower-spectral-bound"),
                DeclarationHandle.Create(Module + "prime_tail_window_error_of_lower_spectral_bound"),
                H("Uniform error with a lower spectral ceiling"),
                StatementSource.FromAuthor(Disp(UniformBound())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text(
                        "For each pair β, γ satisfying the displayed assumptions, one K works "
                        + "for every real B and every left endpoint in [2,B]. The β-line may be empty. "
                        + "Here E(a,B)=N(a,B)/B^p−I∞(Re,β,φ(log B)).")),
                    Paragraph(Text(
                        "Subtract the exact β-line from the root-scaled zero series. Each remaining "
                        + "term has norm at most its coefficient norm times exp((γ−1/2)u). "
                        + "The same majorant absorbs the bounded corrections on the late tail and "
                        + "extends to the fixed initial interval by continuity. The negative part "
                        + "is 1-Lipschitz, so the majorant also bounds the absolute log density error.")),
                    Paragraph(Text(
                        "The fixed-window substitution integrates that bound from log a to log B. "
                        + "When γ>1/2, this gives a constant times B^(γ−1/2), and dividing by B^p "
                        + "gives B^(γ−β). At γ=1/2 the integrated majorant is proportional to log(B/a). "
                        + "The omitted phase tail contributes the term (a/B)^p in both cases."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Half => new Formula.Fraction(D(1), D(2));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ExistsReal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Real, body);

    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);

    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);

    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);

    private static Formula CumulativeBound()
    {
        var rho = F.Id("rho");
        var z = F.Id("z");
        var beta = Call("Re", rho);
        var re = Call("Re", z);
        var max = All("z", Complex, Implies(Call("NontrivialZero", z), Le(re, beta)));
        var gap = All("z", Complex, Implies(Call("NontrivialZero", z), Implies(Lt(re, beta), Le(re, Half))));
        var b = F.Id("B");
        var b0 = Seq(b, Underscore, Grp(D(0)));
        var c = F.Id("c");
        var cap = F.Id("C");
        var log = Call("log", b);
        var phase = Seq(F.Id("I"), Underscore, Grp(Infty), Open, F.Id("Re"), Comma, Sp, beta, Comma, Sp,
            Call("phi", log), Close);
        var error = Subtract(Call("N", D(2), b), Multiply(new Formula.Power(b, Subtract(beta, Half)), phase));
        var bounds = And(Le(Multiply(c, log), error), Le(error, Multiply(cap, log)));
        var late = All("B", Real, Implies(Le(b0, b), bounds));
        var threshold = Seq(F.Exists, Sp, b0, Colon, Sp, Real, Comma, Sp, late);
        var conclusion = ExistsReal("c", And(Lt(D(0), c), ExistsReal("C", And(Lt(D(0), cap), threshold))));
        return All("rho", Complex, Implies(Call("NontrivialZero", rho),
            Implies(Lt(Half, beta), Implies(max, Implies(gap, conclusion)))));
    }
    private static Formula UniformBound()
    {
        var beta = F.Id("beta");
        var gamma = F.Id("gamma");
        var z = F.Id("z");
        var re = Call("Re", z);
        var p = Subtract(beta, Half);
        var max = All("z", Complex, Implies(Call("NontrivialZero", z), Le(re, beta)));
        var gap = All("z", Complex, Implies(Call("NontrivialZero", z), Implies(Lt(re, beta), Le(re, gamma))));
        var b = F.Id("B");
        var a = F.Id("a");
        var k = F.Id("K");
        var error = new Formula.Absolute(Call("E", a, b));
        var extent = new Formula.Power(new Formula.Fraction(a, b), p);
        var logRate = Multiply(new Formula.Power(b, new Formula.Negate(p)),
            Call("log", new Formula.Fraction(b, a)));
        var powerRate = new Formula.Power(b, Subtract(gamma, beta));
        var critical = Implies(Equal(gamma, Half), Le(error, Multiply(k, Add(extent, logRate))));
        var above = Implies(Lt(Half, gamma), Le(error, Multiply(k, Add(extent, powerRate))));
        var uniform = All("B", Real, All("a", Real,
            Implies(And(Le(D(2), a), Le(a, b)), And(critical, above))));
        var conclusion = ExistsReal("K", And(Lt(D(0), k), uniform));
        return All("beta", Real, All("gamma", Real,
            Implies(Le(Half, gamma), Implies(Lt(gamma, beta), Implies(max, Implies(gap, conclusion))))));
    }

}
