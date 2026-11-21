using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeOnlyTailCorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative-part windows of the Chebyshev tail",
        H("Prime-power correction and persistence of negative values"),
        Blocks(Describe.Lean(
            DescribeId.Create("critical-window-correction"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_power_window_correction"),
            H("Prime-power correction and negative-part window bound"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For α equal to the prime-power function ψ or the prime-only function ϑ, let "
                    + "Qα(x) be the absolutely convergent integral of (α(t)−t)/t² from x ≥ 1 to infinity. "
                    + "Write D(x)=Qψ(x)−Qϑ(x). For 1 ≤ a ≤ b, let W(a,b) be the integral from a to b of "
                    + "[max(−Qϑ(x),0)−max(−Qψ(x),0)]/√x. All variables are real.")),
                Paragraph(Text(
                    "For every x ≥ 1, subtracting the two tails expresses D(x) as the integral "
                    + "of the nonnegative kernel (ψ(t)−ϑ(t))/t². The prime number theorem gives "
                    + "(ψ(t)−ϑ(t))/√t → 1. For any ε > 0 the ratio lies within ε of one at every sufficiently large t, "
                    + "so for every sufficiently large x the entire tail lies between (1−ε) and (1+ε) times the integral "
                    + "of t to the power −3/2. That integral equals 2/√x.")),
                Paragraph(Text(
                    "A Chebyshev bound ψ(t)−ϑ(t) ≤ C√t exists unconditionally. Negative parts "
                    + "reverse order and are 1-Lipschitz, so the window integrand is between "
                    + "zero and 2C/x. In particular b=a to the power 3/2 costs at most C log a."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-window-lower"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection.prime_tail_negative_window_lower"),
                H("A negative interior value forces window mass"),
                StatementSource.FromAuthor(NegativeWindowClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the displayed statement Q is the prime-only tail Qϑ. Write N(a,b) for "
                        + "the integral of max(−Qϑ(z),0)/√z over [a,b]. The hypothesis "
                        + "on the window leaves a relative margin r on both sides of x.")),
                    Paragraph(Text(
                        "Monotonicity of ϑ bounds the increment Qϑ(z)−Qϑ(x) by "
                        + "log(z/x)+ϑ(x)(1/z−1/x). This integral comparison holds at prime jumps. "
                        + "Choose z on the left when ϑ(x)≤x and on the right when ϑ(x)≥x. "
                        + "On the chosen side the upper bound is at most log(z/x)+x/z−1. "
                        + "Using log(t)≤t−1 bounds it by (z−x)²/(zx), at most 2r².")),
                    Paragraph(Text(
                        "The negative part is therefore at least 2r² throughout a subinterval of "
                        + "length rx, where √z≤2√x. Integrating gives r³√x. A budget strictly below "
                        + "r³√x excludes the asserted depth at that interior point. The estimate "
                        + "requires a given window and gives no existence result for small-budget windows."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var x = F.Id("x");
        var t = F.Id("t");
        var c = F.Id("C");
        var a = F.Id("a");
        var b = F.Id("b");
        var one = F.D(1);
        var two = F.D(2);
        var twiceC = Multiply(two, c);
        var difference = Call("D", x);
        var window = Call("W", a, b);
        var limit = Call("Tendsto",
            F.Seq(F.Open, F.LambdaLower, F.Sp, x, F.Sp, F.Mapsto, F.Sp,
                Multiply(Call("sqrt", x), difference), F.Close),
            F.Id("atTop"), Call("nhds", two));
        var hypothesis = All("t", Implies(Le(one, t),
            Le(Subtract(new Formula.Apply(F.Psi, [t]), new Formula.Apply(F.Theta, [t])),
                Multiply(c, Call("sqrt", t)))));
        var points = All("x", Implies(Le(one, x),
            And(Le(F.D(0), difference), Le(difference, new Formula.Fraction(twiceC, Call("sqrt", x))))));
        var windows = All("a", All("b", Implies(And(Le(one, a), Le(a, b)),
            And(Le(F.D(0), window), Le(window,
                Multiply(twiceC, Call("log", new Formula.Fraction(b, a))))))));
        return F.Disp(And(limit, All("C", Implies(hypothesis, And(points, windows)))));
    }

    private static Formula NegativeWindowClaim()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var x = F.Id("x");
        var r = F.Id("r");
        var one = F.D(1);
        var square = new Formula.Power(r, F.D(2));
        var cube = new Formula.Power(r, F.D(3));
        var left = Multiply(F.Seq(F.Open, Subtract(one, r), F.Close), x);
        var right = Multiply(F.Seq(F.Open, one, F.Plus, r, F.Close), x);
        var positiveRadius = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, r);
        var radiusBound = Le(r, new Formula.Fraction(one, F.D(2)));
        var depth = Le(Call("Q", x), Subtract(F.D(0), Multiply(F.D(4), square)));
        var hypothesis = And(And(Le(one, a), Le(a, left)),
            And(Le(right, b), And(And(positiveRadius, radiusBound), depth)));
        var conclusion = Le(Multiply(cube, Call("sqrt", x)), Call("N", a, b));
        return F.Disp(All("a", All("b", All("x", All("r", Implies(hypothesis, conclusion))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Seq(F.Mathbb, F.Grp(F.Id("R"))), body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
