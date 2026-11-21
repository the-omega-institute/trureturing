using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeWindowPoleGrowthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeta zeros and the negative part of the prime tail",
        H("Growth on every late power window"),
        Blocks(
            Paragraph(Text("Let Q(t) be the integral from t to infinity of (θ(x)−x)/x², "
                + "where θ counts each prime with logarithmic weight. Write A(b,Y) for the integral "
                + "of max(−Q(x),0)/√x from Y to Yᵇ. The prime powers of exponent at least two "
                + "change the corresponding complete Mangoldt budget by at most a multiple of log Y.")),
            Describe.Lean(DescribeId.Create("pole-window-growth"),
                DeclarationHandle.Create(Module + "off_line_zero_forces_window_mass"),
                H("Lower bound from a zero to the right of the critical line"),
                StatementSource.FromAuthor(Growth()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let β be the real part of the given zero. On a vertical line of "
                    + "large real part σ, choose two disks of equal radius. The disk centered at σ is "
                    + "free of zeros. A vertical displacement gives a unique closest zero in the second "
                    + "disk, at distance d less than σ−β+δ. After subtracting the principal part, "
                    + "Cauchy's estimate bounds the analytic remainder. The pole term gives a geometric "
                    + "lower bound for all sufficiently high normalized derivatives. "
                    + "The zero in the second disk can differ from the original zero.")),
                    Paragraph(Text("Adding the derivative at the real center bounds this quantity by "
                    + "twice the positive Mangoldt moment. Set a=log Y and choose order floor(σha) "
                    + "with 1<h<b. Tilting the two gamma tails controls the parts outside [a,ba]. "
                    + "Inside the window the kernel of order k is bounded by exp(−u/2)/(σ−1/2)ᵏ. "
                    + "Choosing h close to b and δ small gives the stated "
                    + "exponent at every sufficiently large Y."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("subpower-prime-windows"),
                DeclarationHandle.Create(Module + "rh_iff_frequently_small_prime_windows"),
                H("The Riemann hypothesis and arbitrarily late small windows"),
                StatementSource.FromAuthor(Criterion()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under RH the complete Mangoldt remainder divided by √x is "
                    + "eventually bounded, so the complete window integral is at most a constant times "
                    + "log Y. The prime-power correction obeys the same upper bound. Conversely, a "
                    + "right-half-strip zero forces a positive power of Y in every sufficiently late "
                    + "window. Choosing a smaller η contradicts the small-window condition. The "
                    + "functional equation carries this exclusion to the other half of the strip."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Real, body);
    private static Formula Implies(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula And(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Power(Formula x, Formula y) => F.Seq(x, F.Caret, F.Grp(y));
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Growth()
    {
        var z = F.Id("z");
        var b = F.Id("b");
        var e = F.Id("e");
        var y = F.Id("Y");
        var t = F.Id("T");
        var half = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)));
        var beta = At("Re", z);
        var power = F.Seq(b, F.Open, beta, F.Minus, half, F.Close, F.Minus, e);
        var tail = Exists("T", All("Y", Real, Implies(Le(t, y), Le(Power(y, power), At("A", b, y)))));
        var windows = All("b", Real, Implies(Less(F.D(1), b),
            All("e", Real, Implies(Less(F.D(0), e), tail))));
        var zero = new Formula.Relation(At("zeta", z), FormulaRelationOperator.Equal, F.D(0));
        return F.Disp(All("z", Complex, Implies(And(zero, Less(half, beta)), windows)));
    }

    private static Formula Criterion()
    {
        var b = F.Id("b");
        var e = F.Id("e");
        var y = F.Id("Y");
        var t = F.Id("T");
        var late = All("T", Real, Exists("Y", And(Le(t, y), Le(At("A", b, y), Power(y, e)))));
        var small = All("e", Real, Implies(Less(F.D(0), e), late));
        return F.Disp(All("b", Real, Implies(Less(F.D(1), b),
            new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff, small))));
    }
}
