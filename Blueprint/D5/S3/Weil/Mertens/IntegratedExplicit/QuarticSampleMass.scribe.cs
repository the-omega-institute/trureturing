using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class QuarticSampleMassDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted fourth-power samples and the Riemann hypothesis",
        H("Prime windows and discrete sample mass"),
        Blocks(
            Paragraph(Text("Let U be the integrated complete Mangoldt remainder "
                + "CompleteMertensPeak.U. For natural numbers a ≤ b, let S(a,b) be the sum of "
                + "max(U(n⁴),0)/n³ over all natural n from a through b. The positive part is "
                + "taken before summing. Let w(n) be this sample weight, with w(0) = 0. The prime-only mass P(a,b) is the integral of max(−Q(x),0)/√x "
                + "from a⁴ to b⁴, with Q the Chebyshev tail PrimeOnlyTailCorrection.primeTail.")),
            Describe.Lean(DescribeId.Create("prime-window-sample-mass"),
                DeclarationHandle.Create(Module + "prime_mass_le_samples"),
                H("Prime-only mass is controlled by the fourth-power samples"),
                StatementSource.FromAuthor(Comparison()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a ≥ 2, the prime-only mass plus 15 w(b) is at most 135 S(a,b) "
                        + "plus a uniform nonnegative constant times log b−log a. Between "
                        + "n⁴ and (n+1)⁴ the Mangoldt ramp sum lies below its endpoint chord. "
                        + "The centering error is at most 225n², the cell has length at most "
                        + "15n³, and x√x is at least n⁶. These estimates bound the complete "
                        + "mass of each cell by 15 times the left sample weight, 120 times "
                        + "the right sample weight, and 3375/n.")),
                    Paragraph(Text("Summing cells assigns coefficient at most 135 to each "
                        + "sample weight and keeps the terminal correction 15 w(b) on the left. The errors telescope against the logarithm using "
                        + "1/n ≤ 2(log(n+1)−log n). The prime-power correction adds another "
                        + "uniform multiple of log b−log a. The restriction a ≥ 2 places "
                        + "the interval in the domain of the complete Chebyshev tail identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-sample-harmonic-bound"),
                DeclarationHandle.Create(Module + "eventual_logarithmic_bound"),
                H("A harmonic upper bound under RH"),
                StatementSource.FromAuthor(Harmonic()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under RH, S(a,b) < 1/a + log b−log a for every "
                    + "sufficiently large a and all b ≥ a. The strict quartic sample "
                    + "estimate puts each sufficiently late sample weight below 1/n. "
                    + "The left endpoint contributes strictly less than 1/a. Each subsequent "
                    + "reciprocal is at most the logarithmic increment from the previous integer."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-zero-sample-growth"),
                DeclarationHandle.Create(Module + "off_line_zero_forces_sample_mass"),
                H("A right-of-line zero forces eventual power growth"),
                StatementSource.FromAuthor(Growth()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a zeta zero z with Re z > 1/2 and any positive "
                    + "loss ε, S(k³,k⁴) is at least k to the power 16(Re z−1/2)−ε for all "
                    + "sufficiently large natural k. The prime-only lower bound on "
                    + "[k¹²,k¹⁶] gives the factor 16. Part of the exponent loss absorbs "
                    + "both the factor 135 and the logarithmic error in the sample comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-subpower-sample-mass"),
                DeclarationHandle.Create(Module + "rh_iff_subpower_sample_mass"),
                H("RH is equivalent to cofinal subpower sample mass"),
                StatementSource.FromAuthor(Criterion()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive η and every natural threshold A, "
                        + "the condition asks for a natural k ≥ max(A,2) with S(k³,k⁴) ≤ k raised to η. "
                        + "Under RH the block bound 1/k³ + log k eventually lies below any "
                        + "positive power of k. Conversely, each right-of-line zero forces "
                        + "eventual growth above some positive power of k, ruling out "
                        + "cofinally many blocks below that power. Excluding those zeros "
                        + "in the right half of the critical strip gives RH.")),
                    Paragraph(Text("The subpower condition controls a sum and allows "
                        + "isolated large samples. An unconditional estimate of this "
                        + "sum on cofinally many blocks would therefore prove RH."))),
                DescribeRole.Theorem))));

    private static Formula Natural => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula p, Formula q) =>
        new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula And(Formula p, Formula q) =>
        new Formula.Logic(p, FormulaLogicOperator.And, q);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Power(Formula x, Formula e) => F.Seq(x, F.Caret, F.Grp(e));
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula LogGap(Formula a, Formula b) => F.Seq(At("log", b), F.Minus, At("log", a));

    private static Formula Block(Formula k) => At("S", Power(k, F.D(3)), Power(k, F.D(4)));

    private static Formula Comparison()
    {
        var c = F.Id("C");
        var a = F.Id("a");
        var b = F.Id("b");
        var bound = F.Seq(F.D(1, 3, 5), At("S", a, b), F.Plus, c, F.Open, LogGap(a, b), F.Close);
        var windows = All("a", Natural, All("b", Natural,
            Implies(And(Le(F.D(2), a), Le(a, b)), Le(F.Seq(At("P", a, b), F.Plus, F.D(1, 5), At("w", b)), bound))));
        return F.Disp(Exists("C", Real, And(Le(F.D(0), c), windows)));
    }

    private static Formula Harmonic()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var reciprocal = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(a));
        var inequality = Lt(At("S", a, b), F.Seq(reciprocal, F.Plus, LogGap(a, b)));
        var tail = Exists("N", Natural, All("a", Natural,
            Implies(Le(F.Id("N"), a), All("b", Natural, Implies(Le(a, b), inequality)))));
        return F.Disp(Implies(F.Id("RiemannHypothesis"), tail));
    }

    private static Formula Growth()
    {
        var e = F.Id("e");
        var k = F.Id("k");
        var z = F.Id("z");
        var beta = At("Re", z);
        var half = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)));
        var exponent = F.Seq(F.D(1, 6), F.Open, beta, F.Minus, half, F.Close, F.Minus, e);
        var tail = Exists("N", Natural, All("k", Natural,
            Implies(Le(F.Id("N"), k), Le(Power(k, exponent), Block(k)))));
        return F.Disp(All("z", Complex,
            Implies(And(Eq(At("zeta", z), F.D(0)), Lt(half, beta)),
                All("e", Real, Implies(Lt(F.D(0), e), tail)))));
    }

    private static Formula Criterion()
    {
        var a = F.Id("A");
        var k = F.Id("k");
        var e = F.Id("e");
        var cofinal = All("A", Natural, Exists("k", Natural,
            And(Le(At("max", a, F.D(2)), k), Le(Block(k), Power(k, e)))));
        return F.Disp(new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff,
            All("e", Real, Implies(Lt(F.D(0), e), cofinal))));
    }
}
