using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumPhaseCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumPhaseCutoff";
    private static readonly LibraryNoteRef Lamzouri =
        LibraryNoteRef.Create("D5/L/Weil/lamzouri2024effective");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite character separation and a retained mass bound give uniform weighted sine recurrence.",
        H("Power cutoffs for weighted sine recurrence"),
        Blocks(
            Paragraph(Text("Fix a locally finite positive spectrum with index type I, " +
                "frequency γ(j) and nonnegative weights w(j). Write J(T) for the finite set " +
                "of indices satisfying γ(j) ≤ T. "),
                Ref("D5/S3/Analytic/Oscillation/OrdinateCounting")),
            Describe.Lean(DescribeId.Create("mass"), DeclarationHandle.Create(Owner + ".mass"),
                H("Spectral mass"), StatementSource.FromAuthor(MassStatement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The cutoff is inclusive."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sine"), DeclarationHandle.Create(Owner + ".sine"),
                H("Weighted sine score"), StatementSource.FromAuthor(SineStatement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The score uses the same weights as W."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("has-box-gap"), DeclarationHandle.Create(Owner + ".HasBoxGap"),
                H("Separation on each fixed coefficient box"), StatementSource.FromAuthor(GapStatement()),
                AssessedProvenance.FromRepo(Lamzouri),
                Blocks(Paragraph(Text("One positive C works for every fixed integer bound M " +
                    "at the chosen exponent slack d. The cutoff from which the inequality " +
                    "holds may depend on M."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eventual-sine-cutoff-tradeoff"),
                DeclarationHandle.Create(Owner + ".eventual_sine_cutoff_tradeoff"),
                H("A weighted sine threshold in every translated window"),
                StatementSource.FromAuthor(TradeoffStatement()),
                AssessedProvenance.FromRepo(Lamzouri),
                Blocks(
                    Paragraph(Text("Write D(X) = |J(X)| and G for the coefficient box " +
                        "separation condition. W and S use the same arbitrary weight family. " +
                        "For every 0 < α < 1, the assumed retained mass fraction W(T^α)/W(T) " +
                        "converges to a value q at least α².")),
                    Paragraph(Text("Choose 0 < α < min(b,1) and 0 < e₀ ≤ 1 with " +
                        "2(1 − α²) + α²e₀ < e. Set X = T^α and choose a positive integer M " +
                        "with 1/M < e₀. Apply the finite recurrence at frequencies γ(j)/r " +
                        "and target angle π/2, with probabilities w(j)/W(X). The gap " +
                        "condition gives δ = C exp(−X^(1+d))/r. "),
                        Ref("D5/S3/Fourier/WeightedPhaseRecurrence")),
                    Paragraph(Text("Pick d > 0 with α(1+d) < b. The logarithm of exp(T^b)δ " +
                        "is T^b − T^(α(1+d)) + log(C/r). The bound on D(X) gives " +
                        "D(X) log M = O(T^α log T). The two growth costs and the fixed " +
                        "constants fit the strict recurrence budget. The retained score " +
                        "therefore has normalized loss below e₀ at a point in every window.")),
                    Paragraph(Text("At that point the omitted coordinates contribute " +
                        "at most twice their weight to the full loss. With q_T = W(X)/W(T), " +
                        "the full normalized loss is less than 2(1 − q_T) + q_T e₀. " +
                        "This expression decreases with q_T, and its limit is below e.")),
                    Paragraph(Text("For the actual positive zeta ordinates, assume RH " +
                        "and Lamzouri's Conjecture 1.1. Use mγ γ/(1/4 + γ²) as the weight, " +
                        "where mγ is the analytic multiplicity. The count N(X) eventually " +
                        "exceeds any fixed M, so the conjecture supplies G. Distinct mode " +
                        "count is bounded by N(X), which is O(X log X), and W(T)/log² T " +
                        "tends to 1/(4π). Hence W(T)>0 eventually and q = α². The " +
                        "specialization gives the displayed bound for these actual weights " +
                        "under the two conjectures. "),
                        Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine")),
                    Paragraph(Text("Lamzouri's Theorem 1.5 concerns the extrema on [2,X] " +
                        "of sums truncated at X² under Effective LI and its coefficient " +
                        "assumptions."))),
                DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Nats => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
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
    private static Formula J(Formula cutoff) => Call("J", cutoff);
    private static Formula W(Formula cutoff) => Call("W", cutoff);
    private static Formula Lambda(Formula var, Formula body) =>
        F.Seq(F.Open, var, F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula Eventually(Formula var, Formula body) =>
        Call("Eventually", Lambda(var, body), Id("atTop"));
    private static Formula Sum(Formula term, Formula cutoff) =>
        F.Seq(F.Sum, F.Underscore, F.Grp(In(Id("j"), J(cutoff))), F.Sp, term);

    private static Formula MassStatement()
    {
        var t = Id("T");
        return F.Disp(All("T", Reals, Equal(W(t), Sum(Call("w", Id("j")), t))));
    }

    private static Formula SineStatement()
    {
        var t = Id("T");
        var v = Id("v");
        var j = Id("j");
        var term = Multiply(Call("w", j), Call("sin", Multiply(Call("gamma", j), v)));
        return F.Disp(All("T", Reals, All("v", Reals, Equal(Call("S", t, v), Sum(term, t)))));
    }

    private static Formula GapStatement()
    {
        var x = Id("X");
        var j = Id("j");
        var d = Id("d");
        var c = Id("C");
        var m = Id("M");
        var coefficient = Call("k", j);
        var box = And(Exists("j", J(x), NotEqual(coefficient, Num(0))),
            All("j", J(x), Le(new Formula.Absolute(coefficient), m)));
        var frequency = Sum(Multiply(coefficient, Call("gamma", j)), x);
        var separation = Le(Multiply(c, Call("exp", new Formula.Negate(Power(x, Add(Num(1), d))))),
            new Formula.Absolute(frequency));
        var cutoff = Eventually(x, All("k", Power(new Formula.Integers(), J(x)), Imp(box, separation)));
        var bound = All("d", Reals, Imp(Lt(Num(0), d),
            Exists("C", Reals, And(Lt(Num(0), c), All("M", Nats, cutoff)))));
        return F.Disp(new Formula.Logic(Id("G"), FormulaLogicOperator.Iff, bound));
    }

    private static Formula TradeoffStatement()
    {
        var r = Id("r");
        var b = Id("b");
        var e = Id("e");
        var t = Id("T");
        var x = Id("X");
        var a = Id("a");
        var u = Id("u");
        var alpha = Id("alpha");
        var q = Id("q");
        var B = Id("B");
        var nonnegative = All("j", Id("I"), Le(Num(0), Call("w", Id("j"))));
        var positive = Eventually(t, Lt(Num(0), W(t)));
        var dimension = Exists("B", Reals, And(Lt(Num(0), B),
            Eventually(x, Le(Call("D", x), Multiply(B, Multiply(x, Call("log", x)))))));
        var ratio = Div(W(Power(t, alpha)), W(t));
        var retained = All("alpha", Reals, Imp(And(Lt(Num(0), alpha), Lt(alpha, Num(1))),
            Exists("q", Reals, And(Le(Power(alpha, Num(2)), q),
                Call("Tendsto", Lambda(t, ratio), Id("atTop"), Call("nhds", q))))));
        var cutoff = Multiply(Num(2), Subtract(Num(1), Power(Call("min", b, Num(1)), Num(2))));
        var conditions = And(Lt(Num(0), r), And(Lt(Num(0), b), Lt(cutoff, e)));
        var loss = Subtract(Num(1), Div(Call("S", t, Div(u, r)), W(t)));
        var endpoint = Add(a, Call("exp", Power(t, b)));
        var window = F.Seq(F.OpenBracket, a, F.Comma, F.Sp, endpoint, F.CloseBracket);
        var recurrence = All("a", Reals, Exists("u", Reals, And(In(u, window), Lt(loss, e))));
        var conclusion = Eventually(t, And(Lt(Num(0), W(t)), recurrence));
        var hypotheses = And(nonnegative, And(positive, And(dimension, And(Id("G"), retained))));
        return F.Disp(Imp(hypotheses,
            All("r", Reals, All("b", Reals, All("e", Reals, Imp(conditions, conclusion))))));
    }
}
