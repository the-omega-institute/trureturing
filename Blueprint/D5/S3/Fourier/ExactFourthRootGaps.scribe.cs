using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ExactFourthRootGapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact fourth-root character gaps give a finite step lower bound on the common-time sine deficit.",
        H("Exact Fourth-Root Gaps"),
        Blocks(
            Paragraph(Text(
                "Let S be a finite subset of an index type J with real frequencies g and weights w. "
                + "An incompatible "
                + "relation is an integer vector k whose frequency sum is zero and whose coefficient "
                + "sum is indivisible by four. Its support consists of the coordinates in S with "
                + "nonzero coefficients, and its length is the sum of their absolute values. "
                + "The threshold τ is the squared chord gap from 1 to i raised to the coefficient "
                + "sum, divided by twice the squared length. Write R(k) for incompatibility, "
                + "V(k) for support, len(k) for length and M(v) for the support maximum. "
                + "The sine loss E(t,j) is 1 − sin(g(j)t). Write C(x) for the candidate omitted "
                + "weight fractions and Q(x) for their minimum. A(t) is the weighted sine average and D(T) is "
                + "one minus its supremum over T. The integral bounds and length comparisons "
                + "assume nonnegative weights. The support, minimum and partition assertions "
                + "allow arbitrary real weights.")),
            Result("coordinate_loss_same_time", "Exact coordinate loss at a common time",
                Coordinate(),
                "The relation has positive length and its threshold lies in (0, 2]. Choose a "
                + "support coordinate of maximal loss. Apply the weighted character chord estimate "
                + "to the orbit and the quarter-phase target. Bound the sum of the chord lengths "
                + "by the coefficient length times the maximal chord. Squaring and using the "
                + "chord-sine identity yields the loss threshold at that coordinate."),
            Result("supportMaximum_zero_or_attained", "Attainment on each exact support",
                Attainment(),
                "For each nonempty residue class of the coefficient sum modulo four, choose a "
                + "relation of minimum positive integer length. The numerator is constant within "
                + "the class. The attained maximum over these finitely many candidates is the "
                + "support maximum. The squared gaps of incompatible residues are 2 and 4. "
                + "An empty support family contributes the default zero."),
            Result("least_hitting_weight", "Minimum omitted weight at each threshold",
                All("x", Reals, Call("IsLeast", Call("C", F.Id("x")), Q(F.Id("x")))),
                "At threshold x, the omitted set meets every incompatible relation support whose "
                + "threshold is at least x. Each candidate fraction is the weight of the omitted "
                + "set divided by the total weight of S. Retaining the empty set gives a candidate."),
            Result("breakpoint_partition", "Finite partition into intervals of constant cost",
                Partition(),
                "Add 0 and 2 to the maxima of all exact supports in the powerset of S. For a "
                + "positive threshold, a retained subset is admissible precisely when every "
                + "support it contains has maximum strictly below the threshold. On each "
                + "interval from one cut to the next, exclude the left endpoint and include "
                + "the right endpoint. Write B for the nonzero cuts, prev(b) for the cut preceding b "
                + "and I(b) for the cell ending at b. The active support family is constant throughout "
                + "each cell."),
            Result("finite_step_integral", "Exact finite sum for the integral",
                FiniteIntegral(),
                "Sum the width of each interval times the omission fraction at its right endpoint."),
            Result("integrated_Q_same_time", "Integrated bound at a common time",
                All("t", Reals, Le(Integral(), Sub(D(1), Call("A", F.Id("t"))))),
                "At one real time t, the coordinates whose sine loss is at least x meet all "
                + "active supports. Integrating the resulting weight tail gives the normalized "
                + "sum of coordinate losses, by integrating each coordinate's interval indicator. "
                + "If total weight is zero, every omission fraction is zero by Lean's division convention."),
            Result("integrated_Q_le_deficit", "Integrated bound over the allowed times",
                All("T", Seq(Mathcal, Grp(F.Id("P")), Open, Reals, Close), Le(Integral(), Call("D", F.Id("T")))),
                "For any nonempty set T of allowed real times, take the supremum of the normalized "
                + "sine average. For empty T the deficit is 1 and the same-time bound at zero applies."),
            Result("partial_length_le_integral", "Comparison with partial length sums",
                PartialComparison(),
                "An incompatible relation of length at most h has threshold at least 1/h². "
                + "Throughout the inverse-square interval ending at 1/h², the exact threshold "
                + "cost bounds the minimum omission fraction at length h. Integrate the "
                + "inequality over the adjacent intervals. The interval from 0 to the next "
                + "threshold supplies the single-scale residual. Write P(h) for the omitted fraction "
                + "for incompatible relations of length at most h and T(h) for (h⁻² − (h+1)⁻²)P(h). The full series L sums T(h) over "
                + "positive integer lengths."),
            Result("length_series_le_integral", "Comparison with the length series",
                Le(F.Id("L"), Integral()),
                "Take the limit of the bounded partial sums using convergence of the length series."),
            Result("pair_exact_Q", "Exact cost for frequencies (1, 3)",
                PairCost(),
                "For any common positive weight, every incompatible relation uses both coordinates "
                + "and has length at least four. The relation (3, −1) has length four and squared chord gap four, so "
                + "the threshold is exactly 1/8. At or below it one of the two equal-weight "
                + "coordinates must be omitted. Above it no omission is needed."),
            Result("pair_strict", "Strict improvement for frequencies (1, 3)",
                PairStrict(),
                "With equal positive weights, the interval of cost 1/2 yields an integral of 1/16. "
                + "The length-only "
                + "omission fraction is 1/2 from length four onward and zero at smaller lengths. "
                + "The weighted series telescopes to 1/32."),
            Paragraph(Text(
                "These bounds apply to any finite real frequency system satisfying the stated "
                + "weight conditions. A quantitative application to actual zeta ordinates "
                + "requires separate evidence about which incompatible relations hold, their "
                + "supports and their coefficient lengths.")))));

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Coefficients => new Formula.Power(Seq(Mathbb, Grp(F.Id("Z"))), F.Id("J"));
    private static Formula Q(Formula x) => Call("Q", x);
    private static Formula T(Formula h) => Call("T", h);
    private static Formula P(Formula h) => Call("P", h);
    private static Formula M(Formula v) => Call("M", v);
    private static Formula V(Formula k) => Call("V", k);
    private static Formula Threshold(Formula k) => Seq(F.Tau, Sp, Open, k, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Bound(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Integral() =>
        Seq(Int, Underscore, Grp(D(0)), Caret, Grp(D(2)), Sp, Q(F.Id("x")), Sp, F.Id("d"), F.Id("x"));

    private static Formula Coordinate()
    {
        var k = F.Id("k");
        var t = F.Id("t");
        var j = F.Id("j");
        var coordinate = Some("j", F.Id("J"), And(Bound(j, V(k)), Le(Threshold(k), Call("E", t, j))));
        var positiveLength = Lt(D(0), Call("len", k));
        var thresholdBounds = And(Lt(D(0), Threshold(k)), Le(Threshold(k), D(2)));
        return All("k", Coefficients, Imp(Call("R", k),
            All("t", Reals, And(positiveLength, And(thresholdBounds, coordinate)))));
    }

    private static Formula Attainment()
    {
        var v = F.Id("v");
        var k = F.Id("k");
        var r = F.Id("r");
        var support = And(Call("R", k), Equal(V(k), v));
        var upperBound = All("r", Coefficients,
            Imp(Call("R", r), Imp(Equal(V(r), v), Le(Threshold(r), M(v)))));
        return All("v", Call("Finset", F.Id("J")),
            Or(And(Equal(M(v), D(0)), Seq(Neg, Sp, Grp(Some("k", Coefficients, support)))),
                Some("k", Coefficients, And(support,
                    And(Equal(M(v), Threshold(k)), And(Lt(D(0), M(v)), upperBound))))));
    }

    private static Formula Partition()
    {
        var b = F.Id("b");
        var x = F.Id("x");
        var rights = F.Id("B");
        var cell = Call("I", b);
        var positiveInterval = Seq(Open, D(0), Comma, D(2), CloseBracket);
        var union = Call("Union", rights, F.Id("I"));
        return And(Call("PairwiseDisjoint", rights, F.Id("I")),
            And(Equal(union, positiveInterval),
                All("b", Reals, Imp(Bound(b, rights),
                    All("x", Reals, Imp(Bound(x, cell), Equal(Q(x), Q(b))))))));
    }

    private static Formula FiniteIntegral()
    {
        var b = F.Id("b");
        var width = Seq(Open, Sub(b, Call("prev", b)), Close);
        return Equal(Integral(), Seq(Sum, Underscore, Grp(Bound(b, F.Id("B"))), Sp, Mul(width, Q(b))));
    }

    private static Formula PartialComparison()
    {
        var n = F.Id("n");
        var h = F.Id("h");
        var next = Add(n, D(1));
        var partial = Seq(Sum, Underscore, Grp(Equal(h, D(1))), Caret, Grp(n), Sp, T(h));
        var residual = Frac(P(next), new Formula.Power(Seq(Open, next, Close), D(2)));
        return All("n", Naturals, Le(Add(partial, residual), Integral()));
    }

    private static Formula PairCost()
    {
        var x = F.Id("x");
        var q = Q(x);
        var cutoff = Frac(D(1), D(8));
        return All("x", Reals, And(Imp(Le(x, cutoff), Equal(q, Frac(D(1), D(2)))),
            Imp(Lt(cutoff, x), Equal(q, D(0)))));
    }

    private static Formula PairStrict() =>
        And(Equal(F.Id("L"), Frac(D(1), D(3, 2))),
            And(Equal(Integral(), Frac(D(1), D(1, 6))), Lt(F.Id("L"), Integral())));

    private static DocumentBlock Result(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ExactFourthRootGaps." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
