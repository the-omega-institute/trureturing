using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedForestThresholdAssignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single descending same-digit assignment attains every threshold of the fixed forest at e=0.",
        H("Simultaneous thresholds of the original literal tails"),
        Blocks(
            Paragraph(Text("Take exactly the ordinary unary demands and all original spare slots at e=0. "
                + "For digit c, ColorDemand and ColorSlot are their full digit fibers. Write n and m for their "
                + "cardinalities. E0 is sum_q(baseline(q)-1). A(c,k) counts demands with literal length at least k, and B(c,k) counts slots "
                + "whose target baseline is at least k. Descending order uses permutations of these entire finite "
                + "carriers, including tied lengths. When n<=m, demand rank i is assigned to slot rank i; "
                + "the remaining m-n slots are retained and left unused.")),
            Result("increment_rank", "increment-rank", "The exact ranks that cross a threshold",
                GenericScope(All("k", N, All("i", Call("Fin", Call("card", V("D"))), Seq(
                    And(Seq(V("k"), Le, Call("a", Call("order", V("a"), V("i")))),
                        Seq(Call("b", Call("map", V("a"), V("b"), V("bound"),
                            Call("order", V("a"), V("i")))), Lt, V("k"))), Iff,
                    And(Seq(Call("count", V("b"), V("k")), Lt, Seq(V("i"), Plus, D(1))),
                        Seq(V("i"), Plus, D(1), Le, Call("count", V("a"), V("k")))))))),
                "Use one-based rank i+1. A crossing occurs precisely at B(k)<i+1<=A(k). "
                + "The descending rank/count equivalence holds for every threshold, so no threshold-dependent "
                + "choice of assignment is needed."),
            Result("sortedAssignment", "sorted-assignment", "One original same-digit injection",
                Scope(Imp(CardCondition, Assignment)),
                "Sort each demand fiber by literal length and each full spare-slot fiber by target baseline. "
                + "The first n ranks define an injection in that digit. The disjoint digit fibers combine "
                + "these injections into one original Assignment. There are no extra targets to hit at e=0. "
                + "Empty demand fibers and empty slot fibers require no positive-cardinality assumption.",
                DescribeRole.Definition),
            Result("sorted_thresholds", "sorted-thresholds", "All thresholds attained by the same assignment",
                Scope(Imp(CardCondition, All("c", Digit, All("k", N, EqF(
                    Cross(Call("sortedAssignment", V("F"), V("R")), V("c"), V("k")),
                    Deficit(V("c"), V("k"))))))),
                "For the same stored sortedAssignment, the number of demands crossing threshold k in "
                + "digit c is exactly A(c,k)-B(c,k), with truncated natural subtraction. Surplus slots "
                + "contribute to B even though they are unused. The identity includes k=1 and all ties."),
            Result("arbitrary_threshold_lower", "arbitrary-threshold-lower", "Every injection pays the deficit",
                Scope(All("alpha", Assignment, All("c", Digit, All("k", N, Seq(
                    Deficit(V("c"), V("k")), Le, Cross(V("alpha"), V("c"), V("k"))))))),
                "Partition high demands into those placed at high baselines and those crossing the threshold. "
                + "Injectivity bounds the first class by all high-baseline slots. Consequently every original "
                + "assignment pays at least the same threshold deficit."),
            Result("spare_target_injective", "one-spare-per-target", "At most one spare slot per target",
                Scope(All("s", Call("SpareSlot", V("F"), V("R"), D(0)),
                    All("t", Call("SpareSlot", V("F"), V("R"), D(0)),
                        Imp(EqF(Call("target", V("s")), Call("target", V("t"))), EqF(V("s"), V("t")))))),
                "Q has no spare digit. Every other binary target and Z have exactly one. Since e=0 "
                + "has no extra target, two spare slots with the same target are equal. This is the reason "
                + "the color contributions can be added without charging a target twice."),
            Result("assignment_e0_iff", "ezero-feasibility", "Original assignment feasibility",
                Scope(Seq(Call("Nonempty", Assignment), Iff, CountCondition)),
                "All ordinary literal lengths and all target baselines are positive, so A(c,1)=n(c) "
                + "and B(c,1)=m(c). An injection gives n(c)<=m(c). Conversely these inequalities "
                + "construct the descending original assignment."),
            Result("thresholds_vanish", "finite-threshold-support", "Thresholds above the actual maximum vanish",
                Scope(All("k", N, Imp(Seq(Maximum, Lt, V("k")), All("c", Digit,
                    And(EqF(Call("A", V("F"), V("R"), V("c"), V("k")), D(0)),
                        EqF(Call("B", V("F"), V("R"), V("c"), V("k")), D(0))))))),
                "thresholdMax is the maximum of the actual ordinary literal lengths and all target baselines. "
                + "A maximum over an empty demand class is zero. Above this finite maximum both counts "
                + "are zero. There is no unsupported infinite-sum truncation."),
            Result("tail_cost_layers", "literal-tail-layers", "The same joint tails as threshold crossings",
                Scope(All("alpha", Assignment, EqF(Cost(V("alpha")), Seq(BaseExcess, Plus,
                    SumColors(SumLevels(Cross(V("alpha"), V("c"), V("k")))))))),
                "With at most one ordinary request per target, its increase is the positive part of "
                + "literal length minus baseline. Count the integer levels crossed by that increase. "
                + "Positive baselines remove level 1, so the finite sum starts at k=2. Partition the original "
                + "demands by their absolute digit; the result is exactly sum_q(L_alpha(q)-1)."),
            Result("sorted_cost", "sorted-joint-tail-cost", "The common assignment minimizes the joint tail cost",
                Scope(Imp(CardCondition, And(
                    EqF(Cost(Call("sortedAssignment", V("F"), V("R"))), ThresholdCost),
                    All("beta", Assignment, Seq(ThresholdCost, Le, Cost(V("beta"))))))),
                "The common sorted assignment attains every threshold lower bound and hence their entire "
                + "finite sum. The resulting cost is E0+sum_c sum_{2<=k<=thresholdMax}(A(c,k)-B(c,k))_+. "
                + "This identity concerns the same original target maxima L and is used by the attained "
                + "minimum of actual stationary implementations. At e>0, a target can have three spare "
                + "digits and must retain its joint maximum; this color sum does not apply."))));

    private static Formula V(string n) => F.Id(n);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Digit => Call("Fin", D(3));
    private static Formula Call(string n, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(n)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, t, Comma, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula And(params Formula[] ts) =>
        Seq([.. ts.SelectMany((t, i) => i == 0 ? new[] { Grp(t) } : new[] { Land, Grp(t) })]);
    private static Formula Instances(Formula b, params Formula[] ts) =>
        Seq([.. ts.Select(t => Seq(OpenBracket, t, CloseBracket)), b]);
    private static Formula Scope(Formula b) => All("P", N, All("h", N, All("ell", N,
        All("Node", V("Type"), Instances(All("hP", Seq(D(1), Lt, V("P")),
        All("F", Call("PhysicalForest", V("P"), V("h"), V("ell"), V("Node"), V("hP")),
        All("R", Call("Prescribed", V("F")), b))), Call("Fintype", V("Node")),
            Call("DecidableEq", V("Node")))))));
    private static Formula GenericScope(Formula b) => All("D", V("Type"), All("S", V("Type"),
        Instances(All("a", Seq(V("D"), To, N), All("b", Seq(V("S"), To, N),
        All("bound", Seq(Call("card", V("D")), Le, Call("card", V("S"))), b))),
            Call("Fintype", V("D")), Call("Fintype", V("S")))));
    private static Formula Target => Call("Target", V("F"), V("R"), D(0));
    private static Formula Assignment => Call("Assignment", V("F"), V("R"), D(0));
    private static Formula Demands(Formula c) => Call("ColorDemand", V("F"), V("R"), c);
    private static Formula Slots(Formula c) => Call("ColorSlot", V("F"), V("R"), c);
    private static Formula CardCondition => All("c", Digit, Seq(Call("card", Demands(V("c"))),
        Le, Call("card", Slots(V("c")))));
    private static Formula CountCondition => All("c", Digit, Seq(
        Call("A", V("F"), V("R"), V("c"), D(1)), Le,
        Call("B", V("F"), V("R"), V("c"), D(1))));
    private static Formula Deficit(Formula c, Formula k) => Seq(OpenBracket,
        Call("A", V("F"), V("R"), c, k), Minus, Call("B", V("F"), V("R"), c, k),
        CloseBracket, Underscore, Grp(Plus));
    private static Formula Cross(Formula alpha, Formula c, Formula k) => Call("card", Seq(
        OpenBrace, Sp, V("d"), Colon, Demands(c), Mid, Sp,
        And(Seq(k, Le, Call("delay", V("F"), Call("val", Call("val", V("d"))))),
            Seq(Call("baseline", V("F"), V("R"), Call("target", Call("slot", alpha, Call("val", V("d"))))), Lt, k)),
        CloseBrace));
    private static Formula Maximum => Call("thresholdMax", V("F"), V("R"));
    private static Formula BaseExcess => Call("Ezero", V("F"), V("R"));
    private static Formula SumColors(Formula b) => Seq(Sum, Underscore, Grp(Seq(V("c"), Colon, Digit)), Grp(b));
    private static Formula SumLevels(Formula b) => Seq(Sum, Underscore,
        Grp(Seq(V("k"), InMacro, Sp, Call("Icc", D(2), Maximum))), Grp(b));
    private static Formula ThresholdCost => Seq(BaseExcess, Plus, SumColors(SumLevels(Deficit(V("c"), V("k")))));
    private static Formula Cost(Formula alpha) => Seq(Sum, Underscore,
        Grp(Seq(V("q"), Colon, Target)), Grp(Seq(Call("L", V("F"), V("R"), alpha, V("q")), Minus, D(1))));
    private static DocumentBlock Result(string declaration, string id, string title, Formula statement,
        string explanation, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment." + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
