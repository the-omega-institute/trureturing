using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedForestUnitCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original fixed physical domain has an attained minimum of the joint target tails.",
        H("Extraction and the attained fixed-forest capacity"),
        Blocks(
            Paragraph(Text(
                "Fix arbitrary P>1, h, ell and e and one complete physical forest with its prescribed identities. "
                + "OriginalImplementation quantifies over any finite nominal carrier Q and one total stationary table. "
                + "Its actual history rows and literal requests determine the inventory and assignment. "
                + "Neither an assignment nor a numerical capacity bound is an implementation premise.")),
            Result("targetEquiv", "target-equiv", "All actual nonroot targets",
                ControllerScope(Call("equivalence", Target,
                    Call("NonrootRead", V("C"), V("hP"), Paths))),
                "The forced binary representatives and the resolving target inject into actual nonroot reads. "
                + "The common first read cannot occur at any later history. Subtracting the forced target count "
                + "from the actual count N+1+e leaves exactly e targets. Fin e enumerates that entire complement, "
                + "so the equivalence includes every extra target.", DescribeRole.Definition),
            Result("assignment", "assignment", "The original same-digit assignment",
                ControllerScope(Call("Assignment", V("F"), V("R"), V("e"))),
                "Send each ordinary unary demand to its actual child target and original absolute digit. "
                + "The two distinct prescribed double rows exhaust rawJ+rawXi=2. An ordinary child cannot "
                + "share a forced row or another ordinary child's row. Every extra actual read has an incoming "
                + "physical request; a binary or exceptional request would instead place it in the forced core. "
                + "Thus the map is injective, preserves digits and hits every extra target.", DescribeRole.Definition),
            Result("request_target", "request-target", "Every internal literal request has its actual target",
                ControllerScope(All("n", V("Node"), Imp(Call("Internal", V("F"), V("n")),
                    EqF(ActualControl(Call("targetEquiv", V("F"), V("R"), V("I"),
                        Call("nextTarget", V("F"), V("R"), Extracted, V("n")))),
                        Call("requestTarget", V("I"), V("n")))))),
                "Binary requests use their prescribed representative. K uses H's target, and K1 uses H1's "
                + "resolving target. Every remaining internal node is exactly one ordinary unary demand."),
            Result("actualL_transport", "actual-tail-transport", "One joint maximum equals the actual literal maximum",
                ControllerScope(All("q", Target, EqF(
                    Call("L", V("F"), V("R"), Extracted, V("q")),
                    Call("actualL", V("C"), V("hP"), Paths,
                        Call("targetEquiv", V("F"), V("R"), V("I"), V("q")))))),
                "A source request attains each finite joint maximum and is an actual Arrival. Conversely any "
                + "actual arrival starts at one original indexed read and consists of pure waits to the next read. "
                + "Deterministic first-future-read uniqueness identifies its literal length and actual target. "
                + "Hence the two maxima agree, including every ordinary request and all three digits of an extra."),
            Result("nominal_lower_bound", "nominal-lower-bound", "The lower bound charges the full original Q",
                ControllerScope(Seq(Capacity(Extracted), Le, Call("card", V("Q")))),
                "Transport the joint target sum through the actual-target equivalence. The disjoint resource "
                + "embedding contains all original terminals, all actual reads, the entire common prefix and one "
                + "longest literal tail per actual nonroot target. Its codomain is the original full Q. "
                + "Finite cardinality gives the capacity inequality, retaining every unused nominal state."),
            Result("original_domain_iff", "original-domain-iff", "Compatibility and matching characterize existence",
                Scope(Seq(Call("Nonempty", Call("capacities", V("F"), V("R"), V("e"))), Iff,
                    Grp(Seq(Compatible, Land, Call("Nonempty", Assignment))))),
                "Every original implementation yields both structural compatibility and the extracted assignment. "
                + "Conversely a compatible assignment is realized by the existing total stationary construction. "
                + "The domain is the given fixed forest and identifications; no acquisition strategy is varied."),
            Result("attained_fixed_minimum", "attained-fixed-minimum", "An attained exact nominal minimum",
                MinimumStatement,
                "The original assignment class is finite. Choose a minimizer of sum_q(L_alpha(q)-1) using "
                + "finite minimum selection. Its Realization preserves all original paths, phases, labels and "
                + "deadlines, the graph statistics, and reachability of all constructed states. Its exact nominal "
                + "cardinal belongs to the original capacity set. Every competing nominal controller extracts "
                + "an assignment and is bounded by the full-Q embedding, so the same cardinal is IsLeast. "
                + "The universal lower bound also quantifies over finite carriers in arbitrary universes."),
            Result("empty_domain_no_minimum", "empty-domain-no-minimum", "Empty domains have no minimum",
                Scope(Imp(Seq(Neg, Sp, Grp(And(Compatible, Call("Nonempty", Assignment)))),
                    And(EqF(Call("capacities", V("F"), V("R"), V("e")), Emptyset),
                        All("n", N, Seq(Neg, Sp, Call("IsLeast",
                            Call("capacities", V("F"), V("R"), V("e")), V("n"))))))),
                "Failure of either the prescribed compatibility check or assignment existence empties the "
                + "original capacity set. A least element must belong to its set, so no minimum is asserted."),
            Result("attained_e0_threshold_minimum", "attained-ezero-threshold-minimum",
                "The simultaneous threshold formula is the actual operational minimum",
                ForestScope(All("R", Call("Prescribed", V("F")), ThresholdMinimum(V("P")))),
                "At e=0 choose the single descending same-digit assignment. Its joint tail excess is "
                + "E0+sum_c sum_{2<=k<=thresholdMax}(A(c,k)-B(c,k))_+. Realize that very assignment "
                + "with the original total unit table. Every competing full nominal carrier extracts an "
                + "original injection, whose threshold crossings bound the same sum from below. "
                + "Thus the threshold cardinal belongs to, and is IsLeast of, the original capacity set. "
                + "The statement retains one alpha for all k and also bounds arbitrary finite Q."),
            Result("original_context8319", "original-context-capacity",
                "The complete integer fixed-forest capacity statement",
                OriginalContextStatement,
                "For each integer p>1, P=toNat(p) preserves M=3p and N=3(p-1) exactly. "
                + "The same F and prescribed identities determine all e domains. The statement includes "
                + "existence, the attained joint maximum-tail minimum, empty domains, e=0 numerical "
                + "feasibility and its attained simultaneous threshold specialization."),
            Paragraph(Text(
                "Every original x in ZMod(3P) starts in one common initial control state. W adds one phase unit, "
                + "R preserves the phase and reads floor([s]_(3P)/P), and H_x emits the original x. "
                + "The finite words have prefix W^ell R followed by positive literal wait/read blocks, at most h reads, "
                + "and stop immediately after the last read. The full nominal Q includes unused states, all counters, "
                + "prefix states and terminal labels. The stationary instruction receives no phase, source label, "
                + "time, history or external register. Singleton continuations, positive literal waits and terminating "
                + "read-control cycles are allowed.")),
            Paragraph(Text(
                "The complete physical forest retains each (x,i), original labels, absolute phase x+shift modulo 3P, "
                + "literal waits, child digits, deadlines and exact support intervals within the current digit block. "
                + "It has three first-read fibers, 3P leaves and N binary nodes. Distinct binary parents A and B "
                + "share Q, occupying three digits together. Their common digit contains disjoint histories H and K "
                + "with the same literal request to T. The H1 and K1 children share a digit at T and request the "
                + "same resolving wait to Z, where their child digits differ. H,K,H1,K1 and the two shared rows "
                + "are distinct. The repeated edge is precisely w->v, J=s=Xi=1, r=N+1+e, Z is outside the binary "
                + "targets, and H=A or B and T=Q remain permitted. Incompatible prescribed identities give an empty domain.")),
            Paragraph(Text(
                "The inventory consists of N-1 binary targets, Z and e extra targets. Q has no spare digit; "
                + "each other binary target and Z has one; each extra has three. Ordinary demands are exactly the "
                + "unary histories except K,H1,K1, with their literal lengths and absolute child digits retained. "
                + "Assignments inject these demands into same-digit spares and hit every extra. Binary baselines "
                + "are maxima of parent literal requests, Z uses the common resolving request, and extras start at one. "
                + "L_alpha(q) is the maximum of that baseline and all assigned requests to q.")),
            Paragraph(Text(
                "Each compatible feasible assignment produces one total stationary table preserving every original "
                + "unit action, phase, read index, label, deadline and graph statistic. Every constructed control state "
                + "is reachable. Its full nominal cardinal is 3P+2N+1+ell+2e+sum_q(L_alpha(q)-1). "
                + "The minimum is over implementations of this fixed forest and identifications. At e>0 an extra "
                + "target retains one joint maximum across all its spare digits. At e=0, feasibility is exactly "
                + "A(c,1)<=B(c,1), subject to the prescribed compatibility, and one descending alpha attains every "
                + "threshold. The finite sum starts at k=2 and vanishes above the actual maximum literal value.")) )));

    private static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((t, i) => i == 0 ? new[] { Grp(t) } : new[] { Land, Grp(t) })]);
    private static Formula MinimumStatement => Scope(
        Imp(And(Compatible, Call("Nonempty", Assignment)),
            ExistsF("alpha", Assignment, And(
                Call("Nonempty", Call("Realization", V("F"), V("R"), V("alpha"))),
                All("beta", Assignment, Seq(Cost(V("alpha")), Le, Cost(V("beta")))),
                Call("IsLeast", Call("capacities", V("F"), V("R"), V("e")), Capacity(V("alpha"))),
                UniversalLower(Capacity(V("alpha")))))));

    private static Formula TargetAt(Formula e) => Call("Target", V("F"), V("R"), e);
    private static Formula AssignmentAt(Formula e) => Call("Assignment", V("F"), V("R"), e);
    private static Formula CompatibleAt(Formula e) => Call("Compatible", V("F"), V("R"), e);
    private static Formula DomainAt(Formula e) => Call("capacities", V("F"), V("R"), e);
    private static Formula CostAt(Formula alpha, Formula e) => Seq(Sum, Underscore,
        Grp(Seq(V("q"), Colon, TargetAt(e))), Grp(Seq(Call("L", V("F"), V("R"), alpha, V("q")), Minus, D(1))));
    private static Formula BaseCapacity(Formula p) => Seq(D(3), p, Plus,
        D(2), Grp(Seq(D(3), Grp(Seq(p, Minus, D(1))))), Plus, D(1), Plus, V("ell"));
    private static Formula CapacityAt(Formula alpha, Formula e, Formula p) =>
        Seq(BaseCapacity(p), Plus, D(2), e, Plus, CostAt(alpha, e));
    private static Formula NominalAt(Formula p, Formula body) =>
        All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        Instances(All("C", Call("Controller", p, V("Q")), body),
            Call("Fintype", V("Q")), Call("DecidableEq", V("Q"))));
    private static Formula LowerAt(Formula p, Formula e, Formula capacity) => NominalAt(p,
        Imp(Call("Nonempty", Call("OriginalImplementation", V("F"), V("R"), V("C"), e)),
            Seq(capacity, Le, Call("card", V("Q")))));
    private static Formula MinimumAt(Formula p, Formula e) =>
        Imp(And(CompatibleAt(e), Call("Nonempty", AssignmentAt(e))),
        ExistsF("alpha", AssignmentAt(e), And(
            Call("Nonempty", Call("Realization", V("F"), V("R"), V("alpha"))),
            All("beta", AssignmentAt(e), Seq(CostAt(V("alpha"), e), Le, CostAt(V("beta"), e))),
            Call("IsLeast", DomainAt(e), CapacityAt(V("alpha"), e, p)),
            LowerAt(p, e, CapacityAt(V("alpha"), e, p)))));
    private static Formula Digit => Call("Fin", D(3));
    private static Formula CountCondition => All("c", Digit, Seq(
        Call("A", V("F"), V("R"), V("c"), D(1)), Le,
        Call("B", V("F"), V("R"), V("c"), D(1))));
    private static Formula ThresholdCost => Seq(Call("Ezero", V("F"), V("R")), Plus,
        Sum, Underscore, Grp(Seq(V("c"), Colon, Digit)), Grp(Seq(Sum, Underscore,
            Grp(Seq(V("k"), InMacro, Sp, Call("Icc", D(2), Call("thresholdMax", V("F"), V("R"))))),
            Grp(Deficit(V("c"), V("k"))))));
    private static Formula Cross(Formula alpha) => Call("card", Seq(OpenBrace, Sp, V("d"),
        Colon, Call("ColorDemand", V("F"), V("R"), V("c")), Mid, Sp,
        And(Seq(V("k"), Le, Call("delay", V("F"), Call("val", Call("val", V("d"))))),
            Seq(Call("baseline", V("F"), V("R"), Call("target", Call("slot", alpha, Call("val", V("d"))))),
                Lt, V("k"))), CloseBrace));
    private static Formula ThresholdMinimum(Formula p) =>
        Imp(And(CompatibleAt(D(0)), CountCondition), ExistsF("alpha", AssignmentAt(D(0)), And(
            Call("Nonempty", Call("Realization", V("F"), V("R"), V("alpha"))),
            All("c", Digit, All("k", N, EqF(Cross(V("alpha")), Deficit(V("c"), V("k"))))),
            EqF(CostAt(V("alpha"), D(0)), ThresholdCost),
            Call("IsLeast", DomainAt(D(0)), Seq(BaseCapacity(p), Plus, ThresholdCost)),
            LowerAt(p, D(0), Seq(BaseCapacity(p), Plus, ThresholdCost)),
            All("c", Digit, All("k", N, Imp(
                Seq(Call("thresholdMax", V("F"), V("R")), Lt, V("k")), And(
                    EqF(Call("A", V("F"), V("R"), V("c"), V("k")), D(0)),
                    EqF(Call("B", V("F"), V("R"), V("c"), V("k")), D(0)))))))));
    private static Formula Deficit(Formula c, Formula k) => Seq(OpenBracket,
        Call("A", V("F"), V("R"), c, k), Minus, Call("B", V("F"), V("R"), c, k),
        CloseBracket, Underscore, Grp(Plus));
    private static Formula OriginalContextStatement => IntegerScope(And(
        EqF(Call("intCast", Seq(D(3), NatP)), Seq(D(3), V("p"))),
        EqF(Call("intCast", Seq(D(3), Grp(Seq(NatP, Minus, D(1))))),
            Seq(D(3), Grp(Seq(V("p"), Minus, D(1))))),
        Seq(Call("Nonempty", DomainAt(V("e"))), Iff,
            And(CompatibleAt(V("e")), Call("Nonempty", AssignmentAt(V("e"))))),
        MinimumAt(NatP, V("e")),
        Imp(Seq(Neg, Sp, Grp(And(CompatibleAt(V("e")), Call("Nonempty", AssignmentAt(V("e")))))),
            And(EqF(DomainAt(V("e")), Emptyset), All("n", N,
                Seq(Neg, Sp, Call("IsLeast", DomainAt(V("e")), V("n")))))),
        Seq(Call("Nonempty", DomainAt(D(0))), Iff, And(CompatibleAt(D(0)), CountCondition)),
        ThresholdMinimum(NatP)));
    private static Formula NatP => Call("toNat", V("p"));
    private static Formula IntegerScope(Formula body) =>
        All("p", Seq(Mathbb, Sp, Grp(V("Z"))), All("hp", Seq(D(1), Lt, V("p")),
        All("h", N, All("ell", N, All("e", N, All("Node", V("Type"),
        Instances(All("F", Call("PhysicalForest", NatP, V("h"), V("ell"), V("Node"),
            Call("natGreaterThanOne", V("p"), V("hp"))),
            All("R", Call("Prescribed", V("F")), body)),
            Call("Fintype", V("Node")), Call("DecidableEq", V("Node")))))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula ExistsF(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(t => Seq(OpenBracket, t, CloseBracket)), body]);
    private static Formula ForestScope(Formula body) =>
        All("P", N, All("h", N, All("ell", N, All("Node", V("Type"),
        Instances(All("hP", Seq(D(1), Lt, V("P")),
            All("F", Call("PhysicalForest", V("P"), V("h"), V("ell"), V("Node"), V("hP")), body)),
            Call("Fintype", V("Node")), Call("DecidableEq", V("Node")))))));
    private static Formula Scope(Formula body) => ForestScope(All("e", N,
        All("R", Call("Prescribed", V("F")), body)));
    private static Formula NominalScope(Formula body) =>
        All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        Instances(All("C", Call("Controller", V("P"), V("Q")), body),
            Call("Fintype", V("Q")), Call("DecidableEq", V("Q"))));
    private static Formula ControllerScope(Formula body) => Scope(NominalScope(
        All("I", Call("OriginalImplementation", V("F"), V("R"), V("C"), V("e")), body)));
    private static Formula Target => Call("Target", V("F"), V("R"), V("e"));
    private static Formula Assignment => Call("Assignment", V("F"), V("R"), V("e"));
    private static Formula Compatible => Call("Compatible", V("F"), V("R"), V("e"));
    private static Formula Paths => Call("paths", V("F"), V("R"), V("I"));
    private static Formula Extracted => Call("assignment", V("F"), V("R"), V("I"));
    private static Formula ActualControl(Formula q) => Call("val", Call("val", q));
    private static Formula Cost(Formula alpha) => Seq(Sum, Underscore,
        Grp(Seq(V("q"), Colon, Target)), Grp(Seq(Call("L", V("F"), V("R"), alpha, V("q")), Minus, D(1))));
    private static Formula Capacity(Formula alpha) => Seq(D(3), V("P"), Plus,
        D(2), Grp(Seq(D(3), Grp(Seq(V("P"), Minus, D(1))))), Plus, D(1), Plus,
        V("ell"), Plus, D(2), V("e"), Plus, Cost(alpha));
    private static Formula UniversalLower(Formula capacity) => NominalScope(
        Imp(Call("Nonempty", Call("OriginalImplementation", V("F"), V("R"), V("C"), V("e"))),
            Seq(capacity, Le, Call("card", V("Q")))));
    private static DocumentBlock Result(string declaration, string id, string heading,
        Formula statement, string explanation, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity." + declaration),
            H(heading), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);
}
