using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryWeightedHistoryOverlapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual full-history multiplicity gives a background-sensitive retained-weight inequality for every original initialized controller.",
        H("Actual weighted history overlap"),
        Blocks(
            Paragraph(Text(
                "Fix an arbitrary integer P greater than one, represented in Lean by its positive natural value, "
                + "arbitrary finite ell and h, a full finite nominal carrier Q, Controller P Q, and "
                + "Initialized C hP ell h. Each original label in ZMod(3P) starts at the same initial control. "
                + "The exact action word is W^ell R(W^+R)*, with at most h reads and immediate stopping "
                + "after the last read. All positive literal waits, singleton continuations, and cycles "
                + "terminating for every initialized label are retained. Unused nominal states remain charged. "
                + "No supplied forest, row acyclicity, bounded wait, fixed P, injection, or J/s/Xi equation "
                + "is a premise. NeZero(3P) and DecidableEq Q are representation instances; the original "
                + "finite carrier supplies Fintype Q for the final charge.")),
            Paragraph(Text(
                "All inventories below use the same C/hP/I. Node is its actual full History type, "
                + "Event is a label together with its actual read index, and row(n)=(readControl(n),color(n)). "
                + "The actual unique parent map determines children. The inherited score-independent core "
                + "is the union of all binary targets and s distinct selected pure resolving targets. "
                + "Its cardinal is N=3(P-1); extras are the remaining e targets. Binary baselines are "
                + "maxima of all positive representatives 1+((delta-1) mod P), selected resolving baselines "
                + "are their literal waits, and extras have baseline one. Tail(q)=L_q is the original "
                + "actualL longest literal arrival. Every baseline l_q lies in [1,L_q].")),
            Paragraph(Text(
                "BackgroundParent(n) means n is binary or lies on a selected pure resolving source row. "
                + "OrdinaryParent(n) means n has exactly one child and is not a background parent. "
                + "Ordinary is the subtype of all these actual parent histories. OrdinaryChild selects "
                + "the unique child, not a row or a weight representative. OrdinaryChildren(q) is its "
                + "target-q image. BackgroundChildren(q) includes every child of a background parent.")),
            Result("actual_child_partition", "actual-child-partition", "Unique-parent child inventory",
                Scope(All("q", V("Q"), And(
                    EqF(SetOf("n", At("nonroots"), EqF(At("readControl", V("n")), V("q"))),
                        Call("union", At("backgroundChildren", V("q")), At("ordinaryChildren", V("q")))),
                    Call("Disjoint", At("backgroundChildren", V("q")), At("ordinaryChildren", V("q"))),
                    Call("Injective", At("ordinaryChild"))))),
                "Every nonroot history has one original forest parent. Branching is at most two; "
                + "a nonbackground internal parent is consequently unary. Unique parents make the "
                + "ordinary child map injective and the two inventories disjoint. Equal rows, equal "
                + "positive delays, or repeated drawings never identify different ordinary histories."),
            Result("actual_indexed_partition", "actual-indexed-partition", "Indexed occurrence separation",
                Scope(And(
                    All("v", At("Event"), Unique("n", At("Node"), Member(V("v"), At("indexedSupport", V("n"))))),
                    All("n", At("Node"), All("m", At("Node"), Imp(Neq(V("n"), V("m")),
                        Call("Disjoint", At("indexedSupport", V("n")), At("indexedSupport", V("m")))))),
                    All("d", At("Ordinary"), All("dprime", At("Ordinary"), Imp(Neq(V("d"), V("dprime")),
                        Call("Disjoint", At("indexedSupport", At("ordinaryChild", V("d"))),
                            At("indexedSupport", At("ordinaryChild", V("dprime"))))))))),
                "The event stores (x,i), and its full prefix is uniquely determined. An ancestor "
                + "and descendant containing the same label still use different indices. The ordinary "
                + "child injectivity transports the original indexed-history separation without erasing "
                + "equal-row occurrences. This helper is consumed by the classified event partition."),
            Result("actual_event_partition", "actual-event-partition", "Background and ordinary indexed events",
                Scope(All("q", V("Q"), And(
                    EqF(SetOf("v", At("Event"), And(
                        Neq(At("parent", At("event", V("v"))), V("none")),
                        EqF(At("readControl", At("event", V("v"))), V("q")))),
                        Call("union", At("backgroundEvents", V("q")), At("ordinaryEvents", V("q")))),
                    Call("Disjoint", At("backgroundEvents", V("q")), At("ordinaryEvents", V("q"))),
                    All("v", At("Event"), Unique("n", At("Node"), Member(V("v"), At("indexedSupport", V("n")))))))),
                "BackgroundEvents(q) and OrdinaryEvents(q) filter actual indexed occurrences by "
                + "membership of their full prefix in the corresponding child inventory. Pulling "
                + "back the unique-parent partition proves exact coverage and disjointness. The root "
                + "events remain the original first-read events; every later occurrence is in this partition."),
            Paragraph(Text(
                "Let f range over real-valued functions on positive integers. Score(f,d) is internally "
                + "the nonnegative real conversion of f(d) for d>0, with zero only as a total-function "
                + "default at d=0. Every ordinary literal delta is positive, so under nonnegativity "
                + "this is exactly f(delta). Weight(d)=Score(f,delta_d). Demands(q,c) is the finite "
                + "subtype inventory of all ordinary parent histories whose child has slot (q,c). "
                + "Af sums weights over every ordinary history. a(q,c) sums weights in Demands(q,c); "
                + "m(q,c) is its finite maximum, with empty maximum zero. Distinct identities with equal "
                + "weights contribute separately to Af and a. For an occupied background digit z=a; "
                + "for a free digit z=a-m. Zf sums z over every actual nonfirst target and all three "
                + "digits. Retained(q) sums m over the background-free digits.")),
            Result("retained_identity", "retained-identity", "Exact retained weights and literal fidelity",
                Scope(All("f", ScoreType, And(
                    EqF(W("Af"), Seq(W("Zf"), Plus, SumOver("q", At("targets"), W("retained", V("q"))))),
                    LE(D(0), W("Zf")),
                    All("q", V("Q"), All("c", Fin3, EqF(W("a", V("q"), V("c")),
                        Seq(W("z", V("q"), V("c")), Plus,
                            Call("if", Member(V("c"), At("backgroundDigits", V("q"))), D(0), W("m", V("q"), V("c"))))))),
                    All("q", V("Q"), All("c", Fin3, Imp(EqF(At("demands", V("q"), V("c")), V("empty")),
                        EqF(W("m", V("q"), V("c")), D(0))))),
                    Imp(Call("Nonnegative", V("f")), And(
                        EqF(W("Af"), SumOver("d", At("Ordinary"), Call("f", At("delay", Call("val", V("d")))))),
                        All("q", V("Q"), All("c", Fin3,
                            EqF(W("a", V("q"), V("c")), SumOver("d", At("demands", V("q"), V("c")),
                                Call("f", At("delay", Call("val", V("d")))))))))),
                    Imp(EqF(Call("f", D(1)), D(0)), All("d", At("Ordinary"),
                        Imp(EqF(At("delay", Call("val", V("d"))), D(1)), EqF(W("weight", V("d")), D(0))))),
                    All("d", At("Ordinary"), All("dprime", At("Ordinary"),
                        Imp(EqF(At("row", Call("val", V("d"))), At("row", Call("val", V("dprime")))),
                            EqF(At("delay", Call("val", V("d"))), At("delay", Call("val", V("dprime")))))))))),
                "Finite fiber summation counts each actual ordinary history once. Maximum is at "
                + "most the nonnegative sum, so free-slot subtraction is the exact real difference "
                + "and Zf is nonnegative. Summing the slot identity gives Af=Zf+sum Retained. "
                + "The same result exposes the exact positive-literal sums, empty maxima, zero "
                + "weight for literal wait one when f(1)=0, and original same-source-row delay coherence. "
                + "The wait-one histories remain in Ordinary; no restricted zero-correction transport is asserted."),
            Result("core_retained_bound", "core-retained-bound", "One spare core digit",
                Scope(All("f", ScoreType, All("hf", Call("Nonnegative", V("f")),
                    All("hm", Call("Monotone", V("f")), All("hl", Call("LipschitzWith", D(1), V("f")),
                    All("q", V("Q"), All("hq", Member(V("q"), At("core")),
                        LE(W("retained", V("q")), Seq(At("k", V("q")), Times, Sp, Call("score", V("f"), At("baseline", V("q"))), Plus,
                            Grp(Seq(At("tail", V("q")), Minus, At("baseline", V("q"))))))))))))),
                "Each actual ordinary delay at q is at most its original longest tail L_q. "
                + "Monotonicity bounds every maximum by f(L_q). The actual core has k_q<=1; "
                + "if k_q=0 no ordinary weight remains, and if k_q=1 the positive-integer "
                + "Lipschitz bound gives f(L_q)<=f(l_q)+(L_q-l_q). No reduced wait is charged as a literal tail."),
            Result("extra_retained_bound", "extra-retained-bound", "Three-digit extra target bound",
                Scope(All("f", ScoreType, All("hf", Call("Nonnegative", V("f")),
                    All("hm", Call("Monotone", V("f")), All("hcap", Cap,
                    All("q", V("Q"), All("hq", Member(V("q"), At("extras")),
                        LE(W("retained", V("q")), Seq(At("tail", V("q")), Plus, D(1)))))))))),
                "An extra target has no background digits. Its three retained maxima are "
                + "individually bounded by f(L_q), and the contract 3f(L)<=L+1 pays their total "
                + "with one joint longest target tail, irrespective of history multiplicity."),
            Paragraph(Text(
                "E=sum over all Targets of (L_q-1); E0=sum over Core of (l_q-1). These are natural "
                + "sums with no negative truncation on actual targets, because 1<=l_q<=L_q. "
                + "The inherited target set is exactly the disjoint union Core and Extras, with |Extras|=e.")),
            Result("exact_tail_decomposition", "exact-tail-decomposition", "Every actual tail is charged once",
                Scope(EqF(Seq(At("E"), Plus, D(2), Times, Sp, At("e")),
                    Seq(At("E0"), Plus,
                        SumOver("q", At("core"), Seq(At("tail", V("q")), Minus, At("baseline", V("q")))),
                        Plus, SumOver("q", At("extras"), Seq(At("tail", V("q")), Plus, D(1)))))),
                "On a core, L_q-1=(l_q-1)+(L_q-l_q). Each extra has L_q-1 plus its own "
                + "two units from 2e, yielding L_q+1. The disjoint actual partition ensures that "
                + "every target and tail growth is charged exactly once."),
            Result("necessary_inequality", "necessary-inequality", "Original overlap correction and full nominal charge",
                Scope(Instances(All("f", ScoreType, All("hf", Call("Admissible", V("f")), And(
                    LE(Seq(At("E0"), Plus, W("Af"), Minus,
                        SumOver("q", At("core"), Seq(At("k", V("q")), Times, Sp, Call("score", V("f"), At("baseline", V("q"))))), Minus, W("Zf")),
                        Seq(At("E"), Plus, D(2), Times, Sp, At("e"))),
                    LE(Seq(D(3), Times, Sp, V("P"), Plus, D(2), Times, Sp, NBinary, Plus, D(1), Plus,
                        D(2), Times, Sp, At("e"), Plus, V("ell"), Plus, At("E")), Call("card", V("Q")))))),
                    Call("Fintype", V("Q")))),
                "Admissible means f is nonnegative and monotone on positive integers, "
                + "LipschitzWith 1, f(1)=0, and 3f(L)<=L+1 for every positive L. The retained "
                + "identity, core/extra bounds, and exact tail decomposition yield "
                + "E+2e>=E0+Af-sum_core k_q f(l_q)-Zf. Score(f,l_q) equals the literal positive "
                + "f(l_q), and the compiled original-domain application checks that form directly. "
                + "The exact target-to-NonrootRead equivalence and the frozen full_nominal_resource_embedding "
                + "then charge all terminal states, actual reads, common-prefix positions and longest "
                + "wait-chain units against full Q, including unused states."),
            Paragraph(Text(
                "This is the necessary general overlap bound, with unrestricted J, s and Xi. "
                + "Zf remains present for multiple collisions. The original 83.12/82.14 restricted "
                + "zero-correction transport, occupied-digit equality and injection of remaining "
                + "demands are separate obligations. No synthesis, sufficiency or unconditional "
                + "nine-point capacity twenty-nine assertion follows here.")))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Hist => At("History");
    private static Formula Fin3 => Call("Fin", D(3));
    private static Formula ScoreType => Seq(Call("PNat"), Rightarrow, Call("Real"));
    private static Formula W(string name, params Formula[] args) =>
        Call(name, [V("C"), V("hP"), V("I"), V("f"), .. args]);
    private static Formula Neq(Formula a, Formula b) => Call("Not", EqF(a, b));
    private static Formula Unique(string name, Formula type, Formula body) =>
        Call("ExistsUnique", V(name), type, body);
    private static Formula Cap => All("L", Call("PNat"),
        LE(Seq(D(3), Times, Sp, Call("f", V("L"))), Seq(V("L"), Plus, D(1))));
    private static Formula NBinary => Seq(D(3), Times, Sp, Grp(Seq(V("P"), Minus, D(1))));
    private static Formula Emptyset => Call("empty");
    private static Formula At(string name, params Formula[] args) =>
        Call(name, [V("C"), V("hP"), V("I"), .. args]);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula LE(Formula a, Formula b) => Seq(a, Le, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula SetOf(string name, Formula set, Formula condition) =>
        Seq(OpenBrace, V(name), InMacro, Sp, set, Mid, Grp(condition), CloseBrace);
    private static Formula SumOver(string name, Formula set, Formula summand) =>
        Seq(Sum, Underscore, Grp(Member(V(name), set)), Grp(summand));
    private static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((t, i) => i == 0 ? new[] { Grp(t) } : new[] { Land, Grp(t) })]);
    private static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(t => Seq(OpenBracket, t, CloseBracket)), body]);
    private static Formula Scope(Formula body) => All("P", Nat, All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        Instances(All("C", Call("Controller", V("P"), V("Q")),
        All("hP", Seq(D(1), Lt, V("P")), All("ell", Nat, All("h", Nat,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")), body))))),
        Call("DecidableEq", V("Q")), Call("NeZero", Seq(D(3), Times, Sp,  Sp, V("P"))))));
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
    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
