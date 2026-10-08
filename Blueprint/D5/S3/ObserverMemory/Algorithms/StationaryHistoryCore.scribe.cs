using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted actual slot incidence selects structural core targets and literal-tail baselines.",
        H("StationaryHistoryCore"),
        Blocks(
            Paragraph(Text(
                "B is the image of all binary histories under nextTarget. Its multiplicity at q counts "
                + "all binary parents targeting q; s sums multiplicity minus one over B. Thus |B|=N-s. "
                + "Select exactly s targets from G minus B. For each selected q choose an actual "
                + "pure resolving row with target q. Core is B union selectedTargets, extras is Targets "
                + "minus Core, and e=|Targets|-N. Every history on a pure resolving row is unary. "
                + "The selected rows are distinct because their target identities are distinct.")),
            Result("structural_core", "structural-core", "Exact controller-derived core and extras",
                Scope(And(EqF(Card(At("B")), Seq(NBinary, Minus, At("s"))),
                    EqF(Card(At("core")), NBinary), EqF(Card(At("extras")), At("e")),
                    EqF(Card(At("readStates")), Seq(NBinary, Plus, D(1), Plus, At("e"))),
                    All("q", V("Q"), Imp(Member(V("q"), At("selectedTargets")), And(
                        Member(At("selectedRow", V("q")), At("resolvingRows")),
                        EqF(At("target", At("selectedRow", V("q"))), V("q"))))),
                    All("n", Hist, Imp(Member(At("row", V("n")), At("resolvingRows")),
                        EqF(Card(At("children", V("n"))), D(1)))))),
                "These sets and all their counts are obtained from C/I. A further exact equivalence "
                + "readStateEquiv identifies the finite readStates image with the original ActualRead "
                + "type. No supplied forest, N-core, read-count, injection, or J/s/Xi equation is a premise."),
            Result("resolving_selection", "resolving-selection", "Distinct selected resolving rows",
                Scope(And(LE(At("s"), At("J")),
                    Call("InjOn", At("selectedRow"), At("selectedTargets")))),
                "The selected row's actual next-target identity recovers q, giving injectivity. "
                + "Their cardinal s is consequently bounded by the already derived resolving-row count J."),
            Paragraph(Text(
                "For every internal history n the positive representative is 1+((delay(n)-1) mod P). "
                + "A binary history has representative strictly below P; an internal unary history "
                + "can have representative P. BinaryBaseline(q) is the maximum of all binary-parent "
                + "representatives targeting q, with empty maximum zero. Baseline(q) uses this value "
                + "on B, the selected resolving row's literal wait on selectedTargets, and one elsewhere. "
                + "TargetRead identifies an actual nonfirst target with the original NonrootRead type. "
                + "Tail(q) is actualL of that target, the maximum of actual positive literal arrivals. "
                + "These definitions have no score function parameter.")),
            Result("baseline_bounds", "baseline-bounds", "Literal-tail bounds for all baselines",
                Scope(All("q", V("Q"), Imp(Member(V("q"), At("targets")), And(
                    LE(D(1), At("baseline", V("q"))),
                    LE(At("baseline", V("q")), At("tail", V("q"))),
                    Imp(Member(V("q"), At("extras")), EqF(At("baseline", V("q")), D(1))))))),
                "Every selected parent's actual indexed run constructs an Arrival in the original "
                + "controller. The canonical actualL maximum bounds its literal delay and hence its "
                + "positive representative. Supremum over all binary parents preserves the bound; "
                + "selected resolving baselines remain literal waits, and extra baselines remain one."),
            Paragraph(Text(
                "BackgroundParent(n) holds exactly when n is binary or row(n) is the selected row "
                + "of a selected resolving target. These alternatives cannot coincide. BackgroundChildren(q) "
                + "retains each full history n targeting q whose unique forest parent is a background parent. "
                + "BackgroundDigits(q) is its color image, and k(q)=3-|BackgroundDigits(q)|. "
                + "Only this digit occupancy takes an image: the history collection retains all different "
                + "prefix identities, including equal-row histories with equal literal waits.")),
            Result("background_structure", "background-structure", "Actual core digit occupancy",
                Scope(And(All("q", V("Q"), Imp(Member(V("q"), At("core")), And(
                        LE(D(2), Card(At("backgroundDigits", V("q")))), LE(At("k", V("q")), D(1))))),
                    All("q", V("Q"), Imp(Member(V("q"), At("extras")),
                        EqF(At("backgroundChildren", V("q")), Emptyset))),
                    All("q", V("Q"), All("n", Hist, All("m", Hist,
                        Imp(And(Member(V("n"), At("backgroundChildren", V("q"))),
                            Member(V("m"), At("backgroundChildren", V("q"))),
                            Seq(Neg, Sp, Grp(EqF(V("n"), V("m"))))),
                            Call("Disjoint", At("indexedSupport", V("n")), At("indexedSupport", V("m"))))))))),
                "A binary parent supplies two distinct child digits. A selected pure resolving row "
                + "supplies its two distinct actual outgoing target digits through all of its unary "
                + "histories. Thus every core has k in {0,1}; extra targets have no background. "
                + "Different histories have disjoint original (x,i) event sets even if an ancestor and "
                + "descendant contain the same original label."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Hist => At("History");
    private static Formula NBinary => Seq(D(3), Times, Grp(Seq(V("P"), Minus, D(1))));
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
    private static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((t, i) => i == 0 ? new[] { Grp(t) } : new[] { Land, Grp(t) })]);
    private static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(t => Seq(OpenBracket, t, CloseBracket)), body]);
    private static Formula Scope(Formula body) => All("P", Nat, All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        Instances(All("C", Call("Controller", V("P"), V("Q")),
        All("hP", Seq(D(1), Lt, V("P")), All("ell", Nat, All("h", Nat,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")), body))))),
        Call("DecidableEq", V("Q")), Call("NeZero", Seq(D(3), Times, Sp, V("P"))))));
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
    private static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => ResultAt("StationaryHistoryCore", declaration, id, title, statement, explanation);
}
