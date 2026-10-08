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
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.And(StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("B")), Seq(StationaryHistorySlotGraphDocument.NBinary, Minus, StationaryHistorySlotGraphDocument.At("s"))),
                    StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("core")), StationaryHistorySlotGraphDocument.NBinary), StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("extras")), StationaryHistorySlotGraphDocument.At("e")),
                    StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("readStates")), Seq(StationaryHistorySlotGraphDocument.NBinary, Plus, D(1), Plus, StationaryHistorySlotGraphDocument.At("e"))),
                    StationaryHistorySlotGraphDocument.All("q", StationaryHistorySlotGraphDocument.V("Q"), StationaryHistorySlotGraphDocument.Imp(StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.V("q"), StationaryHistorySlotGraphDocument.At("selectedTargets")), StationaryHistorySlotGraphDocument.And(
                        StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.At("selectedRow", StationaryHistorySlotGraphDocument.V("q")), StationaryHistorySlotGraphDocument.At("resolvingRows")),
                        StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.At("target", StationaryHistorySlotGraphDocument.At("selectedRow", StationaryHistorySlotGraphDocument.V("q"))), StationaryHistorySlotGraphDocument.V("q"))))),
                    StationaryHistorySlotGraphDocument.All("n", StationaryHistorySlotGraphDocument.Hist, StationaryHistorySlotGraphDocument.Imp(StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.At("row", StationaryHistorySlotGraphDocument.V("n")), StationaryHistorySlotGraphDocument.At("resolvingRows")),
                        StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("children", StationaryHistorySlotGraphDocument.V("n"))), D(1)))))),
                "These sets and all their counts are obtained from C/I. A further exact equivalence "
                + "readStateEquiv identifies the finite readStates image with the original ActualRead "
                + "type. No supplied forest, N-core, read-count, injection, or J/s/Xi equation is a premise."),
            Result("resolving_selection", "resolving-selection", "Distinct selected resolving rows",
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.And(StationaryHistorySlotGraphDocument.LE(StationaryHistorySlotGraphDocument.At("s"), StationaryHistorySlotGraphDocument.At("J")),
                    StationaryHistorySlotGraphDocument.Call("InjOn", StationaryHistorySlotGraphDocument.At("selectedRow"), StationaryHistorySlotGraphDocument.At("selectedTargets")))),
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
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.All("q", StationaryHistorySlotGraphDocument.V("Q"), StationaryHistorySlotGraphDocument.Imp(StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.V("q"), StationaryHistorySlotGraphDocument.At("targets")), StationaryHistorySlotGraphDocument.And(
                    StationaryHistorySlotGraphDocument.LE(D(1), StationaryHistorySlotGraphDocument.At("baseline", StationaryHistorySlotGraphDocument.V("q"))),
                    StationaryHistorySlotGraphDocument.LE(StationaryHistorySlotGraphDocument.At("baseline", StationaryHistorySlotGraphDocument.V("q")), StationaryHistorySlotGraphDocument.At("tail", StationaryHistorySlotGraphDocument.V("q"))),
                    StationaryHistorySlotGraphDocument.Imp(StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.V("q"), StationaryHistorySlotGraphDocument.At("extras")), StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.At("baseline", StationaryHistorySlotGraphDocument.V("q")), D(1))))))),
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
                StationaryHistorySlotGraphDocument.Scope(StationaryHistorySlotGraphDocument.And(StationaryHistorySlotGraphDocument.All("q", StationaryHistorySlotGraphDocument.V("Q"), StationaryHistorySlotGraphDocument.Imp(StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.V("q"), StationaryHistorySlotGraphDocument.At("core")), StationaryHistorySlotGraphDocument.And(
                        StationaryHistorySlotGraphDocument.LE(D(2), StationaryHistorySlotGraphDocument.Card(StationaryHistorySlotGraphDocument.At("backgroundDigits", StationaryHistorySlotGraphDocument.V("q")))), StationaryHistorySlotGraphDocument.LE(StationaryHistorySlotGraphDocument.At("k", StationaryHistorySlotGraphDocument.V("q")), D(1))))),
                    StationaryHistorySlotGraphDocument.All("q", StationaryHistorySlotGraphDocument.V("Q"), StationaryHistorySlotGraphDocument.Imp(StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.V("q"), StationaryHistorySlotGraphDocument.At("extras")),
                        StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.At("backgroundChildren", StationaryHistorySlotGraphDocument.V("q")), StationaryHistorySlotGraphDocument.Emptyset))),
                    StationaryHistorySlotGraphDocument.All("q", StationaryHistorySlotGraphDocument.V("Q"), StationaryHistorySlotGraphDocument.All("n", StationaryHistorySlotGraphDocument.Hist, StationaryHistorySlotGraphDocument.All("m", StationaryHistorySlotGraphDocument.Hist,
                        StationaryHistorySlotGraphDocument.Imp(StationaryHistorySlotGraphDocument.And(StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.V("n"), StationaryHistorySlotGraphDocument.At("backgroundChildren", StationaryHistorySlotGraphDocument.V("q"))),
                            StationaryHistorySlotGraphDocument.Member(StationaryHistorySlotGraphDocument.V("m"), StationaryHistorySlotGraphDocument.At("backgroundChildren", StationaryHistorySlotGraphDocument.V("q"))),
                            Seq(Neg, Sp, Grp(StationaryHistorySlotGraphDocument.EqF(StationaryHistorySlotGraphDocument.V("n"), StationaryHistorySlotGraphDocument.V("m"))))),
                            StationaryHistorySlotGraphDocument.Call("Disjoint", StationaryHistorySlotGraphDocument.At("indexedSupport", StationaryHistorySlotGraphDocument.V("n")), StationaryHistorySlotGraphDocument.At("indexedSupport", StationaryHistorySlotGraphDocument.V("m"))))))))),
                "A binary parent supplies two distinct child digits. A selected pure resolving row "
                + "supplies its two distinct actual outgoing target digits through all of its unary "
                + "histories. Thus every core has k in {0,1}; extra targets have no background. "
                + "Different histories have disjoint original (x,i) event sets even if an ancestor and "
                + "descendant contain the same original label."))));

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryHistorySlotGraphDocument.ResultAt("StationaryHistoryCore", declaration, id, title, statement, explanation);
}
