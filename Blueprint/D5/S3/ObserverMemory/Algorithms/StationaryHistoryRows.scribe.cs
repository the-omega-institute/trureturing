using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual row execution and branching from original histories.",
        H("StationaryHistoryRows"),
        Blocks(
            Paragraph(Text(
                "The following constructions use the same arbitrary Initialized C. "
                + "For each parent with actual children, delay is the full natural gap "
                + "time(child)-(time(parent)+1), and nextTarget is the child's actual read control. "
                + "These definitions choose one actual child, then prove independence of that choice. "
                + "They are totalized on leaves, where no arrival is requested. All subtraction "
                + "in natural-time expressions is natural subtraction. NeZero(3P) follows from P>1. "
                + "A source row is the pair (readControl,color); physical supports are phases "
                + "at the current read, while indexed supports retain (original input,read index).")),
            Result("event_arrival", "event-arrival", "Actual consecutive-read wait chain",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("x", StationaryReadHistoryDocument.Label, StationaryReadHistoryDocument.All("i", StationaryReadHistoryDocument.N,
                    StationaryReadHistoryDocument.All("hi", StationaryReadHistoryDocument.LT(Seq(StationaryReadHistoryDocument.V("i"), Plus, D(1)), StationaryReadHistoryDocument.Call("reads", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("x"))),
                        StationaryReadHistoryDocument.Call("Waits", StationaryReadHistoryDocument.V("C"),
                            Seq(StationaryReadHistoryDocument.ReadTime("x", Seq(StationaryReadHistoryDocument.V("i"), Plus, D(1))), Minus,
                                Grp(Seq(StationaryReadHistoryDocument.ReadTime("x", StationaryReadHistoryDocument.V("i")), Plus, D(1)))),
                            StationaryReadHistoryDocument.Call("replay", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.Call("initial", StationaryReadHistoryDocument.V("C")),
                                StationaryReadHistoryDocument.Call("eventWord", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.Pair(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.V("i")))),
                            StationaryReadHistoryDocument.Call("control", StationaryReadHistoryDocument.Call("run", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"),
                                StationaryReadHistoryDocument.Pair(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.Call("initial", StationaryReadHistoryDocument.V("C"))),
                                StationaryReadHistoryDocument.ReadTime("x", Seq(StationaryReadHistoryDocument.V("i"), Plus, D(1)))))))))),
                "There is no intervening read between two consecutive indexed reads, and "
                + "no halt occurs in this live segment. The original trajectory_waits theorem "
                + "converts those actual wait instructions into the literal chain; its proof "
                + "is used directly in its original owner."),
            Result("history_row_execution", "history-row-execution", "Recorded answer selects the actual row",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n"], Seq(Exists, Sp, StationaryReadHistoryDocument.V("row"), Colon,
                    Seq(StationaryReadHistoryDocument.Call("Fin", D(3)), To, Sp, StationaryReadHistoryDocument.V("Q")), Comma,
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("instruction", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.At("readControl", "n")), StationaryReadHistoryDocument.Call("read", StationaryReadHistoryDocument.V("row"))),
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("postControl", "n"), StationaryReadHistoryDocument.Call("row", StationaryReadHistoryDocument.At("color", "n"))))))),
                "The pre-read control has a read instruction. Replaying the complete word "
                + "ends at that instruction's successor for the recorded absolute answer."),
            Result("child_arrival", "child-arrival", "Every child has a positive actual arrival",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n", "p"], StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.ParentEdge("n", "p"),
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.LT(D(0), StationaryReadHistoryDocument.Gap("n", "p")),
                        StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.Call("Waits", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.Gap("n", "p"), StationaryReadHistoryDocument.At("postControl", "p"),
                                StationaryReadHistoryDocument.At("readControl", "n")),
                            StationaryReadHistoryDocument.Call("IsRead", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.At("readControl", "n"))))))),
                "The canonical prefix parent is the immediately preceding indexed read. "
                + "WordShape gives a positive literal gap, and the actual next read is the endpoint."),
            Result("same_row_arrival", "same-row-arrival", "One literal wait and target per continuing row",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n", "m", "a", "b"],
                    StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.ParentEdge("a", "n"), StationaryReadHistoryDocument.ParentEdge("b", "m")), StationaryReadHistoryDocument.RowEq("n", "m")),
                        StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Gap("a", "n"), StationaryReadHistoryDocument.Gap("b", "m")),
                            StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("readControl", "a"), StationaryReadHistoryDocument.At("readControl", "b")))))),
                "The same source control and answer determine the same post-read control. "
                + "Deterministic first-future-read uniqueness forces equal literal waits "
                + "and equal read targets even across different levels or terminating control cycles."),
            Result("terminal_row_unique", "terminal-row-unique", "A terminal row has one full history",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n", "m"], StationaryReadHistoryDocument.Imp(
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.Call("IsLeaf", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("n")), StationaryReadHistoryDocument.RowEq("n", "m")),
                    StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.V("n"), StationaryReadHistoryDocument.V("m"))))),
                "A common row has one post-read instruction. If it halts, correctness "
                + "forces a common original label; both histories are that label's final indexed read."),
            Result("child_word", "child-word", "The complete child word retains the literal waits",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n", "p"], StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.ParentEdge("n", "p"),
                    StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("word", StationaryReadHistoryDocument.V("n")), StationaryReadHistoryDocument.Call("append",
                        StationaryReadHistoryDocument.Call("append", StationaryReadHistoryDocument.Call("word", StationaryReadHistoryDocument.V("p")),
                            StationaryReadHistoryDocument.Call("replicate", StationaryReadHistoryDocument.Gap("n", "p"), StationaryReadHistoryDocument.Call("wait"))),
                        StationaryReadHistoryDocument.Call("singleton", StationaryReadHistoryDocument.Call("read", StationaryReadHistoryDocument.At("color", "n")))))))),
                "A child is its complete parent word, every intervening unit wait, and "
                + "one read with its actual answer. No modular reduction shortens this word."),
            Result("child_digit_injective", "child-digit-injective", "One child per absolute answer",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["p", "n", "m"], StationaryReadHistoryDocument.Imp(
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.ParentEdge("n", "p"), StationaryReadHistoryDocument.ParentEdge("m", "p")),
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("color", "n"), StationaryReadHistoryDocument.At("color", "m"))), StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.V("n"), StationaryReadHistoryDocument.V("m"))))),
                "The parent's row fixes the literal continuation. Equal next answers "
                + "therefore give equal complete words, hence the same actual history."),
            Result("child_delay_target", "child-delay-target", "Chosen arrivals are independent of the child",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n", "p"], StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.ParentEdge("n", "p"),
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.LT(D(0), StationaryReadHistoryDocument.At("delay", "p")), StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Gap("n", "p"), StationaryReadHistoryDocument.At("delay", "p")),
                        StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("readControl", "n"), StationaryReadHistoryDocument.At("nextTarget", "p")),
                            StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("historyShift", "n"),
                                Seq(StationaryReadHistoryDocument.At("historyShift", "p"), Plus, StationaryReadHistoryDocument.At("delay", "p"))))))))),
                "Every actual child has the chosen positive literal delay and next target. "
                + "Its physical shift increases by the entire delay, including every wrap."),
            Result("row_delay_target", "row-delay-target", "Actual delay and target cohere on a shared row",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n", "m"], StationaryReadHistoryDocument.Imp(
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.Call("Nonempty", StationaryReadHistoryDocument.At("children", "n")), StationaryReadHistoryDocument.RowEq("n", "m")),
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("delay", "n"), StationaryReadHistoryDocument.At("delay", "m")),
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("nextTarget", "n"), StationaryReadHistoryDocument.At("nextTarget", "m")))))),
                "One continuing history forces every history on its actual row to continue: "
                + "a terminal history there would force them to be the same history. "
                + "They have one literal delay and one read target while retaining their identities."),
            Result("support_successor", "support-successor", "Every supporting input continues",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["p"], StationaryReadHistoryDocument.All("x", StationaryReadHistoryDocument.Label, StationaryReadHistoryDocument.Imp(
                    StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.Call("Nonempty", StationaryReadHistoryDocument.At("children", "p")), StationaryReadHistoryDocument.Member(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.At("support", "p"))),
                    Seq(Exists, Sp, StationaryReadHistoryDocument.V("n"), Colon, StationaryReadHistoryDocument.Hist, Comma,
                        StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.ParentEdge("n", "p"), StationaryReadHistoryDocument.Member(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.At("support", "n")))))))),
                "If the parent has an actual child, its post-read control is not a halt. "
                + "Every input in that parent has its own indexed successor read, including singleton continuations."),
            Result("child_support", "child-support", "Exact translated child fiber",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["n", "p"], StationaryReadHistoryDocument.All("x", StationaryReadHistoryDocument.Label, StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.ParentEdge("n", "p"),
                    Seq(StationaryReadHistoryDocument.Member(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.At("support", "n")), Iff,
                        StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.Member(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.At("support", "p")),
                            StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("digit", StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.Phase("x", "n")), StationaryReadHistoryDocument.At("color", "n")))))))),
                "The child consists exactly of parent labels whose phase at its next read "
                + "has the child's absolute answer. The fiber is derived from actual successors."),
            Result("branching", "branching", "At most two actual children",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.AllH(["p"], Seq(StationaryReadHistoryDocument.Card("children", "p"), Le, Sp, D(2)))),
                "A literal translation of one digit block yields two possible next digits, "
                + "separated by the residue cut. Child-answer injectivity gives at most two nonempty children."),
            Result("binary_count", "binary-count", "Exactly 3(P-1) binary full histories",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("card", StationaryReadHistoryDocument.Call("filter", StationaryReadHistoryDocument.Call("univ"),
                    Seq(StationaryReadHistoryDocument.V("n"), Mapsto, StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Card("children", "n"), D(2))))),
                    Seq(D(3), Times, Grp(Seq(StationaryReadHistoryDocument.V("P"), Minus, D(1)))))),
                "Each actual nonroot has one parent. Summing child counts and retaining "
                + "the unary histories gives leaves minus roots as the binary count: 3P-3."))));

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryReadHistoryDocument.ResultAt("StationaryHistoryRows", declaration, id, title, statement, explanation);
}
