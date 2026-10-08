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
                InitializedScope(All("x", Label, All("i", N,
                    Imp(LT(Seq(V("i"), Plus, D(1)), Call("reads", V("C"), V("hP"), V("I"), V("x"))),
                        Call("Waits", V("C"),
                            Seq(ReadTime("x", Seq(V("i"), Plus, D(1))), Minus,
                                Grp(Seq(ReadTime("x", V("i")), Plus, D(1)))),
                            Call("replay", V("C"), Call("initial", V("C")),
                                Call("eventWord", V("C"), V("hP"), V("I"), Pair(V("x"), V("i")))),
                            Call("control", Call("run", V("C"), V("hP"),
                                Pair(V("x"), Call("initial", V("C"))),
                                ReadTime("x", Seq(V("i"), Plus, D(1))))))))), needsNonzero: false),
                "There is no intervening read between two consecutive indexed reads, and "
                + "no halt occurs in this live segment. The original trajectory_waits theorem "
                + "converts those actual wait instructions into the literal chain."),
            Result("history_row_execution", "history-row-execution", "Recorded answer selects the actual row",
                InitializedScope(AllH(["n"], Seq(Exists, Sp, V("row"), Colon,
                    Seq(Call("Fin", D(3)), To, Sp, V("Q")), Comma,
                    And(EqF(Call("instruction", V("C"), At("readControl", "n")), Call("read", V("row"))),
                        EqF(At("postControl", "n"), Call("row", At("color", "n"))))))),
                "The pre-read control has a read instruction. Replaying the complete word "
                + "ends at that instruction's successor for the recorded absolute answer."),
            Result("child_arrival", "child-arrival", "Every child has a positive actual arrival",
                InitializedScope(AllH(["n", "p"], Imp(ParentEdge("n", "p"),
                    And(LT(D(0), Gap("n", "p")),
                        And(Call("Waits", V("C"), Gap("n", "p"), At("postControl", "p"),
                                At("readControl", "n")),
                            Call("IsRead", V("C"), At("readControl", "n"))))))),
                "The canonical prefix parent is the immediately preceding indexed read. "
                + "WordShape gives a positive literal gap, and the actual next read is the endpoint."),
            Result("same_row_arrival", "same-row-arrival", "One literal wait and target per continuing row",
                InitializedScope(AllH(["n", "m", "a", "b"],
                    Imp(And(And(ParentEdge("a", "n"), ParentEdge("b", "m")), RowEq("n", "m")),
                        And(EqF(Gap("a", "n"), Gap("b", "m")),
                            EqF(At("readControl", "a"), At("readControl", "b")))))),
                "The same source control and answer determine the same post-read control. "
                + "Deterministic first-future-read uniqueness forces equal literal waits "
                + "and equal read targets even across different levels or terminating control cycles."),
            Result("terminal_row_unique", "terminal-row-unique", "A terminal row has one full history",
                InitializedScope(AllH(["n", "m"], Imp(
                    And(Call("IsLeaf", V("C"), V("hP"), V("I"), V("n")), RowEq("n", "m")),
                    EqF(V("n"), V("m"))))),
                "A common row has one post-read instruction. If it halts, correctness "
                + "forces a common original label; both histories are that label's final indexed read."),
            Result("child_word", "child-word", "The complete child word retains the literal waits",
                InitializedScope(AllH(["n", "p"], Imp(ParentEdge("n", "p"),
                    EqF(Call("word", V("n")), Call("append",
                        Call("append", Call("word", V("p")),
                            Call("replicate", Gap("n", "p"), Call("wait"))),
                        Call("singleton", Call("read", At("color", "n")))))))),
                "A child is its complete parent word, every intervening unit wait, and "
                + "one read with its actual answer. No modular reduction shortens this word."),
            Result("child_digit_injective", "child-digit-injective", "One child per absolute answer",
                InitializedScope(AllH(["p", "n", "m"], Imp(
                    And(And(ParentEdge("n", "p"), ParentEdge("m", "p")),
                        EqF(At("color", "n"), At("color", "m"))), EqF(V("n"), V("m"))))),
                "The parent's row fixes the literal continuation. Equal next answers "
                + "therefore give equal complete words, hence the same actual history."),
            Result("child_delay_target", "child-delay-target", "Chosen arrivals are independent of the child",
                InitializedScope(AllH(["n", "p"], Imp(ParentEdge("n", "p"),
                    And(LT(D(0), At("delay", "p")), And(EqF(Gap("n", "p"), At("delay", "p")),
                        And(EqF(At("readControl", "n"), At("nextTarget", "p")),
                            EqF(At("historyShift", "n"),
                                Seq(At("historyShift", "p"), Plus, At("delay", "p"))))))))),
                "Every actual child has the chosen positive literal delay and next target. "
                + "Its physical shift increases by the entire delay, including every wrap."),
            Result("row_delay_target", "row-delay-target", "Actual delay and target cohere on a shared row",
                InitializedScope(AllH(["n", "m"], Imp(
                    And(Call("Nonempty", At("children", "n")), RowEq("n", "m")),
                    And(EqF(At("delay", "n"), At("delay", "m")),
                        EqF(At("nextTarget", "n"), At("nextTarget", "m")))))),
                "One continuing history forces every history on its actual row to continue: "
                + "a terminal history there would force them to be the same history. "
                + "They have one literal delay and one read target while retaining their identities."),
            Result("support_successor", "support-successor", "Every supporting input continues",
                InitializedScope(AllH(["p"], All("x", Label, Imp(
                    And(Call("Nonempty", At("children", "p")), Member(V("x"), At("support", "p"))),
                    Seq(Exists, Sp, V("n"), Colon, Hist, Comma,
                        And(ParentEdge("n", "p"), Member(V("x"), At("support", "n")))))))),
                "If the parent has an actual child, its post-read control is not a halt. "
                + "Every input in that parent has its own indexed successor read, including singleton continuations."),
            Result("child_support", "child-support", "Exact translated child fiber",
                InitializedScope(AllH(["n", "p"], All("x", Label, Imp(ParentEdge("n", "p"),
                    Seq(Member(V("x"), At("support", "n")), Iff,
                        And(Member(V("x"), At("support", "p")),
                            EqF(Call("digit", V("hP"), Phase("x", "n")), At("color", "n")))))))),
                "The child consists exactly of parent labels whose phase at its next read "
                + "has the child's absolute answer. The fiber is derived from actual successors."),
            Result("branching", "branching", "At most two actual children",
                InitializedScope(AllH(["p"], Seq(Card("children", "p"), Le, Sp, D(2)))),
                "A literal translation of one digit block yields two possible next digits, "
                + "separated by the residue cut. Child-answer injectivity gives at most two nonempty children."),
            Result("binary_count", "binary-count", "Exactly 3(P-1) binary full histories",
                InitializedScope(EqF(Call("card", Call("filter", Call("univ"),
                    Seq(V("n"), Colon, Hist, Mapsto, EqF(Card("children", "n"), D(2))))),
                    Seq(D(3), Times, Grp(Seq(V("P"), Minus, D(1)))))),
                "Each actual nonroot has one parent. Summing child counts and retaining "
                + "the unary histories gives leaves minus roots as the binary count: 3P-3."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Label => Call("ZMod", Seq(D(3), Times, Sp, V("P")));
    private static Formula Hist => Call("History", V("C"), V("hP"), V("I"));
    private static Formula At(string name, string n) => Call(name, V("C"), V("hP"), V("I"), V(n));
    private static Formula EqF(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula LT(Formula x, Formula y) => Seq(x, Lt, y);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Member(Formula x, Formula s) => Seq(x, InMacro, Sp, s);
    private static Formula Card(string name, string n) => Call("card", At(name, n));
    private static Formula Phase(string x, string n) => Seq(V(x), Plus, At("historyShift", n));
    private static Formula Gap(string n, string p) =>
        Seq(At("time", n), Minus, Grp(Seq(At("time", p), Plus, D(1))));
    private static Formula ParentEdge(string n, string p) => EqF(At("parent", n), Call("some", V(p)));
    private static Formula RowEq(string n, string m) =>
        And(EqF(At("readControl", n), At("readControl", m)), EqF(At("color", n), At("color", m)));
    private static Formula ReadTime(string x, Formula i) => Call("readTime", V("C"), V("hP"), V("I"), V(x), i);
    private static Formula AllH(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (current, name) => All(name, Hist, current));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula Imp(Formula premise, Formula body) => Seq(Grp(premise), Implies, Grp(body));
    private static Formula And(Formula a, Formula b) => Seq(Grp(a), Land, Grp(b));
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
    private static Formula Scope(Formula body) => All("P", N,
        All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        All("C", Call("Controller", V("P"), V("Q")), All("hP", LT(D(1), V("P")), body))));
    private static Formula InitializedScope(Formula body, bool needsNonzero = true) => Scope(All("ell", N, All("h", N,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")), needsNonzero
            ? Seq(OpenBracket, Call("NeZero", Seq(D(3), Times, Sp, V("P"))), CloseBracket, body)
            : body))));
    private static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => ResultAt("StationaryHistoryRows", declaration, id, title, statement, explanation);
}
