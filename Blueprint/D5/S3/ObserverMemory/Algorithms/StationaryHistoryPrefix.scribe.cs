using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryPrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual complete action prefixes, indexed reads, roots, and original terminal histories.",
        H("StationaryHistoryPrefix"),
        Blocks(
            Paragraph(Text(
                "Fix P greater than one, one controller C on the full nominal carrier Q, "
                + "and Initialized C hP ell h. Every original x in ZMod(3P) starts at "
                + "the common initial control and physical phase x. Wait adds one, read "
                + "returns the absolute digit floor(val/P), and halt stores an original label. "
                + "Each path has ell initial waits, a first read, positive literal waits "
                + "between reads, at most h reads, and halt immediately after its final read. "
                + "Long waits, modular wraps, singleton continuations, unused nominal states, "
                + "and control cycles which terminate on all initialized inputs are retained.")),
            Paragraph(Text(
                "Action records wait, read with its actual answer, or halt with its stored label. "
                + "Trace x t records every action before time t. The finite ordered set "
                + "readTimes x enumerates all actual read times; reads x is its cardinality. "
                + "Event is the dependent pair (x,i), with i in Fin(reads x). Its full "
                + "eventWord ends at that read and includes all previous waits and answers. "
                + "History is the finite image of these words; word(n) means its full list n.val. Drawing an existing "
                + "path again introduces no node. Sharing a row or a wait length does not "
                + "identify two different full words. In a physical-phase expression, every "
                + "natural shift is cast into ZMod(3P); the shift itself remains a literal natural number.")),
            Result("trace_reconstruction", "trace-reconstruction", "Exact prefix replay",
                Scope(All("x", Label, All("t", N,
                    EqF(Call("run", V("C"), V("hP"), Pair(V("x"), Call("initial", V("C"))), V("t")),
                        Pair(Seq(V("x"), Plus, Call("shift", Trace("x", V("t")))),
                            Call("replay", V("C"), Call("initial", V("C")), Trace("x", V("t")))))))),
                "Replay is the left fold of the controller transition over the complete action "
                + "and answer word. The list fold concatenation law separates the earlier "
                + "prefix from its next action, so induction on time reconstructs the control. "
                + "The physical phase is x plus the number of literal wait actions; reads "
                + "and absorbing halts contribute no physical increment."),
            Result("event_surjective", "event-surjective", "Every history has an indexed occurrence",
                InitializedScope(Call("Surjective", Call("event", V("C"), V("hP"), V("I")))),
                "History is the finite image of full indexed read prefixes. Every history therefore "
                + "has an original input and read index producing it."),
            Result("event_input_injective", "event-input-injective", "One history per read index of an input",
                InitializedScope(All("x", Label, Call("Injective",
                    Seq(Open, V("i"), Colon, Call("Fin", Call("reads", V("C"), V("hP"), V("I"), V("x"))),
                        Mapsto, Event("x", V("i")), Close)))),
                "For a fixed original input, equal full prefixes have equal lengths and read times. "
                + "The increasing enumeration of read times then gives the same read index."),
            Result("event_reconstruction", "event-reconstruction", "An indexed prefix reconstructs its read",
                InitializedScope(All("v", Call("Event", V("C"), V("hP"), V("I")), And(
                    EqF(EventRun, Pair(Seq(EventInput, Plus, Call("shift", EventBefore)),
                        Call("replay", V("C"), Call("initial", V("C")), EventBefore))),
                    EqF(EventWord, Call("append", EventBefore,
                        Call("singleton", Call("read", Call("digit", V("hP"), Call("fst", EventRun)))))))), needsNonzero: false),
                "Removing the last action leaves the exact pre-read trace. Replay reconstructs "
                + "its configuration, and the final recorded answer is the actual absolute digit there."),
            Result("history_configuration", "history-configuration", "Configuration of a supporting label",
                InitializedScope(All("n", Hist, All("x", Label,
                    Imp(Member(V("x"), Call("support", V("C"), V("hP"), V("I"), V("n"))),
                        EqF(Call("run", V("C"), V("hP"), Pair(V("x"), Call("initial", V("C"))),
                                At("time", "n")),
                            Pair(Seq(V("x"), Plus, At("historyShift", "n")), At("readControl", "n"))))))),
                "Support consists exactly of original labels whose indexed read produces "
                + "this full prefix. Time is word length minus one, level is the number of "
                + "recorded reads minus one, and historyShift counts every literal wait."),
            Result("parent_successor", "parent-successor", "Unique prefix parent",
                InitializedScope(All("x", Label, All("i", N,
                    Imp(LT(Seq(V("i"), Plus, D(1)), Call("reads", V("C"), V("hP"), V("I"), V("x"))),
                        EqF(Call("parent", V("C"), V("hP"), V("I"),
                                Event("x", Seq(V("i"), Plus, D(1)))),
                            Call("some", Event("x", V("i")))))))),
                "The parent truncates the full word to the greatest earlier read position. "
                + "It is defined from the word itself, so every nonroot history has one "
                + "parent regardless of row sharing or repeated control states."),
            Result("roots_exact", "roots-exact", "Exactly the first-answer roots",
                InitializedScope(All("n", Hist,
                    Seq(EqF(Call("parent", V("C"), V("hP"), V("I"), V("n")), Call("none")), Iff,
                        Exists, Sp, V("c"), Colon, Call("Fin", D(3)), Comma,
                        EqF(V("n"), Call("root", V("C"), V("hP"), V("I"), V("c")))))),
                "The three roots are ell literal waits followed by one read with answer c. "
                + "Every answer occurs because all original input phases are initialized."),
            Result("history_time_decomposition", "history-time-decomposition", "Literal time accounting",
                InitializedScope(All("n", Hist, EqF(At("time", "n"),
                    Seq(At("historyShift", "n"), Plus, At("level", "n"))))),
                "Before the current read, each live action is either one wait or an earlier "
                + "read. Thus time equals physical shift plus read level, without reducing "
                + "the shift modulo P or modulo 3P."),
            Result("leaf_iff_terminal", "leaf-iff-terminal", "Actual graph leaves",
                InitializedScope(All("n", Hist,
                    Seq(Call("IsLeaf", V("C"), V("hP"), V("I"), V("n")), Iff,
                        Exists, Sp, V("x"), Colon, Label, Comma,
                        EqF(Call("instruction", V("C"), Call("replay", V("C"), Call("initial", V("C")),
                            Call("word", V("n")))), Call("halt", V("x")))))),
                "IsLeaf means that no actual history has this prefix as parent. It is "
                + "equivalent to halt immediately after the recorded read. A nonfinal "
                + "read has a later actual child even when its support is a singleton."),
            Result("leaf_original", "leaf-original", "Every leaf emits its original supporting label",
                InitializedScope(AllH(["n"], All("x", Label, Imp(
                    And(At("IsLeaf", "n"), Member(V("x"), At("support", "n"))),
                    EqF(Call("instruction", V("C"),
                            Call("replay", V("C"), Call("initial", V("C")), Call("word", V("n")))),
                        Call("halt", V("x"))))))),
                "A supporting occurrence of a graph leaf is that input's final read. Its "
                + "post-read instruction halts with the same original label."))));

    private static Formula EventInput => Call("fst", V("v"));
    private static Formula EventIndex => Call("snd", V("v"));
    private static Formula EventWord => Call("eventWord", V("C"), V("hP"), V("I"), V("v"));
    private static Formula EventBefore => Call("dropLast", EventWord);
    private static Formula EventRun => Call("run", V("C"), V("hP"),
        Pair(EventInput, Call("initial", V("C"))),
        Call("readTime", V("C"), V("hP"), V("I"), EventInput, EventIndex));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Label => Call("ZMod", Seq(D(3), Times, Sp, V("P")));
    private static Formula Hist => Call("History", V("C"), V("hP"), V("I"));
    private static Formula Trace(string x, Formula t) => Call("trace", V("C"), V("hP"), V(x), t);
    private static Formula At(string name, string n) => Call(name, V("C"), V("hP"), V("I"), V(n));
    private static Formula Event(string x, Formula i) => Call("event", V("C"), V("hP"), V("I"), Pair(V(x), i));
    private static Formula EqF(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula LT(Formula x, Formula y) => Seq(x, Lt, y);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Member(Formula x, Formula s) => Seq(x, InMacro, Sp, s);
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
        Formula statement, string explanation) => ResultAt("StationaryHistoryPrefix", declaration, id, title, statement, explanation);
}
