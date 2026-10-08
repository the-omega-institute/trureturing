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
                StationaryReadHistoryDocument.Scope(StationaryReadHistoryDocument.All("x", StationaryReadHistoryDocument.Label, StationaryReadHistoryDocument.All("t", StationaryReadHistoryDocument.N,
                    StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("run", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.Pair(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.Call("initial", StationaryReadHistoryDocument.V("C"))), StationaryReadHistoryDocument.V("t")),
                        StationaryReadHistoryDocument.Pair(Seq(StationaryReadHistoryDocument.V("x"), Plus, StationaryReadHistoryDocument.Call("shift", StationaryReadHistoryDocument.Trace("x", StationaryReadHistoryDocument.V("t")))),
                            StationaryReadHistoryDocument.Call("replay", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.Call("initial", StationaryReadHistoryDocument.V("C")), StationaryReadHistoryDocument.Trace("x", StationaryReadHistoryDocument.V("t")))))))),
                "Replaying the complete action and answer word reconstructs the control. "
                + "The physical phase is x plus the number of literal wait actions; reads "
                + "and absorbing halts contribute no physical increment."),
            Result("history_configuration", "history-configuration", "Configuration of a supporting label",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("n", StationaryReadHistoryDocument.Hist, StationaryReadHistoryDocument.All("x", StationaryReadHistoryDocument.Label,
                    StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.Member(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.Call("support", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("n"))),
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("run", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.Pair(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.Call("initial", StationaryReadHistoryDocument.V("C"))),
                                StationaryReadHistoryDocument.At("time", "n")),
                            StationaryReadHistoryDocument.Pair(Seq(StationaryReadHistoryDocument.V("x"), Plus, StationaryReadHistoryDocument.At("historyShift", "n")), StationaryReadHistoryDocument.At("readControl", "n"))))))),
                "Support consists exactly of original labels whose indexed read produces "
                + "this full prefix. Time is word length minus one, level is the number of "
                + "recorded reads minus one, and historyShift counts every literal wait."),
            Result("parent_successor", "parent-successor", "Unique prefix parent",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("x", StationaryReadHistoryDocument.Label, StationaryReadHistoryDocument.All("i", StationaryReadHistoryDocument.N,
                    StationaryReadHistoryDocument.All("hi", StationaryReadHistoryDocument.LT(Seq(StationaryReadHistoryDocument.V("i"), Plus, D(1)), StationaryReadHistoryDocument.Call("reads", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("x"))),
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("parent", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"),
                                StationaryReadHistoryDocument.Event("x", Seq(StationaryReadHistoryDocument.V("i"), Plus, D(1)))),
                            StationaryReadHistoryDocument.Call("some", StationaryReadHistoryDocument.Event("x", StationaryReadHistoryDocument.V("i")))))))),
                "The parent truncates the full word to the greatest earlier read position. "
                + "It is defined from the word itself, so every nonroot history has one "
                + "parent regardless of row sharing or repeated control states."),
            Result("roots_exact", "roots-exact", "Exactly the first-answer roots",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("n", StationaryReadHistoryDocument.Hist,
                    Seq(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("parent", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("n")), StationaryReadHistoryDocument.Call("none")), Iff,
                        Exists, Sp, StationaryReadHistoryDocument.V("c"), Colon, StationaryReadHistoryDocument.Call("Fin", D(3)), Comma,
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.V("n"), StationaryReadHistoryDocument.Call("root", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("c")))))),
                "The three roots are ell literal waits followed by one read with answer c. "
                + "Every answer occurs because all original input phases are initialized."),
            Result("history_time_decomposition", "history-time-decomposition", "Literal time accounting",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("n", StationaryReadHistoryDocument.Hist, StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("time", "n"),
                    Seq(StationaryReadHistoryDocument.At("historyShift", "n"), Plus, StationaryReadHistoryDocument.At("level", "n"))))),
                "Before the current read, each live action is either one wait or an earlier "
                + "read. Thus time equals physical shift plus read level, without reducing "
                + "the shift modulo P or modulo 3P."),
            Result("leaf_iff_terminal", "leaf-iff-terminal", "Actual graph leaves",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("n", StationaryReadHistoryDocument.Hist,
                    Seq(StationaryReadHistoryDocument.Call("IsLeaf", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("n")), Iff,
                        Exists, Sp, StationaryReadHistoryDocument.V("x"), Colon, StationaryReadHistoryDocument.Label, Comma,
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("instruction", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.Call("replay", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.Call("initial", StationaryReadHistoryDocument.V("C")),
                            StationaryReadHistoryDocument.Call("word", StationaryReadHistoryDocument.V("n")))), StationaryReadHistoryDocument.Call("halt", StationaryReadHistoryDocument.V("x")))))),
                "IsLeaf means that no actual history has this prefix as parent. It is "
                + "equivalent to halt immediately after the recorded read. A nonfinal "
                + "read has a later actual child even when its support is a singleton."))));

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryReadHistoryDocument.ResultAt("StationaryHistoryPrefix", declaration, id, title, statement, explanation);
}
