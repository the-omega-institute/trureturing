using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class IntervalDiagnosticMergeDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula N => Seq(V("k"), Plus, D(1));
    private static Formula Eval(Formula s) => Call("evaluate", Call("implementation", V("k")), s, V("w"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent interval messages compute the earliest failed seam while retaining the incoming bit.",
        H("Interval Diagnostic Merging"),
        Blocks(
            Paragraph(Text("A word has k+1 literal windows, indexed from zero through k. A nonterminal "
                + "seam is bad when the left window's last bit and the right window's first bit are both one. "
                + "The task returns the smallest bad seam, or the final coordinate when the last window is "
                + "zero, or acceptance when neither failure occurs. Intervals are half-open: [a,b) contains "
                + "coordinates a through b-1. Ordered trees join adjacent nonempty blocks at every fork "
                + "and allow every binary parenthesization.")),
            Paragraph(Text("A failed message stores the first bad internal seam and its interval's incoming "
                + "bit. It has no outgoing field. A live message stores the incoming bit and the last "
                + "window's outgoing bit, except that a block ending at k+1 stores the terminal-zero flag. "
                + "The incoming bit is the first window's first bit, fixed to zero at coordinate zero. "
                + "A leaf is always live; terminal zero is tested only by the root readout.")),
            Paragraph(Text("The merger has four rules, in order. A failed left child keeps its message. "
                + "Otherwise, an outgoing one meeting an incoming one fails at the joining seam, retaining "
                + "the left incoming bit. Otherwise, a failed right child passes its position with the "
                + "left incoming bit. Otherwise, the merged live message keeps the left incoming bit "
                + "and the right outgoing or terminal flag. The seam coordinate is the greatest leaf "
                + "coordinate of the left child; no word is read by the merger.")),
            Describe.Lean(DescribeId.Create("interval-diagnostic-merge"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/IntervalDiagnosticMerge.result"),
                H("Every Ordered Tree Computes the Prescribed Messages"),
                StatementSource.FromAuthor(Seq(
                    Forall, Sp, V("k"), Comma, V("t"), Comma, V("w"), Comma, Sp,
                    Call("Ordered", V("k"), D(0), N, V("t")), Sp, Implies, Sp,
                    Call("Full", V("t")), Sp, Land, Sp,
                    Call("leaves", V("t")), Sp, Eq, Sp, Call("univ", Call("Fin", N)),
                    Sp, Land, Sp, Par(Seq(
                        Forall, Sp, V("s"), Sp, InMacro, Sp, Call("subtrees", V("t")), Comma, Sp,
                        Exists, Sp, V("a"), Comma, V("b"), Comma, Sp,
                        V("a"), Sp, Lt, Sp, V("b"), Sp, Land, Sp, V("b"), Sp, Le, Sp, N,
                        Sp, Land, Sp, Call("leaves", V("s")), Sp, Eq, Sp,
                        Call("interval", V("k"), V("a"), V("b")),
                        Sp, Land, Sp, Par(Seq(Forall, Sp, V("m"), Comma, Sp,
                            Call("Semantics", V("a"), V("b"), V("w"), V("m")), Sp, Iff, Sp,
                            V("m"), Sp, Eq, Sp, Eval(V("s")))))),
                    Sp, Land, Sp, Call("read", Eval(V("t"))), Sp, Eq, Sp, Call("task", V("w")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Semantics describes a message independently of evaluation. In a failed "
                        + "message, its position lies inside the interval, is a bad internal seam, and every "
                        + "earlier internal seam is good. Its incoming field equals the left boundary bit. "
                        + "In a live message, every internal seam is good and both fields equal their "
                        + "prescribed boundary bits. The equivalence characterizes the evaluated message "
                        + "uniquely at every subtree.")),
                    Paragraph(Text("For adjacent blocks [a,b) and [b,c), an internal bad seam belongs to the "
                        + "left block, is b-1, or belongs to the right block. Every left internal seam "
                        + "precedes the joining seam, which precedes every right internal seam. These "
                        + "three ordered possibilities prove the four merger rules and propagate the "
                        + "incoming bit even after failure. Induction over the tree proves the same "
                        + "message meaning at every descendant. At the root the only remaining test is "
                        + "the terminal-zero flag, giving exactly the first rejection task.")),
                    Paragraph(Text("Combining interval summaries is the classical segment-tree pattern; "
                        + "associative reductions and prefix scans are treated by Guy E. Blelloch in "
                        + "Prefix Sums and Their Applications. The concrete summary here retains an "
                        + "incoming bit after internal failure because a later merge with an earlier "
                        + "block can expose an earlier joining failure."))), DescribeRole.Theorem))));
}
