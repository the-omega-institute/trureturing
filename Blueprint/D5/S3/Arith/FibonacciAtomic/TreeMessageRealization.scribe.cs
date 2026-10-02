using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class TreeMessageRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/TreeMessageRealization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/kowshik2011functioncomputation");
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete messages on a labelled binary tree have sharp completion-response capacities.",
        H("Complete Messages on Binary Trees"),
        Blocks(
            Paragraph(Text("I is a finite coordinate set. Each X(i) is finite and nonempty; the task F "
                + "maps the full dependent Cartesian product of these alphabets to an arbitrary output type. "
                + "T is any finite full binary tree with distinct coordinate-labelled leaves. Every terminal "
                + "reads only its coordinate. Every fork applies a fixed function to its two complete child "
                + "messages. A fixed root decoder returns the output. Child order is arbitrary. There are "
                + "no auxiliary input channels. Message types may differ at every node.")),
            Paragraph(Text("For a subtree S, A(S) is its leaf-label set. Its capacity is the number of "
                + "distinct functions from all complementary assignments to task outputs obtained by varying "
                + "the assignment on A(S). Reachable(m,S) counts the actual image of S's evaluated message "
                + "over all raw global inputs. Peak(m,T) is the maximum of these counts, including the root. "
                + "Optimum(F,T) is the infimum of peaks of accurate implementations. A one-leaf task tree "
                + "has height zero, and each actual fork adds one edge to the longest dependency chain.")),
            Describe.Lean(DescribeId.Create("tree-message-lower-bound"),
                DeclarationHandle.Create(Prefix + "implementation_lower_bound"), H("Every Accurate Implementation"),
                StatementSource.FromAuthor(Seq(
                    Call("Full", V("T")), Sp, Land, Sp,
                    Call("Correct", V("F"), V("T"), V("m"), V("g")), Sp, Implies, Sp,
                    Forall, Sp, V("S"), Sp, InMacro, Sp, Call("subtrees", V("T")), Comma, Sp,
                    Call("capacity", V("F"), Call("A", V("S"))), Sp, Le, Sp,
                    Call("reachable", V("m"), V("S")))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A subtree message depends only on that subtree's coordinates. "
                    + "If two such messages agree, substituting them into the same complementary input "
                    + "preserves each ancestor message and hence the root output. Accurate computation "
                    + "therefore requires different messages for different completion responses. "
                    + "Choosing one representative of each response gives an injection into the "
                    + "reachable message image."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tree-message-simultaneous-realization"),
                DeclarationHandle.Create(Prefix + "simultaneous_realization"), H("Simultaneously Sharp Response Messages"),
                StatementSource.FromAuthor(Seq(
                    Call("Full", V("T")), Sp, Land, Sp, Call("A", V("T")), Sp, Eq, Sp, V("I"),
                    Sp, Implies, Sp, Exists, Sp, V("m"), Comma, V("g"), Comma, Sp,
                    Call("Correct", V("F"), V("T"), V("m"), V("g")), Sp, Land, Sp,
                    Forall, Sp, V("S"), Sp, InMacro, Sp, Call("subtrees", V("T")), Comma, Sp,
                    Call("reachable", V("m"), V("S")), Sp, Eq, Sp,
                    Call("capacity", V("F"), Call("A", V("S"))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Use each node's actual completion-response range as its message "
                    + "type. Fix a nominal representative for each message. At a fork, merge the two "
                    + "nominal representatives on their disjoint coordinate blocks, then send the "
                    + "parent's completion response. Replacing the two blocks successively preserves "
                    + "every external response. Induction proves that each evaluated message is the "
                    + "actual response of the input. Every response is reachable from its representative. "
                    + "At the root the complement is empty and the response evaluates to F."))), DescribeRole.Theorem))));
}
