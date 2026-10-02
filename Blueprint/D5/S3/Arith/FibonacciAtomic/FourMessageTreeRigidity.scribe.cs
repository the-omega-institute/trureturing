using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourMessageTreeRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-message cut capacities force an arbitrary labelled binary tree to have two peeling spines.",
        H("Four-Message Tree Rigidity"),
        Blocks(
            Paragraph(Text("Let n=k+1 with k>=2. Coordinates are numbered from zero through k. "
                + "Every coordinate alphabet is the complete five-window alphabet, including the zero "
                + "window. F is the Boolean End output after running all n windows from the state with "
                + "both flags false. All words and all complementary assignments are included; no seam "
                + "or terminal validity promise is imposed.")),
            Paragraph(Text("T is a finite full binary tree with leaves bijectively labelled by all "
                + "coordinates. A(S) is the coordinate block of a subtree S and may be any subset. "
                + "A small proper block is a nonempty global prefix, a nonempty global suffix, or an "
                + "interior singleton. A prefix spine successively peels the largest remaining "
                + "coordinate; a suffix spine successively peels the smallest. Both predicates allow "
                + "an independent exchange of the two children at each fork. DoubleComb means that "
                + "the root joins complementary prefix and suffix spines, in either child order.")),
            Describe.Lean(DescribeId.Create("four-message-cut-rigidity"),
                DeclarationHandle.Create(Prefix + "rigidity_from_capacities"), H("Arbitrary Leaf Labels"),
                StatementSource.FromAuthor(Seq(
                    V("k"), Sp, Ge, Sp, D(2), Sp, Land, Sp, Call("Full", V("T")), Sp, Land, Sp,
                    Call("A", V("T")), Sp, Eq, Sp, Call("coordinates", V("k")), Sp, Land, Sp,
                    Grp(Seq(Forall, Sp, V("S"), Sp, InMacro, Sp, Call("subtrees", V("T")), Comma, Sp,
                        V("S"), Sp, Neq, Sp, V("T"), Sp, Implies, Sp,
                        Call("capacity", V("F"), Call("A", V("S"))), Sp, Le, Sp, D(4))),
                    Sp, Implies, Sp, Call("DoubleComb", V("T")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The exact Boolean capacity is 2^d+epsilon. If epsilon is one, "
                        + "capacity at most four allows at most one crossing seam. Nonempty proper "
                        + "blocks with one crossing are prefixes or suffixes. If epsilon is zero, "
                        + "the block owns neither a terminal coordinate nor an internal seam. Two "
                        + "distinct owned coordinates would then produce three distinct crossing "
                        + "seams, exceeding the capacity bound. The remaining blocks are singletons.")),
                    Paragraph(Text("No small proper block contains both endpoint coordinates. The "
                        + "root therefore separates the two endpoints, and the two root blocks are "
                        + "complementary prefix and suffix intervals. Within a proper prefix, one "
                        + "child contains zero and is again a prefix. The other child contains neither "
                        + "endpoint, hence is a singleton. Disjointness and union force this singleton "
                        + "to be the rightmost remaining coordinate. The suffix argument reverses "
                        + "the endpoint roles. Structural induction determines both spines."))),
                DescribeRole.Theorem))));
}
