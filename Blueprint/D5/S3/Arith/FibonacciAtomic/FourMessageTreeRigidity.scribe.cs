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
                + "the root joins complementary prefix and suffix spines, in either child order. "
                + "DoubleCombAt(j,T) fixes the split after coordinate j-1. An implementation m has "
                + "arbitrary complete messages, leaf encoders and atomic child mergers; g reads the "
                + "root message. Correct means g returns F on every input, and Peak includes every "
                + "node including the root. Height counts parent-child edges, with leaf height zero.")),
            Describe.Lean(DescribeId.Create("four-message-implementation-rigidity"),
                DeclarationHandle.Create(Prefix + "rigidity_from_implementation"), H("Arbitrary Leaf Labels"),
                StatementSource.FromAuthor(Seq(
                    V("k"), Sp, Ge, Sp, D(2), Sp, Land, Sp, Call("Full", V("T")), Sp, Land, Sp,
                    Call("A", V("T")), Sp, Eq, Sp, Call("coordinates", V("k")), Sp, Land, Sp,
                    Call("Correct", V("F"), V("T"), V("m"), V("g")), Sp, Land, Sp,
                    Call("Peak", V("m"), V("T")), Sp, Le, Sp, D(4), Sp, Implies, Sp,
                    Exists, Sp, V("j"), Comma, Sp, D(0), Sp, Lt, Sp, V("j"), Sp, Lt, Sp,
                    Call("n", V("k")), Sp, Land, Sp, Call("DoubleCombAt", V("j"), V("T")),
                    Sp, Land, Sp, Call("height", V("T")), Sp, Eq, Sp,
                    Call("max", V("j"), Seq(Call("n", V("k")), Minus, V("j"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every accurate implementation has at least the cut capacity many reachable "
                        + "messages at each subtree. Peak at most four therefore bounds all these capacities. "
                        + "The exact Boolean capacity is 2^d+epsilon. If epsilon is one, "
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
                        + "the endpoint roles. Structural induction determines both spines. A j-coordinate prefix spine has "
                        + "height j-1, and its complementary suffix spine has height n-j-1. Their "
                        + "root merge has height max(j,n-j)."))),
                DescribeRole.Theorem))));
}
