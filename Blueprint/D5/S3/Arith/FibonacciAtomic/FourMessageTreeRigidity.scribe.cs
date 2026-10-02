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
                    Call("max", V("j"), Seq(Call("n", V("k")), Minus, V("j"))), Sp, Land, Sp,
                    Call("ceilHalf", Call("n", V("k"))), Sp, Le, Sp, Call("height", V("T")))),
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
                        + "root merge has height max(j,n-j), which is at least the ceiling of n/2."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("four-message-tree-classification-and-optimum"),
                DeclarationHandle.Create(Prefix + "result"), H("Sharp Peak and Minimum Height"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every nonempty proper coordinate block, capacity is at most four "
                        + "exactly when the block is a global prefix, a global suffix, or an interior "
                        + "singleton. Each interior singleton has capacity exactly four. Endpoint "
                        + "intervals have one crossing seam; an interior singleton has two crossing "
                        + "seams and has neither an internal seam nor the terminal coordinate.")),
                    Paragraph(Text("Every fully labelled tree contains an interior coordinate as a leaf, "
                        + "so every accurate implementation has peak at least four. Conversely each "
                        + "double comb is full, uses every coordinate once, and has capacity at most "
                        + "four at every subtree. Its proper subtree blocks are endpoint intervals or "
                        + "singletons; its root capacity is two. Simultaneous response-class realization "
                        + "therefore gives an accurate implementation with peak exactly four and "
                        + "Optimum(F,T)=4.")),
                    Paragraph(Text("Every tree with Optimum(F,T)<=4 has height at least ceil(n/2). "
                        + "Choose the root split j=floor(n/2), build a prefix spine on the first j "
                        + "coordinates and a suffix spine on the remaining n-j coordinates, and join "
                        + "them at the root. The resulting full tree has optimum four and height "
                        + "max(j,n-j)=ceil(n/2). Thus the minimum peak over all accurate tree "
                        + "implementations is four, and the minimum height among trees with "
                        + "optimum at most four is the ceiling of n/2."))),
                DescribeRole.Theorem))));
    private static Formula ResultFormula()
    {
        var k = V("k"); var n = V("n"); var a = V("A"); var t = V("T");
        var i = V("i"); var j = V("j"); var m = V("m"); var g = V("g");
        var peak = Call("Peak", m, t); var opt = Call("Optimum", V("F"), t);
        var height = Call("height", t); var half = Call("ceilHalf", n);
        var taskTree = Seq(Call("Full", t), Sp, Land, Sp,
            Call("A", t), Sp, Eq, Sp, Call("coordinates", k));
        var correct = Call("Correct", V("F"), t, m, g);
        var shape = Seq(Exists, Sp, j, Comma, Sp, D(0), Sp, Lt, Sp, j, Sp, Lt, Sp, n,
            Sp, Land, Sp, Call("DoubleCombAt", j, t), Sp, Land, Sp,
            height, Sp, Eq, Sp, Call("max", j, Seq(n, Minus, j)), Sp, Land, Sp,
            half, Sp, Le, Sp, height);
        var classification = Seq(Forall, Sp, a, Comma, Sp,
            Call("nonemptyProper", a), Sp, Implies, Sp,
            Grp(Seq(Call("capacityF", a), Sp, Le, Sp, D(4), Sp, Iff, Sp, Call("SmallBlock", a))));
        var singleton = Seq(Forall, Sp, i, Comma, Sp, D(0), Sp, Lt, Sp, i, Sp, Lt, Sp, k,
            Sp, Implies, Sp, Call("capacityF", Call("singleton", i)), Sp, Eq, Sp, D(4));
        var rigidity = Seq(Forall, Sp, t, Comma, Sp, taskTree, Sp, Implies, Sp,
            Forall, Sp, m, Comma, Sp, Forall, Sp, g, Comma, Sp, correct, Sp, Implies, Sp,
            Grp(Seq(D(4), Sp, Le, Sp, peak, Sp, Land, Sp,
                Grp(Seq(peak, Sp, Le, Sp, D(4), Sp, Implies, Sp, shape)))));
        var realization = Seq(Forall, Sp, t, Comma, Sp, Call("DoubleComb", t), Sp, Implies, Sp,
            Exists, Sp, m, Comma, Sp, Exists, Sp, g, Comma, Sp, correct, Sp, Land, Sp,
            peak, Sp, Eq, Sp, D(4), Sp, Land, Sp, opt, Sp, Eq, Sp, D(4));
        var lower = Seq(Forall, Sp, t, Comma, Sp, taskTree, Sp, Land, Sp,
            opt, Sp, Le, Sp, D(4), Sp, Implies, Sp, half, Sp, Le, Sp, height);
        var attained = Seq(Exists, Sp, t, Comma, Sp, taskTree, Sp, Land, Sp,
            opt, Sp, Eq, Sp, D(4), Sp, Land, Sp, height, Sp, Eq, Sp, half);
        return Seq(k, Sp, Ge, Sp, D(2), Sp, Implies, Sp, Grp(Seq(
            Grp(classification), Sp, Land, Sp, Grp(singleton), Sp, Land, Sp,
            Grp(rigidity), Sp, Land, Sp, Grp(realization), Sp, Land, Sp,
            Grp(lower), Sp, Land, Sp, Grp(attained))));
    }

}
