using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeBiasedFrontierInfimaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeBiasedFrontierInfima.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directional cylinder weights give a bounded native frontier distance satisfying the triangle inequality.",
        H("Biased Native Frontier Distance"), Blocks(
            Item("weight", "Directional Cylinder Weight", "The empty address has weight one. Prefixing a left edge multiplies by theta; prefixing a right edge multiplies by one minus theta. Thus each address has weight theta to its left-edge count times one minus theta to its right-edge count.", DescribeRole.Definition),
            Item("distance", "Pair Frontier Mass", "For any real theta and two finite native sources, distance is the sum of directional weights over their existing first-disagreement frontier. Left is false and right is true. Equal sources contribute zero, distinct root replies contribute one, and common branches split into the two weighted child distances.", DescribeRole.Definition),
            Result("biased_frontier_triangle", "Triangle Inequality", Triangle(), "For every real theta in the closed unit interval and all finite native sources s,z,t, the distance from s to t is at most the sum of the distances through z. Structural induction on the first source, with the other two arbitrary, handles the three common-branch case by the child inequalities and nonnegative weights. Mixed roots use the bound by one and nonnegativity."),
            Result("biased_frontier_bounds", "Probability Bounds", Bounds(), "For every real theta in the closed unit interval and every source pair, the frontier distance lies between zero and one. All directional cylinder weights are nonnegative. Structural induction uses theta plus one minus theta equals one at a common branch."),
            Result("frontier_shift", "Exact Positive-Shift Frontier", ShiftFrontier(), "For every natural a at least one and every source t, the frontier between t and rho iterated a times on t is exactly the set of original leaves of t. The right-spine rank increases by a, excluding equality at each original leaf. Iterated substitution preserves every original branch, so structural induction identifies the entire frontier."),
            Result("leaf_partition", "Weighted Leaf Partition", LeafPartition(), "For every real theta and arbitrary finite full binary source t, the sum of directional weights of its leaves equals one. This algebraic identity includes uneven trees and follows by structural induction and the two directional weight factors."),
            Result("distance_shift", "Unit Distance to Every Positive Shift", ShiftDistance(), "For every real theta, every natural a at least one, and every finite source t, the biased distance from t to its a-fold native substitution is one. The exact leaf frontier and its weighted partition give the identity."),
            Item("tripleFrontier", "Three-Source Frontier", "Three common branches recurse on their respective left and right children. Three equal labelled leaves contribute nothing. Every other root combination contributes the empty address. This is the first disagreement of the three original reply traces.", DescribeRole.Definition),
            Item("tripleMass", "Three-Source Normalized Mass", "The three-source mass is the sum of the same directional weights over the three-source first-disagreement frontier.", DescribeRole.Definition),
            Result("triple_frontier_shift", "Exact Three-Shift Leaf Frontier", TripleShiftFrontier(), "For every positive a, the three sources t, rho iterated a times on t, and rho iterated twice a times on t have exactly the original leaf set of t as their joint first-disagreement frontier. The first two coordinates already disagree at every original leaf, and all three retain the original branches."))));

    private static DocumentBlock Item(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativebiasedfrontierinfima-" + name.Replace("_", "").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static DocumentBlock Result(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("nativebiasedfrontierinfima-" + name.Replace("_", "").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula type, Formula body) => Seq(Forall, Sp, V(s), Colon, Sp, type, Comma, Sp, body);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Source => Call("Source");
    private static Formula Dist(string s, string t) => Call("distance", V("theta"), V(s), V(t));
    private static Formula Le(Formula s, Formula t) => Seq(s, Sp, Leq, Sp, t);
    private static Formula Imp(Formula s, Formula t) => Seq(Open, s, Close, Sp, Rightarrow, Sp, t);
    private static Formula Parameters(Formula body) => All("theta", Real, Imp(Le(D(0), V("theta")), Imp(Le(V("theta"), D(1)), body)));
    private static Formula Triangle() => Parameters(All("s", Source, All("z", Source, All("t", Source, Le(Dist("s", "t"), Seq(Dist("s", "z"), Sp, Plus, Sp, Dist("z", "t")))))));
    private static Formula Bounds() => Parameters(All("s", Source, All("t", Source, Seq(Le(D(0), Dist("s", "t")), Sp, Land, Sp, Le(Dist("s", "t"), D(1))))));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Eq(Formula x, Formula y) => Seq(x, Sp, F.Eq, Sp, y);
    private static Formula Shift(Formula t) => Call("iterate", Call("rho"), V("a"), t);
    private static Formula PositiveA(Formula body) => All("a", Nat, Imp(Le(D(1), V("a")), body));
    private static Formula ShiftFrontier() => PositiveA(All("t", Source, Eq(Call("frontier", V("t"), Shift(V("t"))), Call("leafAddresses", V("t")))));
    private static Formula LeafPartition() => All("theta", Real, All("t", Source, Eq(Call("sum", Call("leafAddresses", V("t")), Call("weight", V("theta"))), D(1))));
    private static Formula ShiftDistance() => All("theta", Real, PositiveA(All("t", Source, Eq(Call("distance", V("theta"), V("t"), Shift(V("t"))), D(1)))));
    private static Formula TripleShiftFrontier() => PositiveA(All("t", Source, Eq(Call("tripleFrontier", V("t"), Shift(V("t")), Shift(Shift(V("t")))), Call("leafAddresses", V("t")))));

}
