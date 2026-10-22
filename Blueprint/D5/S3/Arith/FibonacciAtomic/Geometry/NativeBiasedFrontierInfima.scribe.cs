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
            Result("biased_frontier_bounds", "Probability Bounds", Bounds(), "For every real theta in the closed unit interval and every source pair, the frontier distance lies between zero and one. All directional cylinder weights are nonnegative. Structural induction uses theta plus one minus theta equals one at a common branch."))));

    private static DocumentBlock Item(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativebiasedfrontierinfima-" + name.Replace("_", "")), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static DocumentBlock Result(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("nativebiasedfrontierinfima-" + name.Replace("_", "")), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
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
}
