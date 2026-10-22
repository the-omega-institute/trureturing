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
            Result("triple_frontier_shift", "Exact Three-Shift Leaf Frontier", TripleShiftFrontier(), "For every positive a, the three sources t, rho iterated a times on t, and rho iterated twice a times on t have exactly the original leaf set of t as their joint first-disagreement frontier. The first two coordinates already disagree at every original leaf, and all three retain the original branches."),
            Item("U", "Whole Shift-Copy Sources", "For a supplied natural a, write S for rho iterated a times. U(a,x,y) is the ordered branch (x,(y,S(y))). Both occurrences use the same whole finite native value y.", DescribeRole.Definition),
            Item("Retained", "The Complete Retained Input", "The old cut consists of the root with its complete one-hole row. The final epoch is a. The four literals say branch at the root and R, at epochs zero and a. The positive relation equates epoch-a RL with epoch-zero RR, retaining both endpoint guards. The two negative relations compare epoch-zero RL with RR and the epoch-zero root with L, retaining both guards of each sign. There are no further observations or image or rank conditions. The paid-source and complete-state premise belongs to the supplied acquisition interpretation; these statements concern all original finite sources satisfying its retained native record.", DescribeRole.Definition),
            Result("retained_iff", "The Entire Reconstructed Fiber", RetainedFormula(), "For every a at least one, a finite native source satisfies the entire retained input exactly when it equals U(a,x,y) for some independent finite x and y. The zero-epoch literals expose both branches. The existing exact payload-history correspondence identifies the last hole with S(y). Positive shifts change right-spine rank, and positive leaf counts establish the two original negative comparisons. Every literal and every endpoint guard is retained in the converse."),
            Item("position", "Target Coordinates", "The three indices zero, one and two name the original addresses L, RL and RR, in that order.", DescribeRole.Definition),
            Item("Q", "The Entire Target Cut", "The cut contains exactly L, RL and RR. It is prefix free and every one of its addresses is reached by every shift-copy source.", DescribeRole.Definition),
            Item("exterior", "The Entire Target Exterior", "The literal exterior is the ordered branch (hole L,(hole RL,hole RR)). It retains the whole outer source skeleton.", DescribeRole.Definition),
            Item("labelClass", "The Three Equality Partitions", "Label zero identifies L with RL; label one identifies L with RR; label two makes all three holes distinct. The remaining hole in the first two labels is a singleton class.", DescribeRole.Definition),
            Item("label", "Complete Target Records", "Each label combines the entire exterior with all ordered pairs of equal-class holes, including the reflexive and reversed pairs. Thus absence of a reached pair records the corresponding whole-value disequality.", DescribeRole.Definition),
            Item("rowCondition", "Parameters for Each Label", "For label zero, x equals y. For label one, x equals S(y). For label two, x differs from both y and S(y). Every finite y differs from S(y) for positive a.", DescribeRole.Definition),
            Item("Stratum", "Entire Canonical Row Strata", "A stratum contains exactly the retained originals whose actual canonical target row agrees with a source having the selected complete literal record. The existing canonical-row equivalence identifies this with equality of the entire exterior and partition; no source payload is inserted into the row label.", DescribeRole.Definition),
            Result("label_iff", "Exact Complete-Label Conditions", LabelFormula(), "For every positive a, each label of U(a,x,y) is equivalent to its displayed row condition. The exterior has all three holes, and the finite partition tests every pair of complete subtree values. Positive-shift separation prevents the last two holes from agreeing."),
            Result("stratum_iff", "Every Original in Each Entire Stratum", StratumFormula(), "For every positive a and each of the three labels, membership is equivalent to being U(a,x,y) with precisely that label's parameter condition. Both directions use the full retained fiber and the existing equivalence between canonical rows and complete literal records. Parameters of different alternative originals remain independent."))));

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

    private static Formula IffOf(Formula x, Formula y) => Seq(Open, x, Close, Sp, Iff, Sp, Open, y, Close);
    private static Formula AndOf(Formula x, Formula y) => Seq(Open, x, Close, Sp, Land, Sp, Open, y, Close);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula U(Formula x, Formula y) => Call("U", V("a"), x, y);
    private static Formula RetainedFormula() => PositiveA(All("u", Source, IffOf(Call("Retained", V("a"), V("u")), Some("x", Source, Some("y", Source, Eq(V("u"), U(V("x"), V("y"))))))));
    private static Formula Labels(Formula body) => PositiveA(All("i", Call("Fin", D(3)), All("x", Source, All("y", Source, body))));
    private static Formula LabelFormula() => Labels(IffOf(Eq(Call("literalRecord", Call("Q"), U(V("x"), V("y"))), Call("label", V("i"))), Call("rowCondition", V("a"), V("i"), V("x"), V("y"))));
    private static Formula StratumFormula() => PositiveA(All("i", Call("Fin", D(3)), All("u", Source, IffOf(Call("Stratum", V("a"), V("i"), V("u")), Some("x", Source, Some("y", Source, AndOf(Eq(V("u"), U(V("x"), V("y"))), Call("rowCondition", V("a"), V("i"), V("x"), V("y")))))))));

}
