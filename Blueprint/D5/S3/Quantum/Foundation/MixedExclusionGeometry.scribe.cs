using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class MixedExclusionGeometryDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/MixedExclusionGeometry.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] xs) => xs.Length == 1 ? xs[0] : new Formula.Logic(xs[0], FormulaLogicOperator.And, And(xs[1..]));
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Not(Formula a) => C("not", a);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula K => C("base", Cone, Unit);
    private static Formula P => C("pure", Cone, Unit);
    private static Formula M => C("mixedExcluded", Cone, Unit);
    private static Formula T => C("Icc", D(0), D(1));
    private static Formula S => C("intrinsicFrontier", R, K);
    private static Formula Sigma => C("label", Cone, Unit);
    private static Formula Section => C("centerSection", V("hc"), V("hs"), V("hg"), V("hB"));
    private static Formula Map(string name) => name is "reflection" or "contraction"
        ? C(name,V("hc"),V("hs"),V("hg"),V("hB"))
        : C(name,V("hc"),V("hs"),V("hg"),V("hB"),V("hW"));
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula Val(Formula x) => C("value", x);
    private static Formula Pair(Formula a, Formula b) => C("pair", a, b);
    private static Formula Dp(Formula p) => C("exclusion", Cone, Unit, p);
    private static Formula Center(Formula p) => C("center", V("hB"), p);
    private static Formula Ht(Formula t, Formula x) => App(Map("contraction"),Pair(t,x));
    private static Formula Strict => All("x",Space,Imp(In(V("x"),Cone),
        Imp(Not(Eq(V("x"),D(0))),new Formula.Relation(D(0),FormulaRelationOperator.LessThan,App(Unit,V("x"))))));
    private static Formula Parameters(Formula body) => All("V",V("Type"),Seq(
        OpenBracket,C("NormedAddCommGroup",Space),CloseBracket,Sp,
        OpenBracket,C("NormedSpace",R,Space),CloseBracket,Sp,
        OpenBracket,C("FiniteDimensional",R,Space),CloseBracket,Sp,
        OpenBracket,C("Nontrivial",Space),CloseBracket,Sp,
        All("C",C("PointedCone",R,Space),All("u",C("LinearMap",R,Space,R),
        All("hc",C("IsClosed",Cone),All("hs",Strict,
        All("hg",Eq(C("span",R,Cone),C("top")),All("hB",C("exclusionBalls",Cone,Unit),body))))))));
    private static Formula Context(Formula body) => Parameters(All("hW",C("weakPair",Cone,Unit),body));
    private static Formula HypothesisContext(Formula body) => Parameters(Imp(C("weakPair",Cone,Unit),body));

    public DocumentDefinition Create()
    {
        Formula x=V("x"), p=V("p"), t=V("t");
        Formula section=App(Section,p), tau=Map("reflection");
        Formula theorem=HypothesisContext(And(
            C("subset",P,S),Eq(M,C("difference",S,P)),
            All("x",M,All("p",P,Iff(Eq(App(Sigma,x),p),In(Val(x),C("intrinsicInterior",R,Dp(p)))))),
            C("Continuous",tau),C("Involutive",tau),
            All("x",M,Iff(Eq(App(tau,x),x),In(x,C("range",Section)))),
            C("Continuous",Sigma),C("Continuous",Section),
            All("p",P,Eq(App(Sigma,section),p)),C("Continuous",Map("contraction")),
            All("x",M,And(Eq(Ht(D(0),x),x),Eq(Ht(D(1),x),App(Section,App(Sigma,x))))),
            All("p",P,All("t",T,Eq(Ht(t,section),section))),
            All("p",P,All("t",T,All("x",M,Iff(In(Val(Ht(t,x)),Dp(p)),In(Val(x),Dp(p))))))));
        Formula definitions=Parameters(And(
            All("x",Space,Iff(In(x,M),And(Not(In(x,P)),Ex("p",P,In(x,Dp(p)))))),
            All("p",P,Eq(Val(section),Center(p))),
            All("x",M,Eq(Val(App(tau,x)),C("subtract",C("smul",D(2),Center(App(Sigma,x))),Val(x)))),
            All("t",T,All("x",M,Eq(Val(Ht(t,x)),C("add",
                C("smul",C("subtract",D(1),Val(t)),Val(x)),C("smul",Val(t),Center(App(Sigma,x)))))))));
        Formula pairHomotopy=Context(All("p",P,In(
            App(Map("deletedFiberPairHomotopy"),p),C("TopPairHomotopy",
            C("identity",C("deletedFiberPair",Cone,Unit,p)),
            C("compose",App(Map("pairLabelMap"),p),App(Map("pairCenterMap"),p))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original mixed relative-boundary fibers admit continuous labels, reflection and a strong deformation preserving deleted fibers.",
            H("Mixed exclusion geometry on the original cone base"),Blocks(
                Paragraph(Text("V is any nonzero finite-dimensional real normed space. C is the original closed generating pointed cone, u is its original strictly positive linear unit, K is its entire normalized base, and P consists of all extreme points of K. The effect domain is the entire original interval [0,u]. Every full mixed-state exclusion D_p is an injective affine image of a whole positive-dimensional closed Euclidean unit ball. The only pair hypothesis is weakPair: an original orthogonal pure pair generates a proper minimal face. Dimensions may vary and may equal one. Neither full Pair, a common center, a chosen continuous ball chart, a manifold structure nor a label map is assumed.")),
                Describe.Lean(DescribeId.Create("frontier-covered"), DeclarationHandle.Create(Owner + "frontier_covered"), H("Whole original relative-boundary coverage"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Without a Pair premise, every relative-boundary point of the entire original base belongs to some entire original exclusion. Original unique-confirmation density consumes this at the nearest relative-boundary contacts."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("exclusion-frontier"), DeclarationHandle.Create(Owner + "exclusion_frontier"), H("Entire exclusions lie on the relative boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Under the original closed generating cone, strictly positive unit and entire exclusion balls, every point of each full exclusion lies on the relative boundary of the whole base. No weakPair premise is used. Original unique-confirmation density transports these original points into its auxiliary affine coordinates."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("chart-intrinsic"), DeclarationHandle.Create(Owner + "chart_intrinsic"), H("Exact chart for the full relative interior"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every original pure p and its entire positive-dimensional exclusion chart, the relative interior of the exclusion is the affine chart image of the whole open unit ball. This chart identity has no Pair premise and is used to propagate a positive functional zero from a relative interior point to the whole face."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("exclusion-interior"), DeclarationHandle.Create(Owner + "exclusion_interior"), H("Nonpure points are exactly exclusion-relative interior points"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Without a weakPair premise, the relative interior of the entire original exclusion is precisely that exclusion with the original pure points removed. The density proof uses this original-site equality for its nonpure nearest-boundary contacts."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("actual-mixed-maps"),DeclarationHandle.Create(Owner+"mixedExcluded"),
                    H("Actual mixed states and actual maps"),StatementSource.FromAuthor(Disp(definitions)),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("mixedExcluded initially collects the original nonpure states excluded by some original pure point. label chooses an owner through actual full-effect incidence. centerSection maps each original pure point to the image of zero in its complete exclusion chart; its membership among mixed states is proved. reflection and contraction use the center of the uniquely determined ball. They are maps into the actual mixed-state subset because their values are proved to remain nonpure in that same full exclusion."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("mixed-boundary-contraction"),DeclarationHandle.Create(Owner+"original_mixed_exclusion_contraction"),
                    H("Unique fibers, reflection and strong deformation"),StatementSource.FromAuthor(Disp(theorem)),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("A point on the intrinsic boundary of K is outside the cone interior: an interior cone neighborhood restricts to a relative base neighborhood. Hahn-Banach supplies a nonzero cone support vanishing at the point. The existing positive_support_confirmer theorem normalizes it at an actual maximizing pure point, so the boundary point lies in a full original exclusion. Conversely a zero confirmer and a line extended beyond a relative interior point would give a negative original effect value. Thus every exclusion lies on the intrinsic boundary. Original joint completion places every pure point on that same boundary.")),
                        Paragraph(Text("If two exclusions contain the same nonpure point, their intersection is an extreme convex subset which cannot be a singleton. The existing complete-ball face theorem makes the intersection equal to both exclusions. The existing weakPair exclusion injectivity then identifies their owners. The existing chart_boundary theorem identifies the pure points of each full ball with its whole sphere. Affine restriction to the map range, the native affine-equivalence and affine-isometry intrinsic-interior theorems, and the ordinary unit-ball interior formula identify its nonpure points with its intrinsic interior.")),
                        Paragraph(Text("The actual full-effect incidence is closed: the original proper-effect interval is compact, the one-zero evaluation constraints are closed, and projection through a compact factor is closed. With compactness of all original P supplied by original_pure_compact, the native closed-graph theorem gives global continuity of label. original_continuous_frame_sum gives continuity of p plus twice its ball center, hence of the center section. Its composition with label is the identity on all P; in particular the section identifies P homeomorphically with its image.")),
                        Paragraph(Text("For every mixed boundary point, coordinates in its entire exclusion have norm strictly below one. Negation preserves that strict inequality, so center reflection preserves the same fiber and is a continuous involution. Its fixed points are precisely the actual centers. Straight motion to zero within the open unit ball proves that the displayed affine contraction stays in that same fiber for every time. It starts at the identity, ends at the center section after label, fixes every center at every time, and preserves each complete exclusion fiber in both directions. Consequently it also preserves the complement of any one such fiber."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("deleted-fiber-pair"),DeclarationHandle.Create(Owner+"deletedFiberPairHomotopy"),
                    H("The actual homotopy of deleted-fiber pairs"),StatementSource.FromAuthor(Disp(pairHomotopy)),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("For each original p, deletedFiberPair has literally the ambient space intrinsicFrontier of K minus P, with the subspace obtained by deleting D_p; deletedPointPair is (P, P minus {p}). The proved equality with mixedExcluded identifies the corresponding pairs; both maps and the homotopy are transported through this identification. Since M meets D_p exactly in its intrinsic interior, this removes the complete mixed fiber. pairLabelMap is induced by the actual continuous label; pairCenterMap is induced by the actual center section. The affine contraction induces a TopPair homotopy from the identity of deletedFiberPair to pairLabelMap followed by pairCenterMap. The pair condition is proved at every time from actual fiber preservation, using the existing TopPair.ofSubsetHomotopy constructor and transport through that proved pair isomorphism.")),
                        Paragraph(Text("These are geometric statements about the original full state and effect domain. They supply no local homology computation, Smith fixed-set dimension, ENR-to-local-homology comparison, Alexander duality or constancy of ball dimension. They require none of those conclusions as premises."))),DescribeRole.Definition))));
    }
}
