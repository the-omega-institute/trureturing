using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class BinaryCenterNoncollapseDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => F.Seq(a,F.Sp,F.InMacro,F.Sp,b);
    private static Formula Inst(string s, params Formula[] xs) => F.Seq(F.OpenBracket,Call(s,xs),F.CloseBracket,F.Sp);
    private static Formula V => Id("V");
    private static Formula R => Id("Real");
    private static Formula C => Id("C");
    private static Formula U => Id("u");
    private static Formula P => Call("pure",C,U);
    private static Formula K => Call("base",C,U);
    private static Formula D(Formula p) => Call("exclusion",C,U,p);
    private static Formula Domain(Formula body)
    {
        var x=Id("x");
        var strict=All("x",V,Imp(And(Mem(x,C),new Formula.Relation(x,FormulaRelationOperator.NotEqual,F.D(0))),Lt(F.D(0),Call("u",x))));
        return All("V",Id("Types"),F.Seq(Inst("NormedAddCommGroup",V),Inst("NormedSpace",R,V),Inst("FiniteDimensional",R,V),
            All("C",Call("PointedCone",R,V),All("u",Call("LinearMaps",R,V,R),
                Imp(And(Call("IsClosed",C),And(strict,Eq(Call("span",R,C),Id("top")))),body)))));
    }
    private static Formula Lipschitz()
    {
        var b=Id("b");var p=Id("p");var B=Id("B");
        var bound=new Formula.Fraction(Call("diam",K),F.D(2));
        return Domain(All("B",Call("exclusionBalls",C,U),Imp(Call("binaryCompatible",B),All("p",P,All("b",Call("ExclusionChart",C,U,p),
            Call("LipschitzWith",bound,Call("sphereCenter",B,p,b)))))));
    }
    private static Formula Minimum()
    {
        var h=Id("H");var p=Id("p");var q=Id("q");var z=Id("z");var delta=Id("delta");var a=Id("a");var n=Id("n");
        var B=Call("threeImpliesBalls",h);
        Formula Distance(Formula r) => Call("twiceDistance",p,Call("center",B,r));
        var min=Ex("z",P,And(Mem(z,D(p)),And(Eq(delta,Distance(z)),All("q",P,Imp(Mem(q,D(p)),Le(delta,Distance(q)))))));
        var bound=All("q",P,Imp(Mem(q,D(p)),Le(delta,Call("diam",D(q)))));
        var sequence=All("a",Call("Functions",Id("Nat"),P),Imp(Call("diametersTendToZero",C,U,a),Call("eventuallyAvoids",C,U,p,a)));
        return Domain(All("H",Call("threeBallExclusions",C,U),Imp(Call("binaryCompatible",B),All("p",P,Ex("delta",R,
            And(Lt(F.D(0),delta),And(min,And(bound,sequence))))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary compatibility determines each whole-ball affine center graph, its rank branches and singleton section, as well as fixed-sphere quantitative bounds.",
        H("Whole-ball center graphs and fixed original spheres"),Blocks(
        Paragraph(Text("V, C, u, K, P, all original proper effects and the full original exclusion D(p) have the same meanings as in BinaryCenterGeometry. Closedness, strict positivity on every nonzero cone vector and generating span are retained. B is an actual proof of exclusionBalls, and center is the existing ContinuousFrameSum.center. ExclusionChart parametrizes the whole original ball by an injective affine map of a positive-dimensional Euclidean closed unit ball. sphereCenter(B,p,b) is the function on that chart's unit sphere taking x to center(B,chartPure(p,b,x)); chartPure is the original SingleLabelNormalBody owner. No global center continuity, closed pure locus, global injectivity or width-one premise is used.")),
        Describe.Lean(DescribeId.Create("whole-ball-center-affine"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_affine"),
            H("The unique affine graph on every whole source ball"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For every original domain described above, every proof B of exclusionBalls satisfying the complete original binaryCompatible law, every original pure p and every entire ExclusionChart b of D(p), there exists exactly one real affine map g from the Euclidean chart carrier to V with g(x)=center(B,chartPure(p,b,x)) for every unit vector x, and its entire closed unit ball image is contained in K. The unique map is on the source chart carrier, equivalently on the affine span of the whole original D(p). No uniqueness on all of V is asserted. Since b is injective and its whole closed ball image is D(p), g composed with the inverse chart defines the actual G_F on every point of F=D(p); the sphere is exactly all original pure points of F.")),
                Paragraph(Text("Coordinate reflections preserve the chart sphere. Comparing their original chords by BC gives the change in the center function when one coordinate is reversed. Telescoping over all coordinates and using the common antipodal midpoint determines an affine interpolant with explicit basis coefficients. This constructs the map on the whole chart carrier from the actual original centers. Sphere convex generation and convexity of K give its entire-ball range; affine spanning gives uniqueness."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("whole-ball-center-graph"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_graph"),
            H("Repeated and singleton rank branches"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For every same original domain, B, BC, pure p and entire chart b, there exists an affine g with all the preceding original boundary values and entire-ball range K, unique among all affine maps with those boundary values. If SingleLabel(C,u,p), g is injective and its linear range has dimension b.dim. If SingleLabel fails, g is constant on the entire chart carrier. For an actual three-dimensional original chart the derived rank is therefore three, without an assumed rank certificate.")),
                Paragraph(Text("A nonzero kernel vector would give two distinct antipodal source sphere points with the same original center. Their exclusions share this nonpure point; the original extreme-face intersection and two-point rigidity force equality of their whole exclusions. Singleton-label propagation on the original sphere then identifies the two pure points, a contradiction. In the repeated case, the full reciprocal fibers identify every sphere label's entire exclusion with the opposite ball. Whole-ball center uniqueness and sphere affine spanning force g to be constant."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("whole-ball-center-section"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.whole_ball_center_section"),
            H("Every interior image point and the exact section"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For every same original domain, B and BC, every original pure p with SingleLabel(C,u,p), and every entire chart b, there exists an affine g with the actual original center boundary values, injective with linear range dimension b.dim, sending every chart vector of norm strictly below one into the relative interior of K. Its entire closed unit ball image is exactly K intersect the affine range of g. This affine range is the affine span of that entire image, since the source closed unit ball affinely spans the chart carrier. For every original sphere label q the linear range of g is disjoint from the chosen whole D(q) chart linear range, equivalently the direction of D(q) translated to its center. A common direction would yield two distinct points in the exact section with midpoint c(q), contradicting its extremeness in the image ball.")),
                Paragraph(Text("If an interior image point belonged to the original relative boundary, frontier coverage and an original exposing effect would give a nonnegative affine function vanishing at an interior source point. The original affine_zero_inside_ball owner makes it vanish on all source vectors. Each boundary center then forces its entire original exclusion into that same exposed face. Original whole-face maximality identifies every such exclusion, so g would be constant on its sphere, contradicting injectivity. For the exact section, any K point in the affine range but beyond the image ball would put a sphere-center boundary point on an open segment from the interior image center to that K point. The intrinsic interior segment theorem gives a contradiction."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("affine-ball-frontier"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.affine_ball_frontier"),H("Relative frontier of an injective affine ball"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For every finite dimensional real inner product source E with at least two points, every finite dimensional real normed target V and every injective real affine g:E to V, the intrinsic frontier of g(closedBall(0,1)) is exactly g(sphere(0,1)). Compactness makes the image closed; intrinsic interior transport identifies the removed open ball. This supplies the entire image sphere in the original center and reflected-ball conclusions."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-center-sections"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.original_center_sections"),H("The original three-dimensional sections and dimension bound"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Assume the same closed pointed generating original cone, strict unit, nonzero finite dimensional real carrier, original EB3 and the complete original BC law. The affine dimension of the whole K is at least six and an original singleton-label exclusion exists. For every singleton-label original p there are an entire three-dimensional chart b of D(p) and an affine g with every original center boundary value, injective with linear rank three, sending every norm-below-one source point into the intrinsic interior of K. Its entire closed-ball image equals K intersect its own affine span. Its entire intrinsic frontier equals its sphere image, all those sphere-center points lie on the original intrinsic frontier of K, and its linear range is disjoint from every corresponding whole original exclusion direction. Native singleton-ball dimension bounds and the normalized-base dimension identity are applied to the same original V,C,u. The dimension conclusion has no physical-realization implication."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("sphere-center-lipschitz"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.sphere_center_lipschitz"),
            H("A direct original BC estimate"),StatementSource.FromAuthor(F.Disp(Lipschitz())),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For two distinct unit chart vectors x and y, let d=norm(x-y), k=(x-y)/d and v=(2+d)/4. Then 0<d<=2 and v lies in the closed unit interval. The midpoint of x and -y equals v k+(1-v)(-k), while the antipodal midpoints of y,-y and k,-k agree. Apply original BC to both equalities after the same original whole-ball chart. Subtraction gives c(x)-c(y)=(d/2)(c(k)-c(-k)). Both centers lie in the original compact K, so their distance is at most diam(K). Thus the sphere-center map is Lipschitz with constant diam(K)/2. Equal chart vectors are handled directly. The proof needs only whole positive-dimensional balls and applies, in particular, to EB3."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("fixed-sphere-noncollapse"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.fixed_sphere_noncollapse"),
            H("Attainment, strict positivity, diameter bound and avoidance"),StatementSource.FromAuthor(F.Disp(Minimum())),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("H is the original threeBallExclusions premise, and threeImpliesBalls(H) is the exposed original CommonOldExclusionConfirmation.three_implies_balls. twiceDistance(p,c) means 2 norm(p-c). diametersTendToZero(C,u,a) means that diam(D(a(n))) tends to zero along the natural numbers, and eventuallyAvoids(C,u,p,a) means that all sufficiently late original labels a(n) lie outside D(p). Because those labels are already original pure points, this is precisely eventual avoidance of S(D(p)). The existential delta is inside the quantifier over the fixed original p.")),
                Paragraph(Text("The preceding Lipschitz theorem makes the original center restriction continuous on the compact chart sphere. Original chart_boundary identifies its image labels with every original pure point of the whole fixed ball, so a minimum distance to p is attained. The centerSection theorem says each original center is nonpure; it cannot equal the pure p. Hence the attained minimum is strictly positive. Delta is twice that actual minimum, with its minimizer and universal minimum inequality both stated explicitly.")),
                Paragraph(Text("For every original q on this fixed sphere, zero symmetry puts p in D(q). The unchanged original old_geometry owner reflects p within the same whole D(q). Existing affine-ball center uniqueness identifies its oldCenter with ContinuousFrameSum.center. The two points have distance exactly 2 norm(p-c(q)), giving the diameter bound. Eventually a sequence of diameters tending to zero is below this fixed delta, which excludes each late label from the fixed sphere. Constants for different fixed balls are quantified separately. This proves no uniform lower bound over all balls and no full-axis inner ball."))),DescribeRole.Theorem),
        Paragraph(Text("The minimum statement uses the boundary value c(q), now realized by the whole-ball affine graph. Constants for different fixed balls remain separately quantified. The reflected-ball alternatives and global connections require their own conclusions. No BC to MC, global injectivity, uniform noncollapse, quantum classification, physical realization or literature-priority claim is made.")))));
}
