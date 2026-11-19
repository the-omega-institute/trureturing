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
        var B=Call("ballHyp",h);
        Formula Distance(Formula r) => Call("twiceDistance",p,Call("center",B,r));
        var min=Ex("z",P,And(Mem(z,D(p)),And(Eq(delta,Distance(z)),All("q",P,Imp(Mem(q,D(p)),Le(delta,Distance(q)))))));
        var bound=All("q",P,Imp(Mem(q,D(p)),Le(delta,Call("diam",D(q)))));
        var sequence=All("a",Call("Functions",Id("Nat"),P),Imp(Call("diametersTendToZero",C,U,a),Call("eventuallyAvoids",C,U,p,a)));
        return Domain(All("H",Call("threeBallExclusions",C,U),Imp(Call("binaryCompatible",B),All("p",P,Ex("delta",R,
            And(Lt(F.D(0),delta),And(min,And(bound,sequence))))))));
    }
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Center(Formula p) => Call("center",Id("B"),p);
    private static Formula Combo(Formula t, Formula p, Formula q) => Call("binaryMixture",t,p,q);
    private static Formula Unit(Formula t) => And(Le(F.D(0),t),Le(t,F.D(1)));
    private static Formula BC()
    {
        var p=Id("p"); var q=Id("q"); var r=Id("r"); var s=Id("s"); var t=Id("t"); var v=Id("v");
        var law=All("p",P,All("q",P,All("r",P,All("s",P,All("t",R,All("v",R,
            Imp(And(Unit(t),And(Unit(v),Eq(Combo(t,p,q),Combo(v,r,s)))),
                Eq(Combo(t,Center(p),Center(q)),Combo(v,Center(r),Center(s))))))))));
        return All("V",Id("Types"),F.Seq(Inst("NormedAddCommGroup",V),Inst("NormedSpace",R,V),
            All("C",Call("PointedCone",R,V),All("u",Call("LinearMaps",R,V,R),All("B",Call("exclusionBalls",C,U),
                Iff(Call("binaryCompatible",Id("B")),law))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary compatibility gives a positive diameter bound along each fixed original sphere.",
        H("Noncollapse on a fixed original sphere"),Blocks(
        Paragraph(Text("The carrier V is finite-dimensional over the reals, C is the entire closed pointed generating cone, and u is strictly positive on nonzero cone vectors. K is the full normalized base, P its original pure locus, and D(p) the whole exclusion at p. The original EB3 premise supplies complete three-dimensional charts for those exclusions.")),
        Describe.Lean(DescribeId.Create("binary-compatible"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.binaryCompatible"),H("The entire original binary law"),StatementSource.FromAuthor(F.Disp(BC())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The binaryMixture function sends a weight t and two original pure states x and y to t x + (1-t) y. The two weights are independent in the closed unit interval. The law requires two decompositions of the same original vector to give the same mixture of centers."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("sphere-center-lipschitz"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.sphere_center_lipschitz"),
            H("A direct original BC estimate"),StatementSource.FromAuthor(F.Disp(Lipschitz())),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For two distinct unit chart vectors x and y, let d=norm(x-y), k=(x-y)/d and v=(2+d)/4. Then 0<d<=2 and v lies in the closed unit interval. The midpoint of x and -y equals v k+(1-v)(-k), while the antipodal midpoints of y,-y and k,-k agree. Apply original BC to both equalities after the same original whole-ball chart. Subtraction gives c(x)-c(y)=(d/2)(c(k)-c(-k)). Both centers lie in the original compact K, so their distance is at most diam(K). Thus the sphere-center map is Lipschitz with constant diam(K)/2. Equal chart vectors are handled directly. The proof needs only whole positive-dimensional balls and applies, in particular, to EB3."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("fixed-sphere-noncollapse"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterNoncollapse.fixed_sphere_noncollapse"),
            H("Attainment, strict positivity, diameter bound and avoidance"),StatementSource.FromAuthor(F.Disp(Minimum())),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("H is the original threeBallExclusions premise, and ballHyp(H) is the existing OriginalExclusionLimits.ballHyp. twiceDistance(p,c) means 2 norm(p-c). diametersTendToZero(C,u,a) means that diam(D(a(n))) tends to zero along the natural numbers, and eventuallyAvoids(C,u,p,a) means that all sufficiently late original labels a(n) lie outside D(p). Because those labels are already original pure points, this is precisely eventual avoidance of S(D(p)). The existential delta is inside the quantifier over the fixed original p.")),
                Paragraph(Text("The preceding Lipschitz theorem makes the original center restriction continuous on the compact chart sphere. Original chart_boundary identifies its image labels with every original pure point of the whole fixed ball, so a minimum distance to p is attained. The centerSection theorem says each original center is nonpure; it cannot equal the pure p. Hence the attained minimum is strictly positive. Delta is twice that actual minimum, with its minimizer and universal minimum inequality both stated explicitly.")),
                Paragraph(Text("For every original q on this fixed sphere, zero symmetry puts p in D(q). The original old_geometry theorem reflects p within the same whole D(q). Existing affine-ball center uniqueness identifies its oldCenter with ContinuousFrameSum.center. The two points have distance exactly 2 norm(p-c(q)), giving the diameter bound. Eventually a sequence of diameters tending to zero is below this fixed delta, which excludes each late label from the fixed sphere. Each fixed ball has its own quantified constant."))),DescribeRole.Theorem),
        Paragraph(Text("Theorem XI138.5 applies to every original p, including labels of repeated balls. Each constant belongs to its own fixed sphere.")))));
}
