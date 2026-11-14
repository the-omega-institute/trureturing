using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class BinaryCenterGeometryDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Inst(string s, params Formula[] xs) => F.Seq(F.OpenBracket, Call(s, xs), F.CloseBracket, F.Sp);
    private static Formula Conj(params Formula[] xs) { var r = xs[^1]; for (var i=xs.Length-2;i>=0;i--) r=And(xs[i],r); return r; }
    private static Formula R => Id("Real");
    private static Formula V => Id("V");
    private static Formula C => Id("C");
    private static Formula U => Id("u");
    private static Formula P => Call("pure", C, U);
    private static Formula K => Call("base", C, U);
    private static Formula D(Formula p) => Call("exclusion", C, U, p);
    private static Formula Center(Formula p) => Call("center", Id("B"), p);
    private static Formula Combo(Formula t, Formula p, Formula q) => Call("binaryMixture", t, p, q);
    private static Formula Unit(Formula t) => And(new Formula.Relation(F.D(0), FormulaRelationOperator.LessThanOrEqual, t), new Formula.Relation(t, FormulaRelationOperator.LessThanOrEqual, F.D(1)));
    private static Formula Active(Formula t) => And(Lt(F.D(0),t),Lt(t,F.D(1)));
    private static Formula Domain(Formula body, bool chosen = false)
    {
        var x=Id("x");
        var strict=All("x",V,Imp(And(Mem(x,C),Ne(x,F.D(0))),Lt(F.D(0),Call("u",x))));
        var premises=Conj(Call("IsClosed",C),strict,Eq(Call("span",R,C),Id("top")));
        var balls=Call("exclusionBalls",C,U);
        return All("V",Id("Types"),F.Seq(Inst("NormedAddCommGroup",V),Inst("NormedSpace",R,V),Inst("FiniteDimensional",R,V),
            All("C",Call("PointedCone",R,V),All("u",Call("LinearMaps",R,V,R),
                Imp(premises,chosen ? All("B",balls,body) : Imp(balls,body))))));
    }
    private static Formula BC()
    {
        var p=Id("p"); var q=Id("q"); var r=Id("r"); var s=Id("s"); var t=Id("t"); var v=Id("v");
        var law=All("p",P,All("q",P,All("r",P,All("s",P,All("t",R,All("v",R,
            Imp(Conj(Unit(t),Unit(v),Eq(Combo(t,p,q),Combo(v,r,s))),
                Eq(Combo(t,Center(p),Center(q)),Combo(v,Center(r),Center(s))))))))));
        return All("V",Id("Types"),F.Seq(Inst("NormedAddCommGroup",V),Inst("NormedSpace",R,V),Inst("FiniteDimensional",R,V),
            All("C",Call("PointedCone",R,V),All("u",Call("LinearMaps",R,V,R),All("B",Call("exclusionBalls",C,U),
                Iff(Call("binaryCompatible",Id("B")),law))))));
    }
    private static Formula PairPremise() => Conj(Ne(Id("p"),Id("s")),Eq(D(Id("s")),D(Id("p"))),Mem(Id("q"),D(Id("p"))));
    private static Formula Pair(Formula body, bool chosen=false) => Domain(All("p",P,All("s",P,All("q",P,Imp(PairPremise(),body)))),chosen);
    private static Formula Fibers()
    {
        var p=Id("p");var q=Id("q");var r=Id("r");
        return Pair(Conj(All("r",P,Iff(Eq(D(r),D(q)),Mem(r,D(p)))),All("r",P,Iff(Eq(D(r),D(p)),Mem(r,D(q)))),Call("Disjoint",D(p),D(q))));
    }
    private static Formula Effect()
    {
        var e=Id("e");var x=Id("x");
        Formula Face(Formula value) => new Formula.SetBuilder(x,x,And(Mem(x,K),Eq(Call("e",x),value)));
        return Pair(Ex("e",Call("LinearMaps",R,V,R),Conj(Call("proper",C,U,e),Eq(Face(F.D(0)),D(Id("p"))),Eq(Face(F.D(1)),D(Id("q"))))));
    }
    private static Formula Block => Call("union",D(Id("p")),D(Id("q")));
    private static Formula Finite()
    {
        var n=Id("n");var m=Id("m");var a=Id("a");var b=Id("b");var w=Id("w");var v=Id("v");var i=Id("i");var j=Id("j");
        var premises=Conj(All("i",Call("Fin",n),Mem(Call("a",i),Block)),All("j",Call("Fin",m),Mem(Call("b",j),Block)),Eq(Call("sum",w),F.D(1)),Eq(Call("sum",v),F.D(1)),Eq(Call("weightedSum",w,a),Call("weightedSum",v,b)));
        return Pair(All("n",Id("Nat"),All("m",Id("Nat"),All("a",Call("Functions",Call("Fin",n),P),All("b",Call("Functions",Call("Fin",m),P),All("w",Call("Functions",Call("Fin",n),R),All("v",Call("Functions",Call("Fin",m),R),Imp(premises,
            Eq(Call("weightedCenterSum",Id("B"),w,a),Call("weightedCenterSum",Id("B"),v,b))))))))),true);
    }
    private static Formula Outside()
    {
        var r=Id("r");var a=Id("a");var b=Id("b");var d=Id("d");var t=Id("t");var v=Id("v");
        var premises=Conj(Call("binaryCompatible",Id("B")),Call("Not",Mem(r,Block)),Mem(a,Block),Mem(b,Block),Mem(d,Block),Active(t),Active(v));
        return Pair(All("r",P,All("a",P,All("b",P,All("d",P,All("t",R,All("v",R,Imp(premises,
            Ne(Combo(t,r,a),Combo(v,b,d))))))))),true);
    }
    private static DocumentBlock Result(string id,string selector,string title,Formula formula,string text) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterGeometry."+selector),H(title),
            StatementSource.FromAuthor(F.Disp(formula)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal repeated fibers, one original separating effect and repeated-block compatibility.",H("Original binary-center geometry"),Blocks(
        Paragraph(Text("V is the same finite dimensional real normed carrier, C the closed pointed generating cone, and u the strictly positive original unit. K=base(C,u) is the entire normalized base, P=pure(C,u) all its extreme points. D(p)=exclusion(C,u,p) uses every original proper effect; no restricted effects or alternative state carrier is introduced. The full confirmer minimum corresponds to this exclusion through ExclusionWidthCompactness.comparison_attained and comparison_zero_iff. B is a proof of exclusionBalls on this same original domain. center(B,p) is ContinuousFrameSum.center, and equality of whole balls identifies these existing centers by AffineBallRigidity.center_eq_of_ball_eq. The results below permit all positive chart dimensions and hence apply to EB3.")),
        Paragraph(Text("binaryMixture(t,x,y) denotes t times x plus (1-t) times y. union is set union. sum(w) and weightedSum(w,a) are the sums over every index of the displayed Fin type; weightedCenterSum(B,w,a) replaces each a(i) by center(B,a(i)). Functions denotes the full function type. All endpoint functions take values in the original P. The finite compatibility result holds for arbitrary real normalized weights, in particular all nonnegative pure mixtures, repeated endpoints and zero coefficients. Empty index types are included; their normalization premise is false.")),
        Describe.Lean(DescribeId.Create("binary-compatible"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterGeometry.binaryCompatible"),H("The entire original binary law"),StatementSource.FromAuthor(F.Disp(BC())),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The two weights are independently quantified in the closed unit interval. The law compares two decompositions of the same actual original vector. No MC, global injectivity, pure closedness or common-center premise is included."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("center-eq-of-exclusion-eq"),DeclarationHandle.Create("D5/S3/Quantum/Foundation/BinaryCenterGeometry.center_eq_of_exclusion_eq"),H("Centers of equal whole original balls"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For any finite dimensional real normed carrier V, original pointed cone C and linear unit u, a proof B of exclusionBalls, and any two original pure labels p and q, equality of their entire exclusions implies center(B,p)=center(B,q). No closedness, strict positivity, generating-span, BC or injectivity premise is required. The existing affine-ball center uniqueness theorem applies to the two complete chosen chart images, allowing different chart dimensions. This implication does not identify arbitrary balls from equality of their centers."))),DescribeRole.Theorem),
        Result("repeated-partner-fibers","repeated_partner_fibers","Both original fibers and disjointness",Fibers(),"Assume p and s are distinct original pure labels with the same whole exclusion F, and q is any original pure point of F. For every original r in F, zero symmetry places p and s in D(r), so the two-point whole-ball rigidity gives D(r)=D(q). Conversely equality with D(q) and zero symmetry give r in F. Two distinct original pure points of F give the reciprocal identity I(F)=P intersect D(q). The original repeated_ball_isolated theorem gives disjointness; the equality alternative would put p in its own exclusion. These identities identify the two whole faces used by the common separating effect and the repeated-block relations."),
        Result("repeated-pair-effect","repeated_pair_separating_effect","One original effect on the entire paired balls",Effect(),"Choose antipodal original pure points on the partner ball. Their original whole-face exposing confirmers vanish on F. On the partner ball the two restrictions are 1-alpha+alpha inner(n,z) and 1-beta-beta inner(n,z), with alpha and beta between zero and one half. If either coefficient is zero, that confirmer is already constant one on the partner. Otherwise beta times the first effect plus alpha times the second is constant k=alpha+beta-2 alpha beta>0 there and zero on F. positive_annihilator_maximum puts an actual global maximizer on the partner, so division by k yields a proper effect on the entire original cone. A fixed original pure point of each ball and the same effect or its complement prove both full face equalities. No full-Inj contact theorem is used."),
        Result("repeated-block-finite","repeated_block_finite_compatibility","Every finite relation within the repeated block",Finite(),"The same original separating effect e defines J(x)=c(q)+e(x)(c(p)-c(q)). Both reciprocal fiber identities and whole-ball center uniqueness prove that J equals the original center replacement at every pure point of F union H. Linearity of e and the normalization of the finite sums show that each replaced sum equals J of the original sum. This actual consumer uses the entire paired zero and one faces; the effect is constructed rather than assumed as a classifier field."),
        Result("repeated-block-outside","repeated_block_one_outside","One outside and three inside endpoints cannot cross",Outside(),"Apply BC and the same affine J to a proposed active crossing. Agreement on all three block endpoints and cancellation of the positive outside weight imply c(r)=J(r). The full zero and one faces of e give 0<e(r)<1 for an original pure r outside the block. Any strict mixture of the two ball centers belongs to no original exclusion: otherwise the facial property puts both centers in that exclusion, and the original interior-vanishing theorem puts both whole balls there. Whole-ball maximality identifies both balls, contradicting their disjointness. The actual center c(r) lies in its own exclusion, which gives the contradiction."),
        Paragraph(Text("These are original repeated-block results and prerequisites for the XI138 local geometry. They do not construct the BC boundary-center affine graph on each whole ball or prove its rank dichotomy, exact interior section, reflected sphere dichotomy or fixed-sphere quantitative minimum. BC to MC, global injectivity, global noncollapse, equality of a reflected ball with its source, cross-ball vector gluing and two-outside crossings remain outside these conclusions. No quantum classification, literature priority or physical realization is asserted.")))));
}
