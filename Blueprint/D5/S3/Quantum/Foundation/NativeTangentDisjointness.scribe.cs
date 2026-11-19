using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class NativeTangentDisjointnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/NativeTangentDisjointness.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula In(Formula x, Formula s) => Seq(x, InMacro, Sp, s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula P => C("pure", Cone, Unit);
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula App(Formula f, params Formula[] xs) => C("apply", [f, .. xs]);
    private static Formula Chart(Formula p) => C("ExclusionChart",Cone,Unit,p);
    private static Formula D(Formula p) => C("exclusion",Cone,Unit,p);
    private static Formula Ratio(Formula x, Formula y) => Seq(Frac,Grp(x),Grp(y));
    private static Formula Sq(Formula x) => Seq(Grp(x),Caret,Grp(F.D(2)));
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);

    public DocumentDefinition Create()
    {
        Formula a=V("a"),p=V("p"),q=V("q"),qp=V("qprime"),f=V("f"),b=V("b"),bp=V("bprime"),x=V("x");
        Formula common=All("p",P,C("common",Cone,Unit,p,App(a,p)));
        Formula unique=All("p",P,All("f",Dual,Imp(C("common",Cone,Unit,p,f),Eq(f,App(a,p)))));
        Formula tangents=All("p",P,All("q",P,All("qprime",P,
            Imp(In(q,D(p)),Imp(In(qp,D(p)),Imp(Seq(q,Neq,Sp,qp),
                All("b",Chart(q),All("bprime",Chart(qp),Eq(
                    C("inf",C("tangent",b,App(a,p)),C("tangent",bp,App(a,p))),C("bot"))))))))));
        Formula conclusion=Ex("a",C("Function",P,Dual),And(common,And(unique,tangents)));
        Formula t=V("t"),h=V("h"),hp=V("hprime"),r=V("r"),rp=V("rprime"),z=V("z");
        Formula xt=Ratio(Add(Add(Multiply(Sq(t),p),r),Multiply(Multiply(Multiply(F.D(2),h),t),z)),Add(F.D(1),Sq(t)));
        Formula y=Ratio(Add(Add(p,rp),Multiply(Multiply(F.D(2),hp),z)),F.D(2));
        Formula c0=App(App(a,r),rp),c1=App(App(a,rp),r);
        Formula statement=All("V",V("Type"),Seq(
            OpenBracket,C("NormedAddCommGroup",Space),CloseBracket,Sp,
            OpenBracket,C("NormedSpace",R,Space),CloseBracket,Sp,
            OpenBracket,C("FiniteDimensional",R,Space),CloseBracket,Sp,
            OpenBracket,C("Nontrivial",Space),CloseBracket,Sp,
            All("C",C("PointedCone",R,Space),All("u",Dual,
                Imp(C("IsClosed",Cone),Imp(All("x",Space,Imp(In(x,Cone),Imp(Seq(x,Neq,Sp,F.D(0)),
                    Seq(F.D(0),F.Lt,Sp,App(Unit,x))))),Imp(Eq(C("span",R,Cone),C("top")),
                    Imp(C("exclusionBalls",Cone,Unit),Imp(C("weakPair",Cone,Unit),conclusion)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original weak exclusion-ball geometry forces distinct neighbor tangents to have zero intersection.",
            H("Native tangent disjointness on the full original carrier"),Blocks(
                Paragraph(Text("Source: VIII108.1-108.6 of QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII. The same nonzero finite dimensional real V, closed pointed generating C and strictly positive original u determine the entire base K, every original extreme point P and the entire proper-effect interval [0,u]. W means only exclusionBalls with each entire D_p a Euclidean ball of positive dimension, and weakPair on original orthogonal pairs. No finiteness of P, common center, fullPair, numerical reciprocity, global metric, tangent covering or projection is assumed.")),
                Describe.Lean(DescribeId.Create("directions"),DeclarationHandle.Create(Owner+"directions"),
                    H("Directions of the entire exclusion ball"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("directions b is vectorSpan over the reals of the whole original exclusion set D_q. Its equality with the range of the actual chart's linear part follows by mapping the vector span of the whole coordinate closed unit ball, whose affine span is the full coordinate space. For the center c_q=b.param(0), this is precisely lin(D_q-c_q), independently of the chosen entire chart."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("tangent"),DeclarationHandle.Create(Owner+"tangent"),
                    H("Intrinsic tangent at the original point"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("tangent b a_p is directions b intersect ker(a_p). Given any pure p in D_q, pull it back to a unit chart coordinate e. Apply the existing affine_zero_antipode theorem to the nonnegative affine function 1-a_p on the entire ball. Its nonzero diameter coefficient follows from an original joint companion where a_p vanishes. Thus a_p(b.param.linear(w))=0 forces inner(e,w)=0. All actual tangents are covered, with no extra orthogonality premise in the theorem. The definition includes dimension-one balls and their zero tangent."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("whole-native-tangent-disjointness"),DeclarationHandle.Create(Owner+"whole_native_tangent_disjointness"),
                    H("Distinct original neighbors have zero tangent intersection"),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("Directly consume CommonPositiveExtension.whole_arc_effect: one family a of actual common effects, its uniqueness, and the full-space ArcFamily. For each nonzero common candidate z, each actual chart yields independent positive h=1/norm(w), an original opposite r, a signed B with B(z)=1/(2h), vanishing on the whole span of p and D_p, and the all-space circle identity. The map w is the actual chart preimage of the SAME vector z. The two coordinate norms remain independent.")),
                        Paragraph(Text("Every real pair c,s with c squared plus s squared equal to one is realized by an angle, using pinned mathlib Complex.arg, cos_arg and sin_arg. Consequently the supplied circle consists of actual original pure states, with state expression ((1+c)/2)p+((1-c)/2)r+s h z and corresponding original effect ((1+c)/2)a_p+((1-c)/2)a_r+s B. This obtains the rational half-angle states from original sphere points, not arbitrary formal perturbations.")),
                        Paragraph(Math(Disp(And(Eq(C("x",t),xt),Eq(V("y"),y))))),
                        Paragraph(Text("For every original neighbor v in D_p, its original positive a_v vanishes at p. Evaluating it on the rational native circle and multiplying by the positive denominator gives a_v(r)t squared+2h a_v(z)t nonnegative for every real t. The existing quadratic discriminant theorem forces a_v(z)=0. This is the needed original 108.4 annihilator consequence, proved without N_p or a projection and without assuming the unpaid full VII105.5.")),
                        Paragraph(Text("Fix the second native circle state y=(p+rprime+2hprime z)/2, and evaluate the SAME actual original effect at the SAME y. For the first circle use c=(t squared-1)/(1+t squared), s=2t/(1+t squared). Its original positivity gives t squared+c0+2(hprime/h)t nonnegative, where c0=a_r(rprime). Substitute t=-hprime/h to obtain (hprime/h) squared<=c0; exchange the charts for (h/hprime) squared<=c1 with c1=a_rprime(r). No equality of c0 and c1 is used.")),
                        Paragraph(Math(Disp(And(Le(Sq(Ratio(hp,h)),c0),Le(Sq(Ratio(h,hp)),c1))))),
                        Paragraph(Text("The actual singleton intersections from whole_joint_completion imply distinct neighbors have distinct opposite points. If a_r(rprime)=1, the first original frame sum and a_p(rprime)=0 force a_q(rprime)=0. Both r and rprime then lie in the same singleton D_p intersect D_q, a contradiction. Hence both cross readings are strictly below one. Their nonnegativity and the two reciprocal scale bounds imply 1<=c0 c1<1. This proves zero intersection for every pair of full charts.")),
                        Paragraph(Text("The live new inference is the original tangent annihilation and the combination of two independently scaled native arc families through actual original state-effect positivity. Pure scalar normalization is only an internal step. Reused source suppliers are protected dependencies; this consumer does not approve, freeze, cover or settle the separate VII105.4 delivery. Full VII105.3 spectral generation, VII105.5 projectivity, VIII108.7 dimensions and VIII109 reconstruction remain outside this result. No physical realization, global classification or literature novelty is claimed.")),
                        Paragraph(Text("The same-delivery Reg mirror reconstructs the complete original telescope and proves its actual-positive law. A complete Contract.Registration value additionally needs a lawful enrolled readout, whole-family intervention/sensitivity, observational dependence and exact sourceSelection evidence. The attempted whole-theorem observation has State=Unit, so it cannot supply two unequal state readouts; a faithful varying observation and its exact source reconstruction remain missing. These unfinished slots are tracked in https://github.com/the-omega-institute/trureturing/issues/29702. Compiled source reconstruction alone is not declared_validated."))),DescribeRole.Theorem)
            )));
    }
}
