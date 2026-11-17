using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OrthogonalJointCompletionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OrthogonalJointCompletion.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula P => C("pure", Cone, Unit);
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula Dp(Formula p) => C("exclusion", Cone, Unit, p);
    private static Formula Orth(Formula p, Formula q) => C("excludes", Cone, Unit, p, q);
    private static Formula Joint(Formula p, Formula q, Formula r) => C("jointThird", Cone, Unit, p, q, r);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        OpenBracket, C("Nontrivial", Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));

    public DocumentDefinition Create()
    {
        Formula p = V("p"), q = V("q"), r = V("r"), s = V("s"), a = V("a"), b = V("b"), x = V("x");
        Formula unique = Ex("r", P, And(Joint(p,q,r), All("s", P, Imp(Joint(p,q,s), Eq(s,r)))));
        Formula pairs = All("p", P, All("q", P, Imp(Orth(p,q), unique)));
        Formula every = All("p", P, Ex("q", P, Ex("r", P, Joint(p,q,r))));
        Formula nofour = All("p", P, All("q", P, All("r", P, All("s", P,
            Imp(Orth(p,q), Imp(Orth(p,r), Imp(Orth(p,s), Imp(Orth(q,r), Imp(Orth(q,s),
                new Formula.Not(Orth(r,s)))))))))));
        Formula capacity = And(C("measurement", Cone, Unit, D(3)), All("n", V("Nat"),
            Imp(C("measurement", Cone, Unit, V("n")),
                new Formula.Relation(V("n"), FormulaRelationOperator.LessThanOrEqual, D(3)))));
        Formula strict = All("x", Space, Imp(In(x,Cone), Imp(Seq(x,Neq,Sp,D(0)),
            Seq(D(0),F.Lt,Sp,App(Unit,x)))));
        Formula statement = Context(Imp(C("IsClosed",Cone), Imp(strict,
            Imp(Eq(C("span",R,Cone),C("top")), Imp(C("exclusionBalls",Cone,Unit),
                Imp(C("weakPair",Cone,Unit), And(pairs,And(every,And(nofour,capacity)))))))));
        Formula common = And(C("confirms",Cone,Unit,p,a),
            All("x", Space, Imp(In(x,Dp(p)), Eq(App(a,x),D(0)))));
        Formula weak = All("p",P,All("q",P,Imp(Orth(p,q),
            Seq(C("pairBase",Cone,Unit,p,q),Neq,Sp,C("base",Cone,Unit)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original weak orthogonal-pair properness supplies unique whole joint triples and mathematical capacity three.",
            H("Original orthogonal joint completion"), Blocks(
                Paragraph(Text("V is the original nonzero finite dimensional real normed vector space. C is the original closed generating pointed cone; u is the original real linear unit strictly positive on C away from zero. K=base(C,u) is the entire normalized base and P=pure(C,u) is its entire extreme-point set. Proper effects are ALL linear maps with 0<=f<=u on ALL C. No finiteness or closedness of P, global pairProper, dimension-two condition, joint frame, reciprocal comparison, spectrality, Jordan representation or PSD cone is assumed.")),
                Describe.Lean(DescribeId.Create("weak-pair"),DeclarationHandle.Create(Owner+"weakPair"),
                    H("The original restricted pair entrance"),StatementSource.FromAuthor(Disp(Context(new Formula.Logic(C("weakPair",Cone,Unit),FormulaLogicOperator.Iff,weak)))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("weakPair requires pairBase(C,u,p,q) different from K only when excludes(C,u,p,q) holds. excludes means one original proper effect confirms p and reads zero at q. Complementation gives the opposite orientation. pairBase remains the whole smallest native cone-face slice, rather than the segment or a chosen chart."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("common"),DeclarationHandle.Create(Owner+"common"),
                    H("The entire common confirmation family"),StatementSource.FromAuthor(Disp(Context(All("p",P,All("a",Dual,new Formula.Logic(C("common",Cone,Unit,p,a),FormulaLogicOperator.Iff,common)))))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("common(C,u,p,a) means exactly a belongs to the original A_p: a is proper on the entire cone, a(p)=1 and a vanishes at every mixed state of the entire original D_p. No leastness or uniqueness is included."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("joint-third"),DeclarationHandle.Create(Owner+"jointThird"),
                    H("All clauses of a joint third point"),StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("jointThird(C,u,p,q,r) asserts D_p intersect D_q={r}, H(p,q)=D_r, and the three original zero relations p perpendicular q, p perpendicular r and q perpendicular r. For EVERY specified a in A_p and b in A_q, it asserts c=u-a-b belongs to A_r, all nine delta readings a(p)=b(q)=c(r)=1 with the other six zero, and the identity a+b+c=u as linear maps on the whole original vector space. This is a conclusion predicate, never an entrance assumption."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("measurement"),DeclarationHandle.Create(Owner+"measurement"),
                    H("Finite mathematical distinguishing measurements"),StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("measurement(C,u,n) means there are p:Fin n to ALL P and f:Fin n to the original dual, with every f_i proper on ALL C, f_i(p_j)=if i=j then 1 else 0, and sum_i f_i=u. The delta equations force distinct pure points. It asserts a mathematical effect family and supplies no actual menu, device, wiring or physical implementation."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("whole-joint-completion"),DeclarationHandle.Create(Owner+"whole_joint_completion"),
                    H("Unique joint completion on the entire original domain"),StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("Under original EB_ge1 and weakPair, every original orthogonal p,q has exactly one r satisfying jointThird. Every original pure p belongs to such a triple. Six original pairwise zero relations among four points are impossible. A three-effect mathematical measurement exists, and every finite original mathematical distinguishing measurement has at most three outcomes. Thus the maximum jointly distinguishable original pure capacity is exactly three, without presupposing a finite set of ALL pure points.")),
                        Paragraph(Text("Use ONLY the first two conjuncts of ExclusionBallFaces.exclusion_ball_faces: the common exposure and complete proper convex face classification already follow from EB alone. The whole minimal face of an original orthogonal pair is convex and extreme; weakPair makes that particular face proper. Its two different pure points exclude the singleton classification, so H(p,q)=D_r. Original zero symmetry puts r in both D_p and D_q. If their intersection contained two points, chart_face_eq would make that face the entire ball D_p. But q belongs to D_p and cannot belong to D_q, a contradiction. Therefore the whole intersection is exactly {r}. This is the new weak-entrance geometric bridge.")),
                        Paragraph(Text("For arbitrary specified a in A_p and b in A_q, pull u-a back to the derived whole pair ball D_r. Reuse the original affine_zero_antipode equality theorem. Its endpoint value at q and original proper upper bound force its coefficient to be one; the original pure endpoint coordinates and the inner-product equality criterion identify q with the antipode of p. The same existing equality theorem fixes b's whole restriction, hence a+b=u on every mixed state of D_r. This ball calculation uses the actual whole pair derived above, never a global pair-ball assumption.")),
                        Paragraph(Text("Set c=u-a-b. Original nonnegativity of a,b gives c<=u on ALL C; common zero readings give c(r)=1. The just-proved whole-ball equality gives c=0 on ALL D_r. Directly apply WholeExclusionSupport.whole_exclusion_support to obtain properness of c on the entire original cone, including positivity. Its normalization proof is neither copied nor re-counted. The nine readings and the linear-map unit sum follow. Compact nonpoint D_p has an extreme point of its own, which is original pure by faciality, giving every-pure completion. A fourth original orthogonal point lies in the same singleton intersection. For capacity attainment use pure_span, nontriviality and the common effects supplied by the paid classifier; for the upper bound a delta measurement with more than three outcomes supplies four forbidden original pairwise zero points.")),
                        Paragraph(Text("This implements the complete original VII104.3 all-P target, distinct from the finite-ALL-P classical-triangle target VII104.9. No spectral decomposition of mixed states, global least effect, general nonzero reciprocal values, physical common menu or newer spectral framework is concluded. The mirrored Reg attempt reconstructs the original telescope and records an actual-positive law and conditional erased-relation failure; full four-slot registration is not asserted. Mathematical source and compiled evidence determine the theorem; no literature priority is claimed."))),DescribeRole.Theorem))));
    }
}
