using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class PositiveComplementaryProjectionsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/PositiveComplementaryProjections.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Conj(params Formula[] xs) => xs.Aggregate(And);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula Comp(Formula a, Formula b) => C("comp", a, b);
    private static Formula Star(Formula a) => C("dualMap", a);
    private static Formula Im(Formula c, Formula t) => C("positiveImage", c, t);
    private static Formula Ker(Formula c, Formula t) => C("positiveKernel", c, t);
    private static Formula Pos(Formula c, Formula t) => C("PositiveProjection", c, t);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula End => C("LinearMap", R, Space, Space);
    private static Formula P => C("pure", Cone, Unit);
    private static Formula CDual => C("positiveDual", Cone);
    private static Formula Dp(Formula p) => C("exclusion", Cone, Unit, p);
    private static Formula Hull(Formula s) => C("coneHull", R, s);
    private static Formula Ray(Formula x) => Hull(C("singleton", x));
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        OpenBracket, C("Nontrivial", Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));

    public DocumentDefinition Create()
    {
        Formula p = V("p"), ap = V("ap"), pi = V("Pi"), sigma = V("Sigma"), x = V("x"), f = V("f");
        Formula rank = C("smulRight", ap, p), rs = Star(rank), z = C("zeroPositive", Cone, Unit, p);
        Formula bounds(Formula t) => All("x", Space, Imp(In(x, Cone), And(Le(D(0), App(Unit, App(t, x))), Le(App(Unit, App(t, x)), App(Unit, x)))));
        Formula pointFields = Conj(
            Eq(Star(pi), sigma), Pos(Cone, pi), Pos(Cone, rank), Pos(CDual, sigma), Pos(CDual, rs),
            Eq(App(sigma, Unit), C("sub", Unit, ap)), Eq(App(sigma, ap), D(0)), Eq(App(pi, p), D(0)),
            All("x", Space, Imp(In(x, Dp(p)), Eq(App(pi, x), x))),
            Eq(Im(Cone, pi), Hull(Dp(p))), Eq(Ker(Cone, pi), Ray(p)),
            Eq(Im(Cone, rank), Ray(p)), Eq(Ker(Cone, rank), Hull(Dp(p))),
            Eq(Im(CDual, sigma), z), Eq(Ker(CDual, rs), z),
            Eq(Ker(CDual, sigma), Ray(ap)), Eq(Im(CDual, rs), Ray(ap)),
            All("f", Dual, Eq(App(rs, f), C("smul", App(f, p), ap))),
            All("x", Space, And(Eq(App(Unit, App(pi, x)), App(C("sub", Unit, ap), x)),
                Eq(App(Unit, App(rank, x)), App(ap, x)))), bounds(pi), bounds(rank));
        Formula point = Context(All("p", P, All("ap", Dual, All("Pi", End,
            All("Sigma", C("LinearMap", R, Dual, Dual), Iff(C("PointLaws", Cone, Unit, p, ap, pi, sigma), pointFields))))));
        Formula t = V("T"), r = V("R");
        Formula pairFields = Conj(Pos(Cone, t), Pos(Cone, r), Pos(CDual, Star(t)), Pos(CDual, Star(r)),
            Eq(Im(Cone, t), Ker(Cone, r)), Eq(Ker(Cone, t), Im(Cone, r)),
            Eq(Im(CDual, Star(t)), Ker(CDual, Star(r))), Eq(Ker(CDual, Star(t)), Im(CDual, Star(r))),
            All("x", Space, Imp(In(x, Cone), And(Le(App(Unit, App(t, x)), App(Unit, x)), Le(App(Unit, App(r, x)), App(Unit, x))))));
        Formula pair = Context(All("T", End, All("R", End, Iff(C("ComplementaryPair", Cone, Unit, t, r), pairFields))));
        Formula a = V("a"), b = V("b"), c = V("c"), lam = V("Lambda"), gamma = V("Gamma");
        Formula apoint = App(a, p), resb = C("restriction", b), resc = C("restriction", c);
        Formula s = Comp(lam, resb), primal = C("primal", s);
        Formula chart(Formula q) => C("ExclusionChart", Cone, Unit, q);
        Formula lift(Formula q) => C("LinearMap", R, C("AffineMap", R, C("EuclideanSpace", R, C("Fin", C("dim", q))), R), Dual);
        Formula common = All("p", P, C("common", Cone, Unit, p, apoint));
        Formula unique = All("p", P, All("f", Dual, Imp(C("common", Cone, Unit, p, f), Eq(f, apoint))));
        Formula charts = All("p", P, All("b", chart(p), Ex("Lambda", lift(b), Conj(
            C("ExtensionLaws", b, apoint, lam), Eq(Comp(resb, lam), C("id")),
            C("PointLaws", Cone, Unit, p, apoint, primal, s),
            All("c", chart(p), All("Gamma", lift(c), Imp(C("PositiveLift", c, gamma), Eq(s, Comp(gamma, resc)))))))));
        Formula faces = All("F", C("Face", Cone), Ex("T", End, Ex("R", End,
            And(C("ComplementaryPair", Cone, Unit, t, r), Eq(Im(Cone, t), V("F"))))));
        Formula strict = All("x", Space, Imp(In(x, Cone), Imp(Seq(x, Neq, Sp, D(0)), Seq(D(0), F.Lt, Sp, App(Unit, x)))));
        Formula statement = Context(Imp(C("IsClosed", Cone), Imp(strict, Imp(Eq(C("span", R, Cone), C("top")),
            Imp(C("exclusionBalls", Cone, Unit), Imp(C("weakPair", Cone, Unit),
                Ex("a", C("Function", P, Dual), Conj(common, unique, charts, faces))))))));
        Formula e = V("E"), k = V("K"), l = V("L");
        Formula generic(Formula body) => All("E", V("Type"), Seq(OpenBracket, C("AddCommGroup", e), CloseBracket, Sp,
            OpenBracket, C("Module", R, e), CloseBracket, Sp, All("K", C("PointedCone", R, e),
                All("L", C("LinearMap", R, e, e), body))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Original weak geometry yields positive complementary primal and dual projections for every native cone face.",
            H("Positive complementary projections on the original cone"), Blocks(
                Paragraph(Text("V is the original nonzero finite dimensional real normed space, C the original closed generating pointed cone, and u the original linear unit strictly positive on C away from zero. K=base(C,u) is the entire normalized base and P=pure(C,u) its entire extreme-point set. The hypotheses are all original exclusion balls of positive dimension and weakPair. Proper effects range over every linear functional between zero and u on all C. No finite pure carrier, spectral decomposition, positive projector or positive extension is an additional premise.")),
                Describe.Lean(DescribeId.Create("positive-image"), DeclarationHandle.Create(Owner + "positiveImage"), H("Literal positive image"),
                    StatementSource.FromAuthor(Disp(generic(Eq(Im(k, l), C("inter", C("range", l), k))))), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The positive image is the linear range intersected with the actual cone. It is not defined as the image of that cone."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("positive-kernel"), DeclarationHandle.Create(Owner + "positiveKernel"), H("Literal positive kernel"),
                    StatementSource.FromAuthor(Disp(generic(Eq(Ker(k, l), C("inter", C("ker", l), k))))), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The positive kernel is the linear kernel intersected with the actual cone, with the same definition on the original algebraic dual."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("positive-dual"), DeclarationHandle.Create(Owner + "positiveDual"), H("The actual positive dual"),
                    StatementSource.FromAuthor(Disp(Context(Eq(CDual, C("coneDual", C("dualEval", R, Space), Cone))))), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("A member is an original algebraic linear functional nonnegative at every vector of C. The pairing is evaluation; no self-dual inner product identification is made."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("primal"), DeclarationHandle.Create(Owner + "primal"), H("Genuine finite dimensional dual transport"),
                    StatementSource.FromAuthor(Disp(Context(All("Sigma", C("LinearMap", R, Dual, Dual), Eq(C("primal", sigma),
                        Comp(C("inverse", C("evalEquiv", R, Space)), Comp(Star(sigma), C("evalEquiv", R, Space)))))))), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Finite dimensional algebraic biduality defines Pi on the original V. For every original f and v, f(Pi(v))=Sigma(f)(v); consequently Pi.dualMap=Sigma. This uses the evaluation equivalence, with no perfect-pair topology premise on the algebraic dual."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("positive-projection"), DeclarationHandle.Create(Owner + "PositiveProjection"), H("Positivity and idempotence"),
                    StatementSource.FromAuthor(Disp(generic(Iff(Pos(k, l), And(All("x", e, Imp(In(x, k), In(App(l, x), k))), Eq(Comp(l, l), l)))))), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Positivity is tested on the entire cone. Idempotence is equality of linear maps."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("point-laws"), DeclarationHandle.Create(Owner + "PointLaws"), H("All original pointwise projection laws"),
                    StatementSource.FromAuthor(Disp(point)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Here R=ap.smulRight(p), so R(v)=ap(v)p, and Rstar is its genuine algebraic dual. The eight equalities use actual linear range and kernel intersections. Zp consists of all original positive functionals vanishing at p. cone(Dp) and the two nonnegative rays are native PointedCone hulls, denoted coneHull, including zero.")),
                        Paragraph(Text("The mass identities quantify over ALL v in V. On C both masses lie in [0,u(v)], giving normalization nonincrease. Pi fixes every mixed state of the entire Dp and kills p; Sigma fixes every positive functional in Zp through the positive restriction inverse."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("complementary-pair"), DeclarationHandle.Create(Owner + "ComplementaryPair"), H("Mathematical complementary filters"),
                    StatementSource.FromAuthor(Disp(pair)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Both maps and their genuine duals are positive idempotents. Their positive images and kernels agree in both complementary directions, and both original unit masses do not increase on C. Complementarity imposes no sum-to-identity equation."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("whole-positive-projections"), DeclarationHandle.Create(Owner + "whole_positive_projections"), H("Full original VII105.5"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The common family a and each signed linear extension Lambda are obtained from whole_positive_extension on the original W hypotheses. Restriction followed by Lambda gives Sigma; finite dimensional dual transport gives Pi. res composed with Lambda is the identity on the whole affine coordinate space. The extension laws give Sigma(u)=u-a_p and Sigma(a_p)=0. Every other positive lift in every other chart gives the same Sigma, hence the same genuine Pi.")),
                        Paragraph(Text("Sigma is positive by restriction and positive extension. If Pi(v) were outside the original closed cone for positive v, separation would supply an original continuous linear functional nonnegative on C but negative at Pi(v). Its value equals Sigma(f)(v), a contradiction. This proves positivity on the original V rather than on a chosen coordinate model.")),
                        Paragraph(Text("The zero cone of a_p is exactly cone(Dp), by normalizing every nonzero positive vector using the strictly positive original unit. The maximum face a_p=1 contains p. The complete original proper-face classification makes it a singleton or Dq. In the latter case, original zero symmetry and joint completion produce a point in Dp intersect Dq, where a_p would equal both zero and one. Thus p is its unique normalized maximum. These two exact faces give the four primal range and kernel equalities.")),
                        Paragraph(Text("For the remaining dual kernel, a positive f annihilating the entire Dp must equal f(p)a_p on ALL V. An original joint triple p,q,r identifies the whole pair face of r,p with Dq. Restrict f and a_p to an actual whole Dq ball. Both are nonnegative and vanish at r; affine_zero_antipode gives the same diameter factor. Evaluation at the actual p fixes their coefficient ratio, so the two restrictions agree after multiplication by f(p). Both original functionals vanish at q and are positive. The actual Lambda_q.inverse_positive reconstructs both from those restrictions, proving the equality globally. This reconstruction also fixes every member of Zp and yields both dual positive range and kernel pairs.")),
                        Paragraph(Text("Every F is a native PointedCone.Face C, not merely a selected or exposed face. A nonzero proper face is recovered from its entire unit slice by normalization and conical hull. The complete original proper-face classification makes that slice a pure singleton or an entire Dp, so the appropriate rank-one or Pi pair represents F. Zero and C use zero and identity in the two orders. All native faces are therefore positive images of mathematical complementary filter pairs.")),
                        Paragraph(Text("This concludes mathematical projectivity on the original domain. It asserts no Pi+R=id, no unconditional preservation of pure rays, no physical event or instrument, no applicability of BMU Theorem 16, and no full static completion of later reconstruction results. The two-map and dual conditions are mathematical linear and cone statements."))), DescribeRole.Theorem))));
    }
}
