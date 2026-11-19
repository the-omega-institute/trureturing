using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class TwoKrausRankOneAttenuationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula N => V("n");
    private static Formula J => V("J");
    private static Formula Q => V("q");
    private static Formula X => V("X");
    private static Formula Mat => C("Matrix", N, N, Complex);
    private static Formula Star(Formula a) => C("conjTranspose", a);
    private static Formula Mul(Formula a, Formula b) => C("mul", a, b);
    private static Formula Add(Formula a, Formula b) => C("add", a, b);
    private static Formula Sub(Formula a, Formula b) => C("sub", a, b);
    private static Formula Smul(Formula a, Formula b) => C("smul", a, b);
    private static Formula R => C("jumpFilter", J, Q);
    private static Formula H(Formula a) => C("jumpMap", J, Q, a);
    private static Formula Norm(Formula a) => C("opNorm", a);
    private static Formula Context(Formula b) => All("n", V("Type"), Seq(
        OpenBracket, C("Fintype", N), CloseBracket, Sp,
        OpenBracket, C("DecidableEq", N), CloseBracket, Sp,
        All("J", Mat, All("q", Real, b))));
    private static Formula Car(Formula b) => Imp(Eq(Mul(J, J), D(0)),
        Imp(Eq(Add(Mul(J, Star(J)), Mul(Star(J), J)), D(1)), b));
    private static Formula Range(Formula b) => Imp(Le(D(0), Q), Imp(Le(Q, D(1)), b));
    private static DocumentBlock Entry(string id, string name, string title, Formula statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name),
            DefinitionDsl.H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create()
    {
        Formula f = Mul(J, Star(J));
        Formula k = C("pair", R, Smul(C("ofReal", C("sqrt", Q)), J));
        Formula psi = V("psi"), u = C("ofLp", psi);
        Formula p = C("re", C("dotProduct", C("star", u), C("mulVec", f, u)));
        Formula c = C("dotProduct", C("star", u), C("mulVec", J, u));
        Formula pure = C("vecMulVec", u, C("star", u));
        Formula loss = Mul(Mul(Q, Sub(D(1), Q)), Sub(p, C("normSq", c)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A two-column Gram defect gives quantitative pure-state loss for finite CAR jumps.",
            DefinitionDsl.H("Nilpotent CAR attenuation"), Blocks(
                Paragraph(Text("Matrices act on the existing complex Euclidean space. opNorm(A) means the norm of Matrix.toEuclideanCLM A, equivalently the L2 operator norm. The index type is arbitrary and finite; no nonempty instance is required. A unit vector itself rules out the empty case. Scalar coefficients in matrix expressions use the real-to-complex embedding.")),
                Entry("filter", "jumpFilter", "No-jump filter", Context(Eq(R,
                    Add(Sub(D(1), f), Smul(C("ofReal", C("sqrt", Sub(D(1), Q))), f)))),
                    "F=JJ* is the range projection when J²=0 and JJ*+J*J=I. The filter is I−F+sqrt(1−q)F.", DescribeRole.Definition),
                Entry("kraus-map", "jumpMap", "The canonical finite Kraus map", Context(Eq(C("jumpMap", J, Q), C("ofKraus", k, k))),
                    "ofKraus is FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus, with the same ordered pair K=(R,sqrt(q)J) in both slots. This is a linear map on matrices. It is unital under the CAR and interval hypotheses; trace preservation is not asserted. The imported Kraus implementation retains its Physlib source attribution and Apache license.", DescribeRole.Definition),
                Entry("sandwiches", "jumpMap_apply", "The two actual Kraus sandwiches", Context(Imp(Le(D(0), Q), All("X", Mat,
                    Eq(H(X), Add(Mul(Mul(R, X), Star(R)), Smul(C("ofReal", Q), Mul(Mul(J, X), Star(J)))))))),
                    "For q≥0 the two Kraus summands are RXR* and qJXJ*. The identity uses sqrt(q)²=q.", DescribeRole.Theorem),
                Entry("positive", "jumpMap_positive", "Positivity", Context(Imp(Le(D(0), Q), All("X", Mat, Imp(Le(D(0), X), Le(D(0), H(X)))))),
                    "Each Kraus sandwich preserves positive semidefiniteness. The matrix order is the canonical PSD order.", DescribeRole.Theorem),
                Entry("contraction", "jumpMap_norm_le", "Hermitian contraction", Context(Car(Range(All("X", Mat,
                    Imp(C("IsHermitian", X), Le(Norm(H(X)), Norm(X))))))),
                    "CAR gives F²=F, FJ=J, JF=0 and R²=I−qF. Thus H(I)=I. Positivity and linearity transport −norm(X)I≤X≤norm(X)I to the same interval for H(X), proving contraction on every Hermitian input, including indefinite ones.", DescribeRole.Theorem),
                Entry("rank-one-loss", "nilpotent_jump_rank_one_attenuation", "Quantitative rank-one loss", Context(Car(Range(
                    All("psi", C("EuclideanSpace", Complex, N), Imp(Eq(C("norm", psi), D(1)), Le(Norm(H(pure)), Sub(D(1), loss))))))),
                    "Write u=ofLp(psi), p=Re(u*Fu), c=u*Ju. The two columns Rpsi and sqrt(q)Jpsi give A with H(P)=AA*. Positivity, P≤I and unitality imply A*A≤I by the rectangular L2 norm identity. The Gram entries are 1−qp, sqrt(q)sqrt(1−q)c and its conjugate, and q(1−p). Its defect determinant is q((1−q)(p−normSq(c))+qp²). Both Gram eigenvalues lie in [0,1]; if their maximum is nu, then norm(H(P))=nu≤1−det(I−A*A). Dropping q²p² gives the stated bound. Both parameter endpoints and arbitrary complex phases are included. This is a pure-state estimate, with no assertion about a low-temperature tube or nonnegativity of an entropy gap.", DescribeRole.Theorem))));
    }
}
