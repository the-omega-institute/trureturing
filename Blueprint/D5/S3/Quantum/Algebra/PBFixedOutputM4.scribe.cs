using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBFixedOutputM4Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full self-adjoint M4 carrier realizes the scalar PB vector model. All four coordinates remain in the vector states. For the original diagonal actor and two-leg star, scalar PB for every positive complex-linear functional and every actor-supported Hermitian probe forces a real diagonal residual on the full four-dimensional output. Its environment entry is unrestricted.",
        H("Full M4 realization and original spectral probes"),
        Blocks(
            D("m4C", "The original actor", Eq(I("m4C"), C("diag", N(1), N(2), N(3), N(0))),
                "The first three spectral values are 1, 2 and 3; the fourth, environment value is zero.", DescribeRole.Definition),
            D("m4T", "The original two-leg star", Eq(C("m4T", I("q1"), I("q2")), C("HermitianStar", I("q1"), I("q2"), N(0))),
                "The actor-to-environment column is exactly (q1,q2,0), with its conjugate row. No phase rotation is performed.", DescribeRole.Definition),
            D("m4Kappa", "The oriented commutator", Eq(C("m4Kappa", I("c"), I("iota"), I("x")), C("OrientedHalfCommutator", I("iota"), I("c"), I("x"))),
                "The real-linear row is iota times (cx-xc)/2, with iota fixed as either i or minus i.", DescribeRole.Definition),
            D("m4J", "The concrete M4 Jordan product", Eq(I("m4J"), C("M4JordanProduct")),
                "The carrier is the real self-adjoint submodule of Matrix (Fin 4) (Fin 4) Complex, with literal symmetrized matrix multiplication.", DescribeRole.Definition),
            D("m4VectorModel", "The concrete M4 vector model", Eq(I("m4VectorModel"), C("VectorModel", C("EuclideanSpace", I("Complex"), C("Fin", N(4))), I("m4J"))),
                "The operator is literal matrix action on the entire four-dimensional Euclidean space; the environment coordinate remains in the representation.", DescribeRole.Definition),
            D("m4_full_row_reconstruction", "Hermitian full-row reconstruction", C("HermitianRowReconstruction", I("g"), I("k")),
                "Agreement on every off-diagonal entry of two Hermitian four-by-four matrices leaves a diagonal residual with real entries.", DescribeRole.Theorem),
            D("m4VectorFunctional", "A full-space vector functional", Eq(I("m4VectorFunctional"), C("VectorState", I("v"))),
                "The complex-linear vector state is evaluated on the whole M4 carrier.", DescribeRole.Definition),
            D("m4RealFunctional", "Real restriction of a complex functional", Eq(I("m4RealFunctional"), C("RealRestriction", I("phi"))),
                "Restriction to the self-adjoint real carrier takes the real part.", DescribeRole.Definition),
            D("m4RealFunctional_vector", "Vector restriction identity", C("RestrictionEqualsVectorReading", I("v"), I("A")),
                "For vector states, the restriction is exactly the existing vectorReading.", DescribeRole.Theorem),
            D("m4PosSemidef", "Full complex positive cone", Eq(I("m4PosSemidef"), C("HermitianQuadraticNonnegative")),
                "Positive semidefiniteness is stated as Hermiticity plus nonnegative full-space quadratic forms, avoiding an order on Complex.", DescribeRole.Definition),
            D("m4Positive", "Full matrix positivity predicate", Eq(I("m4Positive"), C("PositiveFunctionalOnM4")),
                "The predicate requires a real, nonnegative value on every matrix in the complete positive cone.", DescribeRole.Definition),
            D("m4VectorFunctional_positive", "Vector states are positive", C("m4Positive", C("m4VectorFunctional", I("v"))),
                "The quadratic-form definition proves positivity of every full-space vector state.", DescribeRole.Theorem),
            D("m4ActorSupported", "Original actor support", Eq(I("m4ActorSupported"), C("FourthRowAndColumnZero")),
                "Actor-supported probes retain the original four-by-four carrier while forcing the fourth row and column to vanish.", DescribeRole.Definition),
            D("m4_positive_pb_transfer", "Positive-functional PB to vector PB", C("PositivePBTransfer", I("hPB")),
                "Applying the original scalar PB to a positive vector state supplies the full-space vector-reading hypothesis used by the Gram argument.", DescribeRole.Theorem),
            D("m4_scalar_pb_diagonal_residual", "Scalar PB reconstructs the complete original output", MainStatement(),
                "Take c=diag(1,2,3,0) and t with actor-to-environment column (q1,q2,0), q1 q2 nonzero, and its conjugate row. Fix iota as either i or minus i. The unknown g is any Hermitian M4 matrix. For every positive complex-linear functional phi on the full M4 algebra and every Hermitian probe x with fourth row and column zero, assume scalarPB with kappa(x)=iota(cx-xc)/2, rho(x)=(cx+xc)/2 and k=(ct+tc)/2. The conclusion gives four real diagonal residuals of g-iota(ct-tc)/2, including an unrestricted environment entry. There is no total response map or independent P2 assumption.", DescribeRole.Theorem,
                "For distinct actor indices i,j, construct e from the two matrix units, j0 with coefficients iota and minus iota, and n=2 times the i-th spectral projection. Literal matrix multiplication supplies the spectral pair, its companion axis, and J(n,V)=V, where V=c_i J(n,t)-J(n,J(c,t)). Both probe families T e+alpha n and T j0+alpha n are actor-supported.",
                "For a unit vector xi with xi_i=0, put y=j0 xi and d=norm(y). If d=0 the quadratic reading vanishes. Otherwise eta=y/d is unit, e xi=-iota y and n eta=2 eta. Apply fixed_output_two_axis_identity on the whole M4 representation. Homogeneous scaling gives inner(j0 xi,g xi)=iota inner(j0 xi,V xi) for every xi with xi_i=0, including zero vectors.",
                "Let P_i remove coordinate i, let Y represent j0 and let A represent g-iota V. The quadratic identity makes the quadratic form of P_i Y A P_i vanish on every full-space vector. Mathlib's complex polarization theorem inner_map_self_eq_zero gives P_i Y A P_i=0. Its j-th output coordinate on each complementary basis vector forces the entire i-th row of A to vanish off the diagonal. The entry formula identifies iota V with the corresponding commutator row. Repeat for all three actor indices; Hermiticity supplies the matching environment row, leaving four real diagonal entries. Each quadratic form uses one common j0 and retains the fourth input coordinate."))));

    private static Formula MainStatement()
    {
        var complex=Seq(Mathbb,Grp(I("C")));
        var real=Seq(Mathbb,Grp(I("R")));
        var carrier=C("selfAdjoint",C("M4",complex));
        var orient=new Formula.Logic(Eq(I("iota"),I("i")),FormulaLogicOperator.Or,Eq(I("iota"),Neg(I("i"))));
        var nonzero=Imp(Eq(Mul(I("q1"),I("q2")),N(0)),I("False"));
        var t=C("m4T",I("q1"),I("q2"));
        var budget=C("scalarPB",I("m4J"),C("m4Kappa",I("m4C"),I("iota")),C("m4J",I("m4C")),
            t,C("m4J",I("m4C"),t),I("g"),I("x"),C("m4RealFunctional",I("phi")));
        var probes=All("x",carrier,Imp(C("m4ActorSupported",I("x")),budget));
        var pb=All("phi",C("ComplexLinearFunctional",C("M4",complex)),Imp(C("m4Positive",I("phi")),probes));
        var result=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("s"),C("Function",C("Fin",N(4)),real),
            Eq(Sub(I("g"),C("m4Kappa",I("m4C"),I("iota"),t)),C("diagonal",C("ofReal",I("s")))));
        var conclusion=All("g",carrier,Imp(pb,result));
        var oriented=All("iota",complex,Imp(orient,conclusion));
        return All("q1",complex,All("q2",complex,Imp(nonzero,oriented)));
    }
    private static Formula All(string s, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),type,body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static DocumentBlock D(string name, string title, Formula formula, string text,
        DescribeRole role, params string[] more) => Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFixedOutputM4."+name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(new[]{Paragraph(Text(text))}.Concat(more.Select(x=>Paragraph(Text(x)))).ToArray()), role);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => Call(s,xs);
    private static Formula N(int n) => Num(n);
    private static Formula Eq(Formula a, Formula b) => Equal(a,b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a,b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a,b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
}
