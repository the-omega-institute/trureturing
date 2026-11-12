using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBFixedOutputM4Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full self-adjoint M4 carrier realizes the scalar PB vector model. All four coordinates remain in the vector states. The original diagonal actor and two-leg star have their literal matrix coefficients; the complete PB row implication remains to be established.",
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
                "The operator is literal matrix action on the entire four-dimensional Euclidean space; the environment coordinate remains in the representation.", DescribeRole.Theorem),
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
                "The predicate quantifies over the complete positive cone.", DescribeRole.Definition),
            D("m4VectorFunctional_positive", "Vector states are positive", C("m4Positive", C("m4VectorFunctional", I("v"))),
                "The quadratic-form definition proves positivity of every full-space vector state.", DescribeRole.Theorem),
            D("m4ActorSupported", "Original actor support", Eq(I("m4ActorSupported"), C("FourthRowAndColumnZero")),
                "Actor-supported probes retain the original four-by-four carrier while forcing the fourth row and column to vanish.", DescribeRole.Definition),
            D("m4_positive_pb_transfer", "Positive-functional PB to vector PB", C("PositivePBTransfer", I("hPB")),
                "Applying the original scalar PB to a positive vector state supplies the full-space vector-reading hypothesis used by the Gram argument.", DescribeRole.Theorem))));

    private static DocumentBlock D(string name, string title, Formula formula, string text,
        DescribeRole role) => Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFixedOutputM4."+name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => Call(s,xs);
    private static Formula N(int n) => Num(n);
    private static Formula Eq(Formula a, Formula b) => Equal(a,b);
}
