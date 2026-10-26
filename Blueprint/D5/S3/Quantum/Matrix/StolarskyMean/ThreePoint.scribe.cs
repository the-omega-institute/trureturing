using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.StolarskyMean;

internal sealed class ThreePointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three exponential nodes witness two positive eigenvalues below parameter two.",
        H("Three point Stolarsky matrices"), Blocks(
            Describe.Lean(DescribeId.Create("stolarsky-three-point-positive-plane"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/StolarskyMean/ThreePoint.two_le_numPosEig_weightedToeplitz"),
                H("A positive plane in a weighted Toeplitz matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let T have rows (1,a,b), (a,1,a), and (b,a,1). If 1+b-2a squared is strictly positive, every congruence DTD by a real diagonal matrix with nonzero entries has at least two positive eigenvalues. On the plane with inverse-weighted coordinates (x,y,x), its quadratic form is (y+2ax) squared plus 2(1+b-2a squared)x squared. This is strictly positive away from zero, and the positive subspace dimension bounds the eigenvalue count."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stolarsky-three-point-counterexample-family"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/StolarskyMean/ThreePoint.exists_threePoint"),
                H("The counterexample family below parameter two"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real parameter gamma between zero inclusive and two exclusive, some positive z makes the Stolarsky matrix on exp(-2z), 1, exp(2z) have at least two positive eigenvalues. The homogeneous mean gives a diagonal congruence to the preceding Toeplitz matrix, with a=psi(z) and b=psi(2z).")),
                    Paragraph(Text("For positive gamma different from one, exp(-z)psi(z) tends at positive infinity to (1/gamma) raised to 1/(gamma-1). Strict concavity of the logarithm makes this coefficient strictly between zero and one half. Therefore exp(-2z)(1+psi(2z)-2psi(z) squared) tends to a strictly positive number. The identric extension has coefficient exp(-1), which satisfies the same bound. At the logarithmic extension, z=2 suffices because the determinant reduces to one plus sinh(2)(cosh(2)-sinh(2))/2. All three node values are strictly positive."))),
                DescribeRole.Theorem))));
}
