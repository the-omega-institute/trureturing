using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class RadialConvexityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/RadialConvexity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/czerwinska2026radial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint derivative pairings imply both Frobenius distance inequalities on ordered matrix intervals.",
        H("Radial convexity and endpoint derivatives"),
        Blocks(
            Describe.Lean(DescribeId.Create("radial-convexity-matrix-functional-calculus"),
                DeclarationHandle.Create(Module + ".matFun"), H("Hermitian functional calculus"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The real scalar function is applied by continuous functional calculus "
                    + "to a complex Hermitian matrix. The predicates use positive definite matrices, "
                    + "whose entire spectrum lies in the function's domain (0,∞)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radial-convexity-frobenius-norm"),
                DeclarationHandle.Create(Module + ".frobeniusNorm"), H("The Frobenius norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The Euclidean norm of the vector of all complex matrix entries "
                    + "is the Frobenius norm: its square is the sum of squared entry moduli. "
                    + "The definition reuses CartesianVariance.vectorize and its norm-square identity. "
                    + "It does not change the norm instance used by continuous functional calculus."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radial-convexity-order"),
                DeclarationHandle.Create(Module + ".RadiallyConvexOrder"), H("Radial convexity of order n"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every positive definite complex n×n triple A≤C≤B, "
                    + "both ‖f(C)−f(A)‖F and ‖f(B)−f(C)‖F are at most ‖f(B)−f(A)‖F. "
                    + "The Loewner order is Mathlib's MatrixOrder: A≤B means B−A is positive semidefinite."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radial-convexity-matrix-monotone-degree"),
                DeclarationHandle.Create(Module + ".MatrixMonotoneDegree"), H("Matrix monotonicity of degree n"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("On all positive definite complex n×n matrices, the functional calculus "
                    + "either preserves every Loewner comparison or reverses every Loewner comparison. "
                    + "This includes both directions allowed by Definition 2.15 of the source."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radial-convexity-endpoint-derivative-positive"),
                DeclarationHandle.Create(Module + ".EndpointDerivativePositive"),
                H("The endpoint positivity property"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every ordered pair U≤V in the domain and every positive direction K, "
                    + "both endpoint pairings ⟨g(V)−g(U),D(U)K⟩ and ⟨g(V)−g(U),D(V)K⟩ are nonnegative."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radial-convexity-endpoint-derivative-criterion"),
                DeclarationHandle.Create(Module + ".radial_inequalities_of_endpoint_derivative"),
                H("Endpoint derivative criterion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let g map an ordered real normed space into a real Hilbert space. "
                    + "Suppose ordered segments remain in the domain, g has derivative D at every domain point, "
                    + "and both endpoint inner products ⟨g(V)−g(U),D(U)K⟩ and ⟨g(V)−g(U),D(V)K⟩ "
                    + "are nonnegative whenever U≤V and K≥0. Then g satisfies both radial norm inequalities "
                    + "on every ordered triple A≤C≤B in the domain.")),
                    Paragraph(Text("Along C+t(B−C), the squared distance from g(A) has nonnegative derivative. "
                    + "Along A+t(C−A), the squared distance from g(B) has nonpositive derivative. "
                    + "The real mean value theorem gives both comparisons, and nonnegativity of norms removes the squares. "
                    + "This criterion separates the calculus argument from the matrix-specific proof of endpoint positivity."))),
                DescribeRole.Theorem))));
}
