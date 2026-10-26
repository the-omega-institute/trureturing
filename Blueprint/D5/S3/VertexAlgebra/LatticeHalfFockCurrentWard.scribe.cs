using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentWardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockCurrentWard.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unrestricted native half-Fock current Ward identity for corrected fields.",
        H("Corrected half-Fock current Ward identity"),
        Blocks(
            Paragraph(Text("For arbitrary LatticeData D, determinant unit hu, colour i, charge b, integer modes q and e, and every actual tensor state x, the canonical corrected field has the native current commutator displayed below. The current is the actual tensor lift on ActualGround(D,hu); all integer modes, including negative modes and the zero mode, are retained.")),
            Paragraph(Text("The right side is the finite sum over n < vectorFrequencyBound D b + 1. Its coefficient is Ring.choose (frequency q) n, its field is correctedField D hu (neutralMode D i n b), and its exponent is e - (2*q + 1) + 2*n. The proof expands the actual tensor Heisenberg commutator, contracts the true singleton mode -q-1, uses polynomialField_X_mul induction with pderiv multiplicity, transports Corr_partial over its finite support, then lifts the finite charge support and applies the original-source truncation.")),
            Describe.Lean(
                DescribeId.Create("corrected-field-current-ward"),
                DeclarationHandle.Create(Prefix + "correctedField_current_ward"),
                H("Full native current Ward identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The exact Lean telescope is D, hu, i, b, q, e and x with no positivity, eigenstate, homogeneity, locality, Jacobi or module-law premise. The finite range preserves n=0 even when the vector frequency bound is zero. Repeated source occurrences remain separate through pderiv, and all support arguments are pointwise on the actual tensor inputs."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is a native algebraic identity only. The complete VOA, conformal field theory, anomaly, fusion, string and AdS/CFT programme remains open beyond this endpoint.")),
            Paragraph(Text("Truth anchor: D5/S3/VertexAlgebra/LatticeHalfFockCorrectedField.correctedField_current_ward.")))));
}
