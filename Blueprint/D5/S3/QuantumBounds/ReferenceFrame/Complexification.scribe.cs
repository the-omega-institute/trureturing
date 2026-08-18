using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.ReferenceFrame;

internal sealed class ComplexificationDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/QuantumBounds/ReferenceFrame/Complexification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite exchange-channel fidelity, sharp optimum, and paired top eigenspace extend from real to complex reference amplitudes.",
        H("Complex Reference-Frame Machinery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complex-fidelity-is-the-nearest-neighbour-quadratic"),
                DeclarationHandle.Create(
                    LeanPrefix + "complex_entanglement_fidelity_eq_nearest_neighbor_quadratic"),
                H("Complex fidelity is the nearest-neighbour quadratic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite Kraus trace expression is evaluated with complex reference "
                    + "amplitudes. Its two surviving off-diagonal entries give exactly the "
                    + "squared complex norm of zero-boundary nearest-neighbour averaging."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complex-optimum-equals-the-real-optimum"),
                DeclarationHandle.Create(
                    LeanPrefix + "complex_tax_optimum_eq_real_optimum"),
                H("The complex optimum equals the real optimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Writing each amplitude as a real part plus I times an imaginary part "
                    + "splits both the unit norm and the averaging quadratic into two real "
                    + "summands. The frozen real upper bound applies to both summands, and a "
                    + "real sine witness attains the same value in the complex domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complex-top-eigenspace-has-dimension-two"),
                DeclarationHandle.Create(LeanPrefix + "complex_top_eigenspace_finrank"),
                H("The complex top eigenspace has dimension two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Real and imaginary parts of a complex squared-top eigenvector lie in the "
                    + "frozen real paired-mode space. Scalar extension preserves independence "
                    + "of the low and high modes, so the full complex eigenspace has complex "
                    + "dimension two for N at least two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complex-flat-vector-has-the-exact-tax"),
                DeclarationHandle.Create(LeanPrefix + "flat_tax_complex"),
                H("The complex flat vector has the exact tax"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The flat complex vector is the real flat vector under the canonical "
                    + "embedding. Its tax is therefore 3/(2N) when N is at least two. The "
                    + "restriction is necessary: the frozen one-level calculation has tax "
                    + "one rather than three halves."))),
                DescribeRole.Theorem))));
}
