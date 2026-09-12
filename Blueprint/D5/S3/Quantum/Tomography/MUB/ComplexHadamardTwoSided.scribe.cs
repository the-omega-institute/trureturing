using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class ComplexHadamardTwoSidedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Hadamards have two-sided Gram laws and scaled relative Grams.",
        H("Complex Hadamard Two Sided"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "two-sided-column-gram-law"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided."
                    + "conjTranspose_mul_self_eq_card_smul"),
                H("Column Gram law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a complex Hadamard H on a nonempty finite coordinate type, "
                    + "H-adjoint times H equals the dimension times the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "two-sided-relative-gram-row-law"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided."
                    + "relativeGram_mul_conjTranspose_eq_card_sq_smul"),
                H("Relative Gram row law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two complex Hadamards on a nonempty finite coordinate type, their "
                    + "relative Gram times its adjoint equals the square of the dimension "
                    + "times the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "two-sided-scaled-hadamard-relative-gram"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided."
                    + "relativeGram_scaledHadamard"),
                H("Scaled Hadamard relative Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two Hadamard-unbiased complex Hadamards on a nonempty finite "
                    + "coordinate type, every relative Gram entry has squared norm equal to "
                    + "the dimension, and its row Gram is the square of the dimension times "
                    + "the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "two-sided-recovery-preserves-the-prescribed-gram"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardTwoSided."
                    + "relativeGram_of_recovered_factor"),
                H("Recovery preserves the prescribed Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a complex Hadamard X on a nonempty finite coordinate type and any "
                    + "square complex matrix P, multiplying X times P by the inverse "
                    + "dimension and then multiplying on the left by X-adjoint returns P."))),
                DescribeRole.Theorem))));
}
