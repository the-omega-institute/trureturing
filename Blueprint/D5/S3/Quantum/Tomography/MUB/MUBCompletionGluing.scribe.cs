using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBCompletionGluingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One relative Gram matrix determines fixed-edge double completions.",
        H("MUB Completion Gluing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "gluing-nonzero-norm-determines-the-partner"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing."
                    + "partner_eq_star_of_normSq_and_product"),
                H("Nonzero norm determines the partner"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex z and w and a nonzero real r, if the squared norm of z is "
                    + "r and z times w is r, then w is the complex conjugate of z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "gluing-conjugate-relative-gram-partner"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing."
                    + "relativeGram_partner_eq_entrywiseConj"),
                H("Conjugate relative Gram partner"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite coordinate type, suppose X and X-prime are "
                    + "Hadamard unbiased and the entrywise product of their relative Gram "
                    + "with that of Y and Y-prime is the dimension constant. Then the latter "
                    + "relative Gram is the entrywise conjugate of the former."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "gluing-scaled-recovery-from-a-relative-gram"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing."
                    + "left_mul_relativeGram_eq_card_smul"),
                H("Scaled recovery from a relative Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If X times its adjoint is the dimension times the identity, "
                    + "multiplying the relative Gram X-adjoint times X-prime on the left by X "
                    + "gives the dimension times X-prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "gluing-recovery-by-inverse-dimension"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing."
                    + "invCard_smul_left_mul_relativeGram"),
                H("Recovery by inverse dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite coordinate type, the row Gram law for X makes "
                    + "inverse-dimension scaling of X times its relative Gram with X-prime "
                    + "equal to X-prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "gluing-fixed-edge-double-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionGluing."
                    + "second_completion_determined_by_one_relativeGram"),
                H("Fixed-edge double completion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let H be entrywise unit and X and Y be complex Hadamards on a nonempty "
                    + "finite coordinate type. Suppose X and X-prime are Hadamard unbiased "
                    + "and the two factorized cube completions have constant cross-Gram equal "
                    + "to the dimension. The relative Gram of Y and Y-prime is then the "
                    + "entrywise conjugate of that of X and X-prime. Multiplication by X or Y "
                    + "and inverse-dimension scaling recover X-prime and Y-prime from those "
                    + "two relative Grams."))),
                DescribeRole.Theorem))));
}
