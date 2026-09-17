using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBCompletionScalarDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Double completion reduces to flatness, row Grams and two scalar defects.",
        H("MUB Completion Scalar Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-completion-relative-gram-defect-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect."
                    + "doubleCompletion_iff_oneRelativeGram_twoScalarDefects"),
                H("Double completion through two scalar defects"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite coordinate type, let H be entrywise unit and X "
                    + "and Y be complex Hadamards. A second Hadamard pair X-prime, Y-prime, "
                    + "with X unbiased to X-prime and constant cube cross-Gram equal to "
                    + "the dimension, exists exactly when there is a matrix P with every "
                    + "entry's squared norm equal to the dimension and the following "
                    + "conditions on each of recoverFirst X P and recoverSecond Y P: "
                    + "the sum over all entries of the square of the squared norm minus "
                    + "one is zero, and the matrix times its adjoint is the dimension "
                    + "times the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-completion-six-dimensional-defects"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionScalarDefect."
                    + "doubleCompletion_iff_oneRelativeGram_twoScalarDefects_six"),
                H("Dimension-six scalar defect criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H, X and Y of type Mat6 under the same entrywise-unit and "
                    + "Hadamard assumptions, double-completion feasibility is equivalent "
                    + "to a matrix P whose entries have squared norm six. Each recovered "
                    + "factor has zero sum of squared deviations of entry squared norms "
                    + "from one, and its row Gram equals six times the identity. The "
                    + "cube cross-Gram on the completion side has every entry equal to six."))),
                DescribeRole.Theorem))));
}
