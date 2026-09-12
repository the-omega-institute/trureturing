using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBCompletionRecoveredRowGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recovered completion factors satisfy automatic row-Gram equations.",
        H("MUB Completion Recovered Row Gram"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("recovered-conjugate-card-square-row-gram"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram."
                    + "entrywiseConj_preserves_cardSq_rowGram"),
                H("Conjugate preserves the cardinality-square row Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The entrywise conjugate of a matrix whose row Gram is the "
                    + "finite-cardinality square times the identity has the same row Gram."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recovered-first-factor-row-gram"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram."
                    + "recoverFirst_rowGram"),
                H("First recovered factor row Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If X is complex Hadamard and P has the cardinality-square row Gram, "
                    + "the rational recovery of the first factor has the cardinality row Gram."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recovered-second-factor-row-gram"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram."
                    + "recoverSecond_rowGram"),
                H("Second recovered factor row Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If Y is complex Hadamard and P has the cardinality-square row Gram, "
                    + "the conjugate-coupled rational recovery has the cardinality row Gram."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recovered-double-completion-polynomial-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram."
                    + "doubleCompletion_iff_scaledRelativeGram_and_twoDefects"),
                H("Polynomial characterization of double completion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For entrywise-unit H and complex Hadamards X and Y, a double completion "
                    + "exists exactly when one relative Gram P has flat entries, the "
                    + "cardinality-square row Gram, and the two recovery defect equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recovered-six-dimensional-specialization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRecoveredRowGram."
                    + "doubleCompletion_iff_scaledRelativeGram_and_twoDefects_six"),
                H("Dimension-six polynomial specialization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For order-six matrices, the double-completion equivalence specializes "
                    + "to flat entries of squared norm six, row Gram thirty-six times the "
                    + "identity, and the two recovery defect equations."))),
                DescribeRole.Theorem))));
}
