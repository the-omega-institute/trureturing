using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBCompletionConsistentRelativeGramEquivalenceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative-Gram reduction retains the transition-consistency equation.",
        H("MUB Completion Consistent Relative Gram Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("consistent-completion-relative-gram-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence."
                    + "consistentDoubleCompletion_iff_oneRelativeGram"),
                H("Relative Gram reduction with transition consistency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite coordinate type, let H be entrywise unit and X "
                    + "and Y be complex Hadamards, with H times X equal to a complex scalar "
                    + "s times the entrywise conjugate of Y. A second Hadamard pair X-prime, "
                    + "Y-prime, with X unbiased to X-prime, constant cube cross-Gram equal "
                    + "to the dimension, and the same transition-consistency equation, "
                    + "exists exactly when a matrix P has every entry's squared norm equal "
                    + "to the dimension and both recoverFirst X P and recoverSecond Y P "
                    + "are complex Hadamards."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("consistent-completion-six-dimensional-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistentRelativeGramEquivalence."
                    + "consistentDoubleCompletion_iff_oneRelativeGram_six"),
                H("Dimension-six consistent completion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H, X and Y of type Mat6 under the same entrywise-unit, Hadamard "
                    + "and transition-consistency assumptions, the equivalence retains "
                    + "the equation H times X-prime equals s times the entrywise conjugate "
                    + "of Y-prime. The cube cross-Gram entries and the squared norms of "
                    + "the entries of P are six, and both recovered factors must be "
                    + "complex Hadamards."))),
                DescribeRole.Theorem))));
}
