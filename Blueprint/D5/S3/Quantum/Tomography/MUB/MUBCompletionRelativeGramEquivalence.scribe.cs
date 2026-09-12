using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBCompletionRelativeGramEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One flat relative Gram characterizes fixed-edge double completion.",
        H("MUB Completion Relative Gram Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "completion-equivalence-entrywise-conjugation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence."
                    + "entrywiseConj"),
                H("Entrywise conjugation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The transparent abbreviation conjugates every entry of a rectangular "
                    + "complex matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "completion-equivalence-first-recovered-factor"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence."
                    + "recoverFirst"),
                H("First recovered factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex square matrices X and P on a finite coordinate type, the "
                    + "first recovered factor is X times P scaled by the inverse coordinate "
                    + "cardinality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "completion-equivalence-second-recovered-factor"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence."
                    + "recoverSecond"),
                H("Second recovered factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex square matrices Y and P on a finite coordinate type, the "
                    + "second recovered factor is Y times the entrywise conjugate of P, scaled "
                    + "by the inverse coordinate cardinality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "completion-equivalence-reconstruction-from-one-relative-gram"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence."
                    + "oneRelativeGram_reconstructs_doubleCompletion"),
                H("Reconstruction from one relative Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite coordinate type, let H be entrywise unit and X and "
                    + "Y be complex Hadamards. Suppose every entry of P has squared norm equal "
                    + "to the coordinate cardinality and both recovered factors are complex "
                    + "Hadamards. Then X is Hadamard unbiased to the first recovered factor, "
                    + "and the cross-Gram of the original and recovered factorized cube "
                    + "matrices is constant with value equal to the coordinate cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "completion-equivalence-exact-double-completion-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence."
                    + "doubleCompletion_iff_oneRelativeGram"),
                H("Exact double completion equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite coordinate type, fix entrywise-unit H and complex "
                    + "Hadamards X and Y. Two complex Hadamard factors X-prime and Y-prime "
                    + "exist with X Hadamard unbiased to X-prime and constant cube cross-Gram "
                    + "equal to the coordinate cardinality if and only if there is a matrix P "
                    + "with every squared entry norm equal to that cardinality and both "
                    + "recovered factors complex Hadamard."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "completion-equivalence-dimension-six-completion-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionRelativeGramEquivalence."
                    + "doubleCompletion_iff_oneRelativeGram_six"),
                H("Dimension-six completion equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For order-six matrices, with H entrywise unit and X and Y complex "
                    + "Hadamards, the double completion equivalence specializes the constant "
                    + "cube cross-Gram and the squared entry norms of P to six, retaining the "
                    + "same two recovery formulas."))),
                DescribeRole.Theorem))));
}
