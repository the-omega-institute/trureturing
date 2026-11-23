using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FibonacciQutritOptimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact retained Umegaki relative entropy for the four Fibonacci likelihood classes under qutrit encoding.",
        H("Fibonacci qutrit Umegaki optimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-qutrit-channel-maximum"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/FibonacciQutritOptimum.isGreatest_channel"),
                H("Attained maximum over all CPTP encoders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonacciqutritoptimum"),
                    LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonaccisingularsupport"),
                    LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonaccimixedqubit")),
                Blocks(
                    Paragraph(Text(
                        "The two input density matrices are diagonal on four classes, with weights "
                        + "p = (88, 25, 28, 0)/141 and q = (66, 15, 12, 48)/141. For every CPTP encoder "
                        + "to a three-dimensional space, the retained Umegaki relative entropy is at most "
                        + "(113/141) log(113/81) + (28/141) log(7/3) nats. This is the greatest element "
                        + "of the set of output scores, including the support-aware extended definition.")),
                    Paragraph(Text(
                        "These four classes correspond to the distinct ratios 4/3, 5/3, 7/3 and 0. "
                        + "Grouping equal likelihood ratios means summing p and q separately within each class. "
                        + "Within a class the two conditional laws coincide whenever its p mass is positive, "
                        + "and the q-conditional law suffices to reconstruct a class of zero p mass. "
                        + "The Lean theorem takes the resulting four diagonal weights as its inputs.")),
                    Paragraph(Text(
                        "On diagonal inputs a channel acts by mixing its density-state preparations of "
                        + "the four diagonal basis states. The pointwise bound pᵢ ≤ (7/3)qᵢ and positivity "
                        + "of those preparations show that the reference kernel lies in the numerator kernel. "
                        + "Thus the extended entropy equals its finite trace-log branch. "
                        + "A singular positive-class reference reduces to a common qubit and retains "
                        + "the null-class log loss. The mixed-qubit overlap deficit bounds the qubit score. "
                        + "A positive definite positive-class reference reaching the benchmark would admit "
                        + "a strictly better preparation with positive-class rank at most two.")),
                    Paragraph(Text(
                        "For attainment, use orthogonal qutrit rays P, Q and R. Prepare P on classes 4/3 "
                        + "and 5/3, Q on class 7/3 and R on class 0. The commuting outputs have weights "
                        + "(113, 28, 0)/141 and (81, 12, 48)/141. The finite preparation construction "
                        + "makes this a CPTP encoder on the entire input matrix algebra.")),
                    Paragraph(Text(
                        "For this pair the measured relative entropy maximum has the same value. "
                        + "Berta, Fawzi and Tomamichel give the variational expression for rank-one "
                        + "projective relative entropy in Lemma 1 and its equality with POVM relative "
                        + "entropy in Theorem 2. A rank-one projective measurement on the qutrit induces "
                        + "a stochastic map from the four classes to three outcomes. Its score is bounded "
                        + "by the classical maximum, which the commuting preparations attain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-qutrit-channel-equality"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/FibonacciQutritOptimum.channel_equality_conditions"),
                H("Necessary equality conditions on the preparations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonacciqutritoptimum")),
                Blocks(
                    Paragraph(Text(
                        "At the optimum the positive-class reference is singular. The 4/3 and 5/3 "
                        + "basis preparations coincide. The common preparation, the 7/3 preparation "
                        + "and the zero-likelihood preparation have pairwise zero matrix products, "
                        + "so their supports are pairwise orthogonal.")),
                    Paragraph(Text(
                        "Optimality forces both nonnegative overlap terms and the null-class log loss "
                        + "to vanish. Trace-one positivity converts unit overlap into equality, and zero "
                        + "overlap into a zero matrix product. Positive coefficients then place the support "
                        + "of the null-class preparation in the kernel of each positive-class preparation."))),
                DescribeRole.Theorem))));
}
