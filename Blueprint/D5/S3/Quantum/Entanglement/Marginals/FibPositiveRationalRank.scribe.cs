using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class FibPositiveRationalRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational rank bound in the positive-occupation Fibonacci marginal problem.",
        H("Rational rank when a pure extension exists"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-positive-rational-rank"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/Marginals/FibPositiveRationalRank."
                    + "positive_rational_rank_le_two_of_pure"),
                H("A rational extension of rank at most two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the compatible Fibonacci edge data have rational coordinates and "
                    + "positive middle occupation. If they admit a complex pure extension, "
                    + "they also admit a positive trace-one extension of rank at most two "
                    + "whose matrix entries have rational real and imaginary parts.")),
                    Paragraph(Text(
                    "A nonzero middle coupling to an occupied endpoint makes the pure "
                    + "extension rational. If the two occupied-endpoint couplings vanish, "
                    + "the only possible nonzero amplitudes are on the vacuum, the middle "
                    + "singleton and the double-endpoint word. Separate the double-endpoint "
                    + "amplitude from the other two. Each edge trace removes the coherences "
                    + "separated in this way. The surviving entries are measured populations "
                    + "and the middle-to-vacuum coherence. The two outer products give the "
                    + "rank bound."))),
                DescribeRole.Theorem))));
}
