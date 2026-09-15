using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MixedPrimeHistoryCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed Prime History Counts.",
        H("Mixed Prime History Counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixedprimehistorycount-reachable-finite"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.reachable_finite"),
                H("Reachability and finite fibres"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Starting at one, each letter adds or multiplies by its labelled prime. "
                    + "Every positive integer is reached by at least one finite word. Every step "
                    + "strictly increases the state, bounding both word length and prime labels "
                    + "at a fixed endpoint, so only finitely many such words exist."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixedprimehistorycount-history-recurrence"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.history_recurrence"),
                H("Counting by the last letter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an endpoint n at least two, each history has a unique last letter. "
                    + "An additive prime q is smaller than n and leaves a predecessor ending at n minus q. "
                    + "A multiplicative prime q divides n and leaves a predecessor ending at n divided by q. "
                    + "Summing these finite predecessor counts gives the total. The two typed letters "
                    + "remain distinct even when their numerical actions agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixedprimehistorycount-length-recurrence"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount.length_recurrence"),
                H("Counting histories of a fixed length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive length k and endpoint n at least two, deleting the last letter "
                    + "leaves length k minus one. The same additive and multiplicative predecessor "
                    + "partition therefore gives the recurrence for histories of exactly length k. "
                    + "The empty word starts and ends at one and provides the length zero convention."))),
                DescribeRole.Theorem))));
}
