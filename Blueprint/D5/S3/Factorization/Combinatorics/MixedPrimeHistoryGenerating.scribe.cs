using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MixedPrimeHistoryGeneratingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed Prime History Generating Polynomials.",
        H("Mixed Prime History Generating Polynomials"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixedprimehistorygenerating-mixed-coefficient"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.mixed_coefficient"),
                H("Coefficients count histories of a fixed length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Start with the polynomial z. At each step, sum over primes q at most J, "
                    + "adding both z to the power q times the previous polynomial and the previous "
                    + "polynomial evaluated at z to the power q. Retain exactly degrees one through J. "
                    + "For every natural length k and every n between one and J, the coefficient of "
                    + "degree n in the kth iterate is the number of typed prime histories of length k "
                    + "ending at n. Addition and multiplication contribute separately, including "
                    + "when they lead to the same endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixedprimehistorygenerating-sharp-length-bound"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating.sharp_length_bound"),
                H("The endpoint bounds the history length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every nonempty typed prime history starts at one and ends at an integer "
                    + "at least twice its length. The first letter reaches at least two. Every "
                    + "subsequent addition increases the state by a prime at least two, while "
                    + "multiplication by a prime increases a state at least two by at least two. "
                    + "Consequently, a history ending at n has length at most the integer part "
                    + "of n divided by two."))),
                DescribeRole.Theorem))));
}
