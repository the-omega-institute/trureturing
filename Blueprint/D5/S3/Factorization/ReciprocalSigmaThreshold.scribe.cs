using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class ReciprocalSigmaThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/ReciprocalSigmaThreshold.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/krizek2015a265714");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal sigma sums and the first crossing of every positive integer threshold.",
        H("Reciprocal Sigma Threshold Minima"),
        Blocks(
            Describe.Lean(DescribeId.Create("reciprocal-sigma-sum"),
                DeclarationHandle.Create(Prefix + "g"), H("Exact divisor sum"),
                StatementSource.FromLean(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a positive integer k, g(k) is the rational sum of "
                    + "1/sigma(d) over every positive divisor d of k. Here sigma(d) is the sum "
                    + "of every positive divisor of d. The value at zero only totalizes the definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("common-positive-minimum"),
                DeclarationHandle.Create(Prefix + "claim"), H("The two positive sets"),
                StatementSource.FromLean(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every positive integer r there is a common least "
                    + "element of the positive integers with floor(g(k)) equal to r and of "
                    + "the positive integers with g(k) at least r. Membership of that common "
                    + "element states nonemptiness of both sets. There is no upper bound on r or k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threshold-minima"),
                DeclarationHandle.Create(Prefix + "result"), H("A common least element"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The prime divisor terms already force g to be unbounded, "
                    + "by divergence of the sum of reciprocal primes. Multiplicativity bounds g(m) "
                    + "by the largest prime divisor P. Removing one copy of P increases the local "
                    + "factor by at most 1+1/(P+1) in the reverse direction. At the first threshold "
                    + "crossing this gives r <= g(m) < r+1. The argument includes r=1 and k=1. "
                    + "The separate integrality question and proposed numerical minima are outside "
                    + "this statement."))), DescribeRole.Theorem))));
}
