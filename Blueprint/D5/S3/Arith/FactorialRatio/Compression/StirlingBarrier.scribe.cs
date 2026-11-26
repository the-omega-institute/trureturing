using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Compression;

internal sealed class StirlingBarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Compression/StirlingBarrier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform finite entropy reduction for individual compact factorial products.",
        H("Stirling reduction of a single compact term"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compact-stirling-entropy-bound"),
                DeclarationHandle.Create(Prefix + "compact_stirling_entropy_bound"),
                H("An error bound uniform in the integer parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural r,s,b satisfying rb<=s, write h(u)=-u log u-(1-u)log(1-u), "
                        + "with h(0)=h(1)=0. The logarithm of the actual compact factorial term "
                        + "differs from rs(log s-1)+rb log r-s sum_{0<=i<r}h(ib/s) "
                        + "by at most 2r(log(s+1)+1). The same bound holds simultaneously "
                        + "for every legal b. It includes b=0, rb=s, s=0 and r=0.")),
                    Paragraph(Text(
                        "Every factorial argument lies between zero and s. Comparing "
                        + "log(n!) with n log n-n therefore costs at most log(s+1)+1 "
                        + "for each factorial occurrence in a factor. These remainders "
                        + "are nonnegative; two occur with positive sign and one with "
                        + "negative sign, giving the factor two in the absolute bound. "
                        + "The linear terms sum to -rs. Shifting the numerator sum "
                        + "from (i+1)b to ib leaves the boundary contribution "
                        + "(rb)log(rb)-rb log b=rb log r. Pairing ib and s-ib gives "
                        + "the binary entropy sum, including its continuous endpoints.")),
                    Paragraph(Text(
                        "At r=M+1 and s=M(M-1), division by M makes the displayed "
                        + "Stirling error O(log M). The boundary term rb log r/M "
                        + "is O(M log M), uniformly in b. Determining the best single "
                        + "term additionally requires a uniform comparison of the finite "
                        + "entropy sums with their integral and optimization over the "
                        + "closed parameter interval."))),
                DescribeRole.Theorem))));
}
