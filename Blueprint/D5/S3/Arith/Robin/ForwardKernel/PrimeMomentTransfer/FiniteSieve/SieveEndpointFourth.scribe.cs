using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveEndpointFourthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveEndpointFourth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth-norm stability under perturbing both interval endpoints.",
        H("Fourth-norm stability under perturbing both interval endpoints."),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sieve-interval-endpoint-norm4-bound"),
                DeclarationHandle.Create(Prefix + "sieve_interval_endpoint_norm4_bound"),
                H("A uniform modulus of endpoint continuity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume MSFinite and fix B>=1. There is C>=1 such that, for all sufficiently large real H "
                        + "and all positive Q with P<=B log H, ordered nonnegative intervals (a,b] and (c,d] "
                        + "whose corresponding endpoints differ by at most delta>=0 satisfy "
                        + "norm4(NI_(a,b]-NI_(c,d])<=C*(sqrt(delta)+H^(-1/4)). "
                        + "The constant and the eventual set of H are uniform in Q, delta and all four endpoints.")),
                    Paragraph(Text(
                        "Write each interval as the difference of two prefixes. Their difference is the signed endpoint interval "
                        + "between b and d minus the signed endpoint interval between a and c. "
                        + "Each endpoint interval has length at most delta, and changing its sign preserves the fourth norm. "
                        + "The scalar bound after division by A_H bounds each piece by C0*(sqrt(delta)+H^(-1/4)). "
                        + "Minkowski adds the two pieces, giving C=2*C0. No disjointness assumption is needed."))),
                DescribeRole.Theorem))));
}
