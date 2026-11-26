using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class LogPowerExchangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squarefree prime-exchange families and their entropy at logarithmic power scales.",
        H("Prime exchange at logarithmic power scales"), Blocks(
            Describe.Lean(DescribeId.Create("log-power-grid-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/LogPowerExchange.log_power_grid_lower"),
                H("Squarefree outputs from signed bins with a strict reserve"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a strictly increasing finite grid t starting at zero, with bin widths delta(i) and densities q(i) strictly between zero and one. " +
                        "For positive C and a, use the internal scale s = C (log P)^a and the diverging count scale W = (P/log P)/s. " +
                        "Assume that the full donor and recipient bin sizes divided by W each tend to delta(i). " +
                        "Assume that the reserve divided by W/s tends to B and that twice the sum of t(i+1) delta(i) q(i) is strictly below B.")),
                    Paragraph(Text(
                        "For all sufficiently large P, the supplied base must consist of primes up to P, contain all donor bins, and have log sum at most P minus the reserve. " +
                        "Remove and add h(i) primes independently in the signed bins, where h(i) is the floor of q(i) times the smaller bin size. " +
                        "The normalized choice sizes tend to delta(i) q(i), so the exchange cost eventually fits strictly within the reserve. " +
                        "The original pointwise fixed-grid exchange gives the resulting family of positive squarefree integers strictly below exp(P), each with exactly as many distinct prime factors as the base. " +
                        "The family is nonempty and has cardinality equal to the product over i of the two binomial coefficients choosing h(i) from the full signed bin sizes.")),
                    Paragraph(Text(
                        "The log of this cardinality is eventually at least W times twice the sum of delta(i) times the binary entropy of q(i), with any positive error subtracted from the coefficient. " +
                        "For the lower-bound step of Proposition 7.9, use a = (r-1)/2, C = (1+eta) pi/sqrt(6 r!), and the base and reserve from far deletion. " +
                        "The logistic grid gives admissible costs and entropies, and the threshold comparison uses the cardinality of the supplied base."))),
                DescribeRole.Theorem))));
}
