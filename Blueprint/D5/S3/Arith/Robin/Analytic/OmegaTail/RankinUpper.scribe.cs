using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class RankinUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second distinct-prime threshold admits an upper exponent of order P divided by log(P) to the power 3/2.",
        H("Sharp Rankin upper bound at the second threshold"),
        Blocks(
            Describe.Lean(DescribeId.Create("sharp-upper-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.sharp_upper_bound"),
                H("Upper bound for every sufficiently large real cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive real epsilon and all sufficiently large real P, "
                        + "the count at exp(P) is at most exp((2*pi/sqrt(3) + epsilon)*Z(P)), where "
                        + "Z(P) = P/log(P)^(3/2). The count uses the strict second-order threshold "
                        + "P/log(P) + P/log(P)^2 and includes the case of a zero count.")),
                    Paragraph(Text("Put c = pi/(2*sqrt(3)), s = c*log(P)^(1/2), and z = P^s. "
                        + "For each prime at most exp(P), split its logarithmic factor into the softplus weight "
                        + "at its absolute logarithmic distance from P and the term s*(log(P) - log(p)) "
                        + "supported on primes at most P. Summing these latter terms gives "
                        + "s*(pi(P)*log(P) - theta(P)). Combining with the Rankin prefactor gives "
                        + "s times the continuous reserve B0(P). The rounded reserve Bk(P) has the same leading limit.")),
                    Paragraph(Text("The finite sum of nonnegative softplus weights is bounded by the summable "
                        + "total over primes. On the scale Z(P), the continuous reserve term tends to 2*c "
                        + "and the softplus sum tends to (pi^2/6)/c. The logarithmic correction from the "
                        + "p-series in the Rankin majorant is bounded for s at least two, so its ratio to Z(P) "
                        + "tends to zero. The two leading coefficients sum to 2*pi/sqrt(3).")),
                    Paragraph(Text("This is the bound of Proposition 7.5 in the theory of the LCM-power "
                        + "Robin kappa threshold."))),
                DescribeRole.Theorem))));
}
