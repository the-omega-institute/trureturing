using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiFiniteMeanZeroWitnessDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFiniteMeanZeroWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual mean-zero H6 source with all shifted Gamma domains and positive original and fullTheta excess.",
        H("Actual mean-zero finite physical witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-mean-zero-positive-full-theta-excess-all-gamma-domains"),
                DeclarationHandle.Create(Owner + "actual_h6_mean_zero_positive_fullTheta_excess_all_gamma_domains"),
                H("Actual mean zero with positive original and full theta excess"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exists one original "
                            + "physical H6 source F with integral over the real line of "
                            + "actualSuzukiEvenBProfile(F) equal to zero. This same F "
                            + "belongs to originalGammaFormDomain(c,F) for every real c, "
                            + "and for every x>=pi the complete physicalTerm series has "
                            + "HasSum F(x). Both literal integrals over x>pi of "
                            + "((x/pi)^6-1)*norm(F(x))^2 and "
                            + "((x/pi)^6-1)*norm(fullTheta(F,x))^2 are strictly positive.")),
                    Paragraph(Text(
                        "Two compactly supported finite features with scales 1 and "
                            + "1/4 supply the construction through finite support and "
                            + "Fourier decay. If the small "
                            + "feature already has zero actual even-B mean, choose it. "
                            + "Otherwise subtract its mean-normalized multiple from the "
                            + "large feature. The complete mean functional is linear: "
                            + "L1 tail mass and the exact even dilation identity retain "
                            + "the endpoint trace. At the large feature center the small "
                            + "feature vanishes, so cancellation cannot erase the source.")),
                    Paragraph(Text(
                        "Continuity and compact support give original H6 and the "
                            + "integrability needed by the mean and Fourier calculations. "
                            + "Finite Fourier decay and a quadratic bound for the Gamma "
                            + "weight give every constant-shift form domain of the actual "
                            + "constructed source. Each branch supplies its own complete "
                            + "same-input HasSum. Its tsum equality identifies fullTheta "
                            + "with F on x>=pi and transfers the original excess to the "
                            + "literal fullTheta excess. This existence result supplies "
                            + "no Gamma domain for an arbitrary H6 mean-zero input and "
                            + "requires no additional trace-zero premise.")),
                    Paragraph(Text(
                        "All six conclusions hold for this one constructed source. "
                            + "The mean-zero cancellation retains the endpoint trace, "
                            + "and the fullTheta positivity uses its complete HasSum "
                            + "identity. The existence result does not settle RH."))),
                DescribeRole.Theorem))));
}
