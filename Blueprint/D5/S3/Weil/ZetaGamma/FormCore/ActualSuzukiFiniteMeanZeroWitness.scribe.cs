using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiFiniteMeanZeroWitnessDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFiniteMeanZeroWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual mean-zero H6 sources with all Gamma domains and raw sixth-moment ratios arbitrarily close to one.",
        H("Actual mean-zero finite physical witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-mean-zero-arbitrarily-small-raw-sixth-ratio"),
                DeclarationHandle.Create(Owner + "actual_h6_mean_zero_arbitrarily_small_raw_sixth_ratio"),
                H("Raw sixth-moment ratio arbitrarily close to one with actual mean zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real r>1 there exists one originalPhysicalH6 source F "
                            + "with actual even-B mean zero, every shifted Gamma form domain "
                            + "and the complete same-source physicalTerm HasSum. Its physical "
                            + "mass D is positive and its literal raw ratio N/(pi^6 D) lies "
                            + "strictly between 1 and r, where N is the integral over x>pi "
                            + "of x^6 norm(F(x))^2 and D is the integral of norm(F(x))^2.")),
                    Paragraph(Text(
                        "The existing two-feature construction is parameterized by scales "
                            + "kappa and kappa/4. Their disjoint logarithmic supports preserve "
                            + "a nonzero center after exact actual-mean cancellation. Compact "
                            + "support gives original H6, while the actual Fourier decay gives "
                            + "each shifted Gamma domain. Support below pi exp(3 kappa/4) "
                            + "bounds the normalized sixth moment by exp(9 kappa/2) times D. "
                            + "Taking a small positive kappa yields the asserted strict cap.")),
                    Paragraph(Text(
                        "The Gamma energies are finite for each constructed input; no "
                            + "uniform energy bound as kappa tends to zero is asserted. This "
                            + "theorem concerns exactly the stated repository H6, trace and "
                            + "Gamma-domain predicates. It does not identify the full literary "
                            + "Suzuki domain, prove a sign for the complete Weil form or settle RH."))),
                DescribeRole.Theorem),
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
                        "The kappa=1 specialization uses finite features with scales 1 and "
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
