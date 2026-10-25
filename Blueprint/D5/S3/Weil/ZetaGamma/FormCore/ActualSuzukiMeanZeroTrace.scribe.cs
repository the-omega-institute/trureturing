// SOURCE_ONLY.UNCOMPILED. Prepared source; no Scribe emission, native proof,
// validated registration, required-check acceptance or publication is claimed.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiMeanZeroTraceDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SOURCE_ONLY.UNCOMPILED: original-source mean-zero moments and actual Gamma-profile domains.",
        H("The same original source and its complete theta transform"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-h6-mean-zero-physical-moment-bounds"),
                DeclarationHandle.Create(Owner + "actual_h6_mean_zero_physical_moment_bounds"),
                H("Both actual Laplace moments, both L1 domains and the product estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every original function F:R->C satisfying originalPhysicalH6 F, retain the literal complete theta transform fullTheta F and its actualGammaProfile F. Define B_F(t)=actualGammaProfile F(t)-(3/2)*rightExponentialTail(5/4,actualGammaProfile F)(t), and the actual even profile by B_F(2*abs(r)). The additional hypothesis is exactly that this even profile has zero integral over the whole real line. No endpoint trace is assumed to vanish.")),
                    Paragraph(Text("Let L0 be the integral over t>0 of exp(-5*t/4)*actualGammaProfile F(t), let Lt be the integral over t>0 of t*exp(-5*t/4)*actualGammaProfile F(t), and let D be the integral over x>pi of ((x/pi)^6-1)*norm(fullTheta F(x))^2. Both complex integrands defining L0 and Lt are genuinely L1 on t>0. The three bounds are norm(L0)^2 <= (3/1000)*pi^(7/2)*D, norm(Lt)^2 <= (3/160)*pi^(7/2)*D, and norm(L0)*norm(Lt) <= (3/400)*pi^(7/2)*D. These five clauses form one law with the complete F,hF,hmean telescope.")),
                    Paragraph(Text("The private L1 coordinate supplier computes the actual profile mass and the endpoint tail in physical coordinates. Its literal endpoint identity remains on the live proof path of the mean-zero moment identity; removing the unused public extraction does not remove this supplier. The actual even-profile mass identity converts hmean into 5*L0 = integral((x^(5/4)-pi^(5/4))*fullTheta F(x),x>pi). A separate logarithmic change of variables identifies Lt with pi^(5/4) times the physical log moment. Apply actual_h6_weighted_physical_moments to fullTheta F after its actual H6 supplier, and combine the two squared estimates to obtain the product bound.")),
                    Paragraph(Text("The faithful Reg source observes only the literal value of let D, retaining both L1 clauses and all three bounds. Constant -1 is a rejected whole-family realization, contradicted at the genuine zero input. Actual dependence requires positive excess of fullTheta F on a valid original mean-zero input; positive original-F excess alone is insufficient. A separate same-compilation-unit constructive witness proposal pays this equality using the actual HasSum for its chosen F. That proposal, this theorem source, the selector and the Reg terms are uncompiled, and no validated registration is claimed.")),
                    Paragraph(Text("This is a quantitative dependency for the stronger original-F Gamma lower comparison. That comparison keeps its original source F, actual mean-zero hypothesis and separately required Gamma form domain. This moment law does not derive that domain from H6, does not replace original excess by transformed excess in the comparison, and does not settle RH. No literature novelty is claimed for this synthesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-h6-gamma-profile-l1-l2"),
                DeclarationHandle.Create(Owner + "actual_h6_gamma_profile_l1_l2"),
                H("Actual positive-half-line profile L1 and L2 from the original H6 source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every original F:R->C satisfying originalPhysicalH6 F, the actualGammaProfile F is IntegrableOn on Ioi 0 and belongs to MemLp 2 for volume restricted to Ioi 0. Both domain conclusions belong to the same full law. This law has no mean-zero premise and no assumed convergence or desired domain conclusion.")),
                    Paragraph(Text("The L1 clause reuses the private physical coordinate supplier. For L2, the actual fullTheta H6 supplier makes x^(7/2)*norm(fullTheta F(x))^2 integrable on x>pi by domination with its sixth moment, since pi>1. The literal substitution x=pi*exp(t), with its Jacobian and the exact exponent 9/4 in actualGammaProfile, gives the square-norm integral on t>0. The MemLp conclusion follows from genuine integrability of that square norm.")),
                    Paragraph(Text("The faithful Reg source observes the actual profile function in the first L1 clause and retains the second MemLp clause literally. Constant profile 1 is rejected at the genuine zero H6 input because Ioi 0 has infinite volume. The existing full finite-Gamma-energy theorem at K=2 and B=0 supplies a genuine H6 input with positive actual Gamma energy, so its actual profile differs from the zero input's profile. These are complete-source sensitivity and dependence proposals, with native terms and raw selector binding still unverified.")),
                    Paragraph(Text("Profile L1/L2 does not assert integrability of the additional Gamma-weighted Fourier form. The stronger original-F comparison still needs its originalGammaFormDomain hypothesis. The actual complete theta profile and original source domain remain unchanged. Every artifact in this preparation is SOURCE_ONLY.UNCOMPILED."))),
                DescribeRole.Theorem))));
}
