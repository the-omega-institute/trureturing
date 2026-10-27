using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaExplicit;

internal sealed class ExponentialStripSamplingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaExplicit/ExponentialStripSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponential damping supplies noncompact closed-strip zero sampling under logarithmic Fourier energy.",
        H("Noncompact exponential sampling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noncompact-two-family-sampling"),
                DeclarationHandle.Create(Owner + "weighted_zero_sampling_exponential"),
                H("A support-independent bound for both original sample families"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a>1/2. There is a nonnegative finite constant C_a, chosen before "
                        + "the zero configuration Z, local count constant A, and complex input h. "
                        + "Assume A>=1 and Z.N(t,t+1)<=A*log(|t|+3) for every real t, with "
                        + "the original natural multiplicities. Assume h is L1 and "
                        + "log(|s|+3)*normSq(paperFT(h,s)) is integrable on the real line. "
                        + "Set f(x)=exp(-a*|x|)*h(x). Both original families "
                        + "m(rho)*normSq(paperFT(f,gammaOf(rho))) and "
                        + "m(rho)*normSq(paperFT(f,conj(gammaOf(rho)))) are summable. "
                        + "Each sum is at most C_a*A*totalWeight times that same logarithmic "
                        + "Fourier energy of h. No support radius occurs in the constant.")),
                    Paragraph(Text(
                        "For |beta|<=1/2, split exp(-a*|x|-beta*x) at zero and compute its "
                        + "literal paper transform as 2*a/(a^2+(t+i*beta)^2). The normalized "
                        + "Cauchy kernel is K_a(z)=(a/pi)/(a^2+z^2). With "
                        + "m=min(1,a^2-1/4)>0 and C=a/(pi*m), the real part of the "
                        + "denominator bounds its norm below by m*(1+Re(z)^2), hence "
                        + "norm(K_a(z))<=C/(1+Re(z)^2) throughout the closed half strip. "
                        + "Fourier inversion has exponent exp(-i*t*x) and supplies the "
                        + "tilted damping exactly. The existing L1 Fubini argument gives "
                        + "paperFT(f,t+i*beta)=integral K_a(t-s+i*beta)*paperFT(h,s) ds. "
                        + "Weighted Cauchy-Schwarz and the existing original zero counting "
                        + "consumer give C_a=8*pi*C^2 for both sample families.")),
                    Paragraph(Text(
                        "The repository's zetaZeroConfig_local_count supplies A for the "
                        + "actual zeta zero carrier, without assuming RH or replacing "
                        + "multiplicities. The input may be noncompact, complex, and uneven. "
                        + "This is an upper sampling estimate. The logarithmic Fourier "
                        + "energy is a joint domain requirement and is not inferred from "
                        + "the original H6 physical moment or from the Gamma form domain. "
                        + "For an intended actual even-B profile, one must separately "
                        + "supply these hypotheses for h=exp(a*|x|)*f. This result neither "
                        + "changes the signed zero pairing to a modulus square nor proves "
                        + "a global positivity statement or RH."))),
                DescribeRole.Theorem))));
}
