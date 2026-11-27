using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CauchyPairEnergyDocument : IScribeDocumentDefinition
{
    private const string ModulePath = "D5/S3/Fourier/Concentration/CauchyPairEnergy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Localization of the Cauchy-smoothed energy gives a finite Lorentz pair-sum lower bound.",
        H("Cauchy energy and a Lorentz pair sum"),
        Blocks(
            Describe.Lean(DescribeId.Create("cauchy-mass-buffer-interval"),
                DeclarationHandle.Create(ModulePath + ".cauchy_mass_buffer_interval"),
                H("Mass in an enlarged interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a unit-scale Cauchy density be centered at x in [0,Y] and let R > 0. Its mass in [-R,Y+R] is at least 1 - 2/(pi R). The enlarged interval contains [x-R,x+R]. Its mass on that subinterval is 2 arctan(R)/pi, and arctan(1/R) <= 1/R bounds the omitted mass."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lorentz-pair-lower-bound"),
                DeclarationHandle.Create(ModulePath + ".lorentz_pair_lower_bound"),
                H("Energy controls the magnitude of the total coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take a finite family of locations x_j in [0,Y] with Y >= 0, complex coefficients a_j, and R > 0. Write S = sum a_j and N = sum |a_j|. The ordered-pair sum of Re(a_i conjugate(a_j)) times 4/(4+(x_i-x_j)^2) is at least 2 pi/(Y+2R) times the square of max(|S|-2N/(pi R),0).")),
                    Paragraph(Text("The sum equals 2 pi times the squared L2 norm of the combination of translated unit-scale Cauchy densities. The probability convolution identity gives the kernel of scale two. On [-R,Y+R], the integral of the smoothed combination differs from S by at most 2N/(pi R). Cauchy-Schwarz converts this magnitude bound into the stated energy bound."))),
                DescribeRole.Theorem))));
}
