using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class MildPathVelocityPressureRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/MildPathVelocityPressureRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original mild Fourier path has jointly smooth velocity and pressure reconstructions on the full closed interval.",
        H("Mild Path Velocity and Pressure Regularity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mild-path-velocity-pressure-contdiff"),
                DeclarationHandle.Create(Prefix + "mild_path_velocity_pressure_contdiff"),
                H("Joint smoothness of velocity and pressure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive real numbers nu and tau. Frequencies range over the full lattice Z x Z. Let V be the complex Euclidean space of two components and let H be the square-summable V-valued coefficient space. For a frequency k, rho is the sum of the squares of its coordinates, kappa is the corresponding vector, P is the orthogonal projection away from the complex span of kappa, w is the grade weight, and dec divides a coefficient by that weight. The bilinear coefficient expression N is the imaginary unit times P applied to the lattice convolution with the kappa contraction.")),
                    Paragraph(Text("For a continuous coefficient path x2 on the closed interval from zero to tau, set a t k to x2 t k divided by one plus rho k. Assume the zero mode, conjugate symmetry, divergence constraint, initial weighted summability, and the coefficientwise mild identity with viscosity nu on the same interval. The pressure coefficient pc is zero at the zero frequency and otherwise is the negative kappa contraction of the convolution of a divided by rho.")),
                    Paragraph(Text("Let character be the complex Fourier character on the two real spatial coordinates. The velocity map u takes the real part of the componentwise Fourier synthesis of a, and the pressure map p takes the real part of the Fourier synthesis of pc. Both maps are real C-infinity on the product of the original closed time interval with the full spatial space Fin 2 -> R.")),
                    Paragraph(Text("The weighted convolution estimate supplies the required fractional weighted coefficient paths and the continuous bilinear pressure map. The finite-dimensional multiplier given by the negative kappa contraction divided by rho is bounded away from the zero mode, while the zero branch is retained exactly. Joint Fourier synthesis at every finite order then gives smoothness of the velocity and pressure series, with the literal coefficient series identified on the full lattice and at both endpoints of the unchanged interval."))),
                DescribeRole.Theorem))));
}
