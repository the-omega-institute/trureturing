using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class CapWeightedEnergySharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit integrable scalar family proves optimality of the abstract cap and weighted-energy coefficient.",
        H("Attaining the cap and energy bound"),
        Blocks(
            Paragraph(Text("Fix real 0<alpha<1. For B>=0 and cutoff a>0, take w(t)=B for t<=a and w(t)=B(a/t)^(alpha+1) for t>a. Only the positive half-line is integrated. The profile is measurable, nonnegative and bounded by B there. The following statements include actual integrability; they do not rely on a nonintegrable Bochner integral being assigned zero.")),
            Describe.Lean(
                DescribeId.Create("cap-energy-scalar-extremizer"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer"),
                H("The cap and free-optimizer profile"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The definition is total on all real parameters. Its analytic interpretation here uses 0<alpha<1, B>=0 and a>0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cap-energy-extremizer-moments"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.extremizer_admissible_and_moments"),
                H("Admissibility and both exact moments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real alpha,B,a with 0<alpha<1, B>=0 and a>0, this profile is almost everywhere strongly measurable on (0,infinity), its norm is at most B almost everywhere, its energy t times norm(w(t)) squared is integrable with integral B^2 a^2(alpha+1)/(2alpha), and t^(-alpha)w(t) is integrable with integral B a^(1-alpha)(1/(1-alpha)+1/(2alpha)). The proof splits at a and uses the exact power integrals already supplied by CapWeightedEnergy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cap-energy-coefficient-optimal"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/CapWeightedEnergySharpness.sharp_constant_le_of_uniform_bound"),
                H("No smaller uniform coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real alpha,C with 0<alpha<1, suppose the norm bound C B^alpha delta^((1-alpha)/2) holds for every real-valued almost everywhere strongly measurable w on (0,infinity), every B>=0 and delta>=0, whenever its norm is bounded by B almost everywhere and its actual integrable weighted energy has integral at most delta. Then sharpConstant(alpha)<=C. This lower bound already follows from the scalar profile B=a=1 and its exact moments. Together with the Banach-space upper bound, it proves that coefficient is optimal for the abstract class.")),
                    Paragraph(Text("These are classical extremal integral calculations. No literature novelty is asserted. Sharpness in the whole abstract class does not establish that an actual modular resolvent difference, or an actual Petz recovery channel, realizes the same profile or the same optimal constant."))),
                DescribeRole.Theorem))));
}
