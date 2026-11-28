using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class PlanarWindowSamplingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/PlanarWindowSampling";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier mode estimates control weighted sampling of small periodic windows.",
        H("Sampling smooth planar windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("character"),
                DeclarationHandle.Create(Owner + ".character"),
                H("Planar torus character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an integer frequency m and a planar representative p, the character is "
                    + "exp(2πi⟨p,m⟩). The factor 2π fixes the period of each coordinate to one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compact-window-sampling"),
                DeclarationHandle.Create(Owner + ".compact_window_sampling"),
                H("Uniform error for a rescaled smooth window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a smooth compactly supported complex function f on the Euclidean plane. "
                        + "There is a nonnegative constant K depending on f. For 0 < ε ≤ 1 and any "
                        + "center, scale f by ε and sum its integer translates. Take any finite sample "
                        + "of planar representatives with nonnegative real weights totaling one. "
                        + "For a positive integer J and nonnegative reals c and d, suppose that each "
                        + "nonzero mode of radius k ≤ J has weighted character average of norm at most "
                        + "c + dk². The radius is the maximum of the two absolute coordinates.")),
                    Paragraph(Text(
                        "The norm of the difference between the weighted average of the periodized "
                        + "window and ε² times the plane integral of f is at most "
                        + "27Kc + 27Kd/ε² + 2K/(ε⁴J⁴).")),
                    Paragraph(Text(
                        "The change of variables gives an ε² factor in each Fourier coefficient. "
                        + "Schwartz decay bounds the remaining factor by a constant times "
                        + "(1+εk)⁻⁸, uniformly over the center. Compact support makes the "
                        + "integer translates locally finite, so coordinate Poisson summation "
                        + "identifies the periodization with its absolutely convergent series. "
                        + "An enclosing lattice square and the sixth-power tail bound control the "
                        + "absolute coefficient sum and its second moment. Unit-modulus characters "
                        + "and the normalization of the weights bound the discarded-mode averages by one.")),
                    Paragraph(Text(
                        "For a sample of zero ordinates, the bounds on the retained modes are "
                        + "arithmetic inputs. Counts for an indicator window also require upper and "
                        + "lower approximations of that indicator."))),
                DescribeRole.Theorem))));
}
