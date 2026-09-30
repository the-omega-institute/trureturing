using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class HeatProjectedDivergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/HeatProjectedDivergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full Fourier heat-divergence multiplier has an inverse-square-root time bound.",
        H("Projected heat divergence on the full lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("heat-projected-divergence-operator"),
                DeclarationHandle.Create(Prefix + "heat_projected_divergence_operator"),
                H("Projected heat-divergence operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive viscosity nu and positive elapsed time r, use every frequency in the two-dimensional integer lattice. The source is the square-summable space of complex two-by-two tensor coefficients, and the target is the square-summable space of complex two-vector coefficients. Both are unweighted lp spaces; in the H2 application, their inputs are already multiplied by one plus the squared frequency. The theorem constructs a continuous complex-linear operator whose coefficient at k is the heat factor exp(-nu*r*|k|^2) times the imaginary unit, the Leray orthogonal projection, and contraction of the tensor at k with the frequency vector.")),
                    Paragraph(Text("For every tensor input, the output norm is at most (nu*r)^(-1/2) times its input norm. This includes the zero mode, where the frequency contraction vanishes. The proof bounds contraction by |k|, uses that the projection is an orthogonal contraction, then applies the Gaussian inequality |k| exp(-nu*r*|k|^2) <= (nu*r)^(-1/2) uniformly over the full lattice. The coordinate operators assemble into a bounded lp map.")),
                    Paragraph(Text("This is a fixed positive-time multiplier estimate. It does not construct a time integral, prove continuity at r=0, build a mild path, or prove the original Recovery 25.3 or 25.4 conclusions."))),
                DescribeRole.Theorem))));
}
