using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class PlanarSublevelSandwichDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/PlanarSublevelSandwich";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An invertible derivative gives smooth bounds for a local planar sublevel.",
        H("Smooth bounds near a regular planar zero"),
        Blocks(Describe.Lean(
            DescribeId.Create("smooth-local-ellipse-sandwich"),
            DeclarationHandle.Create(Owner + ".smooth_local_ellipse_sandwich"),
            H("Smooth tests for the localized sublevel"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let f map the Euclidean plane to itself, with f(z) = 0 and invertible "
                    + "Fréchet derivative A at z. Choose 0 < η < 1 and two radii ρ and σ with "
                    + "0 < ρ < (1+η)⁻¹ and (1−η)⁻¹ < σ.")),
                Paragraph(Text(
                    "There are a chart radius r > 0 and smooth compactly supported real tests "
                    + "lower and upper. The integral of lower is at least πρ²/|det A| and "
                    + "the integral of upper is at most πσ²/|det A|.")),
                Paragraph(Text(
                    "For every ε > 0 with ε‖A⁻¹‖/(1+η) < r, these same tests bound the "
                    + "indicator of ε‖u‖ < r and ‖f(z+εu)‖ < ε pointwise at every u. "
                    + "The norm of A⁻¹ is its operator norm.")),
                Paragraph(Text(
                    "The derivative approximation compares ‖f(z+h)‖ with ‖Ah‖ up to factors "
                    + "1−η and 1+η in the chart. Pulling radial bump functions back along A "
                    + "gives the two tests. The determinant formula for measure under an invertible "
                    + "linear map converts their inner and outer disk areas into integral bounds.")),
                Paragraph(Text(
                    "A periodic counting application also needs neighborhoods of all relevant "
                    + "zeros, control on their complement, and bounds on the sampling modes."))),
            DescribeRole.Theorem))));
}
