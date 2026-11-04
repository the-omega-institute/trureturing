using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramDualImageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramDualImage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The realizing hyperbolic range is exactly the dual/cap Lorentz sign region.",
        H("Dual and cap sign characterization of the realizing range"),
        Blocks(
            Paragraph(Text(
                "For a realizing row matrix M, the inverse-Gram dual vectors read off "
                + "the four coefficient coordinates, while pairing with the original rows "
                + "reads off the four Gram inequalities. The determinant identity makes M "
                + "invertible, so every hyperbolic lift satisfying these eight signs has a "
                + "unique coefficient vector. The normalized radial image theorem then puts "
                + "that vector back in the cut body and reconstructs the point.")),
            Describe.Lean(
                DescribeId.Create("length-gram-dual-image-range"),
                DeclarationHandle.Create(Prefix + "range_eq_dualCapRegion"),
                H("The range equals the dual/cap sign region"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward direction uses the exact lift of the coordinate witness. "
                    + "For the reverse direction, the inverse matrix recovers coefficients "
                    + "from an arbitrary lift; the negative unit quadratic and the two sign "
                    + "families are then precisely the hypotheses of the radial image theorem."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement() => F.Disp(F.Id("rangeEqDualCapRegion"));
}
