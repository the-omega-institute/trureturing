using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramStrictOpenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramStrictOpen.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict dual/cap Lorentz sign region is open in hyperbolic three-space.",
        H("Openness of strict dual and cap signs"),
        Blocks(
            Paragraph(Text(
                "The hyperbolic lift is continuous in upper-half-space coordinates. Each "
                + "dual and original-row Lorentz pairing is therefore continuous, and the "
                + "finite intersection of their strict sign sets is open.")),
            Describe.Lean(
                DescribeId.Create("length-gram-strict-open"),
                DeclarationHandle.Create(Prefix + "strictDualCapRegion_isOpen"),
                H("The strict dual/cap region is open"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof expands the lift coordinates, proves continuity of the lift, "
                    + "and applies finite intersection to the eight strict inequalities."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement() => F.Disp(F.Id("strictDualCapRegionIsOpen"));
}
