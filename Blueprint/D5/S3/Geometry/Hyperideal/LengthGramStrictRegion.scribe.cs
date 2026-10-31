using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramStrictRegionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/LengthGramStrictRegion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict dual/cap Lorentz region contains the realizing barycenter.",
        H("Nonempty strict dual and cap signs"),
        Blocks(
            Paragraph(Text(
                "At the coefficient barycenter, all inverse-Gram dual pairings are positive "
                + "and all original-row pairings are negative. The normalized radial lift and "
                + "the coordinate reconstruction transfer these strict signs to the realizing "
                + "hyperbolic point.")),
            Describe.Lean(
                DescribeId.Create("length-gram-strict-region-nonempty"),
                DeclarationHandle.Create(Prefix + "strictDualCapRegion_nonempty"),
                H("The strict dual/cap region is nonempty"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof consumes the strict barycenter inequalities from the shared "
                    + "radial body and derives the corresponding strict Lorentz signs."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement() => F.Disp(F.Id("strictDualCapRegionNonempty"));
}
