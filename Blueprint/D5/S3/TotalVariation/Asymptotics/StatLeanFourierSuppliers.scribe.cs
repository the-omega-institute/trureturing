using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class StatLeanFourierSuppliersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian Hermite integration evaluates the signed first Edgeworth density and its characteristic function.",
        H("Gaussian Hermite and Edgeworth identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("edgeworth-density-integral"),
                DeclarationHandle.Create(Prefix + "densityCDF_edgeworthDensity"),
                H("Integrating the first Hermite correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The first Edgeworth density is the standard Gaussian density multiplied by one plus a cubic Hermite correction. Its integral over a lower half-line is the Gaussian distribution function plus the quadratic Hermite correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edgeworth-density-fourier"),
                DeclarationHandle.Create(Prefix + "charFunDensity_edgeworthDensity"),
                H("The characteristic function of the signed Edgeworth density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Gaussian integration by parts evaluates the cubic Hermite Fourier integral. The result is the Gaussian characteristic function multiplied by its first cubic correction, with the same coefficient as in the density."))),
                DescribeRole.Theorem))));
}
