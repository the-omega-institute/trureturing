using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSitePencilsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSitePencils";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The triplet and singlet coordinates of the observed four-site Gram",
        H("The triplet and singlet coordinates of the observed four-site Gram"),
        Blocks(
            Claim("swapCoordinates_cyclic", "The swap-basis decomposition",
                "A binary cyclic four-site flattening splits into a triplet and a singlet. In the rational swap basis the singlet is the middle diagonal of the triplet minus twice its corner."),
            Claim("triplet_partner_of_product", "The adjugate supplies the partner",
                "For a nonzero product proportional to the observed triplet, the right polynomial factor is proportional to the adjugate of the left polynomial factor."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-pencils-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
