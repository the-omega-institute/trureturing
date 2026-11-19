using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteSpecialFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteSpecialFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A classified five-site periodic two-site marginal fiber",
        H("A classified five-site periodic two-site marginal fiber"),
        Blocks(
            Claim("supported_of_corner_zero", "Support on three necklaces",
                "A zero probability for two adjacent ones makes the corresponding flattening row vanish by positivity."),
            Claim("special_fiber_classification", "Classification up to unit phase",
                "Fixing the separated-pair amplitude to one leaves two possibilities for the purely imaginary singleton amplitude."),
            Claim("special_fiber_realized", "Actual periodic realizations",
                "Both necklace vectors are realized by the trace-aligned quadratic map and a common fifth-root scaling."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesitespecialfiber-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
