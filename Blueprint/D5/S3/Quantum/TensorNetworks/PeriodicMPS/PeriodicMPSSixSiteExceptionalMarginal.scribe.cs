using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteExceptionalMarginalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteExceptionalMarginal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site exceptional rays and the special marginal",
        H("Six-site exceptional rays and the special marginal"),
        Blocks(
            Claim("firstChart_difference_eq_zero", "First trace chart",
                "With zero adjacent-ones weight, an exceptional amplitude has identical singleton diagonal and exchange entries."),
            Claim("secondChart_corner_ne_zero", "Second trace chart",
                "Every nonzero exceptional amplitude has nonzero adjacent-ones weight in the swapped chart."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsiteexceptionalmarginal-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
