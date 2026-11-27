using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteMarginalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMarginal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No-adjacent-ones support at six sites",
        H("No-adjacent-ones support at six sites"),
        Blocks(
            Claim("flatten_gram", "Literal two-site observation",
                "The necklace flattening computes the adjacent two-site density of the full periodic amplitude, with the correct multiplicities."),
            Claim("exists_nilpotentRay", "Nilpotent representation",
                "Zero adjacent-ones weight and nonzero singleton weight force the second tensor to be traceless and singular. The alternating triple amplitude fixes the scalar chart."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitemarginal-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
