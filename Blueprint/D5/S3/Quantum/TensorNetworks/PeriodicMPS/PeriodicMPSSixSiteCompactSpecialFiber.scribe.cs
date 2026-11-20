using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCompactSpecialFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCompactSpecialFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-point compact six-site marginal fiber",
        H("The two-point compact six-site marginal fiber"),
        Blocks(
            Claim("observation_eq_target_iff", "Exact two-point classification",
                "The compact fiber of the selected normalized two-site observation consists of two ordinary lifts. Each lift has an actual periodic realization.", DescribeRole.Theorem))));

    private static DocumentBlock Claim(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitecompactspecialfiber-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
