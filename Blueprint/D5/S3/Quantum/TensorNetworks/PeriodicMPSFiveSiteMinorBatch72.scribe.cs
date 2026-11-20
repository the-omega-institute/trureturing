using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteMinorBatch72Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch72";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-minor evaluations at residues 72 through 75",
        H("Critical-minor evaluations at residues 72 through 75"),
        Blocks(
            Claim("pointValues", "The displayed triangular factors check the two residual minors against their certified polynomial values."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesiteminorbatch72-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
