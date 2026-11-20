using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteMinorBatch64Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch64";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-minor evaluations at residues 64 through 71",
        H("Critical-minor evaluations at residues 64 through 71"),
        Blocks(
            Claim("pointValues", "The displayed triangular factors check the two residual minors against their certified polynomial values."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesiteminorbatch64-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
