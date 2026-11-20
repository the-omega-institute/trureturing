using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteWeightedMinorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteWeightedMinors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted degree of the five-site Jacobian minors",
        H("Weighted degree of the five-site Jacobian minors"),
        Blocks(
            Claim("symbolicMinor_weight", "Deleting the column of either selected trace variable gives a determinant of weighted degree 75."),
            Claim("evaluated_symbolicMinor", "Evaluating the symbolic determinant agrees with the derivative computed using dual numbers."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesiteweightedminors-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
