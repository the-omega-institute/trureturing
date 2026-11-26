using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSWeightedLineSpecializationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSWeightedLineSpecialization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Detecting common divisors by full-degree specialization",
        H("Detecting common divisors by full-degree specialization"),
        Blocks(
            Claim("isRelPrime_of_full_degree_specialization", "Preserving the full weighted degree of a nonzero homogeneous polynomial preserves the positive degree of every nonunit factor."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsweightedlinespecialization-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
