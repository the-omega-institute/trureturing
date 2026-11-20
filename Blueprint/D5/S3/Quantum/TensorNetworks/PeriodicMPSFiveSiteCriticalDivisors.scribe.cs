using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteCriticalDivisorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalDivisors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full five-site minors have no common nonunit factor",
        H("The full five-site minors have no common nonunit factor"),
        Blocks(
            Claim("relatively_prime_minors", "Full weighted degree on the certified line rules out a common nonunit factor of the multivariate Jacobian minors."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesitecriticaldivisors-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
