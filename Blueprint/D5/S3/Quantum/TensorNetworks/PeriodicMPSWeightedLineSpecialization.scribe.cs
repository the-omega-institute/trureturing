using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSWeightedLineSpecializationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSWeightedLineSpecialization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Detecting common divisors by full-degree specialization",
        H("Detecting common divisors by full-degree specialization"),
        Blocks(
            Claim("isRelPrime_of_full_degree_specialization", "Preserving the full weighted degree of a nonzero homogeneous polynomial preserves the positive degree of every nonunit factor."),
            Claim("isWeightedHomogeneous_of_dvd", "The highest and lowest degrees after weighted scaling add under multiplication over a domain. Their equality for the product forces their equality for each factor."),
            Claim("associated_X_of_irreducible_common_pairing_dvd", "The total degree and the three pairing degrees determine each exponent vector of a common divisor. An irreducible common divisor of the three corresponding homogeneous polynomials is associated to one root coordinate."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsweightedlinespecialization-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
