using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSWeightedHomogeneousDivisorsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSWeightedHomogeneousDivisors";
    private const string Title = "Weighted homogeneous divisors and root pairings";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsweightedlinespecialization-isweightedhomogeneous-of-dvd"),
                DeclarationHandle.Create(Module + ".isWeightedHomogeneous_of_dvd"),
                H("Divisors inherit weighted homogeneity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The highest and lowest degrees after weighted scaling add under multiplication over a domain. Their equality for the product forces equality for each factor."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsweightedlinespecialization-associated-x-of-irreducible-common-pairing-dvd"),
                DeclarationHandle.Create(Module + ".associated_X_of_irreducible_common_pairing_dvd"),
                H("An irreducible common divisor is associated to a root coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total degree and the three pairing degrees determine each exponent vector. Over a field, an irreducible common divisor of the three homogeneous polynomials is associated to one root coordinate."))),
                DescribeRole.Theorem))));
}
