using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteJetCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteJetCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational jets of the six-site adjacent marginal",
        H("Rational jets of the six-site adjacent marginal"),
        Blocks(
            Claim("raw", "Real polynomial readout",
                "The four complex coordinates and one real gain give ten real adjacent-marginal coordinates.", DescribeRole.Definition),
            Claim("tangentJacobian", "Tangential derivative matrix",
                "The first nine components define the square tangent matrix used at both special lifts.", DescribeRole.Definition))));

    private static DocumentBlock Claim(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitejetcoordinates-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
