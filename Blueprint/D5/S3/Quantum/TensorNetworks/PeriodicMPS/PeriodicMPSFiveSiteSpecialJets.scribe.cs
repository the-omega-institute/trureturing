using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteSpecialJetsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialJets";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact jets at the four special lifts",
        H("Exact jets at the four special lifts"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitespecialjets-result"),
            DeclarationHandle.Create(Module + ".exact_jet_coefficients"),
            H("Exact jets at the four special lifts"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Rational Taylor coefficients certify the tangent, quadratic and cubic data at all four special lifts."))),
            DescribeRole.Theorem))));
}
