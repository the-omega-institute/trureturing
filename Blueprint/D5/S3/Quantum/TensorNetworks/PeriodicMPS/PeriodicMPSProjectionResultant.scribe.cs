using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSProjectionResultantDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSProjectionResultant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Resultants for relatively prime polynomials",
        H("Resultants for relatively prime polynomials"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsprojectionresultant-result"),
            DeclarationHandle.Create(Module + ".resultant_ne_zero_of_isRelPrime"),
            H("Resultants for relatively prime polynomials"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Relatively prime polynomials, with one monic, have nonzero resultant under the stated domain hypotheses."))),
            DescribeRole.Theorem))));
}
