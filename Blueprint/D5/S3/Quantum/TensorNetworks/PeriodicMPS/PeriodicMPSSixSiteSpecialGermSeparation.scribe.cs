using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteSpecialGermSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized germ separation of the two six-site lifts",
        H("Normalized germ separation of the two six-site lifts"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitespecialgermseparation-specialpoint-germs-distinct"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialGermSeparation.specialPoint_germs_distinct"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Fixing the raw trace transfers the unequal normal cubic terms to distinct normalized physical observation germs."))), DescribeRole.Theorem))));
}
