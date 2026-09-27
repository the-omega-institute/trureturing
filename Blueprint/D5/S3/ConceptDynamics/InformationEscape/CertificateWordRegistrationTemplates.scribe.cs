using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class CertificateWordRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/CertificateWordRegistrationTemplates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six finite readouts retain every code of a certificate word.",
        H("CertificateWordRegistrationTemplates"),
        Blocks(
            Node("certificateSignature",
                "The signature has six CUT positions, each returning one value in Fin 5, "
                    + "and has no anchor positions."),
            Node("certificateWordRealization",
                "The realization reads the supplied certificate word at the selected position "
                    + "without replacing, aggregating, or classifying its code."))));

    private static DocumentBlock.Describe Node(string declaration, string text) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
