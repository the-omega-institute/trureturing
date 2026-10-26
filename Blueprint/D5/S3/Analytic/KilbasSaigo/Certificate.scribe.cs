using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KilbasSaigo;

internal sealed class CertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fractional Gamma-ratio kernel certificate.",
        H("Kilbas–Saigo fractional kernel"), Blocks(
            Describe.Lean(DescribeId.Create("kilbas-saigo-kernel-zero-increment"),
                DeclarationHandle.Create("D5/S3/Analytic/KilbasSaigo/Certificate.certificate"),
                H("Zero increment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fractional kernel is defined from the affine Gamma-ratio parameters. When the increment exponent is zero, the integrand vanishes and the two Gamma-ratio terms coincide."))),
                DescribeRole.Theorem))));
}
