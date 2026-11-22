using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteCriticalResidueCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalResidueCertificate";
    private const string Title = "Nonzero modular resultant for the literal seven-site critical cofactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensitecriticalresiduecertificate-seven-site-modular-resultant"),
                DeclarationHandle.Create(Module + ".seven_site_modular_resultant"),
                H("Full-degree residue-field resultant certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over the field modulo 1009, the cofactors deleting rows zero and one each factor by the mixed-trace coordinate. The two resulting quotients have degree forty-six on the specified affine line, and their univariate resultant is nonzero. Interpolation identifies their line restrictions with the coefficient tables, whose Bézout identity gives the resultant certificate."))),
                DescribeRole.Theorem))));
}
