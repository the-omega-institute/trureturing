using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteCriticalCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCertificate";
    private const string Title = "Mixed-trace divisibility of the seven-site critical cofactors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensitecriticalcertificate-reduced-cofactor-eq-six"),
                DeclarationHandle.Create(Module + ".reduced_cofactor_eq_six"),
                H("Reduction of the critical determinant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over a commutative ring with a chosen square root of minus one, the reduced critical determinant is six times the corresponding literal critical determinant for each deleted row."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensitecriticalcertificate-critical-cofactor-quotient"),
                DeclarationHandle.Create(Module + ".critical_cofactor_quotient"),
                H("Mixed-trace factor and degree bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over an integral domain with a chosen square root of minus one and with six nonzero, each deleted-row critical determinant factors as the mixed-trace coordinate times a polynomial of total degree at most forty-six. The reduced determinant gives the degree bound, and the phase-rotation identity gives divisibility."))),
                DescribeRole.Theorem))));
}
