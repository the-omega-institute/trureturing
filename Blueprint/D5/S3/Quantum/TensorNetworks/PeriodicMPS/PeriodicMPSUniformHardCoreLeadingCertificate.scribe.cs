using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreLeadingCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLeadingCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The simple opposite root and its analytic partner",
        H("The simple opposite root and its analytic partner"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreleadingcertificate-reduced-fold-hasderivat"),
                DeclarationHandle.Create(Module + ".reduced_fold_hasDerivAt"),
                H("The reduced fold root is simple"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eliminating the regular real correction leaves a scalar fold equation. At the opposite slope its derivative is a product of the nonzero reduction scale, the difference of the two slopes and the nonzero leading fold coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreleadingcertificate-exists-opposite-curve"),
                DeclarationHandle.Create(Module + ".exists_opposite_curve"),
                H("An analytic path with exactly matched fold data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each length n ≥ 7 the simple reduced root and the invertible regular blocks certify the leading system. Analytic inversion supplies a partner agreeing with the reference path in all seven normalized regular readouts and the fold coherence near zero. The paths have different imaginary slopes and are distinct sufficiently close to zero on the punctured interval. Parity gives the imaginary expansion through degree three and the real expansion through degree four."))),
                DescribeRole.Theorem))));
}
