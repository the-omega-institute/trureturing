using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreLeadingRowsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLeadingRows";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Leading coefficients of the cross-multiplied equations",
        H("Leading coefficients of the cross-multiplied equations"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreleadingrows-real-leading-row"),
                DeclarationHandle.Create(Module + ".real_leading_row"),
                H("Quadratic real rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The quadratic leading coefficient of each cross-multiplied real row equals the corresponding normalized coefficient difference multiplied by the square of the witness mass. This includes the coherence row of the fold."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreleadingrows-imag-leading-row"),
                DeclarationHandle.Create(Module + ".imag_leading_row"),
                H("Linear imaginary rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The linear leading coefficients of the imaginary rows are the normalized regular first differential along the candidate leading direction, with the reference direction subtracted and the square of the witness mass restored."))),
                DescribeRole.Theorem))));
}
