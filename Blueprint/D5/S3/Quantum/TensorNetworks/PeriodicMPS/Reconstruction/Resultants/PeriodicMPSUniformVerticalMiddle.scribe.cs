using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Resultants;

internal sealed class PeriodicMPSUniformVerticalMiddleDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Resultants/PeriodicMPSUniformVerticalMiddle";
    private const string Title = "Transfer expansion of the middle trace block";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalmiddle"),
                DeclarationHandle.Create(Module + ".section_middleTraceBlock_det"),
                H("Middle trace determinant on the singlet zero locus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Where the indicated complete-series coefficient vanishes, the middle block determinant factors into the trace-feature determinant, the product of the four section roots, and the middle factor."))),
                DescribeRole.Theorem))));
}
