using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class UniformNativeSliceReadoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeSliceReadout";
    private const string Title = "Cartesian columns of the native critical matrix";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("uniformnativeslicereadout"),
                DeclarationHandle.Create(Module + ".fderiv_rawReadout_sliceColumn"),
                H("Polynomial evaluation of a Cartesian column"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The five Cartesian columns of the raw readout derivative are the real parts of evaluated polynomial partial derivatives."))),
                DescribeRole.Theorem))));
}
