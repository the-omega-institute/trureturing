using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformTransferSquareClassesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferSquareClasses";
    private const string Title = "Square classes of the transfer radicals";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformtransfersquareclasses"),
                DeclarationHandle.Create(Module + ".genericRadicalAlgebra_isField"),
                H("The generic transfer radical algebra is a field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over a field of characteristic different from two, the guard c minus b squared gives the nonvanishing condition under which adjoining both radicals over the two-parameter rational function field produces a field."))),
                DescribeRole.Theorem))));
}
