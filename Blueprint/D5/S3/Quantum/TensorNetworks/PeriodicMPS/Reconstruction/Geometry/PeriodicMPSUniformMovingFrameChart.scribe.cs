using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformMovingFrameChartDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrameChart";
    private const string Title = "Algebraic charts on generic paired sections";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformmovingframechart"),
                DeclarationHandle.Create(Module + ".genericSection_has_algebraicChart"),
                H("Balanced generic section"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a pairing with nonvanishing obstruction on the divisor and nonzero trace sum, an algebraic field extension supplies a nonzero balancing parameter. The normalized ket and bra traces become (1, 0) and their mixed traces agree."))),
                DescribeRole.Theorem))));
}
