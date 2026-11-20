using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records;

internal sealed class PrimitiveRecordDiamondCoefficientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordDiamondCoefficient";
    private const string Title = "Exact leading diamond distance for the periodic record channel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title, H(Title),
        Blocks(Describe.Lean(DescribeId.Create("primitiverecorddiamondcoefficient-result"),
            DeclarationHandle.Create(Module + ".jointChannel_diamond_asymptotic"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/watrous2009completelybounded"),
                LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps")),
            Blocks(
                Paragraph(Text("The controlled channel retains the adjacent pair and the address. Its unhalved diamond distance to its dephased counterpart has leading coefficient (205 + 25 sqrt(41)) / 328 at the alpha-to-the-ring-length scale.")),
                Paragraph(Text("The coefficient is the trace norm of the leading cross reduction. Exact reversal eigenvectors give its singular values. On the same scale, discarding the pair yields a coherence multiplier with coefficient one."))),
            DescribeRole.Theorem))));
}
