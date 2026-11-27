using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class PairedRibbonMaskDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonMask";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal paired ribbon mask supplies a tensor Bell amplitude.",
        H("From an actual paired ribbon mask to normalized Bell amplitudes"),
        Blocks(
            Describe.Lean(DescribeId.Create("literal-tensor-transport"),
                DeclarationHandle.Create(Owner + ".literal_tensor_transport"),
                H("The masked physical amplitude factors after the right Hadamards"),
                StatementSource.FromAuthor(MaskStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Construct a cyclic gap involution and literal marked ports as consecutive four-port packets. A whole four-port packet contains two interlaced bands, with no interlacement to any other packet. Retain its twisted band. The actual protected masked phase factors into the local binary phase xy+xd+yc+tau cd. The chart mismatch between raw switch and oriented twist bits is handled before phase extraction.")),
                    Paragraph(Text("Right Hadamards transform the normalized conditional phase into a product of Bell amplitudes, with one overall sign determined by the deleted twists and labels. The proof uses the literal band mask and not a postulated labelling of Bell states."))),
                DescribeRole.Theorem))));
    private static Formula MaskStatement()
    {
        var u = F.Id("u");
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("u"),
            Call("LiteralInterlacedPairedRibbonMasks"),
            Equal(Call("NormalizedRightHadamardAmplitude", u), Call("SignedTensorBellAmplitude", u))));
    }
}
