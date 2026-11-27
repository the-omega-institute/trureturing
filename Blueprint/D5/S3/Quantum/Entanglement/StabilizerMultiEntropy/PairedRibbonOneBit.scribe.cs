using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class PairedRibbonOneBitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonOneBit";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp one-bit classical record capacity for paired signed-ribbon erasure.",
        H("Joint nonlinear records preserve negativity after paired ribbon erasure"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-joint-bit-gap"),
                DeclarationHandle.Create(Owner + ".actual_joint_bit_gap"),
                H("The exact joint one-bit trace norm is 5/4; separate and linear trace norms are 1"),
                StatementSource.FromAuthor(ExactStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix any nonempty packet of consecutive interlaced two-band blocks in one literal marked signed ribbon chart. Retain the twisted band of each block and delete the other, with arbitrary twists on the deleted bands. The two computational-basis outcomes per deleted block have the uniform Born mass proved for the actual mask. The right local Hadamard turns the normalized conditional phase amplitude into a tensor of Bell states, up to a phase that cancels from the projector.")),
                    Paragraph(Text("Keep both classical message blocks with their original outcome weights. The flagged partial-transpose trace norm becomes the mean of max(1, absolute transformed record), where the transform is the orthogonal Bell sign matrix. The quadratic envelope gives 5/4, attained by a deterministic yes/no test of one full Pauli label. Any affine parity of the full raw label, or any stochastic function of one fixed bank alone, instead gives norm 1. A protocol computing two bank messages and combining them is not a one-bank record. The result is an exact norm separation; it does not determine optimal distillable entanglement or claim an advantage in sampling."))),
                DescribeRole.Theorem))));
    private static Formula ExactStatement()
    {
        var u = F.Id("u");
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("u"),
            Call("NonemptyLiteralPairedRibbonMasks"),
            Call("JointAffineAndOneBankFlaggedTraceOptima", u, Call("ExactFiveQuarters"), Call("ExactOne"), Call("ExactOne"))));
    }
}
