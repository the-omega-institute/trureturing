using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SixthOrderPairingExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial pairing convolutions on at most six labels reduce to the empty and single-edge contributions.",
        H("Sixth-order partial pairing expansion"),
        Blocks(Describe.Lean(
            DescribeId.Create("partial-pairing-six-convolution"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderPairingExpansion.partialPairing_six_convolution"),
            H("Convolution after vanishing of small defects"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let U be a finite label set with at most six elements, N a real number, and delta a real function on label subsets. "
                + "Assume delta(V)=0 for every V contained in U with at most two elements. "
                + "The sum over partial pairings P of U of N^card(P)*delta(U minus pairingSupport(P)) equals "
                + "delta(U)+N times the sum of delta(U minus e) over all two-element subsets e of U. "
                + "Disjointness gives card(pairingSupport(P))=2*card(P). Every pairing with at least two edges therefore leaves "
                + "at most two labels and contributes zero. The empty pairing contributes delta(U); the singleton pairings "
                + "correspond bijectively to two-element subsets. The identity is finite and requires no probabilistic assumptions."))),
            DescribeRole.Theorem))));
}
