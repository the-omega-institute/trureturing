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
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sixth-four-defect-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderPairingExpansion.sixth_four_defect_lower"),
                H("A quantitative fourth-order defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real N>=100, sqrt(15)*N*(N-1)*(N-2)*(N-3)/N^2-3*(N-1)^2 is at least N^2/2. "
                    + "The falling product is at least N^4-6*N^3 and sqrt(15)>=15/4. "
                    + "This explicit inequality converts the four-label defect of the biased-cube model into a uniform positive quadratic contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transfer-error-small"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderPairingExpansion.transfer_error_small"),
                H("Cubic-scale transfer error bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real N>=1 and K<=sqrt(N), K*N^3*(sqrt(1/N)+1/N)<=2*N^3. "
                    + "Both K/sqrt(N) and K/N are at most one because sqrt(N)<=N. "
                    + "This bounds the transfer remainder after selecting a sufficiently large model size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sixth-defect-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderPairingExpansion.sixth_defect_lower"),
                H("Domination of the cubic comparison scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let N>=1, C<=N, |delta6|<=C*N^2, delta4>=N^2/2, and |E|<=2*N^3. "
                    + "If V=delta6+15*N*delta4+E, then V>=N^3. "
                    + "The fifteen one-edge terms contribute at least (15/2)*N^3, "
                    + "while the sixth-order defect and remainder cost at most N^3 and 2*N^3 respectively."))),
                DescribeRole.Theorem))));
}
