using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SixthOrderTopPairingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sixth-order top pairing transfer is refuted by a positive finite mixture.",
        H("Sixth-order top pairing transfer fails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed sixth-order implication"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a fixed constant C at least one, assume a sequence of finitely indexed families in real algebras with normalized linear functionals nonnegative on squares, "
                    + "with centered coordinates satisfying Y squared equals a Y plus b, one at most L at most H, "
                    + "absolute values of a and b at most C L, and index cardinality at most C H. Assume every "
                    + "coefficient family bounded by one has distinct-index moment at most C sqrt(H L) to its order "
                    + "at orders two through five. At order six require the distinct moment minus its perfect-pairing "
                    + "polynomial to have absolute value at most C (H L) cubed divided by H, uniformly in all bounded "
                    + "weights. The proposed implication says that L/H tending to zero forces the full sixth moment "
                    + "with unit weights minus its full-moment pairing polynomial, divided by (H L) cubed, to tend to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A symmetric mixture refutes the implication"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take L=1, H=N, a=0 and b=1. Sample Z with values plus or minus the fourth root of fifteen, "
                        + "each of mass one divided by twice the square root of fifteen, and zero with the remaining mass. "
                        + "Conditional on Z, sample N independent signs of mean Z/sqrt(N). For N at least four this is a "
                        + "probability distribution. Coordinate signs are centered and square to one. The mixing moments "
                        + "at orders zero through six are 1, 0, 1, 0, sqrt(15), 0 and 15. Products at distinct coordinates "
                        + "have moment m_r divided by sqrt(N) to the r, giving all lower moment bounds with constant four.")),
                    Paragraph(Text(
                        "Write A_i for the sum of the i-th coefficient function. Removing noninjective sixth-order tuples "
                        + "changes the product of the A_i by at most 36 N to the fifth. Thus the sixth distinct moment differs "
                        + "from 15 times the product of the A_i divided by N cubed by at most 540 N squared. Every second "
                        + "distinct moment equals (A_i A_j minus the diagonal weight sum) divided by N. There are fifteen "
                        + "perfect pairings of six labels, and their rank-one terms have the same product. Perturbing their "
                        + "three factors costs at most 180 N squared in total. Consequently the uniform top distinct pairing "
                        + "defect is at most 720 N squared.")),
                    Paragraph(Text(
                        "Apply quadratic_pairing_defect_transfer with unit weights and lower-moment constant four. "
                        + "Defects on at most two labels vanish, so only the empty partial pairing and the fifteen single-edge "
                        + "partial pairings remain. A four-label distinct defect is sqrt(15) times N(N-1)(N-2)(N-3)/N squared "
                        + "minus 3(N-1) squared. For N at least one hundred it is at least N squared divided by two. Each "
                        + "single-edge term multiplies it by N. Choose a fixed natural offset large enough that N=n+offset "
                        + "also dominates 720 and the square of the transfer-error constant. The empty-pairing defect then "
                        + "costs at most N cubed, the transfer error at most twice N cubed, and the full sixth defect is at "
                        + "least N cubed. Its normalized value is therefore always at least one, although L/H tends to zero.")),
                    Paragraph(Text(
                        "This proves the top-order insufficiency assertion of Proposition 500.5 in "
                        + "FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II. The formal result uses an explicit positive lower "
                        + "bound rather than asserting the sharper numerical limit 15(sqrt(15)-3). The model is a finite "
                        + "probability counterexample; no assertion about prime correlations or the Riemann hypothesis follows."))),
                DescribeRole.Theorem))));
}
