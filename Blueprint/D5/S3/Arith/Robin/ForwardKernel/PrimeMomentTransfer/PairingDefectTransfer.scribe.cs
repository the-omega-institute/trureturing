using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PairingDefectTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectTransfer.";

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite arbitrary-order propagation of pairing defects for a quadratic family.",
        H("Pairing defect transfer"),
        Blocks(
            Paragraph(Text(
                "Let D be finite, A a commutative real algebra, ell a real linear functional with ell(1)=1, "
                + "and Y a centered family satisfying Y(d)^2=a*Y(d)+b*1. No positivity or independence is assumed. "
                + "For weights f indexed by Fin k, write R(U) for the ordered distinct-index moment on a label subset U, "
                + "V(U) for the full moment, T(e) for the sum of the product of the weights on e, "
                + "and Delta(U)=R(U)-W_U(R), where W is the perfect-pairing polynomial. "
                + "A partial pairing P has uncovered set U(P)=univ minus its support and T(P) is the product of T(e) over its edges. "
                + "The theorem is the finite identity of Theorem 500.2 in FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II, "
                + "with edge-subset inclusion-exclusion in place of partition-lattice inversion. "
                + "The proved error constant is k^k * 2^k * 2^(k*k) * (C+1)^(k+1), larger than the volume's displayed "
                + "2^k * k^k * k! * (C+1)^(k+1); the sharper displayed constant is not established here.")),
            Entry("pairing-defect-constant", "pairingDefectConstant", "Explicit uniform constant",
                "For natural k and real C, pairingDefectConstant(k,C) is k^k * 2^k * 2^(k*k) * (C+1)^(k+1). "
                + "The first factors bound the number of partition and retained-subset configurations and the number of collision edge subsets.", DescribeRole.Definition),
            Entry("quadratic-pairing-defect-transfer", "quadratic_pairing_defect_transfer", "The finite pairing-defect transfer theorem",
                "For every finite index type D, commutative real algebra A, natural k, real linear functional ell, centered family Y, "
                + "and weights f(i,d), assume ell(1)=1, Y(d)^2=a*Y(d)+b*1 for all d, C>=1, H>=L>=1, "
                + "|a|,|b|<=C*L, card(D)<=C*H and |f(i,d)|<=1. Set s=sqrt(H*L). "
                + "Assume |R_r(f(B_1),...,f(B_r))|<=C*s^r for every 2<=r<k and nonempty pairwise disjoint label subsets B_j, "
                + "where f(B) is the product of the original weights over B. "
                + "Then there exists one real E such that V(univ)=sum_P b^card(P)*T(P)*R(U(P))+E, "
                + "and V(univ)-W_univ(V)=sum_P b^card(P)*T(P)*Delta(U(P))+E, "
                + "with |E|<=pairingDefectConstant(k,C)*s^k*(sqrt(L/H)+1/H). "
                + "Both sums run over all partial pairings. The top distinct-index moment R(univ) occurs unchanged and requires no upper bound. "
                + "Grouping tuples by equality partitions and reducing powers gives the signed block moments. "
                + "Edge inclusion-exclusion factors each collision term into free component sums and a retained distinct moment on merged disjoint labels. "
                + "Positive collision degree gains sqrt(L/H); removing a free component from degree zero gains 1/H. "
                + "Zero degree means retained singleton blocks and free pair blocks, and their bijection with partial pairings identifies the main sum. "
                + "Finally the quadratic second-moment identity gives the exact covariance pairing convolution, so both equations share the same E.", DescribeRole.Theorem))));
}
