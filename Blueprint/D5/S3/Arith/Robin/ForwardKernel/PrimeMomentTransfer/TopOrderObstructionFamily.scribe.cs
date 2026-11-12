using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class TopOrderObstructionFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TopOrderObstructionFamily.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every order at least five admits a positive finite-mixture obstruction to top-order pairing transfer.",
        H("All-order top-order obstruction family"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("top-order-transfer"), DeclarationHandle.Create(Prefix + "TopOrderTransfer"),
                H("The proposed transfer at arbitrary order"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the finite algebraic moment data of MixtureMomentLemmas. Fix a natural order k. The proposition TopOrderTransfer(k) quantifies over every real constant C at least one "
                    + "and every sequence of finitely indexed families in real commutative algebras. The linear functional is normalized "
                    + "and nonnegative on squares. Each coordinate is centered and satisfies Y_d squared = a Y_d + b. "
                    + "The scales satisfy 1 <= L <= H, the absolute values of a and b are at most C L, and the number of coordinates "
                    + "is at most C H. Write s=sqrt(H L). For every order 2 <= r < k and every coefficient family bounded in absolute "
                    + "value by one, the distinct-index moment has absolute value at most C s^r. At order k, the difference between "
                    + "the distinct-index moment and its perfect-pairing polynomial has absolute value at most C s^k/H, "
                    + "uniformly over the same coefficient bound. The proposed conclusion is that, whenever L/H tends to zero, "
                    + "the full unit-weight moment minus its full-moment pairing polynomial, divided by s^k, tends to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("top-order-transfer-fails"), DeclarationHandle.Create(Prefix + "top_order_transfer_fails"),
                H("The transfer fails at every order at least five"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural k >= 5, TopOrderTransfer(k) is false. The examples have L=1, H=N, a=0 and b=1. "
                        + "Choose a finitely supported real random variable Z with mean zero. Conditional on Z, take N independent "
                        + "signs with mean Z/sqrt(N), and let the functional be expectation. A fixed shift N=n+offset ensures "
                        + "that every conditional sign probability is nonnegative. Thus the functionals are positive and normalized, "
                        + "the coordinate signs are centered, and each sign squares to one.")),
                    Paragraph(Text(
                        "Write m_j=E[Z^j], Q_0=1, Q_r=(2r-1)!!, and gamma_j(v)=Q_(j/2) v^(j/2) for even j, "
                        + "with gamma_j(v)=0 for odd j. The scalar defect is d_j=m_j-gamma_j(m_2). For distinct coordinates "
                        + "the moment is m_j/(sqrt(N))^j. Consequently all bounded-coefficient distinct moments of order j "
                        + "have absolute value at most |m_j| (sqrt(N))^j. Removing noninjective assignments compares their "
                        + "coefficient sum with the product of coefficient sums, with an error bounded by choose(j,2) N^(j-1). "
                        + "Comparing the second-moment pairing polynomial with its rank-one leading "
                        + "term gives a uniform normalized defect error bounded by a constant depending on j and the mixing law, divided by N.")),
                    Paragraph(Text(
                        "A partial pairing with p edges covers 2p labels. Choosing those labels and then pairing them gives "
                        + "n_(k,p)=choose(k,2p) Q_p partial pairings. For unit coefficients, each paired edge contributes N. "
                        + "The normalized defect on the remaining j=k-2p labels tends to d_j: the normalized descending factorial "
                        + "N(N-1)...(N-j+1)/N^j tends to one, and the normalized second-moment factor tends to m_2. "
                        + "The quadratic moment transfer formula therefore gives the limit "
                        + "c_k=sum_(p=0,...,floor(k/2)) choose(k,2p) Q_p d_(k-2p). "
                        + "Its remainder is bounded by a fixed constant times sqrt(1/N)+1/N and tends to zero.")),
                    Paragraph(Text(
                        "For odd k >= 5, put D_k=3^(k+1)-2^(k+1)-5. Give Z the values -2, 1 and 3 with respective masses "
                        + "(3^k-3)/D_k, (2*3^k-3*2^k)/D_k and (2^k-2)/D_k. These masses are positive and sum to one. "
                        + "They give m_1=m_k=0. Hence the top distinct-index moment vanishes for every bounded coefficient family, "
                        + "and the odd-order pairing polynomial also vanishes. For q_j=(2^j-2)/(3^j-3), "
                        + "the difference after cross multiplication is 3^j(2^j-4)+3*2^j, which is positive for j>=2. "
                        + "Thus q_j strictly decreases and every odd moment m_j with 3 <= j < k is negative. "
                        + "All nonzero summands in c_k are negative, and the contribution with j=3 has positive multiplicity. Therefore c_k<0.")),
                    Paragraph(Text(
                        "For even k=2m >= 6, put t=Q_m^(1/(m-1)). Give each of sqrt(t) and -sqrt(t) mass 1/(2t), "
                        + "and give zero mass 1-1/t. Here t>1, so all three masses are positive. The odd moments vanish and "
                        + "m_(2r)=t^(r-1) for r>=1. In particular m_2=1 and m_(2m)=Q_m, so d_(2m)=0. "
                        + "The leading top defect vanishes. The injective comparison costs Q_m choose(2m,2)/N after normalization, "
                        + "and the pairing-product perturbation costs m Q_m/N. Their sum is 2 m^2 Q_m/N, "
                        + "giving the uniform top bound 2 m^2 Q_m s^k/N. "
                        + "The numbers t_r=Q_r^(1/(r-1)), for r>=2, strictly increase: t_r is the geometric mean "
                        + "of 3,5,...,2r-1, hence t_r<=2r-1<2r+1. Therefore d_(2r)>0 for 2<=r<m. "
                        + "The propagation sum has positive terms and contains the term with j=4, so c_(2m)>0.")),
                    Paragraph(Text(
                        "In either parity choose one fixed C bounding all lower scalar moments and the top defect constant. "
                        + "The models satisfy every premise of TopOrderTransfer(k), including L/H tending to zero, "
                        + "but their normalized full pairing defects tend to c_k rather than zero. This contradiction proves the theorem. "
                        + "The uniform leading-term estimate and propagation limit are supplied by TopOrderObstructionCore. The construction and argument are from Theorem 503.4, using Lemmas 503.2 and 503.3 of FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II."))),
                DescribeRole.Theorem))));
}
