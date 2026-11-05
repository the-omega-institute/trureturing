using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class ParitySectorMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/ParitySectorMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/cepollaro2025stabilizer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Qudit parity sectors in odd dimensions, canonical orthonormal frames and projectors, parity-commuting Clifford reduction of Weyl labels to pure clock powers, diagonal cosine compressions and power sums, and closed-form Haar fourth moments of nonzero Weyl labels.",
        H("Parity-sector Clifford reduction and diagonal cosine fourth moments"),
        Blocks(
            Node("paritysectormoments-parity-matrix-definition",
                "Qudit parity operator", "parityMatrix",
                "For a natural dimension d, parityMatrix(d) is the permutation matrix P |j> = |-j> acting on C^d indexed by Z / dZ.",
                DescribeRole.Definition),
            Node("paritysectormoments-even-sector-subspace-definition",
                "Even parity subspace", "evenSectorSubspace",
                "For a nonzero dimension d, evenSectorSubspace(d) = ker(P - I) is the +1 eigenspace E_d of the parity operator in C^d.",
                DescribeRole.Definition),
            Node("paritysectormoments-odd-sector-subspace-definition",
                "Odd parity subspace", "oddSectorSubspace",
                "For a nonzero dimension d, oddSectorSubspace(d) = ker(P + I) is the -1 eigenspace O_d of the parity operator in C^d.",
                DescribeRole.Definition),
            Node("paritysectormoments-even-projector-definition",
                "Even-sector orthogonal projector", "evenProjector",
                "For a dimension d, evenProjector(d) = (I + P) / 2 is the orthogonal projector onto the even parity sector.",
                DescribeRole.Definition),
            Node("paritysectormoments-odd-projector-definition",
                "Odd-sector orthogonal projector", "oddProjector",
                "For a dimension d, oddProjector(d) = (I - P) / 2 is the orthogonal projector onto the odd parity sector.",
                DescribeRole.Definition),
            Node("paritysectormoments-even-isometry-definition",
                "Canonical even-sector isometric frame", "evenIsometry",
                "For a nonzero dimension d, evenIsometry(d) : C^{(d + 1) / 2} -> C^d has column 0 equal to |0> and column j for 1 <= j < (d + 1) / 2 equal to (|j> + |-j>) / sqrt(2).",
                DescribeRole.Definition),
            Node("paritysectormoments-odd-isometry-definition",
                "Canonical odd-sector isometric frame", "oddIsometry",
                "For a nonzero dimension d, oddIsometry(d) : C^{(d - 1) / 2} -> C^d has column idx for 0 <= idx < (d - 1) / 2 equal to (|idx + 1> - |-(idx + 1)>) / sqrt(2).",
                DescribeRole.Definition),
            Node("paritysectormoments-even-clock-diag-definition",
                "Even-sector compressed clock eigenvalues", "evenClockDiag",
                "For a dimension d and integer clock exponent h, evenClockDiag(d, h) assigns 1 to index 0 and cos(2 pi h j / d) to each positive index 1 <= j < (d + 1) / 2.",
                DescribeRole.Definition),
            Node("paritysectormoments-odd-clock-diag-definition",
                "Odd-sector compressed clock eigenvalues", "oddClockDiag",
                "For a dimension d and integer clock exponent h, oddClockDiag(d, h) assigns cos(2 pi h (idx + 1) / d) to each index 0 <= idx < (d - 1) / 2.",
                DescribeRole.Definition),
            Node("paritysectormoments-even-clock-power-sum-definition",
                "Even-sector compressed clock power sums", "evenClockPowerSum",
                "For d, h, and m, evenClockPowerSum(d, h, m) is the m-th power sum sum_{idx} evenClockDiag(d, h, idx)^m across the (d + 1) / 2 eigenvalues on E_d.",
                DescribeRole.Definition),
            Node("paritysectormoments-odd-clock-power-sum-definition",
                "Odd-sector compressed clock power sums", "oddClockPowerSum",
                "For d, h, and m, oddClockPowerSum(d, h, m) is the m-th power sum sum_{idx} oddClockDiag(d, h, idx)^m across the (d - 1) / 2 eigenvalues on O_d.",
                DescribeRole.Definition),
            Node("paritysectormoments-weyl-label-order-definition",
                "Projective order of a phase-space label", "weylLabelOrder",
                "For a dimension d and label a = (a_1, a_2) in (Z / dZ)^2, weylLabelOrder(d, a) = d / gcd(val(a_1), gcd(val(a_2), d)) is the additive order of a in (Z / dZ)^2.",
                DescribeRole.Definition),
            Node("paritysectormoments-parity-sectors-bases-and-isometries-theorem",
                "Parity involution, canonical sector bases, dimensions, and isometry invariance",
                "parity_sectors_bases_and_isometries",
                "For every odd dimension d >= 3, parityMatrix(d) is Hermitian and involutory (P^2 = I, P^* = P). The canonical frames evenIsometry(d) and oddIsometry(d) are isometries whose range projectors equal evenProjector(d) and oddProjector(d), whose column spaces equal evenSectorSubspace(d) of dimension (d + 1) / 2 and oddSectorSubspace(d) of dimension (d - 1) / 2, and every isometric embedding E : C^S -> C^d with image E_d (respectively O_d) has |S| = (d + 1) / 2 (respectively (d - 1) / 2) and shares the same projector, labelFourthMoment values, and aseGap as the canonical frame.",
                DescribeRole.Theorem),
            Node("paritysectormoments-parity-clifford-label-reduction-theorem",
                "Parity-commuting Clifford reduction of nonzero Weyl labels to pure clock powers",
                "parity_clifford_label_reduction",
                "For every odd dimension d >= 3, both canonical parity frames have unit fourth moment at the origin (0, 0), and for every nonzero label a in (Z / dZ)^2 there exists an integer h with gcd(h, d) = gcd(val(a_1), gcd(val(a_2), d)) such that labelFourthMoment(V, a) = labelFourthMoment(V, (0, h mod d)) simultaneously for V in {E_d, O_d}. The reduction conjugates Weyl operators by the discrete Fourier transform F |j> = d^{-1 / 2} sum_l omega^{j l} |l> and the odd-d quadratic phase gate S |j> = tau^{j^2} |j>, both unitary and commuting with P, which act on phase-space labels up to unimodular scalars as (x, y) -> (-y, x) and (x, y) -> (x, x + y), implementing Euclidean gcd reduction on nonnegative integer lifts.",
                DescribeRole.Theorem),
            Node("paritysectormoments-parity-clock-compression-and-power-sums-theorem",
                "Diagonal cosine compressions of pure clock powers and closed-form power sums",
                "parity_clock_compression_and_power_sums",
                "For every odd dimension d >= 3 and every integer h, compressing D_{(0, h mod d)} = Z^h onto E_d and O_d in the canonical bases yields the real diagonal matrices diag(evenClockDiag(d, h)) and diag(oddClockDiag(d, h)). Whenever h is not divisible by d, letting n = d / gcd(h, d) >= 3 (which is odd) and writing epsilon = +1 for E_d and epsilon = -1 for O_d, character orthogonality over Z / dZ gives the power sums p_1 = epsilon / 2, p_2 = (d + 2 epsilon) / 4, p_3 = (d + 4 epsilon) / 8 when n = 3 and epsilon / 2 when n != 3, and p_4 = (3 d + 8 epsilon) / 16.",
                DescribeRole.Theorem),
            Node("paritysectormoments-parity-nonzero-label-fourth-moment-theorem",
                "Closed-form Haar fourth moment of a nonzero Weyl label with order-three bifurcation",
                "parity_nonzero_label_fourth_moment",
                "For every odd dimension d >= 3 and every nonzero label a in (Z / dZ)^2 of order n = weylLabelOrder(d, a), substituting the compressed clock power sums into the five-term Hermitian fourth-moment polynomial on E_d (dimension k = (d + 1) / 2) and O_d (dimension k = (d - 1) / 2) yields labelFourthMoment(E_d, a) = labelFourthMoment(O_d, a) = 3 / ((d + 1)(d + 3)) whenever n != 3, whereas for n = 3 it yields labelFourthMoment(E_d, a) = (3 d + 35) / ((d + 1)(d + 5)(d + 7)) and labelFourthMoment(O_d, a) = (3 d - 5) / ((d - 1)(d + 1)(d + 5)).",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
