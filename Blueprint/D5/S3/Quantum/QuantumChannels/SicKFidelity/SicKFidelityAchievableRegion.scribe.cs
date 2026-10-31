using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.SicKFidelity;

internal sealed class SicKFidelityAchievableRegionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mayer2021zerofidelity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact planar regions of pairs (F_k(Lambda), F(Lambda)) realized by n-qubit completely positive trace-preserving maps across k = 0, 1 <= k <= n - 1, and k >= n, closed-form upper and lower process-fidelity envelopes at prescribed 0-fidelity, unimodal maximizer analysis of the binomial weight kernel, and non-identifiability of F(Lambda) from any single F_k(Lambda) for n >= 2 and k <= n - 1.",
        H("Achievable (k-fidelity, process fidelity) regions and single-fidelity non-identifiability"),
        Blocks(
            Node("sickfidelityregion-achievable-region-definition",
                "Achievable (k-fidelity, process fidelity) region", "achievableRegion",
                "For n qubits and truncation order k, achievableRegion(n, k, rho) is the subset of R^2 consisting of all pairs (realKFidelity(rho, k, Lambda), realProcessFidelity(Lambda)) as Lambda ranges over completely positive trace-preserving n-qubit maps.",
                DescribeRole.Definition),
            Node("sickfidelityregion-tail-coeff-definition",
                "Unsigned Pauli-weight binomial kernel", "tailCoeff",
                "Defines g_k(w) = 3^{-w} C(w - 1, k) for natural numbers k and w.",
                DescribeRole.Definition),
            Node("sickfidelityregion-opt-weight-definition",
                "Maximizing Hamming weight w*", "optWeight",
                "Defines w*(n, k) = min(n, floor(3 k / 2) + 1).",
                DescribeRole.Definition),
            Node("sickfidelityregion-extremal-abscissa-definition",
                "Signed extremal horizontal vertex abscissa", "extremalAbscissa",
                "Defines x_k(n) = (-1)^k g_k(w*(n, k)), the nonzero horizontal coordinate among vertices on the axis F = 0 for 1 <= k <= n - 1.",
                DescribeRole.Definition),
            Node("sickfidelityregion-zero-characterization-theorem",
                "Exact 0-fidelity achievable triangle, single-qubit segment, and extremal envelopes",
                "achievableRegion_zero_characterization",
                "For every n >= 1, R_0 equals the closed convex hull of (1, 1), (3^{-n}, 0), and (1 / 3, 0). When n >= 2, (F_0, F) belongs to R_0 if and only if F >= 0 and 1 - (3 / 2)(1 - F_0) <= F <= (F_0 - 3^{-n}) / (1 - 3^{-n}), with the upper edge attained by mixtures t id + (1 - t) Z^{tensor n} (.) Z^{tensor n} and the lower edge attained by weight-1 Pauli mixtures; at every prescribed F_0 in [3^{-n}, 1], the maximum of F is (F_0 - 3^{-n}) / (1 - 3^{-n}) (strictly below F_0 for F_0 < 1 with gap (1 - F_0) 3^{-n} / (1 - 3^{-n})) and the minimum of F is max(0, 1 - (3 / 2)(1 - F_0)). When n = 1, R_0 collapses to the line segment F = 1 - (3 / 2)(1 - F_0) over 1 / 3 <= F_0 <= 1.",
                DescribeRole.Theorem),
            Node("sickfidelityregion-intermediate-and-high-characterization-theorem",
                "Intermediate achievable triangles, unimodal maximizers, and high-order diagonal segment",
                "achievableRegion_intermediate_and_high_characterization",
                "For 1 <= k <= n - 1, the kernel g_k(w) = 3^{-w} C(w - 1, k) satisfies 0 < g_k(w*) < 1 and attains its maximum over 1 <= w <= n uniquely at w* = min(n, floor(3 k / 2) + 1), except when k is even and 3 k / 2 + 1 <= n where the maximum is attained at {3 k / 2, 3 k / 2 + 1}; the achievable region R_k is the closed triangle conv{(1, 1), (0, 0), (x_k, 0)}, cut out by F >= 0 and F_k <= F <= (F_k - x_k) / (1 - x_k) for odd k and by F >= 0 and (F_k - x_k) / (1 - x_k) <= F <= F_k for even k (implying 0 <= F <= 1), with vertices attained by the identity map, weight-1 Pauli conjugation, and weight-w* Pauli conjugation. For k >= n >= 1, R_k is the diagonal segment {(F_k, F) | F_k = F and 0 <= F <= 1}.",
                DescribeRole.Theorem),
            Node("sickfidelityregion-non-identifiability-theorem",
                "Non-identifiability of process fidelity from a single lower-order k-fidelity",
                "kFidelity_non_identifiability_of_processFidelity",
                "For every n >= 2 and every 0 <= k <= n - 1, there exist two n-qubit completely positive trace-preserving maps with the same k-fidelity F_k, one having zero entanglement process fidelity and one having strictly positive entanglement process fidelity (and hence distinct process fidelities).",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
