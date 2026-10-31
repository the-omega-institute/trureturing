using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.SicKFidelity;

internal sealed class SicKFidelityJointSimplexDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mayer2021zerofidelity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal alternating linear relation among F_0, ..., F_{n-1} and the entanglement process fidelity F for arbitrary trace-preserving linear qubit maps, affine independence of the n + 1 Pauli-weight vertices in R^n, and exact n-simplex characterization of the joint CPTP k-fidelity range with unique barycentric recovery of (Q_0, ..., Q_n) and F.",
        H("Trace-preserving linear reconstruction and CPTP joint k-fidelity simplex geometry"),
        Blocks(
            Node("sickfidelitysimplex-vertex-definition",
                "Joint k-fidelity simplex vertices", "simplexVertex",
                "Defines the n + 1 vectors V_0, ..., V_n in R^n by V_0 = (1, ..., 1) and (V_w)_k = (-1)^k 3^{-w} C(w - 1, k) for 1 <= w <= n and 0 <= k <= n - 1.",
                DescribeRole.Definition),
            Node("sickfidelitysimplex-joint-vec-definition",
                "Joint lower-order k-fidelity vector", "jointKFidelityVec",
                "Collects the first n real SIC k-fidelities (F_0(Lambda), ..., F_{n-1}(Lambda)) in R^n for an n-qubit map Lambda.",
                DescribeRole.Definition),
            Node("sickfidelitysimplex-joint-range-definition",
                "CPTP joint k-fidelity range", "jointKFidelityRange",
                "Defines the subset of R^n consisting of all joint vectors (F_0(Lambda), ..., F_{n-1}(Lambda)) realized by completely positive trace-preserving n-qubit maps Lambda.",
                DescribeRole.Definition),
            Node("sickfidelitysimplex-tp-exact-reconstruction-theorem",
                "Universal linear relation and exact fidelity reconstruction for trace-preserving maps",
                "tp_exact_fidelity_reconstruction",
                "For every n, every choice of single-qubit SICs, and every trace-preserving complex-linear map Lambda on M_{2^n}(C) (without requiring complete positivity), 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda) + (-2)^n F(Lambda) = 1, equivalently F(Lambda) = (-2)^{-n} (1 - 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda)), together with the corresponding real identity when Lambda is completely positive.",
                DescribeRole.Theorem),
            Node("sickfidelitysimplex-cptp-joint-range-theorem",
                "Affine independence, n-simplex joint range, and unique barycentric Pauli-weight recovery",
                "cptp_joint_kFidelity_simplex_range",
                "For every n >= 1, the n + 1 vertices V_0, ..., V_n in R^n are affinely independent, the set of joint k-fidelity vectors (F_0(Lambda), ..., F_{n-1}(Lambda)) over completely positive trace-preserving n-qubit maps equals the n-simplex conv{V_0, ..., V_n}, the Pauli-weight sums (Q_0(Lambda), ..., Q_n(Lambda)) are the unique barycentric coordinates of (F_0(Lambda), ..., F_{n-1}(Lambda)) in this simplex, and F(Lambda) = Q_0(Lambda) = (-2)^{-n} (1 - 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda)).",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
