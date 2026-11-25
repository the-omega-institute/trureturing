using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuPhysicalProductCutDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuPhysicalProductCut.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical rank-two cuts and exact Hilbert–Schmidt transport for Wu’s two signed CAR modes.",
        H("Two-mode CAR product cuts"),
        Blocks(
            Paragraph(Text("For the two-mode cubic setting of Wu v1, equation (3.54), use occupation order 00, 01, 10, 11 and ordinary matrix trace. The degree-one frame consists of I⊗X, I⊗Y, X⊗Z, Y⊗Z. The occupation imbalance F is diag(1, 0, 0, −1). For a unit frame direction G, its paired observable is Z(G) = F − GFG and the cut is Q = (I + uG + ρZ(G))/2.")),
            Entry("projection", "carProductCut_projection", "Rank and occupation imbalance",
                "For unit real direction coefficients and u² + ρ² = 1, Q is Hermitian and idempotent, has ordinary trace 2, and has Re Tr(FQ) = ρ. The construction uses two anticommuting Hermitian involutions G and Z(G)."),
            Entry("mode-rotation", "carProductCut_modeRotation", "Product form under the signed mode rotation",
                "The unitary U fixes the empty and doubly occupied states in the construction and commutes with F. It conjugates I⊗q to Q, where q = (I + uX + ρZ)/2. For the literal lowering operators J₁ = E₀₁ − E₂₃ and J₂ = E₀₂ + E₁₃ in occupation order, conjugation sends J₁ to zJ₁ + wJ₂ and J₂ to −w̄J₁ + z̄J₂, where z = a − ib and w = c − id."),
            Entry("distance", "carProductCut_distance", "Hilbert–Schmidt overlap formula",
                "For any Hermitian idempotent P with trace 2, let H = 2P − I. The ordinary squared Hilbert–Schmidt distance from P to Q equals 2 − (u Re Tr(HG) + ρ Re Tr(HZ(G)))/2."),
            Entry("transport", "carProductCut_transport", "Exact transport to a CAR cut",
                "Let k be the Euclidean norm of the four real Pauli coefficients Re Tr(HW)/4, let R = Re Tr(FP), and let θ = √(k² + R²). There is a unit direction and a unit real pair (u, ρ) with θ ≤ 1, θu = k, and θρ = R. The resulting cut is Hermitian and idempotent with trace 2, imbalance ρ, and ordinary squared Hilbert–Schmidt distance 2(1 − θ) from P. When k vanishes the traceless parity blocks admit a matching direction, so the construction covers all complex rank-two projections."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
