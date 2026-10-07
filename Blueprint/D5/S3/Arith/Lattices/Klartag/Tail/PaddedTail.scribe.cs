using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class PaddedTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Padded Tail"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate padded tail to the stochastic ellipsoid construction.")),
            Node("claim-1", "Phi", "Phi",
                "Φ(r) = min(1/2, e^{−r²/2}/(√(2π)·r)), Klartag eq. (48).", DescribeRole.Definition),
            Node("claim-4", "integral_Ioi_mul_exp_neg_sq", "integral Ioi mul exp neg sq",
                "x ↦ x·e^{−x²/2} integrates to e^{−a²/2} over (a, ∞).", DescribeRole.Theorem),
            Node("claim-5", "integrableOn_exp_neg_sq", "integrable On exp neg sq",
                "e^{−x²/2} is integrable on any (r, ∞).", DescribeRole.Theorem),
            Node("claim-6", "gaussian_tail_le", "gaussian tail le",
                "For positive r, the Gaussian tail integral is at most exp(-r^2/2)/r. On the half-line beyond r, bounding one by x/r reduces the estimate to an exactly integrable derivative.", DescribeRole.Theorem),
            Node("claim-7", "gaussianReal_Ici_le_tail", "gaussian Real Ici le tail",
                "P(Z ≥ r) ≤ e^{−r²/2}/(√(2π)·r) for a standard Gaussian Z and r > 0.", DescribeRole.Theorem),
            Node("claim-8", "gaussianReal_Ici_zero", "gaussian Real Ici zero",
                "P(Z ≥ 0) = 1/2 for a standard Gaussian, by symmetry.", DescribeRole.Theorem),
            Node("claim-9", "gaussianReal_Ici_le_Phi", "gaussian Real Ici le Phi",
                "P(Z ≥ r) ≤ Φ(r) for a standard Gaussian and r > 0 — Klartag eq. (49).", DescribeRole.Theorem),
            Node("claim-10", "gaussianReal_Ici_le_Phi_var", "gaussian Real Ici le Phi var",
                "The same bound for a centred Gaussian of variance σ²: P(Z ≥ a) ≤ Φ(a/σ).", DescribeRole.Theorem),
            Node("claim-11", "padded_increment_tail", "padded increment tail",
                "The padded-increment tail (Prop 4.1, discrete form). hit is the event {∃ k ≤ N, M_k ≤ 0} (the lattice point x becomes a contact point by time T); lev is the event {min_{k ≤ N} S̃_k ≤ −M₀} for the *padded* walk S̃, whose increments are i.i.d. N(0, δ) with δ = h·|x|⁴; S is the terminal value S̃_N, whose law is N(0, T·q²) with q = |x|² (because N·δ = T·|x|⁴). The two supplied inequalities are the two places the discrete argument replaces continuous time: * hsym — conditional symmetry of the padding at the first passage time, replacing Dambis-Dubins-Schwartz (factor 2); * hlevy — Lévy's maximal inequality for i.i.d. symmetric increments, replacing the reflection principle (factor 2). The conclusion carries the constant 4 against the paper's 2: the discretisation costs exactly one factor of 2, which moves only the universal constant c of Theorem 1.2 and not the n² (the n² is fixed by n²T/4 = 4 log n against e^{n²T/8} = n², and a constant in front of K_t(L) is absorbed by ∫₀^T e^{n²t/8} dt ≤ (8/n²)·e^{n²T/8}).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
