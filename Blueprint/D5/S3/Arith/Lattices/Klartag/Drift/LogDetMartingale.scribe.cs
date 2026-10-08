using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class LogDetMartingaleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Log Det Martingale"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate log det martingale to the stochastic ellipsoid construction.")),
            Node("claim-1", "mgIncr", "mg Incr",
                "The martingale increment Δ_k = ⟪V_k, ξ_k⟫, with V_k the *stopped* π_k(A_k⁻¹).", DescribeRole.Definition),
            Node("claim-2", "mgPart", "mg Part",
                "The martingale M_K = ∑_{k<K} Δ_k.", DescribeRole.Definition),
            Node("claim-4", "stronglyMeasurable_V_coord", "strongly Measurable V coord",
                "Each coordinate of V_k is ℱ k-measurable, at the chain's own filtration.", DescribeRole.Theorem),
            Node("claim-5", "stronglyMeasurable_mgIncr", "strongly Measurable mg Incr",
                "Δ_k is ℱ (k+1)-measurable: V_k is ℱ k-measurable and ξ_k is ℱ (k+1)-measurable.", DescribeRole.Theorem),
            Node("claim-6", "abs_mgIncr_le", "abs mg Incr le",
                "|Δ_k| ≤ (√n/m)·‖ξ_k‖ — Cauchy–Schwarz against DriftStopped2.norm_stoppedV_le, which holds on every path.", DescribeRole.Theorem),
            Node("claim-8", "integrable_mgIncr_sq", "integrable mg Incr sq",
                "Δ_k² ≤ (n/m²)‖ξ_k‖², so Δ_k is square-integrable.", DescribeRole.Theorem),
            Node("claim-11", "integrable_mgIncr_mul", "integrable mg Incr mul",
                "Every product of two increments is integrable — L² × L² ⊆ L¹.", DescribeRole.Theorem),
            Node("claim-12", "condExp_mgIncr_zero", "cond Exp mg Incr zero",
                "E[Δ_k | ℱ_k] = 0 — StepInputs2.condExp_inner_eq_zero at the chain's own V_k, exactly as DriftInputsStopped.driftInputs_step_stopped uses it for the drift.", DescribeRole.Theorem),
            Node("claim-14", "integral_mgIncr_sq_le", "integral mg Incr sq le",
                "E[Δ_k²] ≤ h·n/m². 94a's LogDetVariance.condExp_inner_sq gives E[Δ_k² | ℱ_k] = h‖V_k‖² — the *isotropy* is what saves the factor dim; the pointwise bound |Δ_k| ≤ ‖V_k‖‖ξ_k‖ would cost h·d·n/m² instead — and DriftStopped2.norm_stoppedV_le bounds ‖V_k‖² ≤ n/m².", DescribeRole.Theorem),
            Node("claim-15", "integral_mgPart_sq_le", "integral mg Part sq le",
                "E[(M_K)²] ≤ K·h·n/m². Expand the square into a double sum, kill every off-diagonal term by orthogonality (§3), and price each diagonal term by §4. E[M_K] = 0, so this is the variance.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
