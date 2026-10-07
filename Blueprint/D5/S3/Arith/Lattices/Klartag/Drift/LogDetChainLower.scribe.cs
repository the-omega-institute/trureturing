using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class LogDetChainLowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Log Det Chain Lower"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate log det chain lower to the stochastic ellipsoid construction.")),
            Node("claim-3", "frobenius_symMat", "frobenius sym Mat",
                "symMat is a Frobenius isometry: ∑ᵢⱼ (symMat x)ᵢⱼ² = ‖x‖².", DescribeRole.Theorem),
            Node("claim-4", "logDet_add_ge", "log Det add ge",
                "LogDetLowerSharp.log_det_add_ge_sharp_of_stateBounds, in EuclideanSpace coordinates.", DescribeRole.Theorem),
            Node("claim-5", "incr", "incr",
                "The one-step increment H_j = A_{j+1} − A_j. By StateInvariant.preState_eq and StateInvariant.liftStep it is gaussStep_j + liftStep_j.", DescribeRole.Definition),
            Node("claim-7", "incr_eq", "incr eq",
                "incr = gaussStep + liftStep — the split the martingale and the drift read.", DescribeRole.Theorem),
            Node("claim-8", "logDet_chain_ge", "log Det chain ge",
                "The pathwise lower bound on the chain's log-determinant. Pure telescoping: the hypotheses are the state bounds at every index below K and a per-step operator-norm ceiling, both of which goodCut supplies.", DescribeRole.Theorem),
            Node("claim-9", "logDet_chain_ge_split", "log Det chain ge split",
                "The bound in the shape ShortfallBound.shortfall_le consumes: X ≥ c + M − D with c = logDet A₀, M the trace sum and D the Frobenius sum scaled by κ.", DescribeRole.Theorem),
            Node("claim-10", "norm_incr_sq_le", "norm incr sq le",
                "The Frobenius sum, dominated by the unprojected steps plus the lift. ‖a + b‖² ≤ (1+ε)‖a‖² + (1+1/ε)‖b‖², and ‖gaussStep_j‖ ≤ ‖ξ_j‖ because it is an orthogonal projection.", DescribeRole.Theorem),
            Node("claim-11", "Vcoef", "Vcoef",
                "The chain's martingale coefficient V_j = π_j (matToUT A_j⁻¹) — the V of StepInputs2.driftInputs_step_chain and of DriftStopped2.norm_stoppedV_le.", DescribeRole.Definition),
            Node("claim-12", "chain_succ_eq_lift", "chain succ eq lift",
                "A_{j+1} = lift (preState j).", DescribeRole.Theorem),
            Node("claim-13", "liftStep_eq_lift_sub", "lift Step eq lift sub",
                "liftStep j = lift (preState j) − preState j, the shape inner_matToUT_lift_sub_nonneg consumes.", DescribeRole.Theorem),
            Node("claim-14", "trace_incr_eq", "trace incr eq",
                "The trace term splits into the martingale increment and the lift's trace cost.", DescribeRole.Theorem),
            Node("claim-15", "inner_liftStep_nonneg", "inner lift Step nonneg",
                "The lift's trace cost is non-negative against A_j⁻¹, which is positive semi-definite on the state bounds. This is what lets the drift's *upper* accounting be dropped entirely in the lower direction: the lift can only raise the log-determinant.", DescribeRole.Theorem),
            Node("claim-16", "logDet_chain_ge_martingale", "log Det chain ge martingale",
                "The pathwise lower bound, final shape. X ≥ c + M − D with c = logDet A₀, M = ∑_{j<K} ⟪V_j, ξ_j⟫ the martingale and D = κ · ∑_{j<K} ‖H_j‖² the drift proxy. This is exactly ShortfallBound.shortfall_le's hlow.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
