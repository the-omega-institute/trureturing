using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainErrBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Err Budget"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain err budget to the stochastic ellipsoid construction.")),
            Node("claim-1", "inv_quad_nonneg", "inv quad nonneg",
                "Q_{A⁻¹} is non-negative: with x = A⁻¹y, ⟪y, A⁻¹y⟫ = ⟪x, Ax⟫ ≥ m‖x‖² ≥ 0.", DescribeRole.Theorem),
            Node("claim-2", "inv_quad_le", "inv quad le",
                "Q_{A⁻¹}(y) ≤ ‖y‖²/m, from DriftStopped2.norm_inv_apply_le and Cauchy–Schwarz.", DescribeRole.Theorem),
            Node("claim-3", "quadForm_eq_innerLp", "quad Form eq inner Lp",
                "Q_M(x) = ⟪x, Mx⟫ in the EuclideanSpace currency the state bounds are stated in.", DescribeRole.Theorem),
            Node("claim-5", "quadForm_inv_nonneg", "quad Form inv nonneg",
                "0 ≤ Q_{A⁻¹}.", DescribeRole.Theorem),
            Node("claim-6", "quadForm_inv_le", "quad Form inv le",
                "Q_{A⁻¹}(x) ≤ (x ⬝ᵥ x)/m.", DescribeRole.Theorem),
            Node("claim-7", "neg_quadForm_le_opNorm", "neg quad Form le op Norm",
                "−Q_B(x) ≤ ‖B‖_op · (x ⬝ᵥ x): the increment's overshoot along one constraint direction.", DescribeRole.Theorem),
            Node("claim-8", "norm_qUT", "norm q UT",
                "‖q x‖ = x ⬝ᵥ x: the constraint vector's norm is the squared length of the lattice point.", DescribeRole.Theorem),
            Node("claim-10", "inner_matToUT_lift_sub", "inner mat To UT lift sub",
                "ChainWiring.inner_lift_sub with the test matrix in matrix currency.", DescribeRole.Theorem),
            Node("claim-11", "lift_coeff_nonneg", "lift coeff nonneg",
                "The coefficients of the one-sided lift are non-negative.", DescribeRole.Theorem),
            Node("claim-12", "inner_matToUT_lift_sub_nonneg", "inner mat To UT lift sub nonneg",
                "The lift's trace cost is non-negative against any positive semi-definite test matrix.", DescribeRole.Theorem),
            Node("claim-13", "inner_matToUT_lift_sub_le", "inner mat To UT lift sub le",
                "The lift's trace cost, with no Frobenius norm. ChainWiring.coeff_le replaces the coefficient by the step's own increment against the same constraint, ‖q i‖ = x_i ⬝ᵥ x_i cancels the squared length, and each broken constraint costs at most t/m — the increment's operator scale over the state's lower bound. A Frobenius Cauchy–Schwarz would cost a further √n.", DescribeRole.Theorem),
            Node("claim-14", "liftCost_le", "lift Cost le",
                "The freeze cost, above. StepInputs2.log_det_step_unconj at the pre-lift state bounds log det by its linearisation; §3 prices the linearisation at |violated| · t / m.", DescribeRole.Theorem),
            Node("claim-15", "liftCost_nonneg", "lift Cost nonneg",
                "The freeze cost is non-negative. log_det_step_unconj run *backwards* — at the lifted state, with H = −Δ — bounds log det A' by log det (lift A') minus the trace term, and that term is ∑_i λ_i ⟪(lift A')⁻¹ x_i, x_i⟫ ≥ 0: the coefficients of a one-sided lift are non-negative and the inverse of a positive definite matrix is positive semi-definite. So the two-sided freeze budget is the one-sided one.", DescribeRole.Theorem),
            Node("claim-16", "preState_eq_sum", "pre State eq sum",
                "A'_k = A₀ + Σ_{j<k+1} π_jξ_j + Σ_{j<k} Δ_j: the pre-lift state carries the accumulated Gaussian part at k+1 and the accumulated lift at k.", DescribeRole.Theorem),
            Node("claim-17", "stateBounds_preState", "state Bounds pre State",
                "StateBounds at the pre-lift state, at the same m and M as the chain's own states: stateGood (k+1) bounds the accumulated Gaussian part at k+1 and stateGood k the lift at k.", DescribeRole.Theorem),
            Node("claim-19", "card_newActive_le", "card new Active le",
                "The count of constraints broken at one step, bounded by the accumulated contact count.", DescribeRole.Theorem),
            Node("claim-20", "chainErr_abs_le_of_lt_tau", "chain Err abs le of lt tau",
                "The two-sided form, as hbdabs reads it, at ε = c₃ · η / m.", DescribeRole.Theorem),
            Node("claim-22", "lt_tau_of_le_pred", "lt tau of le pred",
                "k + 1 ≤ τ − 1 is k + 1 < τ, since the chain never stops at 0.", DescribeRole.Theorem),
            Node("claim-23", "StoppedErrBudget", "Stopped Err Budget",
                "The reformulation of GoodPathBounds.goodPathAt_of_S's hbdabs. That binder reads ∀ ω, ∀ k, |chainErr … k ω| ≤ ε, on *every* path; this is the same bound restricted to the one branch of DriftStopped.stoppedErr (:70) that evaluates chainErr, namely k + 1 ≤ τ ω − 1. Off the stopping event the chain's state has no lower bound and chainErr is not bounded at all, so the unrestricted binder is not provable; this one is (§7).", DescribeRole.Definition),
            Node("claim-24", "stoppedErrBudget_of_params", "stopped Err Budget of params",
                "The deliverable. ε = c₃ · η / (a₀ − (r₀ + c₃η)) — the accumulated contact bound times the per-step increment's operator scale, over the state's lower bound.", DescribeRole.Theorem),
            Node("claim-25", "epsAt", "eps At",
                "ε at the adopted parameters, at a free contact threshold: the accumulated contact bound c₃ times the per-step increment scale η, over the state's lower bound mAt n c₃.", DescribeRole.Definition),
            Node("claim-26", "integrable_stoppedErr_of_stopped", "integrable stopped Err of stopped",
                "A uniform error bound before the stopping index ensures integrability of the stopped error. Outside that range the stopped error vanishes.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
