# Chain Err Budget

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain err budget to the stochastic ellipsoid construction.

**Theorem 1.1 (inv quad nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inv_quad_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inv_quad_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Q_{A⁻¹} is non-negative: with x = A⁻¹y, ⟪y, A⁻¹y⟫ = ⟪x, Ax⟫ ≥ m‖x‖² ≥ 0.

**Theorem 1.2 (inv quad le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inv_quad_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inv_quad_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Q_{A⁻¹}(y) ≤ ‖y‖²/m, from DriftStopped2.norm_inv_apply_le and Cauchy–Schwarz.

**Theorem 1.3 (quad Form eq inner Lp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_eq_innerLp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_eq_innerLp` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Q_M(x) = ⟪x, Mx⟫ in the EuclideanSpace currency the state bounds are stated in.

**Theorem 1.4 (quad Form inv nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_inv_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_inv_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

0 ≤ Q_{A⁻¹}.

**Theorem 1.5 (quad Form inv le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_inv_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_inv_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Q_{A⁻¹}(x) ≤ (x ⬝ᵥ x)/m.

**Theorem 1.6 (neg quad Form le op Norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.neg_quadForm_le_opNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.neg_quadForm_le_opNorm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

−Q_B(x) ≤ ‖B‖_op · (x ⬝ᵥ x): the increment's overshoot along one constraint direction.

**Theorem 1.7 (norm q UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.norm_qUT`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.norm_qUT` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

‖q x‖ = x ⬝ᵥ x: the constraint vector's norm is the squared length of the lattice point.

**Theorem 1.8 (inner mat To UT lift sub).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ChainWiring.inner_lift_sub with the test matrix in matrix currency.

**Theorem 1.9 (lift coeff nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.lift_coeff_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.lift_coeff_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The coefficients of the one-sided lift are non-negative.

**Theorem 1.10 (inner mat To UT lift sub nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The lift's trace cost is non-negative against any positive semi-definite test matrix.

**Theorem 1.11 (inner mat To UT lift sub le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The lift's trace cost, with no Frobenius norm. ChainWiring.coeff_le replaces the coefficient by the step's own increment against the same constraint, ‖q i‖ = x_i ⬝ᵥ x_i cancels the squared length, and each broken constraint costs at most t/m — the increment's operator scale over the state's lower bound. A Frobenius Cauchy–Schwarz would cost a further √n.

**Theorem 1.12 (lift Cost le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.liftCost_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.liftCost_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The freeze cost, above. StepInputs2.log_det_step_unconj at the pre-lift state bounds log det by its linearisation; §3 prices the linearisation at |violated| · t / m.

**Theorem 1.13 (lift Cost nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.liftCost_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.liftCost_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The freeze cost is non-negative. log_det_step_unconj run *backwards* — at the lifted state, with H = −Δ — bounds log det A' by log det (lift A') minus the trace term, and that term is ∑_i λ_i ⟪(lift A')⁻¹ x_i, x_i⟫ ≥ 0: the coefficients of a one-sided lift are non-negative and the inverse of a positive definite matrix is positive semi-definite. So the two-sided freeze budget is the one-sided one.

**Theorem 1.14 (pre State eq sum).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.preState_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.preState_eq_sum` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A'_k = A₀ + Σ_{j<k+1} π_jξ_j + Σ_{j<k} Δ_j: the pre-lift state carries the accumulated Gaussian part at k+1 and the accumulated lift at k.

**Theorem 1.15 (state Bounds pre State).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.stateBounds_preState`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.stateBounds_preState` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

StateBounds at the pre-lift state, at the same m and M as the chain's own states: stateGood (k+1) bounds the accumulated Gaussian part at k+1 and stateGood k the lift at k.

**Theorem 1.16 (card new Active le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.card_newActive_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.card_newActive_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The count of constraints broken at one step, bounded by the accumulated contact count.

**Theorem 1.17 (chain Err abs le of lt tau).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.chainErr_abs_le_of_lt_tau`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.chainErr_abs_le_of_lt_tau` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The two-sided form, as hbdabs reads it, at ε = c₃ · η / m.

**Theorem 1.18 (lt tau of le pred).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.lt_tau_of_le_pred`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.lt_tau_of_le_pred` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

k + 1 ≤ τ − 1 is k + 1 < τ, since the chain never stops at 0.

**Definition 1.19 (Stopped Err Budget).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.StoppedErrBudget`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.StoppedErrBudget` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reformulation of GoodPathBounds.goodPathAt_of_S's hbdabs. That binder reads ∀ ω, ∀ k, |chainErr … k ω| ≤ ε, on *every* path; this is the same bound restricted to the one branch of DriftStopped.stoppedErr (:70) that evaluates chainErr, namely k + 1 ≤ τ ω − 1. Off the stopping event the chain's state has no lower bound and chainErr is not bounded at all, so the unrestricted binder is not provable; this one is (§7).

**Theorem 1.20 (stopped Err Budget of params).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.stoppedErrBudget_of_params`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.stoppedErrBudget_of_params` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The deliverable. ε = c₃ · η / (a₀ − (r₀ + c₃η)) — the accumulated contact bound times the per-step increment's operator scale, over the state's lower bound.

**Definition 1.21 (eps At).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.epsAt`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.epsAt` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ε at the adopted parameters, at a free contact threshold: the accumulated contact bound c₃ times the per-step increment scale η, over the state's lower bound mAt n c₃.

**Theorem 1.22 (integrable stopped Err of stopped).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.integrable_stoppedErr_of_stopped`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.integrable_stoppedErr_of_stopped` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A uniform error bound before the stopping index ensures integrability of the stopped error. Outside that range the stopped error vanishes.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.StoppedErrBudget`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.card_newActive_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.chainErr_abs_le_of_lt_tau`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.epsAt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inner_matToUT_lift_sub_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.integrable_stoppedErr_of_stopped`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inv_quad_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.inv_quad_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.liftCost_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.liftCost_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.lift_coeff_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.lt_tau_of_le_pred`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.neg_quadForm_le_opNorm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.norm_qUT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.preState_eq_sum`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_eq_innerLp`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_inv_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.quadForm_inv_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.stateBounds_preState`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget.stoppedErrBudget_of_params`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds](../Completion/GoodPathBounds.md)
