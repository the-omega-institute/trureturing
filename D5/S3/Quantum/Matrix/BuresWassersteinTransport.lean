/- GID: D5/S3/Quantum/Matrix/BuresWassersteinTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/BuresWassersteinTransport
   mirror-E: none(waiver:noncomputable-matrix-analysis)
   anchors: [lit/bhatiajainlim2018wasserstein]
   utility: none
   digest: Finite transport certificates identify the unique actual Bures–Wasserstein minimizer. -/

import D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

/-!
The finite transport optimality condition is established in Bhatia–Jain–Lim,
arXiv:1712.01504v1, Theorem 8 and (62)–(63). The elementary dual proof is
also Lemma 2 of the Ma–Zhang revision2 note (CC BY 4.0, issue #29594).
Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: NUS and ChronoAI, Singapore.
This formal interface generalizes the actual equal-weight binary consumer;
it is not a claim of a new scientific characterization.

Proof shape: the new inference is that equality of the finite positive
weighted objective forces every nonnegative fidelity gap to vanish, hence
one invertible transport fixes the minimizer. The existing fidelity
inequality, rigidity, and square-root/distance bridges are reused intact.
No separate API is retained merely for weighted summation.
All declarations are noncomputable general matrix analysis, not finite
certified instances, bounded enumeration, checkers, or numeric reductions.
-/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open private fidelity_young_rigid fidelity_transport bures_sq
  from D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation

namespace D5.S3.Quantum.Matrix.BuresWassersteinTransport

/-- A strictly positive normalized finite transport certificate proves global
minimality, characterizes every competing minimizer, and identifies the
existing epsilon-selected actual Bures–Wasserstein barycenter. -/
theorem finite_barycenter_of_dual {m n : ℕ} (w : Fin n → ℝ)
    (A T : Fin n → Matrix (Fin m) (Fin m) ℂ)
    {W : Matrix (Fin m) (Fin m) ℂ}
    (hw : ∀ j, 0 < w j) (hws : ∑ j, w j = 1)
    (hA : ∀ j, (A j).PosDef) (hW : W.PosDef)
    (hT : ∀ j, (T j).PosDef)
    (htransport : ∀ j, T j * W * T j = A j)
    (hbalance : ∑ j, w j • T j = 1) :
    (∀ X : Matrix (Fin m) (Fin m) ℂ, X.PosDef →
      (∑ j, w j * buresWassersteinDistance W (A j) ^ 2) ≤
        ∑ j, w j * buresWassersteinDistance X (A j) ^ 2) ∧
    (∀ X : Matrix (Fin m) (Fin m) ℂ, X.PosDef →
      (((∑ j, w j * buresWassersteinDistance X (A j) ^ 2) ≤
        ∑ j, w j * buresWassersteinDistance W (A j) ^ 2) ↔ X = W)) ∧
    wassersteinBarycenter w A = W := by
  classical
  let objective (X : Matrix (Fin m) (Fin m) ℂ) :=
    ∑ j, w j * buresWassersteinDistance X (A j) ^ 2
  let gap (X : Matrix (Fin m) (Fin m) ℂ) (j : Fin n) :=
    (T j * X).trace.re + ((T j)⁻¹ * A j).trace.re -
      2 * traceNorm (CFC.sqrt (A j) * CFC.sqrt X)
  have hg (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef) (j : Fin n) :
      0 ≤ gap X j := by
    have h := (fidelity_young_rigid hX (hA j) (hT j)).1
    exact sub_nonneg.mpr h
  have htr (X : Matrix (Fin m) (Fin m) ℂ) :
      ∑ j, w j * (T j * X).trace.re = X.trace.re := by
    have h := congrArg (fun Z : Matrix (Fin m) (Fin m) ℂ => (Z * X).trace.re) hbalance
    simpa only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
      Complex.re_sum, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, one_mul] using h
  have hgap (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef) :
      ∑ j, w j * gap X j = objective X - objective W := by
    have hf (j : Fin n) := fidelity_transport hW (hA j) (hT j) (htransport j)
    have hj (j : Fin n) : w j * gap X j =
        w j * buresWassersteinDistance X (A j)^2 -
          w j * buresWassersteinDistance W (A j)^2 +
          (w j * (T j * X).trace.re - w j * X.trace.re) -
          (w j * (T j * W).trace.re - w j * W.trace.re) := by
      rw [bures_sq hX (hA j), bures_sq hW (hA j), (hf j).1]
      dsimp only [gap]
      rw [(hf j).2]
      ring
    calc
      _ = (objective X - objective W) +
          ((∑ j, w j * (T j * X).trace.re) - ∑ j, w j * X.trace.re) -
          ((∑ j, w j * (T j * W).trace.re) - ∑ j, w j * W.trace.re) := by
        simp_rw [hj]
        simp only [objective, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by
        rw [htr, htr, ← Finset.sum_mul, ← Finset.sum_mul, hws]
        ring
  have hmin (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef) :
      objective W ≤ objective X := by
    have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      mul_nonneg (hw j).le (hg X hX j))
    rw [hgap X hX] at h
    exact sub_nonneg.mp h
  have hunique (X : Matrix (Fin m) (Fin m) ℂ) (hX : X.PosDef)
      (hx : objective X ≤ objective W) : X = W := by
    have hzero : ∑ j, w j * gap X j = 0 := by
      rw [hgap X hX]
      exact sub_eq_zero.mpr (le_antisymm hx (hmin X hX))
    have h_each (j : Fin n) : gap X j = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
        mul_nonneg (hw j).le (hg X hX j))).mp hzero j (Finset.mem_univ j)
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw j))
    have hn : n ≠ 0 := by
      intro hn
      subst n
      norm_num at hws
    let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have heq : 2 * traceNorm (CFC.sqrt (A j) * CFC.sqrt X) =
        (T j * X).trace.re + ((T j)⁻¹ * A j).trace.re := by
      have he := h_each j
      exact (sub_eq_zero.mp he).symm
    have ht := (fidelity_young_rigid hX (hA j) (hT j)).2 heq
    have he : T j * X * T j = T j * W * T j := ht.trans (htransport j).symm
    have hi := Matrix.nonsing_inv_mul (T j)
      ((Matrix.isUnit_iff_isUnit_det (T j)).mp (hT j).isUnit)
    have hi' := Matrix.mul_nonsing_inv (T j)
      ((Matrix.isUnit_iff_isUnit_det (T j)).mp (hT j).isUnit)
    have hc (Y : Matrix (Fin m) (Fin m) ℂ) :
        (T j)⁻¹ * (T j * Y * T j) * (T j)⁻¹ = Y := by
      calc
        _ = ((T j)⁻¹ * T j) * Y * (T j * (T j)⁻¹) := by noncomm_ring
        _ = Y := by rw [hi, hi']; simp
    exact (hc X).symm.trans ((congrArg
      (fun Z : Matrix (Fin m) (Fin m) ℂ => (T j)⁻¹ * Z * (T j)⁻¹) he).trans (hc W))
  refine ⟨hmin, ?_, ?_⟩
  · intro X hX
    exact ⟨hunique X hX, fun h => by subst X; exact le_rfl⟩
  · let pred := fun X : Matrix (Fin m) (Fin m) ℂ =>
      X.PosDef ∧ ∀ Y : Matrix (Fin m) (Fin m) ℂ, Y.PosDef → objective X ≤ objective Y
    have heps : pred (Classical.epsilon pred) := Classical.epsilon_spec ⟨W, hW, hmin⟩
    exact hunique _ heps.1 (heps.2 W hW)

end D5.S3.Quantum.Matrix.BuresWassersteinTransport
