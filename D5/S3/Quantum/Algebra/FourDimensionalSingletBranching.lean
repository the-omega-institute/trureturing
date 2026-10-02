/- GID: D5/S3/Quantum/Algebra/FourDimensionalSingletBranching
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FourDimensionalSingletBranching
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No det-1 rep on C^4 without singlet has singlets on all cyclic subgroups (1710.09237). -/

/-
proof_shape: result: bind-only (the determinant identity for `1 - A` on `ℂ⁴`, the averaging of
  the representation, and the rank of the idempotent `(∑ D h ⊗ D h)(1 - Swap)/(2|H|)` via
  `LinearMap.IsProj.trace`; every step is a local `have` of `result`)
escape_witness: null
admission_basis: open-problem-resolution (issue #11489)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.FourDimensionalSingletBranching

/-!
S. Groot Nibbelink, O. Loukas, A. Mütter, E. Parr and P. K. S. Vaudrevange, *Tension between a
vanishing cosmological constant and non-supersymmetric heterotic orbifolds*, arXiv:1710.09237
(Fortschr. Phys. 68 (2020) 2000044), conjecture that no finite group `H` has a four-dimensional
representation `D` with (i) `det D(h) = 1` for all `h`, (ii) no trivial singlet, and (iii) a
trivial singlet in the branching to every cyclic subgroup. It holds. For `det A = 1` on `ℂ⁴`,
`det(1 - A) = 2 - tr A - tr A⁻¹ + e₂(A)`. Summing over `H`, the linear terms vanish by (ii), and
`∑ e₂(D h) = |H| · rank Q` for the idempotent `Q = (∑ D h ⊗ D h)(1 - Swap)/(2|H|)`. So
`∑ det(1 - D h) = |H|(2 + rank Q) ≠ 0`, while (iii) makes every `det(1 - D h)` vanish.
-/

open Matrix
open scoped Kronecker

/-- The conjecture of arXiv:1710.09237: no finite group has a four-dimensional representation with
(i) trivial determinant and (ii) no trivial singlet whose branchings to all cyclic subgroups
(iii) contain the trivial singlet. -/
def claim : Prop :=
  ∀ (H : Type) [Group H] [Fintype H] (D : H →* Matrix (Fin 4) (Fin 4) ℂ),
    (∀ h, (D h).det = 1) →
    (∀ v : Fin 4 → ℂ, (∀ h, D h *ᵥ v = v) → v = 0) →
    ¬ ∀ K : Subgroup H, IsCyclic K → ∃ v : Fin 4 → ℂ, v ≠ 0 ∧ ∀ k ∈ K, D k *ᵥ v = v

/-- The conjecture holds. -/
theorem result : claim := by
  intro H _ _ D hdet hfix hcyc
  have hid : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, (1 - A).det =
      1 - A.trace + ((A.trace) ^ 2 - (A * A).trace) / 2 - A.adjugate.trace + A.det := by
    intro A
    simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero, Matrix.trace,
      Matrix.diag_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.mul_apply,
      Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, Fin.succAbove,
      Fin.sum_univ_zero]
    simp
    ring
  have hsing : ∀ h, (1 - D h).det = 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := hcyc (Subgroup.zpowers h) inferInstance
    have hker : (1 - D h) *ᵥ v = 0 := by
      rw [sub_mulVec, one_mulVec, hv h (Subgroup.mem_zpowers h), sub_self]
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩
  have hadj : ∀ h, (D h).adjugate = D h⁻¹ := by
    intro h
    have hl : D h⁻¹ * D h = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [← Matrix.inv_eq_left_inv hl, Matrix.inv_def, hdet h]
    simp
  have hS : ∑ h, D h = 0 := by
    have hinv : ∀ g, D g * ∑ h, D h = ∑ h, D h := by
      intro g
      rw [Finset.mul_sum]
      simp only [← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
    ext i j
    have hv := hfix ((∑ h, D h) *ᵥ Pi.single j 1) (fun g => by rw [mulVec_mulVec, hinv])
    have := congrFun hv i
    simpa [mulVec_single] using this
  have htr : ∑ h, (D h).trace = 0 := by rw [← trace_sum, hS, trace_zero]
  have htrinv : ∑ h, (D h⁻¹).trace = 0 := by
    rw [← htr]
    exact Fintype.sum_equiv (Equiv.inv H) _ _ (fun _ => rfl)
  have sum_e2 : ∃ m : ℕ, ∑ h, (((D h).trace) ^ 2 - (D h * D h).trace) / 2 =
      (Fintype.card H : ℂ) * m := by
    let W : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
      Matrix.of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0
    let T : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ := ∑ h, D h ⊗ₖ D h
    have hWcomm : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, (A ⊗ₖ A) * W = W * (A ⊗ₖ A) := by
      intro A
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [W, mul_apply, kroneckerMap_apply, of_apply, Fintype.sum_prod_type]
      simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]
    have hWW : W * W = 1 := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [W, mul_apply, of_apply, Fintype.sum_prod_type, one_apply, Prod.mk.injEq]
      simp [ite_and, Finset.sum_ite_eq']
    have htrW : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, ((A ⊗ₖ A) * W).trace = (A * A).trace := by
      intro A
      simp only [W, trace, diag_apply, mul_apply, kroneckerMap_apply, of_apply,
        Fintype.sum_prod_type]
      simp [ite_and, Finset.sum_ite_eq']
    have hTW : T * W = W * T := by
      change (∑ h, D h ⊗ₖ D h) * W = W * ∑ h, D h ⊗ₖ D h
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => hWcomm _
    have hTT : T * T = (Fintype.card H : ℂ) • T := by
      have hrow : ∀ g : H, (D g ⊗ₖ D g) * T = T := by
        intro g
        change (D g ⊗ₖ D g) * ∑ h, D h ⊗ₖ D h = ∑ h, D h ⊗ₖ D h
        rw [Finset.mul_sum]
        simp only [← mul_kronecker_mul, ← map_mul]
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
      calc T * T = ∑ g, (D g ⊗ₖ D g) * T := by
            change (∑ g, D g ⊗ₖ D g) * T = _
            rw [Finset.sum_mul]
        _ = ∑ _g : H, T := Finset.sum_congr rfl fun g _ => hrow g
        _ = (Fintype.card H : ℂ) • T := by
            rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    let c : ℂ := (2 * (Fintype.card H : ℂ))⁻¹
    let Q := c • (T * (1 - W))
    have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hQ : Q * Q = Q := by
      have h1 : (1 - W) * (1 - W) = (2 : ℂ) • (1 - W) := by
        rw [sub_mul, mul_sub, mul_sub, hWW]; simp only [one_mul, mul_one]; module
      have hc : (1 - W) * T = T * (1 - W) := by
        rw [sub_mul, mul_sub, one_mul, mul_one, hTW]
      have e : T * (1 - W) * (T * (1 - W)) = T * T * ((1 - W) * (1 - W)) := by
        rw [mul_assoc, ← mul_assoc (1 - W) T (1 - W), hc, mul_assoc T (1 - W) (1 - W),
          ← mul_assoc T T]
      simp only [Q, e, hTT, h1, smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      simp only [c]
      field_simp
    have hId : IsIdempotentElem Q.toLin' := by
      change Q.toLin'.comp Q.toLin' = Q.toLin'
      rw [← Matrix.toLin'_mul, hQ]
    refine ⟨Module.finrank ℂ (LinearMap.range Q.toLin'), ?_⟩
    have hrank : Q.trace = (Module.finrank ℂ (LinearMap.range Q.toLin') : ℂ) :=
      (Matrix.trace_toLin'_eq Q).symm.trans (LinearMap.IsIdempotentElem.isProj_range _ hId).trace
    rw [← hrank]
    simp only [Q, c, trace_smul, mul_sub, mul_one, trace_sub, T, Finset.sum_mul, trace_sum,
      htrW, trace_kronecker, smul_eq_mul]
    have hsplit : ∑ h, (((D h).trace) ^ 2 - (D h * D h).trace) / 2 =
        ((∑ h, (D h).trace * (D h).trace) - ∑ h, (D h * D h).trace) / 2 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.sum_sub_distrib, pow_two]
    rw [hsplit]
    field_simp
  obtain ⟨m, hm⟩ := sum_e2
  have hsum : ∑ h, (1 - D h).det = (Fintype.card H : ℂ) * (2 + m) := by
    simp only [hid, hdet, hadj]
    have e : ∀ h, 1 - (D h).trace + (((D h).trace) ^ 2 - (D h * D h).trace) / 2 -
        (D h⁻¹).trace + 1 = 2 + (((D h).trace) ^ 2 - (D h * D h).trace) / 2 -
        (D h).trace - (D h⁻¹).trace := fun h => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, htr, htrinv, hm,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  simp only [hsing, Finset.sum_const_zero] at hsum
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : (2 + (m : ℂ)) ≠ 0 := by
    have : (2 + (m : ℂ)) = ((2 + m : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 2 + m ≠ 0)
  exact mul_ne_zero hcard h2 hsum.symm

end D5.S3.Quantum.Algebra.FourDimensionalSingletBranching
