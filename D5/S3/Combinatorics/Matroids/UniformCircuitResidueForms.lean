/- GID: D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/UniformCircuitResidueForms
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Alternating form reduction of the uniform circuit and boundary equations. -/

module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-! The effect of a distinguished coordinate on a pair of exterior operations. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms

open AlternatingMap
set_option autoImplicit false

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] {n : ℕ}

/-- Multiplication by a covector on alternating forms. -/
def covectorWedge (a : M →ₗ[R] R) (f : M [⋀^Fin n]→ₗ[R] N) :
    M [⋀^Fin (n + 1)]→ₗ[R] N :=
  alternatizeUncurryFin (a.smulRight f)

/-- Inserting a vector into a covector product gives a scalar term and a product
of the insertion into the original form. -/
theorem curry_covectorWedge (a : M →ₗ[R] R) (x : M) (f : M [⋀^Fin (n + 1)]→ₗ[R] N) :
    (covectorWedge a f).curryLeft x = a x • f - covectorWedge a (f.curryLeft x) := by
  ext v
  rw [curryLeft_apply_apply, covectorWedge, alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  simp only [curryLeft_apply_apply, covectorWedge, alternatizeUncurryFin_apply,
    Matrix.vecCons, Fin.val_zero, pow_zero, one_smul,
    Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons, smul_apply, sub_apply,
    LinearMap.smulRight_apply]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hr : i.succ.removeNth (Fin.cons x v : Fin (n + 2) → M) =
      (Fin.cons x (i.removeNth v) : Fin (n + 1) → M) :=
    Fin.cons_comp_succ_succAbove x v i
  rw [Fin.cons_succ, hr, Fin.val_succ, pow_succ, mul_smul, neg_one_smul, smul_neg]

private lemma covectorWedge_zero (a : M →ₗ[R] R) :
    covectorWedge a (0 : M [⋀^Fin n]→ₗ[R] N) = 0 := by
  ext v
  simp [covectorWedge, alternatizeUncurryFin_apply]

private lemma covectorWedge_sq (a : M →ₗ[R] R) (f : M [⋀^Fin n]→ₗ[R] N) :
    covectorWedge a (covectorWedge a f) = 0 := by
  let b := a.smulRight (a.smulRight f)
  have hb : a.smulRight (covectorWedge a f) = alternatizeUncurryFinLM ∘ₗ b := by
    apply LinearMap.ext
    intro x
    simp [b, covectorWedge]
  rw [covectorWedge, hb]
  apply alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
  intro x y
  simp only [b, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]
  rw [mul_comm]

private lemma curry_curry_swap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (x y : M) :
    (f.curryLeft x).curryLeft y = -(f.curryLeft y).curryLeft x := by
  ext v
  have h := f.map_insertNth (Fin.succ 0) y (Fin.cons x v)
  rw [Fin.insertNth_succ_cons, Fin.insertNth_zero'] at h
  simpa [curryLeft_apply_apply, Matrix.vecCons] using h

/-- A pivot on which the covector takes the value one splits the simultaneous
kernel of covector multiplication and insertion. -/
theorem closed_horizontal_iff (a : M →ₗ[R] R) (x y : M) (hx : a x = 1)
    (f : M [⋀^Fin (n + 2)]→ₗ[R] N) :
    covectorWedge a f = 0 ∧ f.curryLeft y = 0 ↔
      ∃ g : M [⋀^Fin (n + 1)]→ₗ[R] N, g.curryLeft x = 0 ∧
        f = covectorWedge a g ∧ a y • g = 0 ∧ g.curryLeft y = 0 := by
  constructor
  · rintro ⟨hclosed, hhorizontal⟩
    let g := f.curryLeft x
    have hgy : g.curryLeft y = 0 := by
      change (f.curryLeft x).curryLeft y = 0
      rw [curry_curry_swap, hhorizontal, curryLeft_zero, LinearMap.zero_apply, neg_zero]
    have heq := curry_covectorWedge a x f
    rw [hclosed, curryLeft_zero, LinearMap.zero_apply, hx, one_smul] at heq
    have hf : f = covectorWedge a g := sub_eq_zero.mp heq.symm
    refine ⟨g, curryLeft_same f x, hf, ?_, hgy⟩
    rw [hf, curry_covectorWedge, hgy] at hhorizontal
    simpa only [covectorWedge_zero, sub_zero] using hhorizontal
  · rintro ⟨g, _, rfl, hweighted, hgy⟩
    refine ⟨covectorWedge_sq a g, ?_⟩
    rw [curry_covectorWedge, hweighted, hgy]
    rw [covectorWedge_zero, sub_zero]

end D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms
