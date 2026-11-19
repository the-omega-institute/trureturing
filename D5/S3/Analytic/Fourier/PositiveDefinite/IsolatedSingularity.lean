/- GID: D5/S3/Analytic/Fourier/PositiveDefinite/IsolatedSingularity
   generality: G
   mirror-B: D5/B/S3/Analytic/Fourier/PositiveDefinite/IsolatedSingularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef, mathlib/module/Mathlib.Analysis.Asymptotics.Lemmas]
   utility: none
   digest: An isolated failure of a linear increment bound forces strict finite translation Gram positivity. -/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Strictness from an isolated singularity of the increment bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Filter Asymptotics
open scoped BigOperators Topology ComplexOrder

namespace D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity

/-- A null vector annihilates every translated section, including sections at
nodes already present in the configuration. -/
private lemma null_vector_translate {V : Type*} [NormedAddCommGroup V] {k : V → ℂ}
    (hk : ∀ (n : ℕ) (x : Fin n → V), Matrix.PosSemidef (fun i j => k (x j - x i)))
    {n : ℕ} (x : Fin n → V) (c : Fin n → ℂ)
    (hc : (fun i j => k (x j - x i)) *ᵥ c = 0) (t : V) :
    ∑ i, k (x i - t) * c i = 0 := by
  classical
  let y : Fin (n + 1) → V := Fin.lastCases t x
  let d : Fin (n + 1) → ℂ := Fin.lastCases 0 c
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun i j => k (y j - y i)
  have hA : A.PosSemidef := hk (n + 1) y
  have hrow (i : Fin n) : (A *ᵥ d) i.castSucc = 0 := by
    have hi := congrFun hc i
    simpa [A, y, d, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc] using hi
  have henergy : star d ⬝ᵥ A *ᵥ d = 0 := by
    rw [dotProduct, Fin.sum_univ_castSucc]
    simp only [Pi.star_apply]
    have hsum : (∑ i : Fin n, star (d i.castSucc) * (A *ᵥ d) i.castSucc) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hrow i, mul_zero]
    rw [hsum]
    simp [d]
  have hnull : A *ᵥ d = 0 := hA.dotProduct_mulVec_zero_iff.mp henergy
  have hlast := congrFun hnull (Fin.last n)
  simpa [A, y, d, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc] using hlast

/-- A translation positive definite complex kernel whose increments have a
linear bound at every nonzero base point, but no such bound at zero, has
strictly positive Gram matrices on every finite injective configuration in a normed additive commutative group.
No continuity hypothesis is needed. -/
theorem posDef_of_isolated_non_lipschitz {V : Type*} [NormedAddCommGroup V]
    {k : V → ℂ}
    (hk : ∀ (n : ℕ) (x : Fin n → V), Matrix.PosSemidef (fun i j => k (x j - x i)))
    (hregular : ∀ r : V, r ≠ 0 →
      (fun h : V => k (r + h) - k r) =O[𝓝 0] (fun h : V => h))
    (hsingular : ¬ (fun h : V => k h - k 0) =O[𝓝 0] (fun h : V => h))
    (n : ℕ) (x : Fin n → V) (hx : Function.Injective x) :
    Matrix.PosDef (fun i j => k (x j - x i)) := by
  classical
  let G : Matrix (Fin n) (Fin n) ℂ := fun i j => k (x j - x i)
  have hG : G.PosSemidef := hk n x
  have hker : ∀ c : Fin n → ℂ, G *ᵥ c = 0 → c = 0 := by
    intro c hc
    by_contra hne
    have hex : ∃ j, c j ≠ 0 := by
      by_contra! hh
      exact hne (funext hh)
    obtain ⟨j, hj⟩ := hex
    have hrel (t : V) : ∑ i, k (x i - t) * c i = 0 :=
      null_vector_translate hk x c hc t
    let E : V → Fin n → ℂ :=
      fun h i => c i * (k (x i - x j + h) - k (x i - x j))
    have hsum (h : V) : ∑ i, E h i = 0 := by
      calc
        ∑ i, E h i = (∑ i, k (x i - (x j - h)) * c i) -
            ∑ i, k (x i - x j) * c i := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          have ha : x i - (x j - h) = x i - x j + h := by abel
          rw [ha]
          dsimp only [E]
          ring
        _ = 0 := by rw [hrel, hrel, sub_self]
    have hisolate (h : V) : c j * (k h - k 0) =
        -(∑ i ∈ (Finset.univ : Finset (Fin n)).erase j, E h i) := by
      apply eq_neg_iff_add_eq_zero.mpr
      have hjE : E h j = c j * (k h - k 0) := by simp [E]
      rw [← hjE, add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      exact hsum h
    have hrest : (fun h => ∑ i ∈ (Finset.univ : Finset (Fin n)).erase j, E h i)
        =O[𝓝 0] (fun h : V => h) := by
      apply Asymptotics.IsBigO.fun_sum
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      have hr : x i - x j ≠ 0 := sub_ne_zero.mpr (fun he => hij (hx he))
      exact (hregular (x i - x j) hr).const_mul_left (c i)
    apply hsingular
    apply (Asymptotics.isBigO_const_mul_left_iff hj).mp
    exact hrest.neg_left.congr_left (fun h => (hisolate h).symm)
  apply (Matrix.posDef_iff_posSemidef_and_mulVec_injective).mpr
  refine ⟨hG, ?_⟩
  intro u v huv
  apply sub_eq_zero.mp
  exact hker (u - v) (by rw [Matrix.mulVec_sub, huv, sub_self])

end D5.S3.Analytic.Fourier.PositiveDefinite.IsolatedSingularity
