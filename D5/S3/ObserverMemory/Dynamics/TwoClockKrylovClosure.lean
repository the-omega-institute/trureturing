/- GID: D5/S3/ObserverMemory/Dynamics/TwoClockKrylovClosure
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/TwoClockKrylovClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two incommensurable exponential samples generate the full real Krylov closure. -/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NormedSpace ContinuousLinearMap

namespace D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

local instance : NormedAlgebra ℚ (V →L[ℝ] V) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

private theorem exp_preserves (A : V →L[ℝ] V) (U : Submodule ℝ V)
    (hA : ∀ x ∈ U, A x ∈ U) (t : ℝ) :
    ∀ x ∈ U, exp (t • A) x ∈ U := by
  intro x hx
  have hp : ∀ k : ℕ, ((t • A) ^ k) x ∈ U := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      simpa [pow_succ', mul_apply] using U.smul_mem t (hA _ ih)
  have hs := (ContinuousLinearMap.apply ℝ V x).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℝ) (t • A))
  change (ContinuousLinearMap.apply ℝ V x) (exp (t • A)) ∈ U
  rw [← hs.tsum_eq]
  exact tsum_mem U.closed_of_finiteDimensional fun k =>
    U.smul_mem _ (hp k)

private theorem generator_mem_of_two_samples
    (A : V →L[ℝ] V) (U : Submodule ℝ V) (a b : ℝ)
    (hirr : Irrational (a / b))
    (ha : ∀ x ∈ U, exp (a • A) x ∈ U)
    (hb : ∀ x ∈ U, exp (b • A) x ∈ U) :
    ∀ x ∈ U, A x ∈ U := by
  have hadd (s t : ℝ) : exp ((s + t) • A) = exp (s • A) * exp (t • A) := by
    rw [add_smul, exp_add_of_commute]
    exact ((Commute.refl A).smul_left s).smul_right t
  have hcancel (t : ℝ) : exp ((-t) • A) * exp (t • A) = 1 := by
    rw [← hadd, neg_add_cancel, zero_smul, exp_zero]
  let H : AddSubgroup ℝ := {
    carrier := {t | ∀ x ∈ U, exp (t • A) x ∈ U}
    zero_mem' := by simp
    add_mem' := by
      intro s t hs ht x hx
      rw [hadd, mul_apply_eq_comp]
      exact hs _ (ht _ hx)
    neg_mem' := by
      intro t ht
      let f : U →ₗ[ℝ] U := (exp (t • A)).toLinearMap.restrict ht
      have hinj : Function.Injective f := by
        intro x y heq
        apply Subtype.ext
        have heq' := congrArg (fun z : U => exp ((-t) • A) z.1) heq
        change exp ((-t) • A) (exp (t • A) x.1) =
          exp ((-t) • A) (exp (t • A) y.1) at heq'
        simpa only [← mul_apply_eq_comp, hcancel, one_apply_eq_self] using heq'
      have hsurj := LinearMap.surjective_of_injective hinj
      intro x hx
      obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
      have heq := congrArg (fun z : U => exp ((-t) • A) z.1) hy
      change exp ((-t) • A) (exp (t • A) y.1) = exp ((-t) • A) x at heq
      have hxy : exp ((-t) • A) x = y.1 := by
        simpa only [← mul_apply_eq_comp, hcancel, one_apply_eq_self] using heq.symm
      rw [hxy]
      exact y.property }
  have hpair : AddSubgroup.closure ({a, b} : Set ℝ) ≤ H := by
    apply (AddSubgroup.closure_le H).2
    exact Set.pair_subset_iff.mpr ⟨ha, hb⟩
  have hd : Dense (H : Set ℝ) :=
    ((dense_addSubgroupClosure_pair_iff).2 hirr).mono hpair
  have hall : ∀ (t : ℝ) (x : V), x ∈ U → exp (t • A) x ∈ U := by
    intro t x hx
    have hclosed : IsClosed {s : ℝ | exp (s • A) x ∈ U} :=
      U.closed_of_finiteDimensional.preimage
      ((exp_continuous.comp (continuous_id.smul continuous_const)).clm_apply continuous_const)
    exact hd.induction (fun s hs => hs x hx) hclosed t
  intro x hx
  have hd0 := (ContinuousLinearMap.apply ℝ V x).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const A (0 : ℝ))
  have hm := U.closed_of_finiteDimensional.mem_of_tendsto hd0.tendsto_slope_zero
    (by
      filter_upwards with s
      exact U.smul_mem _ (U.sub_mem (hall (0 + s) x hx) (hall 0 x hx)))
  simpa using hm

/-- In finite real dimension, mixed nonnegative powers of two exponential samples
with irrational time ratio span exactly the generator's full Krylov orbit. -/
theorem two_clock_span_eq_krylov
    (A : V →L[ℝ] V) (W : Submodule ℝ V) (a b : ℝ)
    (hirr : Irrational (a / b)) :
    Submodule.span ℝ {x | ∃ (k l : ℕ) (w : V), w ∈ W ∧
      x = (exp (a • A) ^ k) ((exp (b • A) ^ l) w)} =
    Submodule.span ℝ {x | ∃ (k : ℕ) (w : V), w ∈ W ∧ x = (A ^ k) w} := by
  let F := exp (a • A)
  let G := exp (b • A)
  let U := Submodule.span ℝ {x | ∃ (k l : ℕ) (w : V), w ∈ W ∧
    x = (F ^ k) ((G ^ l) w)}
  let K := Submodule.span ℝ {x | ∃ (k : ℕ) (w : V), w ∈ W ∧ x = (A ^ k) w}
  change U = K
  have hcomm : Commute G F :=
    (((Commute.refl A).smul_left b).smul_right a).exp
  have hW_U : W ≤ U := by
    intro w hw
    exact Submodule.subset_span ⟨0, 0, w, hw, by simp⟩
  have hF : ∀ x ∈ U, F x ∈ U := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => F x ∈ U) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨k, l, w, hw, rfl⟩
      exact Submodule.subset_span ⟨k + 1, l, w, hw, by simp [pow_succ']⟩
    · simp
    · intro x y _ _ hx hy
      simpa using U.add_mem hx hy
    · intro c x _ hx
      simpa using U.smul_mem c hx
  have hG : ∀ x ∈ U, G x ∈ U := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => G x ∈ U) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨k, l, w, hw, rfl⟩
      apply Submodule.subset_span
      refine ⟨k, l + 1, w, hw, ?_⟩
      change (G * F ^ k) ((G ^ l) w) = _
      rw [(hcomm.pow_right k).eq]
      simp [pow_succ']
    · simp
    · intro x y _ _ hx hy
      simpa using U.add_mem hx hy
    · intro c x _ hx
      simpa using U.smul_mem c hx
  have hAU := generator_mem_of_two_samples A U a b hirr hF hG
  have hK_U : K ≤ U := by
    apply Submodule.span_le.2
    rintro x ⟨k, w, hw, rfl⟩
    induction k with
    | zero => simpa using hW_U hw
    | succ k ih => simpa [pow_succ'] using hAU _ ih
  have hW_K : W ≤ K := by
    intro w hw
    exact Submodule.subset_span ⟨0, w, hw, by simp⟩
  have hAK : ∀ x ∈ K, A x ∈ K := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => A x ∈ K) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨k, w, hw, rfl⟩
      exact Submodule.subset_span ⟨k + 1, w, hw, by simp [pow_succ']⟩
    · simp
    · intro x y _ _ hx hy
      simpa using K.add_mem hx hy
    · intro c x _ hx
      simpa using K.smul_mem c hx
  have hFK := exp_preserves A K hAK a
  have hGK := exp_preserves A K hAK b
  apply le_antisymm _ hK_U
  apply Submodule.span_le.2
  rintro x ⟨k, l, w, hw, rfl⟩
  have hl : (G ^ l) w ∈ K := by
    induction l with
    | zero => simpa using hW_K hw
    | succ l ih => simpa [G, pow_succ'] using hGK _ ih
  induction k with
  | zero => simpa using hl
  | succ k ih => simpa [F, pow_succ'] using hFK _ ih

#print axioms two_clock_span_eq_krylov

end D5.S3.ObserverMemory.Dynamics.TwoClockKrylovClosure
