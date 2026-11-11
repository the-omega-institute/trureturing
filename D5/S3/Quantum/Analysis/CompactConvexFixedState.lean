/- GID: D5/S3/Quantum/Analysis/CompactConvexFixedState
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompactConvexFixedState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact convex invariant sets and uniqueness from the entire real fixed dual. -/

import Mathlib

/-! # Invariant compact convex sets and the full real fixed dual -/

namespace D5.S3.Quantum.CompactConvexFixedState

open Filter Function Set
open scoped Topology

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- A real linear map has a fixed point in each nonempty compact convex invariant set. -/
theorem exists_fixed_mem (Phi : A →ₗ[ℝ] A) {B : Set A}
    (hB : IsCompact B) (hne : B.Nonempty) (hconv : Convex ℝ B)
    (hinv : MapsTo Phi B B) : ∃ x ∈ B, Phi x = x := by
  classical
  obtain ⟨b, hb⟩ := hne
  let avg : ℕ → A := fun N => birkhoffAverage ℝ (Phi : A → A) id (N + 1) b
  have hiter (k : ℕ) : (Phi : A → A)^[k] b ∈ B := by
    induction k with
    | zero => exact hb
    | succ k ih => simpa only [iterate_succ_apply'] using hinv ih
  have havg (N : ℕ) : avg N ∈ B := by
    have hN : (N + 1 : ℝ) ≠ 0 := by positivity
    have hw : ∑ _k ∈ Finset.range (N + 1), ((N + 1 : ℕ) : ℝ)⁻¹ = 1 := by
      simp [hN]
    simpa only [avg, birkhoffAverage, birkhoffSum, id_eq, Finset.smul_sum] using
      hconv.sum_mem (t := Finset.range (N + 1))
        (fun _ _ => inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ)))
        hw (fun k _ => hiter k)
  obtain ⟨x, hx, seq, hseq, hlim⟩ := hB.tendsto_subseq havg
  have hbounded : Bornology.IsBounded (range fun k => (Phi : A → A)^[k] b) :=
    hB.isBounded.subset (range_subset_iff.mpr hiter)
  have hmap (N : ℕ) : Phi (avg N) =
      birkhoffAverage ℝ (Phi : A → A) id (N + 1) (Phi b) := by
    simp only [avg, birkhoffAverage, birkhoffSum, map_smul, map_sum, id_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← iterate_succ_apply' (Phi : A → A) k b, iterate_succ_apply]
  have hdiff : Tendsto (fun N => Phi (avg N) - avg N) atTop (𝓝 0) := by
    simpa only [avg, hmap, Function.comp_def, id_eq] using
      (tendsto_birkhoffAverage_apply_sub_birkhoffAverage
        (𝕜 := ℝ) (f := (Phi : A → A)) (g := id) (x := b) hbounded).comp
        (tendsto_add_atTop_nat 1)
  refine ⟨x, hx, sub_eq_zero.mp ?_⟩
  exact tendsto_nhds_unique
    (((Phi.continuous_of_finiteDimensional.tendsto x).comp hlim).sub hlim)
    (hdiff.comp hseq.tendsto_atTop)

/-- The full real fixed-dual hypothesis determines every fixed vector from its original mass.
No interior condition on the normalized fixed vector is used. -/
theorem fixed_eq_mass_smul (Phi : A →ₗ[ℝ] A) (u : Module.Dual ℝ A)
    (hmass : u.comp Phi = u)
    (hdual : ∀ f : Module.Dual ℝ A, f.comp Phi = f → ∃ c : ℝ, f = c • u)
    {sigma : A} (hsigma : Phi sigma = sigma) (hu : u sigma = 1)
    {x : A} (hx : Phi x = x) : x = u x • sigma := by
  classical
  let T := Phi - LinearMap.id
  have hdualDim : Module.finrank ℝ (LinearMap.ker T.dualMap) ≤ 1 := by
    let v : LinearMap.ker T.dualMap := ⟨u, by
      apply LinearMap.ext
      intro a
      change u (Phi a - a) = 0
      simp only [map_sub]
      exact sub_eq_zero.mpr (congrArg (fun f : Module.Dual ℝ A => f a) hmass)⟩
    exact finrank_le_one v (by
      intro f
      have hf : (f : Module.Dual ℝ A).comp Phi = f := by
        ext a
        have hz := congrArg (fun g : Module.Dual ℝ A => g a) f.property
        change (f : Module.Dual ℝ A) (Phi a - a) = 0 at hz
        simpa only [map_sub, sub_eq_zero, LinearMap.comp_apply] using hz
      obtain ⟨c, hc⟩ := hdual f hf
      exact ⟨c, Subtype.ext hc.symm⟩)
  have hdim : Module.finrank ℝ (LinearMap.ker T) ≤ 1 := by
    have h₁ := T.finrank_range_add_finrank_ker
    have h₂ := T.dualMap.finrank_range_add_finrank_ker
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h₂
    omega
  have hs0 : sigma ≠ 0 := by
    intro hz
    simpa [hz] using hu
  have hline : Submodule.span ℝ {sigma} ≤ LinearMap.ker T := by
    rw [Submodule.span_singleton_le_iff_mem]
    change Phi sigma - sigma = 0
    exact sub_eq_zero.mpr hsigma
  have heq : Submodule.span ℝ {sigma} = LinearMap.ker T :=
    Submodule.eq_of_le_of_finrank_le hline (by
      simpa only [finrank_span_singleton hs0] using hdim)
  have hxmem : x ∈ Submodule.span ℝ {sigma} := by
    rw [heq]
    change Phi x - x = 0
    exact sub_eq_zero.mpr hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxmem
  have hcMass : u x = c := by rw [← hc, map_smul, hu, smul_eq_mul, mul_one]
  simpa only [hcMass] using hc.symm

end D5.S3.Quantum.CompactConvexFixedState
