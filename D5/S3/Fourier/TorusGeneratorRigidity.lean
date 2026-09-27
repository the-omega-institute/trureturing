/- GID: D5/S3/Fourier/TorusGeneratorRigidity
   generality: G
   mirror-B: D5/B/S3/Fourier/TorusGeneratorRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common power-orbit closures force torus generators to be constant on preconnected sets. -/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.TorusGeneratorRigidity

open Set

/-- A continuous family with one common natural-power orbit closure is constant
on every preconnected parameter subset. The index type need not be finite. -/
theorem result {P I : Type*} [TopologicalSpace P] {S : Set P}
    (hS : IsPreconnected S) (g : P → I → Circle) (hg : ContinuousOn g S)
    (G : Set (I → Circle))
    (hG : ∀ p ∈ S, closure (range (fun n : ℕ => g p ^ n)) = G) :
    ∀ p ∈ S, ∀ q ∈ S, g p = g q := by
  classical
  intro p hp q hq
  funext i
  let f : P → Circle := fun t => g t i
  have hf : ContinuousOn f S := (continuous_apply i).comp_continuousOn hg
  by_cases ht : ∃ t ∈ S, IsOfFinOrder (f t)
  · obtain ⟨t, ht, hfinite⟩ := ht
    have hclosed : IsClosed {v : I → Circle | v i ∈ Submonoid.powers (f t)} :=
      hfinite.finite_powers.isClosed.preimage (continuous_apply i)
    have hbound : closure (range (fun n : ℕ => g t ^ n)) ⊆
        {v : I → Circle | v i ∈ Submonoid.powers (f t)} := by
      apply closure_minimal _ hclosed
      rintro v ⟨n, rfl⟩
      exact Submonoid.mem_powers_iff _ _ |>.mpr ⟨n, rfl⟩
    have hmaps : MapsTo f S (Submonoid.powers (f t)) := by
      intro u hu
      have hmem : g u ∈ closure (range (fun n : ℕ => g t ^ n)) := by
        rw [hG t ht, ← hG u hu]
        exact subset_closure ⟨1, pow_one _⟩
      exact hbound hmem
    exact hS.constant_of_mapsTo hfinite.finite_powers.isDiscrete hf hmaps hp hq
  · have hnot (t : P) (htS : t ∈ S) : ¬ IsOfFinOrder (f t) :=
      fun h => ht ⟨t, htS, h⟩
    let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
    let a : P → AddCircle (1 : ℝ) := fun t => e.symm (f t)
    have ha : ContinuousOn a S := e.symm.continuous.comp_continuousOn hf
    have hea (t : P) : AddCircle.toCircle (a t) = f t := by
      simpa only [e, AddCircle.homeomorphCircle_apply] using e.apply_symm_apply (f t)
    have haInf (t : P) (htS : t ∈ S) : ¬ IsOfFinAddOrder (a t) := by
      intro htfin
      obtain ⟨n, hn, hzero⟩ := htfin.exists_nsmul_eq_zero
      apply hnot t htS
      refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
      rw [← hea t, ← AddCircle.toCircle_nsmul, hzero, AddCircle.toCircle_zero]
    let r : P → ℝ := fun t => AddCircle.equivIco (1 : ℝ) 0 (a t)
    have hr : ContinuousOn r S := by
      intro t htS
      have hne : a t ≠ (0 : ℝ) := by
        simpa using fun h : a t = 0 => haInf t htS (h ▸ IsOfFinAddOrder.zero)
      exact continuous_subtype_val.continuousAt.comp_continuousWithinAt
        ((AddCircle.continuousAt_equivIco (1 : ℝ) 0 hne).comp_continuousWithinAt (ha t htS))
    have hirrat (t : P) (htS : t ∈ S) (v : ℚ) : (v : ℝ) ≠ r t := by
      intro hv
      apply haInf t htS
      rw [← AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := a t)]
      apply AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div.mpr
      exact ⟨v, by simpa only [div_one] using hv⟩
    have heq (u : P) (hu : u ∈ S) (v : P) (hv : v ∈ S) : ¬ r u < r v := by
      intro huv
      obtain ⟨b, hb₁, hb₂⟩ := exists_rat_btwn huv
      obtain ⟨t, htS, ht⟩ := hS.intermediate_value hu hv hr ⟨hb₁.le, hb₂.le⟩
      exact hirrat t htS b ht.symm
    have hrpq : r p = r q := le_antisymm (le_of_not_gt (heq q hq p hp))
      (le_of_not_gt (heq p hp q hq))
    have hapq : a p = a q := by
      simpa only [r, AddCircle.coe_equivIco] using
        congrArg (fun x : ℝ => (x : AddCircle (1 : ℝ))) hrpq
    exact (hea p).symm.trans ((congrArg AddCircle.toCircle hapq).trans (hea q))

end D5.S3.Fourier.TorusGeneratorRigidity
