/- GID: D5/S3/ConceptDynamics/Experiment/SelfCalibratingActionObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/SelfCalibratingActionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-read exact recovery protocols have no uniform finite atomic-action bound. -/

import D5.S3.ConceptDynamics.Experiment.SelfCalibratingFibers

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace D5.S3.ConceptDynamics.Experiment.SelfCalibratingActionObstruction
open SelfCalibratingRulings
open SelfCalibratingFibers
noncomputable section

/-- A globally valid three-read protocol cannot have a uniform bound on literal actions.
The witness is a positive shear fiber whose third read requires a continuation longer
than any prescribed natural bound. -/
theorem three_read_action_unbounded
    (P : History → Sum Query Label) (hp : OriginalValid P) :
    ∀ C : ℕ, ∃ (R : Source) (fuel : ℕ) (tr : History) (out : Label),
      PassivePolicyNormalization.execute read P fuel [] R = some (tr, out) ∧
      tr.length ≤ 3 ∧ out.1 = R.val ∧ C < actualCost tr out := by
  intro C
  have hx : (0 : ℝ) < 1 := by norm_num
  obtain ⟨paidWord, k, hsel, hk, hendpoint⟩ :=
    (second_query_shear P hp 1 hx).1
  rcases hendpoint with hupper | hlower
  · let upper : Bool := true
    have hpaid : matrix paidWord = endpoint upper k := by
      simpa [upper, endpoint] using hupper
    let N : ℕ := C + k + 3
    have hN : 0 < N := by dsimp [N]; omega
    let z : ℝ := 1 / (N : ℝ)
    have hz : 0 < z := by
      dsimp [z]
      positivity
    have hratio : (1 : ℝ) / z = N := by
      dsimp [z]
      field_simp
    have hceilR : (N : ℝ) ≤ (⌈(1 : ℝ) / z⌉₊ : ℝ) := by
      rw [hratio]
      exact Nat.le_ceil _
    have hceil : N ≤ ⌈(1 : ℝ) / z⌉₊ := by exact_mod_cast hceilR
    have all := full_fiber_and_signed_capacity upper 1 z hx hz k hk []
    have hpositive := all.2.2.2.1 (1 / 2) (by constructor <;> norm_num :
      (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    let R : Source := ⟨fiber upper 1 z (1 / 2), hpositive⟩
    have hreads := (all.2.2.1 R).mpr ⟨1 / 2, by constructor <;> norm_num, rfl⟩
    obtain ⟨v, hnext, hinj, hcost⟩ := all.2.2.2.2.2.2.2.1 P hp paidWord hpaid hsel
    obtain ⟨fuel, tr, out, hexec, hchron, hlen, hout⟩ := hp.2 R
    refine ⟨R, fuel, tr, out, hexec, hlen, hout, ?_⟩
    have hbound := hcost R hreads.1 hreads.2 fuel tr out hexec
    dsimp [upper] at hbound ⊢
    omega
  · let upper : Bool := false
    have hpaid : matrix paidWord = endpoint upper k := by
      simpa [upper, endpoint] using hlower
    let N : ℕ := C + k + 3
    have hN : 0 < N := by dsimp [N]; omega
    let z : ℝ := 1 / (N : ℝ)
    have hz : 0 < z := by
      dsimp [z]
      positivity
    have hratio : (1 : ℝ) / z = N := by
      dsimp [z]
      field_simp
    have hceilR : (N : ℝ) ≤ (⌈(1 : ℝ) / z⌉₊ : ℝ) := by
      rw [hratio]
      exact Nat.le_ceil _
    have hceil : N ≤ ⌈(1 : ℝ) / z⌉₊ := by exact_mod_cast hceilR
    have all := full_fiber_and_signed_capacity upper 1 z hx hz k hk []
    have hpositive := all.2.2.2.1 (1 / 2) (by constructor <;> norm_num :
      (1 / 2 : ℝ) ∈ Set.Ioo 0 1)
    let R : Source := ⟨fiber upper 1 z (1 / 2), hpositive⟩
    have hreads := (all.2.2.1 R).mpr ⟨1 / 2, by constructor <;> norm_num, rfl⟩
    obtain ⟨v, hnext, hinj, hcost⟩ := all.2.2.2.2.2.2.2.1 P hp paidWord hpaid hsel
    obtain ⟨fuel, tr, out, hexec, hchron, hlen, hout⟩ := hp.2 R
    refine ⟨R, fuel, tr, out, hexec, hlen, hout, ?_⟩
    have hbound := hcost R hreads.1 hreads.2 fuel tr out hexec
    dsimp [upper] at hbound ⊢
    omega

#print axioms three_read_action_unbounded

end
end D5.S3.ConceptDynamics.Experiment.SelfCalibratingActionObstruction
