/- GID: D5/S3/ConceptDynamics/Attribution/FiniteSimplexSelection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/FiniteSimplexSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive normalized profiles with a singleton weight form a path-connected set. -/

import D5.S3.Topology.FiniteSubspaceComplement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card

namespace D5.S3.ConceptDynamics.Attribution.FiniteSimplexSelection

open Set
variable {I : Type*} [Fintype I]

private def HasSingleton (x : I → ℝ) : Prop :=
  ∃ i, ∀ j, x j = x i → j = i

private def Peer := {f : I → I // ∀ i, f i ≠ i}

private def peerSpace (f : Peer (I := I)) : Submodule ℝ (I → ℝ) where
  carrier := {x | ∀ i, x i = x (f.1 i)}
  zero_mem' := fun _ => rfl
  add_mem' hx hy i := congrArg₂ (· + ·) (hx i) (hy i)
  smul_mem' c _ hx i := congrArg (c * ·) (hx i)

omit [Fintype I] in
private theorem singleton_iff_avoid_peerSpaces (x : I → ℝ) :
    HasSingleton x ↔ x ∉ ⋃ f : Peer (I := I), (peerSpace f : Set (I → ℝ)) := by
  classical
  constructor
  · rintro ⟨i, hi⟩ h
    obtain ⟨f, hf⟩ := mem_iUnion.mp h
    exact f.2 i (hi _ (hf i).symm)
  · intro h
    by_contra hn
    simp only [HasSingleton, not_exists, not_forall] at hn
    choose f hxf hne using hn
    exact h (mem_iUnion.mpr ⟨⟨f, hne⟩, fun i => (hxf i).symm⟩)

private theorem exists_outside_pair (h : 2 < Fintype.card I) (i j : I) :
    ∃ k : I, k ≠ i ∧ k ≠ j := by
  classical
  by_contra hn
  have hsubset : (Finset.univ : Finset I) ⊆ {i, j} := by
    intro k _
    by_contra hk
    have hki : k ≠ i := fun e => hk (by simp [e])
    have hkj : k ≠ j := fun e => hk (by simp [e])
    exact hn ⟨k, hki, hkj⟩
  have hcard := Finset.card_le_card hsubset
  simp only [Finset.card_univ] at hcard
  have htwo : ({i, j} : Finset I).card ≤ 2 := Finset.card_le_two
  exact (not_le_of_gt h) (hcard.trans htwo)

private theorem peerSpace_proper_with_line (h : 2 < Fintype.card I)
    (f : Peer (I := I)) (x : I → ℝ) :
    peerSpace f ⊔ Submodule.span ℝ {x} ≠ ⊤ := by
  classical
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let i : I := Classical.choice inferInstance
  obtain ⟨k, hki, hkj⟩ := exists_outside_pair h i (f.1 i)
  intro htop
  have spike (a : I) : ∃ c : ℝ, ∀ u,
      (Pi.single a (1 : ℝ) : I → ℝ) u - (Pi.single a (1 : ℝ) : I → ℝ) (f.1 u) = c * (x u - x (f.1 u)) := by
    have ha : Pi.single a (1 : ℝ) ∈ peerSpace f ⊔ Submodule.span ℝ {x} := by
      rw [htop]
      trivial
    obtain ⟨v, hv, s, hs, hvsa⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    refine ⟨c, fun u => ?_⟩
    have eq_u := congrFun hvsa u
    have eq_fu := congrFun hvsa (f.1 u)
    change v u + c * x u = (Pi.single a (1 : ℝ) : I → ℝ) u at eq_u
    change v (f.1 u) + c * x (f.1 u) = (Pi.single a (1 : ℝ) : I → ℝ) (f.1 u) at eq_fu
    linear_combination -eq_u + eq_fu + hv u
  by_cases hx : x i = x (f.1 i)
  · obtain ⟨c, hc⟩ := spike i
    have neq := f.2 i
    simpa [Pi.single_apply, neq, hx] using hc i
  · obtain ⟨c, hc⟩ := spike k
    have hzero : 0 = c * (x i - x (f.1 i)) := by
      simpa [Pi.single_apply, hki.symm, hkj.symm] using hc i
    have hc0 : c = 0 := (mul_eq_zero.mp hzero.symm).resolve_right (sub_ne_zero.mpr hx)
    have neq := f.2 k
    simpa [Pi.single_apply, neq, hc0] using hc k

private def positiveProfiles (I : Type*) : Set (I → ℝ) := {x | ∀ i, 0 < x i}

private theorem goodCone_pathConnected (h : 2 < Fintype.card I) :
    IsPathConnected {x : I → ℝ | x ∈ positiveProfiles I ∧ HasSingleton x} := by
  have hopen : IsOpen (positiveProfiles I) := by
    rw [show positiveProfiles I = ⋂ i : I, (fun x : I → ℝ => x i) ⁻¹' Ioi 0 from by
      ext x
      simp [positiveProfiles]]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage (continuous_apply i)
  have hconv : Convex ℝ (positiveProfiles I) := by
    intro x hx y hy a b ha hb hab i
    change 0 < a * x i + b * y i
    rcases eq_or_lt_of_le ha with rfl | ha
    · simpa using mul_pos (by linarith) (hy i)
    · exact add_pos_of_pos_of_nonneg (mul_pos ha (hx i)) (mul_nonneg hb (le_of_lt (hy i)))
  have hne : (positiveProfiles I).Nonempty := ⟨fun _ => 1, fun _ => zero_lt_one⟩
  let : Finite (Peer (I := I)) := Finite.of_injective Subtype.val Subtype.val_injective
  have result := D5.S3.Topology.FiniteSubspaceComplement.pathConnected_complement_in_open_convex
    (positiveProfiles I) hopen hconv hne peerSpace (peerSpace_proper_with_line h)
  convert result using 1
  ext x
  exact and_congr_right fun _ => singleton_iff_avoid_peerSpaces x

/-- For at least three labels, positive normalized profiles with at least one singleton weight
form a path-connected set. -/
theorem pathConnected_normalized_profiles (h : 2 < Fintype.card I) :
    IsPathConnected {x : I → ℝ | (∀ i, 0 < x i) ∧ (∑ i, x i) = 1 ∧ ∃ i, ∀ j, x j = x i → j = i} := by
  classical
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let norm (x : I → ℝ) (i : I) : ℝ := x i / ∑ j, x j
  let good : Set (I → ℝ) := {x | x ∈ positiveProfiles I ∧ HasSingleton x}
  have hpos (x : I → ℝ) (hx : x ∈ good) : 0 < ∑ j, x j :=
    Finset.sum_pos (fun j _ => hx.1 j) Finset.univ_nonempty
  have hcont : ContinuousOn norm good := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply i).continuousOn.div
      (continuous_finsetSum _ fun j _ => continuous_apply j).continuousOn
      (fun x hx => ne_of_gt (hpos x hx))
  have hp := (goodCone_pathConnected h).image' hcont
  convert hp using 1
  ext x
  constructor
  · intro hx
    exact ⟨x, ⟨hx.1, hx.2.2⟩, funext fun i => by simp [norm, hx.2.1]⟩
  · rintro ⟨y, hy, rfl⟩
    have hY := hpos y hy
    refine ⟨fun i => div_pos (hy.1 i) hY, ?_, ?_⟩
    · simp only [norm, ← Finset.sum_div, div_self (ne_of_gt hY)]
    · obtain ⟨i, hi⟩ := hy.2
      exact ⟨i, fun j hj => hi j ((div_left_inj' (ne_of_gt hY)).mp hj)⟩

#print axioms pathConnected_normalized_profiles

end D5.S3.ConceptDynamics.Attribution.FiniteSimplexSelection
