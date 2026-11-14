/- GID: D5/S3/Combinatorics/Geometry/RowmotionIncomparableToggles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionIncomparableToggles
   mirror-E: none(waiver:abstract-order-identity)
   anchors: []
   utility: none
   digest: Legal interval-closed toggles at incomparable points commute. -/

import D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport

open scoped symmDiff
open D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport

namespace D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles

variable {P : Type*} [PartialOrder P]

private lemma flip_other (S : Set P) (x z : P) (hz : z ≠ x) :
    z ∈ S ∆ {x} ↔ z ∈ S := by
  simp [Set.mem_symmDiff, hz]

-- A legal one-point flip depends only on membership at points comparable with it.
private lemma transfer_flip {S T : Set P} {x : P}
    (hT : T.OrdConnected)
    (agree : ∀ z, (z ≤ x ∨ x ≤ z) → (z ∈ S ↔ z ∈ T))
    (hSx : (S ∆ {x}).OrdConnected) : (T ∆ {x}).OrdConnected := by
  classical
  have flip_agree (z : P) (hz : z ≤ x ∨ x ≤ z) :
      z ∈ S ∆ {x} ↔ z ∈ T ∆ {x} := by
    simp only [Set.mem_symmDiff, Set.mem_singleton_iff, agree z hz]
  constructor
  intro u hu v hv z hz
  by_cases hux : u = x
  · subst u
    have hsu := (flip_agree x (Or.inl le_rfl)).mpr hu
    have hsv := (flip_agree v (Or.inr (le_trans hz.1 hz.2))).mpr hv
    exact (flip_agree z (Or.inr hz.1)).mp (hSx.out hsu hsv hz)
  by_cases hvx : v = x
  · subst v
    have hsu := (flip_agree u (Or.inl (le_trans hz.1 hz.2))).mpr hu
    have hsv := (flip_agree x (Or.inl le_rfl)).mpr hv
    exact (flip_agree z (Or.inl hz.2)).mp (hSx.out hsu hsv hz)
  by_cases hzx : z = x
  · subst z
    have hsu := (flip_agree u (Or.inl hz.1)).mpr hu
    have hsv := (flip_agree v (Or.inr hz.2)).mpr hv
    exact (flip_agree x (Or.inl le_rfl)).mp (hSx.out hsu hsv hz)
  exact (flip_other T x z hzx).mpr
    (hT.out ((flip_other T x u hux).mp hu) ((flip_other T x v hvx).mp hv) hz)

private lemma toggle_connected (x : P) {S : Set P} (hS : S.OrdConnected) :
    (toggle x S).OrdConnected := by
  classical
  unfold toggle
  split
  · assumption
  · exact hS

private lemma legal_iff {x y : P} (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x)
    {S : Set P} (hS : S.OrdConnected) :
    ((toggle y S) ∆ {x}).OrdConnected ↔ (S ∆ {x}).OrdConnected := by
  classical
  have agree (z : P) (hz : z ≤ x ∨ x ≤ z) :
      z ∈ S ↔ z ∈ toggle y S := by
    have hzy : z ≠ y := by
      intro heq
      subst z
      exact hz.elim hyx hxy
    unfold toggle
    split
    · exact (flip_other S y z hzy).symm
    · rfl
  constructor
  · exact transfer_flip hS (fun z hz => (agree z hz).symm)
  · exact transfer_flip (toggle_connected y hS) agree

/-- Legal interval-closed toggles at incomparable points commute. -/
theorem incomparable_toggles_commute (x y : P)
    (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x)
    (S : Set P) (hS : S.OrdConnected) :
    toggle x (toggle y S) = toggle y (toggle x S) := by
  classical
  have hx := legal_iff hxy hyx hS
  have hy := legal_iff hyx hxy hS
  by_cases hX : (S ∆ {x}).OrdConnected <;>
    by_cases hY : (S ∆ {y}).OrdConnected
  · have hx' := hx.mpr hX
    have hy' := hy.mpr hY
    simp only [toggle, if_pos hX, if_pos hY] at hx' hy' ⊢
    rw [if_pos hx', if_pos hy']
    rw [symmDiff_assoc, symmDiff_comm ({y} : Set P) {x}, ← symmDiff_assoc]
  · have hy' : ¬ ((S ∆ {x}) ∆ {y}).OrdConnected := by
      simpa only [toggle, if_pos hX] using (mt hy.mp hY)
    simp only [toggle, if_pos hX, if_neg hY, if_neg hy']
  · have hx' : ¬ ((S ∆ {y}) ∆ {x}).OrdConnected := by
      simpa only [toggle, if_pos hY] using (mt hx.mp hX)
    simp only [toggle, if_neg hX, if_pos hY, if_neg hx']
  · simp only [toggle, if_neg hX, if_neg hY]

end D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
