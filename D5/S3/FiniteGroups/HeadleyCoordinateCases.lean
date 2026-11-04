/- GID: D5/S3/FiniteGroups/HeadleyCoordinateCases
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyCoordinateCases
   mirror-E: none(waiver:coordinate-cases)
   anchors: []
   utility: none
   digest: Removing trivial factors and selecting recursive coordinates without losing noncyclicity. -/

import D5.S3.FiniteGroups.HeadleyDoubledCoordinates
import D5.S3.FiniteGroups.HeadleyElementaryCycles

/-! The elementary, two-factor and strictly recursive coordinate cases. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyCoordinateCases
open HeadleyCoordinateKernel HeadleyDoubledCoordinates HeadleyElementaryCycles
open HeadleyExtension Function

/-- Delete precisely the trivial factors, retaining the original positive coordinates. -/
noncomputable def positiveEquiv {r : ℕ} (e : Fin r → ℕ) :
    Coordinates e ≃+ (∀ i : {i // 0 < e i}, ZMod (2 ^ e i.val)) := by
  classical
  let f : Coordinates e →+ (∀ i : {i // 0 < e i}, ZMod (2 ^ e i.val)) := {
    toFun := fun x i => x i.val
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  apply AddEquiv.ofBijective f
  constructor
  · intro x y hxy
    funext k
    by_cases hk : 0 < e k
    · exact congrFun hxy ⟨k, hk⟩
    · have hz : e k = 0 := by omega
      haveI : Subsingleton (ZMod (2 ^ e k)) := by rw [hz, pow_zero]; infer_instance
      exact Subsingleton.elim _ _
  · intro y
    refine ⟨fun k => if hk : 0 < e k then y ⟨k,hk⟩ else 0, ?_⟩
    funext k
    exact dif_pos k.property

/-- Every elementary coordinate family, including rank three, has its field cycle. -/
noncomputable def elementaryCoordinates {r : ℕ} (e : Fin r → ℕ)
    (hall : ∀ k, 0 < e k → e k = 1)
    (htwo : ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j) : RCycle (Coordinates e) := by
  classical
  let I := {i : Fin r // 0 < e i}
  have hcard : 2 ≤ Fintype.card I := by
    obtain ⟨i,j,hij,hi,hj⟩ := htwo
    have hlt := Fintype.one_lt_card_iff.mpr
      (show ∃ a b : I, a ≠ b from ⟨⟨i,hi⟩,⟨j,hj⟩,fun h => hij (congrArg Subtype.val h)⟩)
    omega
  let T : (∀ k : I, ZMod (2 ^ e k.val)) ≃+ (I → ZMod 2) :=
    AddEquiv.piCongrRight fun k =>
      (ZMod.ringEquivCongr (by rw [hall k.val k.property]; norm_num)).toAddEquiv
  let U : (I → ZMod 2) ≃+ (Fin (Fintype.card I) → ZMod 2) :=
    ((RingEquiv.piCongrLeft (fun _ : I => ZMod 2) (Fintype.equivFin I).symm).toAddEquiv).symm
  let E := (positiveEquiv e).trans (T.trans U)
  exact transportCycle E.symm (elementaryCycle (Fintype.card I) hcard)

/-- When all other coordinates are trivial, evaluation gives the actual two-factor type. -/
noncomputable def twoCoordinatesEquiv {r : ℕ} (e : Fin r → ℕ) (i j : Fin r)
    (hji : j ≠ i) (hz : ∀ k, k ≠ i → k ≠ j → e k = 0) :
    Coordinates e ≃+ ZMod (2 ^ e i) × ZMod (2 ^ e j) := by
  classical
  haveI : ∀ k : {k : {k // k ≠ i} // k ≠ ⟨j,hji⟩},
      Subsingleton (ZMod (2 ^ e k.val.val)) := fun k => by
    have hki := k.val.property
    have hkj : k.val.val ≠ j := fun h => k.property (Subtype.ext h)
    rw [hz k.val.val hki hkj, pow_zero]
    infer_instance
  letI : Unique (Rest e i j hji) := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  exact (chart e i j hji).trans AddEquiv.prodUnique

/-- Outside elementary and thin two-factor leaves, two coordinates can be lowered while
retaining two positive coordinates. -/
theorem recursive_pair {r : ℕ} (e : Fin r → ℕ)
    (htwo : ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j)
    (hne : ¬ ∀ k, 0 < e k → e k = 1)
    (hthin : ¬ ∃ i j, i ≠ j ∧ e i = 1 ∧ 0 < e j ∧
      ∀ k, k ≠ i → k ≠ j → e k = 0) :
    ∃ i j, i ≠ j ∧ 0 < e i ∧ 0 < e j ∧
      ∃ u v, u ≠ v ∧ 0 < lower e i j u ∧ 0 < lower e i j v := by
  classical
  push_neg at hne
  obtain ⟨i, hi, hi1⟩ := hne
  have hi2 : 2 ≤ e i := by omega
  obtain ⟨a,b,hab,ha,hb⟩ := htwo
  have hjex : ∃ j, j ≠ i ∧ 0 < e j := by
    by_cases hai : a = i
    · exact ⟨b, fun h => hab (hai.trans h.symm), hb⟩
    · exact ⟨a, hai, ha⟩
  obtain ⟨j,hji,hj⟩ := hjex
  refine ⟨i,j,hji.symm,hi,hj,?_⟩
  by_cases hex : ∃ k, k ≠ i ∧ k ≠ j ∧ 0 < e k
  · obtain ⟨k,hki,hkj,hk⟩ := hex
    refine ⟨i,k,hki.symm,?_,?_⟩
    · simp only [lower, true_or, ite_true]
      omega
    · simpa [lower,hki,hkj] using hk
  · have hz : ∀ k, k ≠ i → k ≠ j → e k = 0 := by
      intro k hki hkj
      by_contra hk
      exact hex ⟨k,hki,hkj,Nat.pos_of_ne_zero hk⟩
    have hj1 : e j ≠ 1 := by
      intro he
      exact hthin ⟨j,i,hji,he,hi,fun k hkj hki => hz k hki hkj⟩
    refine ⟨i,j,hji.symm,?_,?_⟩
    · simp only [lower, true_or, ite_true]
      omega
    · simp only [lower, or_true, ite_true]
      omega

end D5.S3.FiniteGroups.HeadleyCoordinateCases
