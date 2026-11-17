/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exclusion of unit negative-three Huang eigenvectors with support thirty. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeFiveNeighborGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyStructure
import Batteries.Tactic.OpenPrivate

/-! Unit-valued negative-three Huang eigenvectors cannot have support thirty. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyGap

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open HuangIntegralNormGap (Q9)
open private intA intCoeff evenPart oddPart from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private parts_eigen unit_norm_eq_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
open private parity_norms from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangEnergyFiveResidual
open private opposite_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyStructure

open Classical in
/-- The original FALSE-prefix Huang operator has no unit-valued negative-three
 eigenvector supported on exactly thirty vertices. -/
theorem no_unit_negative_three_support_thirty (r : Q9 → ℤ)
    (heig : intA r = fun x => -3 * r x)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (hcard : (Finset.univ.filter (fun x => r x ≠ 0)).card = 30) : False := by
  classical
  let S := Finset.univ.filter (fun x => r x ≠ 0)
  obtain ⟨hdeg, _, hopposite⟩ :=
    HuangUnitThirtyStructure.structure_of_unit_negative_three_support_thirty r heig hu hcard
  obtain ⟨x, hx, y, hy, hxy, hsign⟩ := hopposite
  have hyO : y ∈ S.filter (fun w =>
      (hypercube 9).Adj x w ∧ intCoeff x w * r x * r w = 1) :=
    Finset.mem_filter.mpr ⟨hy, hxy, hsign⟩
  have hOpos : 0 < (S.filter (fun w =>
      (hypercube 9).Adj x w ∧ intCoeff x w * r x * r w = 1)).card :=
    Finset.card_pos.mpr ⟨y, hyO⟩
  have hcount := opposite_count r heig hu x (Finset.mem_filter.mp hx).2
  change 2 * ((S.filter (fun w =>
    (hypercube 9).Adj x w ∧ intCoeff x w * r x * r w = 1)).card : ℤ) + 3 =
    ((S.filter (fun w => (hypercube 9).Adj x w)).card : ℤ) at hcount
  have hfive : (S.filter (fun w => (hypercube 9).Adj x w)).card = 5 := by
    rcases hdeg x hx with hd | hd
    · change (S.filter (fun w => (hypercube 9).Adj x w)).card = 3 at hd
      rw [hd] at hcount
      omega
    · exact hd
  have hnorm : (∑ w, r w ^ 2) = 30 := by
    rw [unit_norm_eq_card r hu, hcard]
    norm_num
  obtain ⟨hne, hno⟩ := parity_norms r heig hnorm
  obtain ⟨he, ho⟩ := parts_eigen r heig
  have heu : ∀ w, evenPart r w = 0 ∨ evenPart r w = 1 ∨ evenPart r w = -1 := by
    intro w
    by_cases hp : cubeParity w = false
    · simpa [evenPart, hp] using hu w
    · simp [evenPart, hp]
  have hou : ∀ w, oddPart r w = 0 ∨ oddPart r w = 1 ∨ oddPart r w = -1 := by
    intro w
    by_cases hp : cubeParity w = true
    · simpa [oddPart, hp] using hu w
    · simp [oddPart, hp]
  have hecard : (Finset.univ.filter (fun w => evenPart r w ≠ 0)).card = 15 := by
    have hc := unit_norm_eq_card (evenPart r) heu
    omega
  have hocard : (Finset.univ.filter (fun w => oddPart r w ≠ 0)).card = 15 := by
    have hc := unit_norm_eq_card (oddPart r) hou
    omega
  cases hpx : cubeParity x
  · have hdiv : ∀ v, (3 : ℤ) ∣ intA (oddPart r) v := by
      intro v
      rw [congrFun ho v]
      exact ⟨-evenPart r v, by ring⟩
    have hf : ((Finset.univ.filter (fun w => oddPart r w ≠ 0)).filter
        (fun w => (hypercube 9).Adj x w)) =
        S.filter (fun w => (hypercube 9).Adj x w) := by
      ext w
      by_cases ha : (hypercube 9).Adj x w
      · have hp : cubeParity w = true := by
          have hn := cubeParity_ne_of_adj ha
          cases hw : cubeParity w <;> simp_all
        simp [S, oddPart, hp, ha, Finset.mem_filter]
      · simp [S, ha, Finset.mem_filter]
    have hrow : ((Finset.univ.filter (fun w => oddPart r w ≠ 0)).filter
        (fun w => (hypercube 9).Adj x w)).card = 5 := by
      rw [hf]
      exact hfive
    have hl := CubeFiveNeighborGap.sixteen_le_support_card_of_neighbor_card_eq_five
      (oddPart r) hou hdiv x hrow
    rw [hocard] at hl
    omega
  · have hdiv : ∀ v, (3 : ℤ) ∣ intA (evenPart r) v := by
      intro v
      rw [congrFun he v]
      exact ⟨-oddPart r v, by ring⟩
    have hf : ((Finset.univ.filter (fun w => evenPart r w ≠ 0)).filter
        (fun w => (hypercube 9).Adj x w)) =
        S.filter (fun w => (hypercube 9).Adj x w) := by
      ext w
      by_cases ha : (hypercube 9).Adj x w
      · have hp : cubeParity w = false := by
          have hn := cubeParity_ne_of_adj ha
          cases hw : cubeParity w <;> simp_all
        simp [S, evenPart, hp, ha, Finset.mem_filter]
      · simp [S, ha, Finset.mem_filter]
    have hrow : ((Finset.univ.filter (fun w => evenPart r w ≠ 0)).filter
        (fun w => (hypercube 9).Adj x w)).card = 5 := by
      rw [hf]
      exact hfive
    have hl := CubeFiveNeighborGap.sixteen_le_support_card_of_neighbor_card_eq_five
      (evenPart r) heu hdiv x hrow
    rw [hecard] at hl
    omega

open private intA_sub from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private parts_eigen_pos from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitNormThirty
open private eigen_norm_six_dvd from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut

open Classical in
private theorem thirty_six_le_support_card (h : Q9 → ℤ)
    (heig : intA h = fun x => 3 * h x)
    (hu : ∀ x, h x = 0 ∨ h x = 1 ∨ h x = -1)
    (hne : h ≠ 0) :
    36 ≤ (Finset.univ.filter (fun x => h x ≠ 0)).card := by
  classical
  have hthirty := HuangUnitNormThirty.thirty_le_support_card h heig hu hne
  let r : Q9 → ℤ := evenPart h - oddPart h
  obtain ⟨he, ho⟩ := parts_eigen_pos h heig
  have hreig : intA r = fun x => -3 * r x := by
    dsimp only [r]
    rw [intA_sub, he, ho]
    funext x
    simp only [Pi.sub_apply]
    ring
  have hru : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1 := by
    intro x
    cases hp : cubeParity x <;>
      rcases hu x with hx | hx | hx <;>
      simp [r, Pi.sub_apply, evenPart, oddPart, hp, hx]
  have hsupport :
      Finset.univ.filter (fun x => r x ≠ 0) =
        Finset.univ.filter (fun x => h x ≠ 0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases hp : cubeParity x <;>
      simp [r, Pi.sub_apply, evenPart, oddPart, hp]
  have hnotthirty : (Finset.univ.filter (fun x => h x ≠ 0)).card ≠ 30 := by
    intro hthirtyeq
    have hr30 : (Finset.univ.filter (fun x => r x ≠ 0)).card = 30 := by
      rw [hsupport]
      exact hthirtyeq
    exact no_unit_negative_three_support_thirty r hreig hru hr30
  have hdvd : (6 : ℤ) ∣
      ((Finset.univ.filter (fun x => h x ≠ 0)).card : ℤ) := by
    rw [← unit_norm_eq_card h hu]
    exact eigen_norm_six_dvd h heig
  obtain ⟨k, hk⟩ := hdvd
  omega


end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyGap
