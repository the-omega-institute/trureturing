/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitNormThirty
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitNormThirty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Every nonzero unit-valued positive-three Huang eigenvector has support at least thirty. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitNormThirty

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap (Q9)
open private intA intCoeff evenPart oddPart parts_add
  intA_even_on_even intA_odd_on_odd intCoeff_zero_of_not_adj intCoeff_sign_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private intA_add pairing_comm unit_norm_eq_card no_singleton_row
  even_diff_of_parity_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
open private eigen_norm_six_dvd from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut
open private diff diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

open Classical in
private theorem parts_eigen_pos (h : Q9 → ℤ)
    (heig : intA h = fun x => 3 * h x) :
    intA (evenPart h) = (fun x => 3 * oddPart h x) ∧
    intA (oddPart h) = (fun x => 3 * evenPart h x) := by
  classical
  have hadd (x : Q9) :
      intA (evenPart h) x + intA (oddPart h) x = 3 * h x := by
    calc
      _ = intA (evenPart h + oddPart h) x :=
        (congrFun (intA_add (evenPart h) (oddPart h)) x).symm
      _ = intA h x := by rw [parts_add]
      _ = 3 * h x := congrFun heig x
  constructor
  · funext x
    change intA (evenPart h) x = 3 * oddPart h x
    cases hp : cubeParity x
    · rw [intA_even_on_even h x hp]
      simp [oddPart, hp]
    · have hx := hadd x
      rw [intA_odd_on_odd h x hp, add_zero] at hx
      simpa [oddPart, hp] using hx
  · funext x
    change intA (oddPart h) x = 3 * evenPart h x
    cases hp : cubeParity x
    · have hx := hadd x
      rw [intA_even_on_even h x hp, zero_add] at hx
      simpa [evenPart, hp] using hx
    · rw [intA_odd_on_odd h x hp]
      simp [evenPart, hp]

open Classical in
private theorem star_rows_zero (r : Q9 → ℤ)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (hdiv : ∀ z, (3 : ℤ) ∣ intA r z)
    (S : Finset Q9) (hS : S = Finset.univ.filter (fun x => r x ≠ 0))
    (center : Q9)
    (hstar : S = Finset.univ.filter (fun x => (hypercube 9).Adj center x)) :
    ∀ z, z ≠ center → intA r z = 0 := by
  classical
  have hcommon_card (z : Q9) (hzc : z ≠ center) :
      (S.filter (fun w => (hypercube 9).Adj z w)).card ≤ 2 := by
    let C := S.filter (fun w => (hypercube 9).Adj z w)
    by_cases hC : C.Nonempty
    · obtain ⟨w, hw⟩ := hC
      have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
      have hwz : (hypercube 9).Adj z w := (Finset.mem_filter.mp hw).2
      have hwc : (hypercube 9).Adj center w :=
        (Finset.mem_filter.mp (hstar ▸ hwS)).2
      obtain ⟨i, hi⟩ := adjacent_exists_flip hwz
      have hdiff := diff_of_adj_flip (x := z) (z := center) hzc i (by
        rw [← hi]
        exact hwc.symm)
      have hsub : C ⊆ (diff z center).image
          (fun j => BalancedCriticalSpectrum.flip z j) := by
        intro u huC
        have huS : u ∈ S := (Finset.mem_filter.mp huC).1
        have huz : (hypercube 9).Adj z u := (Finset.mem_filter.mp huC).2
        obtain ⟨j, hj⟩ := adjacent_exists_flip huz
        have huc : (hypercube 9).Adj center u :=
          (Finset.mem_filter.mp (hstar ▸ huS)).2
        have hdj := diff_of_adj_flip (x := z) (z := center) hzc j (by
          rw [← hj]
          exact huc.symm)
        exact Finset.mem_image.mpr ⟨j, hdj.1, hj.symm⟩
      calc
        C.card ≤ ((diff z center).image
            (fun j => BalancedCriticalSpectrum.flip z j)).card :=
          Finset.card_le_card hsub
        _ ≤ (diff z center).card := Finset.card_image_le
        _ = 2 := hdiff.2
    · have hzero : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      change C.card ≤ 2
      rw [hzero]
      norm_num
  intro z hzc
  let C := S.filter (fun w => (hypercube 9).Adj z w)
  have hrow : intA r z = ∑ w ∈ C, intCoeff z w * r w := by
    unfold intA
    symm
    apply Finset.sum_subset (Finset.subset_univ C)
    intro w _ hw
    by_cases hwS : w ∈ S
    · have hnadj : ¬ (hypercube 9).Adj z w := by
        intro hadj
        exact hw (Finset.mem_filter.mpr ⟨hwS, hadj⟩)
      rw [intCoeff_zero_of_not_adj z w hnadj]
      simp
    · have hw0 : r w = 0 := by
        by_contra hw0
        exact hwS (by simp [hS, hw0])
      simp [hw0]
  have hupper : (∑ w ∈ C, intCoeff z w * r w) ≤ (C.card : ℤ) := by
    calc
      _ ≤ ∑ _w ∈ C, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro w hw
        rcases intCoeff_sign_of_adj z w (Finset.mem_filter.mp hw).2 with hc | hc <;>
          rcases hu w with hv | hv | hv <;> simp [hc, hv] <;> omega
      _ = (C.card : ℤ) := by simp
  have hlower : -(C.card : ℤ) ≤ ∑ w ∈ C, intCoeff z w * r w := by
    calc
      -(C.card : ℤ) = ∑ _w ∈ C, (-1 : ℤ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro w hw
        rcases intCoeff_sign_of_adj z w (Finset.mem_filter.mp hw).2 with hc | hc <;>
          rcases hu w with hv | hv | hv <;> simp [hc, hv] <;> omega
  have hc2 : C.card ≤ 2 := hcommon_card z hzc
  obtain ⟨k, hk⟩ := hdiv z
  rw [hrow] at hk ⊢
  omega

open Classical in
theorem thirty_le_support_card (h : Q9 → ℤ)
    (heig : intA h = fun x => 3 * h x)
    (hu : ∀ x, h x = 0 ∨ h x = 1 ∨ h x = -1)
    (hne : h ≠ 0) :
    30 ≤ (Finset.univ.filter (fun x => h x ≠ 0)).card := by
  classical
  let r : Q9 → ℤ := evenPart h
  let s : Q9 → ℤ := oddPart h
  obtain ⟨hr', hs'⟩ := parts_eigen_pos h heig
  have hr : intA r = fun x => 3 * s x := hr'
  have hs : intA s = fun x => 3 * r x := hs'
  have hru : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1 := by
    intro x
    by_cases hp : cubeParity x = false
    · simpa [r, evenPart, hp] using hu x
    · simp [r, evenPart, hp]
  have hsu : ∀ x, s x = 0 ∨ s x = 1 ∨ s x = -1 := by
    intro x
    by_cases hp : cubeParity x = true
    · simpa [s, oddPart, hp] using hu x
    · simp [s, oddPart, hp]
  have hpair := pairing_comm r s
  have hleft : (∑ x, r x * intA s x) = 3 * ∑ x, r x ^ 2 := by
    rw [hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hright : (∑ x, s x * intA r x) = 3 * ∑ x, s x ^ 2 := by
    rw [hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hnormeq : (∑ x, r x ^ 2) = ∑ x, s x ^ 2 := by
    rw [hleft, hright] at hpair
    omega
  have hsplit : (∑ x, r x ^ 2) + (∑ x, s x ^ 2) = ∑ x, h x ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    cases hp : cubeParity x <;> simp [r, s, evenPart, oddPart, hp]
  let S : Finset Q9 := Finset.univ.filter (fun x => r x ≠ 0)
  let T : Finset Q9 := Finset.univ.filter (fun x => s x ≠ 0)
  let H : Finset Q9 := Finset.univ.filter (fun x => h x ≠ 0)
  have hnormr : (∑ x, r x ^ 2) = (S.card : ℤ) := unit_norm_eq_card r hru
  have hnorms : (∑ x, s x ^ 2) = (T.card : ℤ) := unit_norm_eq_card s hsu
  have hnormh : (∑ x, h x ^ 2) = (H.card : ℤ) := unit_norm_eq_card h hu
  have hcardeq : S.card = T.card := by omega
  have hcardsplit : S.card + T.card = H.card := by omega
  have hHne : H.Nonempty := by
    by_contra hempty
    apply hne
    funext x
    change h x = 0
    by_contra hx
    exact hempty ⟨x, by simp [H, hx]⟩
  have hHpos : 0 < H.card := Finset.card_pos.mpr hHne
  have hlarge : 24 < H.card := by
    by_contra hsmall
    have hScard : S.card ≤ 12 := by omega
    have hSne : S.Nonempty := by
      apply Finset.card_pos.mp
      omega
    have hdiv : ∀ y, (3 : ℤ) ∣ intA r y := by
      intro y
      refine ⟨s y, ?_⟩
      exact congrFun hr y
    have hno : ∀ y, (S.filter (fun x => (hypercube 9).Adj y x)).card ≠ 1 :=
      no_singleton_row r hru hdiv
    have hpar : ∀ x ∈ S, cubeParity x = false := by
      intro x hx
      have hxne : r x ≠ 0 := (Finset.mem_filter.mp hx).2
      by_contra hp
      apply hxne
      simp [r, evenPart, hp]
    have heven : ∀ x ∈ S, ∀ y ∈ S,
        Even (Finset.univ.filter (fun i : Fin 9 => x i ≠ y i)).card := by
      intro x hx y hy
      exact even_diff_of_parity_eq x y ((hpar x hx).trans (hpar y hy).symm)
    obtain ⟨center, hstar⟩ := CubeTwelveSupport.eq_neighbors_of_card_le_twelve
      S hSne hScard hno heven
    have hcardN :
        (Finset.univ.filter (fun x : Q9 => (hypercube 9).Adj center x)).card = 9 := by
      calc
        _ = ((hypercube 9).neighborFinset center).card := by
          rw [(hypercube 9).neighborFinset_eq_filter]
        _ = (hypercube 9).degree center := rfl
        _ = 9 := (hypercube_regular 9).degree_eq center
    have hScard9 : S.card = 9 := by rw [hstar, hcardN]
    have hTcard9 : T.card = 9 := by omega
    have hrowzero : ∀ z, z ≠ center → intA r z = 0 :=
      star_rows_zero r hru hdiv S rfl center hstar
    have hTsub : T ⊆ ({center} : Finset Q9) := by
      intro z hz
      apply Finset.mem_singleton.mpr
      by_contra hzc
      have hszne : s z ≠ 0 := (Finset.mem_filter.mp hz).2
      have hrowz := congrFun hr z
      rw [hrowzero z hzc] at hrowz
      have hsz : s z = 0 := by omega
      exact hszne hsz
    have hTle : T.card ≤ 1 := by
      calc
        T.card ≤ ({center} : Finset Q9).card := Finset.card_le_card hTsub
        _ = 1 := Finset.card_singleton center
    omega
  have hdvd : (6 : ℤ) ∣ (H.card : ℤ) := by
    rw [← hnormh]
    exact eigen_norm_six_dvd h heig
  obtain ⟨k, hk⟩ := hdvd
  change 30 ≤ H.card
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitNormThirty
