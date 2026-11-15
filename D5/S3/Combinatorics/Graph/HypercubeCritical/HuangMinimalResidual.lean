/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangMinimalResidual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangMinimalResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exact nine-cube integral residual classification at norm nine. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
import Batteries.Tactic.OpenPrivate

/-! Classifying integral vectors of squared norm nine for the original Huang operator. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangMinimalResidual

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open BalancedCriticalSpectrum (Q)
open private intCoeff intA intA_square intCoeff_sign_of_adj intCoeff_zero_of_not_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

open Classical in
private theorem support_sum_eq (r : Q9 → ℤ) (S : Finset Q9)
    (hS : S = Finset.univ.filter (fun x => r x ≠ 0)) :
    (∑ x ∈ S, r x ^ 2) = ∑ x, r x ^ 2 := by
  classical
  rw [hS]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  push_neg at hx
  simp [hx]

open Classical in
private theorem support_term_ge_one (r : Q9 → ℤ) {S : Finset Q9}
    (hS : S = Finset.univ.filter (fun x => r x ≠ 0)) {x : Q9} (hx : x ∈ S) :
    (1 : ℤ) ≤ r x ^ 2 := by
  classical
  have hne : r x ≠ 0 := by
    rw [hS] at hx
    exact (Finset.mem_filter.mp hx).2
  by_cases hp : 0 < r x
  · have : 1 ≤ r x := by omega
    nlinarith
  · have hn : r x ≤ -1 := by omega
    nlinarith

open Classical in
private theorem support_card_le_nine (r : Q9 → ℤ)
    (hnorm : (∑ x, r x ^ 2) = 9) {S : Finset Q9}
    (hS : S = Finset.univ.filter (fun x => r x ≠ 0)) : S.card ≤ 9 := by
  classical
  have h1 : (S.card : ℤ) ≤ ∑ x ∈ S, r x ^ 2 := by
    calc
      (S.card : ℤ) = ∑ _x ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ x ∈ S, r x ^ 2 := by
        exact Finset.sum_le_sum (fun x hx => support_term_ge_one r hS hx)
  have h2 : (∑ x ∈ S, r x ^ 2) ≤ ∑ x, r x ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro x _ _
    positivity
  have hi : (S.card : ℤ) ≤ 9 := by simpa [hnorm] using h1.trans (h2.trans_eq hnorm)
  omega

open Classical in
private theorem support_nonempty (r : Q9 → ℤ)
    (hnorm : (∑ x, r x ^ 2) = 9) {S : Finset Q9}
    (hS : S = Finset.univ.filter (fun x => r x ≠ 0)) : S.Nonempty := by
  classical
  by_contra h
  have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hz (x : Q9) : r x = 0 := by
    by_contra hx
    have : x ∈ S := by simp [hS, hx]
    rw [hzero] at this
    simp at this
  have : (∑ x, r x ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [hz x]
  omega

open Classical in
private theorem row_on_singleton (r : Q9 → ℤ) {S : Finset Q9} {y x : Q9}
    (hS : S = Finset.univ.filter (fun z => r z ≠ 0))
    (hfilter : S.filter (fun z => (hypercube 9).Adj y z) = {x}) :
    intA r y = intCoeff y x * r x := by
  classical
  unfold intA
  apply Finset.sum_eq_single x
  · intro z hz hzx
    by_cases hzS : z ∈ S
    · have hzAdj : ¬ (hypercube 9).Adj y z := by
        intro hadj
        have hzF : z ∈ S.filter (fun w => (hypercube 9).Adj y w) :=
          Finset.mem_filter.mpr ⟨hzS, hadj⟩
        rw [hfilter] at hzF
        exact hzx (Finset.mem_singleton.mp hzF)
      rw [intCoeff_zero_of_not_adj y z hzAdj]
      simp
    · have hz0 : r z = 0 := by
        by_contra hz0
        exact hzS (by simp [hS, hz0])
      simp [hz0]
  · simp

open Classical in
private theorem two_point_sum_le (r : Q9 → ℤ) (hnorm : (∑ x, r x ^ 2) = 9)
    {x z : Q9} (hxz : x ≠ z) : r x ^ 2 + r z ^ 2 ≤ 9 := by
  classical
  have hsub : ({x, z} : Finset Q9) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun w _ _ => (sq_nonneg (r w)))
  simpa [Finset.sum_insert, hxz, hnorm] using h

open Classical in
theorem classify_nine_residual (r : Q9 → ℤ)
    (hnorm : (∑ x, (r x)^2) = 9)
    (hdiv : ∀ x, (3 : ℤ) ∣ intA r x) :
    (∃ (y : Q9) (s : ℤ), s^2 = 1 ∧ r = (fun x => if x = y then 3*s else 0)) ∨
    (∃ (y : Q9) (s : ℤ), s^2 = 1 ∧ r = (fun x => s*intCoeff x y)) := by
  let S : Finset Q9 := Finset.univ.filter (fun x => r x ≠ 0)
  have hS : S = Finset.univ.filter (fun x => r x ≠ 0) := rfl
  have hSne : S.Nonempty := support_nonempty r hnorm hS
  have hScard : S.card ≤ 9 := support_card_le_nine r hnorm hS
  by_cases hsingle : ∃ y : Q9, (S.filter (fun x => (hypercube 9).Adj y x)).card = 1
  · obtain ⟨y, hy⟩ := hsingle
    obtain ⟨x, hfilter⟩ := Finset.card_eq_one.mp hy
    have hxF : x ∈ S.filter (fun z => (hypercube 9).Adj y z) := by
      rw [hfilter]
      simp
    have hxS : x ∈ S := (Finset.mem_filter.mp hxF).1
    have hxy : (hypercube 9).Adj y x := (Finset.mem_filter.mp hxF).2
    have hrow := row_on_singleton r hS hfilter
    have hdivy := hdiv y
    rw [hrow] at hdivy
    have hmul : (3 : ℤ) ∣ r x := by
      rcases intCoeff_sign_of_adj y x hxy with hc | hc
      · simpa [hc] using hdivy
      · simpa [hc] using hdivy
    obtain ⟨k, hk⟩ := hmul
    have hkx : r x = 3 * k := by simpa using hk
    have hnonzero : r x ≠ 0 := by simpa [hS] using (Finset.mem_filter.mp hxS).2
    have hkne : k ≠ 0 := by
      intro hk0
      apply hnonzero
      rw [hkx, hk0, mul_zero]
    have hk_sq : 1 ≤ k^2 := by
      by_cases hkpos : 0 < k
      · have : 1 ≤ k := by omega
        nlinarith
      · have : k ≤ -1 := by omega
        nlinarith
    have hrxlow : (9 : ℤ) ≤ r x ^ 2 := by rw [hkx]; nlinarith
    have hrxhigh : r x ^ 2 ≤ 9 := by
      have hsingle : r x ^ 2 ≤ ∑ z, r z ^ 2 := by
        exact Finset.single_le_sum (s := (Finset.univ : Finset Q9))
          (f := fun z : Q9 => r z ^ 2) (fun z _ => sq_nonneg (r z))
          (Finset.mem_univ x)
      simpa [hnorm] using hsingle
    have hrxsq : r x ^ 2 = 9 := by omega
    have hksq : k^2 = 1 := by rw [hkx] at hrxsq; nlinarith
    have hrzero (z : Q9) (hz : z ≠ x) : r z = 0 := by
      by_contra hne
      have hsq : 1 ≤ r z ^ 2 := by
        have htmp : z ∈ S := by simp [hS, hne]
        exact support_term_ge_one r hS htmp
      have htwo := two_point_sum_le r hnorm hz.symm
      nlinarith [hrxsq]
    left
    refine ⟨x, k, hksq, ?_⟩
    funext z
    by_cases hz : z = x
    · subst z; simp [hkx]
    · simp [hz, hrzero z hz]
  · have hno : ∀ y : Q9, (S.filter (fun x => (hypercube 9).Adj y x)).card ≠ 1 := by
      intro y hy; exact hsingle ⟨y, hy⟩
    obtain ⟨y, hyS⟩ :=
      CubeNineSupport.eq_neighbors_of_no_singleton S hSne hScard hno
    have hcardN : (Finset.univ.filter (fun x : Q9 => (hypercube 9).Adj y x)).card = 9 := by
      calc
        _ = ((hypercube 9).neighborFinset y).card := by
          rw [(hypercube 9).neighborFinset_eq_filter]
        _ = (hypercube 9).degree y := rfl
        _ = 9 := (hypercube_regular 9).degree_eq y
    have hScard9 : S.card = 9 := by rw [hyS, hcardN]
    have hsumS : (∑ x ∈ S, r x ^ 2) = 9 := by
      rw [support_sum_eq r S hS, hnorm]
    have hsquare_one (w : Q9) (hw : w ∈ S) : r w ^ 2 = 1 := by
      have herase : (S.erase w).card = 8 := by
        rw [Finset.card_erase_of_mem hw, hScard9]
      have hrest : (8 : ℤ) ≤ ∑ z ∈ S.erase w, r z ^ 2 := by
        calc
          (8 : ℤ) = ((S.erase w).card : ℤ) := by rw [herase]; norm_num
          _ = ∑ _z ∈ S.erase w, (1 : ℤ) := by simp
          _ ≤ ∑ z ∈ S.erase w, r z ^ 2 := by
            exact Finset.sum_le_sum (fun z hz => support_term_ge_one r hS
              (Finset.mem_of_mem_erase hz))
      have hadd : r w ^ 2 + ∑ z ∈ S.erase w, r z ^ 2 = 9 := by
        rw [add_comm, Finset.sum_erase_add S (fun z => r z ^ 2) hw, hsumS]
      have hlow := support_term_ge_one r hS hw
      nlinarith
    have hr_sign (w : Q9) (hw : w ∈ S) : r w = 1 ∨ r w = -1 := by
      have hs := hsquare_one w hw
      have hfactor : (r w - 1) * (r w + 1) = 0 := by nlinarith [hs]
      rcases mul_eq_zero.mp hfactor with hleft | hright
      · left; omega
      · right; omega
    have hcommon_card (z : Q9) (hzy : z ≠ y) :
        (S.filter (fun w => (hypercube 9).Adj z w)).card ≤ 2 := by
      let C := S.filter (fun w => (hypercube 9).Adj z w)
      by_cases hC : C.Nonempty
      · obtain ⟨w, hw⟩ := hC
        have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
        have hwzy : (hypercube 9).Adj z w := (Finset.mem_filter.mp hw).2
        have hwy : (hypercube 9).Adj y w := (Finset.mem_filter.mp (hyS ▸ hwS)).2
        obtain ⟨i, hi⟩ := adjacent_exists_flip hwzy
        have hdiff := diff_of_adj_flip (x:=z) (z:=y) hzy i (by
          rw [← hi]
          exact hwy.symm)
        have hsub : C ⊆ (diff z y).image (fun j => BalancedCriticalSpectrum.flip z j) := by
          intro u hu
          have huS : u ∈ S := (Finset.mem_filter.mp hu).1
          have huz : (hypercube 9).Adj z u := (Finset.mem_filter.mp hu).2
          obtain ⟨j, hj⟩ := adjacent_exists_flip huz
          have huy : (hypercube 9).Adj y u := (Finset.mem_filter.mp (hyS ▸ huS)).2
          have hdj := diff_of_adj_flip (x:=z) (z:=y) hzy j (by
            rw [← hj]
            exact huy.symm)
          exact Finset.mem_image.mpr ⟨j, hdj.1, hj.symm⟩
        calc
          C.card ≤ ((diff z y).image (fun j => BalancedCriticalSpectrum.flip z j)).card :=
            Finset.card_le_card hsub
          _ ≤ (diff z y).card := Finset.card_image_le
          _ = 2 := hdiff.2
      · have hzero : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
        change C.card ≤ 2
        rw [hzero]
        norm_num
    have hrow_zero (z : Q9) (hzy : z ≠ y) : intA r z = 0 := by
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
      rw [hrow]
      have hupper : (∑ w ∈ C, intCoeff z w * r w) ≤ C.card := by
        calc
          _ ≤ ∑ _w ∈ C, (1 : ℤ) := by
            apply Finset.sum_le_sum
            intro w hw
            have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
            rcases intCoeff_sign_of_adj z w (Finset.mem_filter.mp hw).2 with hc | hc <;>
              rcases hr_sign w hwS with hr | hr <;> simp [hc, hr] <;> omega
          _ = C.card := by simp
      have hlower : -(C.card : ℤ) ≤ ∑ w ∈ C, intCoeff z w * r w := by
        calc
          -(C.card : ℤ) = ∑ _w ∈ C, (-1 : ℤ) := by simp
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro w hw
            have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
            rcases intCoeff_sign_of_adj z w (Finset.mem_filter.mp hw).2 with hc | hc <;>
              rcases hr_sign w hwS with hr | hr <;> simp [hc, hr] <;> omega
      have hc2 : C.card ≤ 2 := hcommon_card z hzy
      have hdivz := hdiv z
      rcases hdivz with ⟨k, hk⟩
      rw [hrow] at hk
      omega
    let a : ℤ := intA r y
    have hA : intA r = fun z => if z = y then a else 0 := by
      funext z
      by_cases hzy : z = y
      · simp [a, hzy]
      · simp [hrow_zero z hzy, hzy]
    have hsq := intA_square r
    have hrel (z : Q9) : 9 * r z = a * intCoeff z y := by
      have hz := congrFun hsq z
      rw [hA] at hz
      simpa [intA, mul_ite, mul_comm] using hz.symm
    obtain ⟨x, hxS⟩ := hSne
    have hxy : (hypercube 9).Adj y x := (Finset.mem_filter.mp (hyS ▸ hxS)).2
    rcases intCoeff_sign_of_adj x y (hxy.symm) with hc | hc
    all_goals
      have hrx := hsquare_one x hxS
      have hrelx := hrel x
      let s : ℤ := r x * intCoeff x y
      have hs : s^2 = 1 := by
        dsimp [s]
        rw [hc]
        nlinarith [hrx]
      have ha : a = 9 * s := by
        have hh := congrArg (fun t : ℤ => t * intCoeff x y) hrelx
        dsimp [s]
        rw [hc] at hh ⊢
        nlinarith [hh]
      right
      refine ⟨y, s, hs, ?_⟩
      funext z
      have hz := hrel z
      rw [ha] at hz
      nlinarith [hz]

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangMinimalResidual
