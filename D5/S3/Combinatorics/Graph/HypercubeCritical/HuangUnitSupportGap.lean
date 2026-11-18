/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitSupportGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitSupportGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: No unit-valued negative-three Huang eigenvector has support twenty-four. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangMinimalResidual
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeTwelveSupport
import Mathlib.Algebra.CharP.Basic
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private intA intCoeff evenPart oddPart intCoeff_cast parts_add
  intA_even_on_even intA_odd_on_odd intCoeff_sign_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private huangMatrix_symmetric cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private row_on_singleton from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangMinimalResidual

private theorem even_diff_of_parity_eq {n : Nat} (x y : Fin n → Bool) (hp : cubeParity x = cubeParity y) :
    Even ((Finset.univ.filter (fun i => x i ≠ y i)).card) := by
  classical
  letI : CharP Bool 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by decide)
  apply even_iff_two_dvd.mpr
  apply (CharP.cast_eq_zero_iff Bool 2 _).mp
  have heq : (((Finset.univ.filter (fun i => x i ≠ y i)).card : Nat) : Bool) =
      cubeParity x + cubeParity y := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [Finset.sum_filter]
    unfold cubeParity
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> cases y i <;> decide
  rw [heq, hp]
  exact BooleanRing.add_self _

open Classical in
private theorem intA_add (f g : Q9 → ℤ) : intA (f + g) = intA f + intA g := by
  classical
  funext x
  simp only [intA, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem intCoeff_symmetric (x y : Q9) : intCoeff x y = intCoeff y x := by
  apply Int.cast_injective (α := ℝ)
  rw [intCoeff_cast, intCoeff_cast]
  exact huangMatrix_symmetric x y

open Classical in
private theorem pairing_comm (r s : Q9 → ℤ) :
    (∑ x, r x * intA s x) = ∑ x, s x * intA r x := by
  classical
  unfold intA
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [intCoeff_symmetric y x]
  ring

open Classical in
private theorem parts_eigen (h : Q9 → ℤ)
    (heig : intA h = fun x => -3 * h x) :
    intA (evenPart h) = (fun x => -3 * oddPart h x) ∧
    intA (oddPart h) = (fun x => -3 * evenPart h x) := by
  classical
  have hadd (x : Q9) :
      intA (evenPart h) x + intA (oddPart h) x = -3 * h x := by
    calc
      _ = intA (evenPart h + oddPart h) x :=
        (congrFun (intA_add (evenPart h) (oddPart h)) x).symm
      _ = intA h x := by rw [parts_add]
      _ = -3 * h x := congrFun heig x
  constructor
  · funext x
    change intA (evenPart h) x = -3 * oddPart h x
    cases hp : cubeParity x
    · rw [intA_even_on_even h x hp]
      simp [oddPart, hp]
    · have hx := hadd x
      rw [intA_odd_on_odd h x hp, add_zero] at hx
      simpa [oddPart, hp] using hx
  · funext x
    change intA (oddPart h) x = -3 * evenPart h x
    cases hp : cubeParity x
    · have hx := hadd x
      rw [intA_even_on_even h x hp, zero_add] at hx
      simpa [evenPart, hp] using hx
    · rw [intA_odd_on_odd h x hp]
      simp [evenPart, hp]

open Classical in
private theorem unit_norm_eq_card (f : Q9 → ℤ)
    (hu : ∀ x, f x = 0 ∨ f x = 1 ∨ f x = -1) :
    (∑ x, f x ^ 2) = ((Finset.univ.filter (fun x => f x ≠ 0)).card : ℤ) := by
  classical
  calc
    (∑ x, f x ^ 2) = ∑ x, (if f x ≠ 0 then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rcases hu x with hx | hx | hx <;> simp [hx]
    _ = ((Finset.univ.filter (fun x => f x ≠ 0)).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp

open Classical in
private theorem no_singleton_row (r : Q9 → ℤ)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (hdiv : ∀ y, (3 : ℤ) ∣ intA r y) :
    ∀ y, ((Finset.univ.filter (fun x => r x ≠ 0)).filter
      (fun x => (hypercube 9).Adj y x)).card ≠ 1 := by
  classical
  let S : Finset Q9 := Finset.univ.filter (fun x => r x ≠ 0)
  have hS : S = Finset.univ.filter (fun x => r x ≠ 0) := rfl
  intro y hy
  change (S.filter (fun x => (hypercube 9).Adj y x)).card = 1 at hy
  obtain ⟨x, hfilter⟩ := Finset.card_eq_one.mp hy
  have hxF : x ∈ S.filter (fun z => (hypercube 9).Adj y z) := by
    rw [hfilter]
    simp
  have hxS : x ∈ S := (Finset.mem_filter.mp hxF).1
  have hadj : (hypercube 9).Adj y x := (Finset.mem_filter.mp hxF).2
  have hxne : r x ≠ 0 := (Finset.mem_filter.mp hxS).2
  have hrow := row_on_singleton r hS hfilter
  obtain ⟨k, hk⟩ := hdiv y
  rw [hrow] at hk
  rcases hu x with hx | hx | hx
  · exact hxne hx
  · rcases intCoeff_sign_of_adj y x hadj with hc | hc <;>
      rw [hc, hx] at hk <;> omega
  · rcases intCoeff_sign_of_adj y x hadj with hc | hc <;>
      rw [hc, hx] at hk <;> omega

open Classical in
theorem no_unit_support_card_twenty_four (h : Q9 → ℤ)
    (heig : intA h = fun x => -3 * h x)
    (hu : ∀ x, h x = 0 ∨ h x = 1 ∨ h x = -1)
    (hsupport : (Finset.univ.filter (fun x => h x ≠ 0)).card = 24) : False := by
  classical
  let r : Q9 → ℤ := evenPart h
  let s : Q9 → ℤ := oddPart h
  obtain ⟨hr', hs'⟩ := parts_eigen h heig
  have hr : intA r = fun x => -3 * s x := hr'
  have hs : intA s = fun x => -3 * r x := hs'
  have hru : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1 := by
    intro x
    by_cases hp : cubeParity x = false
    · simpa [r, evenPart, hp] using hu x
    · simp [r, evenPart, hp]
  have hpair := pairing_comm r s
  have hleft : (∑ x, r x * intA s x) = -3 * ∑ x, r x ^ 2 := by
    rw [hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hright : (∑ x, s x * intA r x) = -3 * ∑ x, s x ^ 2 := by
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
  have hnormh : (∑ x, h x ^ 2) = 24 := by
    rw [unit_norm_eq_card h hu, hsupport]
    norm_num
  have hnormr : (∑ x, r x ^ 2) = 12 := by omega
  let S : Finset Q9 := Finset.univ.filter (fun x => r x ≠ 0)
  have hScard : S.card = 12 := by
    have hc := unit_norm_eq_card r hru
    change (∑ x, r x ^ 2) = (S.card : ℤ) at hc
    omega
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hdiv : ∀ y, (3 : ℤ) ∣ intA r y := by
    intro y
    refine ⟨-s y, ?_⟩
    rw [hr]
    ring
  have hno : ∀ y, (S.filter (fun x => (hypercube 9).Adj y x)).card ≠ 1 :=
    no_singleton_row r hru hdiv
  have hpar : ∃ b : Bool, ∀ x ∈ S, cubeParity x = b := by
    refine ⟨false, ?_⟩
    intro x hx
    have hxne : r x ≠ 0 := (Finset.mem_filter.mp hx).2
    by_contra hp
    apply hxne
    simp [r, evenPart, hp]
  obtain ⟨b, hb⟩ := hpar
  have heven : ∀ x ∈ S, ∀ y ∈ S,
      Even (Finset.univ.filter (fun i : Fin 9 => x i ≠ y i)).card := by
    intro x hx y hy
    exact even_diff_of_parity_eq x y ((hb x hx).trans (hb y hy).symm)
  obtain ⟨y, hyS⟩ := CubeTwelveSupport.eq_neighbors_of_card_le_twelve
    S hSne (by omega) hno heven
  have hcardN : (Finset.univ.filter (fun x : Q9 => (hypercube 9).Adj y x)).card = 9 := by
    calc
      _ = ((hypercube 9).neighborFinset y).card := by
        rw [(hypercube 9).neighborFinset_eq_filter]
      _ = (hypercube 9).degree y := rfl
      _ = 9 := (hypercube_regular 9).degree_eq y
  have hScard9 : S.card = 9 := by rw [hyS, hcardN]
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
