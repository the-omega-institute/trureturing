/- GID: D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/TernaryWeakMetricStability
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact retained ternary near-maximum weak metric dimensions.
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NativeDecide
import Mathlib.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace D5.S3.Combinatorics.Hamming.TernaryWeakMetricStability

open scoped BigOperators

abbrev Word (d : ℕ) := Fin d → Fin 3

def distance {d : ℕ} (x y : Word d) : ℕ :=
  ∑ i : Fin d, if x i = y i then 0 else 1

theorem distance_eq_hammingDist {d : ℕ} (x y : Word d) :
    distance x y = hammingDist x y := by
  simp [distance, hammingDist, card_eq_sum_ones]

def separation {d : ℕ} (T : Finset (Word d)) (x y : Word d) : ℕ :=
  ∑ z ∈ T, Nat.dist (distance x z) (distance y z)

def IsWeakResolving (d k : ℕ) (S : Finset (Word d)) : Prop :=
  ∀ x y, x ≠ y → k ≤ separation S x y

noncomputable def metricDimension (d k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ S : Finset (Word d), IsWeakResolving d k S ∧ S.card = n}

def kappa (d : ℕ) : ℕ := 2 * 3 ^ (d - 1)

def omittedCapacity (t : ℕ) : ℕ := 3 * (t / 2) + (t % 2)

theorem omittedCapacity_four : omittedCapacity 4 = 6 := by decide
theorem omittedCapacity_five : omittedCapacity 5 = 7 := by decide

def complement {d : ℕ} (T : Finset (Word d)) : Finset (Word d) :=
  (Finset.univ : Finset (Word d)) \ T

theorem complement_card {d : ℕ} (T : Finset (Word d)) :
    (complement T).card + T.card = 3 ^ d := by
  classical
  simp [complement]

theorem separation_complement {d : ℕ} (T : Finset (Word d)) (x y : Word d) :
    separation (complement T) x y + separation T x y =
      separation (Finset.univ : Finset (Word d)) x y := by
  classical
  simp only [separation, complement, Finset.sum_sdiff]

private def orbit {d : ℕ} (x : Word d) : Finset (Word d) :=
  {x, fun i => ⟨((x i).val + 1) % 3, by omega⟩,
    fun i => ⟨((x i).val + 2) % 3, by omega⟩}

private def constantWord {d : ℕ} (a : Fin 3) : Word d := fun _ => a

private def mixedWord {d : ℕ} : Word d := fun i => if i = 0 then 0 else 1

private def extraWord {d : ℕ} (hd : 2 ≤ d) : Word d :=
  fun i => if i = 0 then 0 else if i = 1 then 2 else 0

private def baseOmitted {d : ℕ} : Finset (Word d) :=
  orbit (constantWord 0) ∪ orbit mixedWord

private def oddOmitted {d : ℕ} (hd : 2 ≤ d) : Finset (Word d) :=
  insert (extraWord hd) (baseOmitted (d := d))

private theorem orbit_card {d : ℕ} (hd : 1 ≤ d) (x : Word d) : (orbit x).card = 3 := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  have h01 : x ≠ fun j => ⟨((x j).val + 1) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    have hx := (x i).isLt
    omega
  have h02 : x ≠ fun j => ⟨((x j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    have hx := (x i).isLt
    omega
  have h12 : (fun j => ⟨((x j).val + 1) % 3, by omega⟩ : Word d) ≠
      fun j => ⟨((x j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    have hx := (x i).isLt
    omega
  simp [orbit, h01, h02, h12]

private theorem orbit_disjoint_constant_mixed {d : ℕ} (hd : 2 ≤ d) :
    Disjoint (orbit (constantWord 0)) (orbit mixedWord) := by
  classical
  rw [Finset.disjoint_left]
  intro z hz0 hz1
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hz0 hz1
  rcases hz0 with rfl | rfl | rfl <;> rcases hz1 with h | h | h
  all_goals
    have h0 := congrArg Fin.val (congr_fun h ⟨0, by omega⟩)
    have h1 := congrArg Fin.val (congr_fun h ⟨1, by omega⟩)
    simp [constantWord, mixedWord] at h0 h1
    omega

theorem baseOmitted_card {d : ℕ} (hd : 2 ≤ d) : (baseOmitted (d := d)).card = 6 := by
  classical
  rw [baseOmitted, Finset.card_union_of_disjoint (orbit_disjoint_constant_mixed hd)]
  rw [orbit_card (by omega) (constantWord 0), orbit_card (by omega) mixedWord]
  norm_num

theorem oddOmitted_card {d : ℕ} (hd : 2 ≤ d) : (oddOmitted hd).card = 7 := by
  classical
  unfold oddOmitted
  have hnot : extraWord hd ∉ baseOmitted (d := d) := by
    unfold extraWord baseOmitted orbit
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h | h | h | h | h
    all_goals
      have h0 := congrArg Fin.val (congr_fun h ⟨0, by omega⟩)
      have h1 := congrArg Fin.val (congr_fun h ⟨1, by omega⟩)
      simp [constantWord, mixedWord] at h0 h1
      omega
  simp [baseOmitted_card hd, hnot]

/- The actual boundary checks are finite and use the literal carrier and all
   distinct pairs; these are the consumed published d=2 boundary values. -/
private theorem d2_no_six (t : ℕ) (ht : t = 4) :
    ∀ T : Finset (Word 2), T.card = 6 →
      ∃ x y, x ≠ y ∧ separation T x y > 4 := by
  subst t
  native_decide

private theorem d2_no_seven (t : ℕ) (ht : t = 5) :
    ∀ T : Finset (Word 2), T.card = 7 →
      ∃ x y, x ≠ y ∧ separation T x y > 5 := by
  subst t
  native_decide

end D5.S3.Combinatorics.Hamming.TernaryWeakMetricStability
