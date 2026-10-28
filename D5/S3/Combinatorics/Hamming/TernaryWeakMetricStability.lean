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
import Mathlib.Data.Fintype.BigOperators
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

private def distanceExcept {d : ℕ} (i : Fin d) (x z : Word d) : ℕ :=
  ∑ j ∈ (Finset.univ.erase i), if x j = z j then 0 else 1

private theorem distance_eq_update_sum {d : ℕ} (i : Fin d) (x z : Word d) :
    distance x z = (if x i = z i then 0 else 1) + distanceExcept i x z := by
  classical
  unfold distance distanceExcept
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp [eq_comm, add_comm]

private theorem adjacent_separation {d : ℕ} (i : Fin d) (a b : Fin 3) (hab : a ≠ b)
    (T : Finset (Word d)) :
    separation T (Function.update (constantWord 0) i a)
        (Function.update (constantWord 0) i b) =
      (T.filter (fun z => z i = a ∨ z i = b)).card := by
  classical
  have hpoint (z : Word d) :
      Nat.dist (distance (Function.update (constantWord 0) i a) z)
          (distance (Function.update (constantWord 0) i b) z) =
        (if z i = a ∨ z i = b then 1 else 0) := by
    rw [distance_eq_update_sum, distance_eq_update_sum]
    by_cases hza : z i = a <;> by_cases hzb : z i = b
    · exact (hab (hza.trans hzb.symm)).elim
    · simp [hza, hzb, Function.update_same, Nat.dist]
    · simp [hza, hzb, Function.update_same, Nat.dist]
    · simp [hza, hzb, Function.update_same, Nat.dist]
  simp only [separation]
  simp_rw [hpoint]
  simp [Finset.card_filter]

private theorem adjacent_pair_bound {d : ℕ} (hd : 1 ≤ d) (T : Finset (Word d))
    {t : ℕ} (hT : ∀ a b : Fin 3, a ≠ b →
      separation T (Function.update (constantWord 0) ⟨0, by omega⟩ a)
        (Function.update (constantWord 0) ⟨0, by omega⟩ b) ≤ t) :
    T.card ≤ omittedCapacity t := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  let a : Fin 3 := 0
  let b : Fin 3 := 1
  let c : Fin 3 := 2
  let x₀ : Word d := Function.update (constantWord 0) i a
  let x₁ : Word d := Function.update (constantWord 0) i b
  let x₂ : Word d := Function.update (constantWord 0) i c
  have h01 : x₀ ≠ x₁ := by
    intro h
    have := congrArg (fun z => z i) h
    simp [x₀, x₁, i] at this
  have h02 : x₀ ≠ x₂ := by
    intro h
    have := congrArg (fun z => z i) h
    simp [x₀, x₂, i] at this
  have h12 : x₁ ≠ x₂ := by
    intro h
    have := congrArg (fun z => z i) h
    simp [x₁, x₂, i] at this
  have h01' := hT a b (by decide)
  have h02' := hT a c (by decide)
  have h12' := hT b c (by decide)
  rw [adjacent_separation i a b (by decide), adjacent_separation i a c (by decide),
    adjacent_separation i b c (by decide)] at h01' h02' h12'
  let n₀ := (T.filter (fun z => z i = a)).card
  let n₁ := (T.filter (fun z => z i = b)).card
  let n₂ := (T.filter (fun z => z i = c)).card
  have hcard : n₀ + n₁ + n₂ = T.card := by
    let A := T.filter (fun z => z i = a)
    let B := T.filter (fun z => z i = b)
    let C := T.filter (fun z => z i = c)
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      simp only [A, B, Finset.mem_filter] at hzA hzB
      exact (by simpa [a, b] using hzA.2.symm.trans hzB.2)
    have hAC : Disjoint A C := by
      rw [Finset.disjoint_left]
      intro z hzA hzC
      simp only [A, C, Finset.mem_filter] at hzA hzC
      exact (by simpa [a, c] using hzA.2.symm.trans hzC.2)
    have hBC : Disjoint B C := by
      rw [Finset.disjoint_left]
      intro z hzB hzC
      simp only [B, C, Finset.mem_filter] at hzB hzC
      exact (by simpa [b, c] using hzB.2.symm.trans hzC.2)
    have hABC : Disjoint (A ∪ B) C := hAC.union hBC
    have hU : A ∪ B ∪ C = T := by
      ext z
      constructor
      · intro hz
        exact (Finset.mem_union.mp hz).elim (fun h => (Finset.mem_filter.mp h).1)
          (fun h => (Finset.mem_filter.mp h).1)
      · intro hz
        have hcases : z i = a ∨ z i = b ∨ z i = c := by
          fin_cases hzv : z i <;> simp [a, b, c, hzv]
        rcases hcases with h | h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz, h⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz, h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hz, h⟩))
    rw [← hU]
    simp only [n₀, n₁, n₂, A, B, C]
    rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hABC]
  have hpair01 : n₀ + n₁ ≤ t := by simpa [n₀, n₁] using h01'
  have hpair02 : n₀ + n₂ ≤ t := by simpa [n₀, n₂] using h02'
  have hpair12 : n₁ + n₂ ≤ t := by simpa [n₁, n₂] using h12'
  dsimp [omittedCapacity]
  omega

private theorem univ_coordinate_card {d : ℕ} (hd : 1 ≤ d) (i : Fin d)
    (a b : Fin 3) (hab : a ≠ b) :
    ((Finset.univ : Finset (Word d)).filter (fun z => z i = a ∨ z i = b)).card =
      2 * 3 ^ (d - 1) := by
  classical
  let s : ∀ _ : Fin d, Finset (Fin 3) := fun _ => Finset.univ
  have hs : Fintype.piFinset s = (Finset.univ : Finset (Word d)) := by
    ext z
    simp [s, Fintype.mem_piFinset]
  rw [← hs, filter_or]
  have hdis : Disjoint
      ((Fintype.piFinset s).filter (fun z => z i = a))
      ((Fintype.piFinset s).filter (fun z => z i = b)) := by
    rw [Finset.disjoint_left]
    intro z hza hzb
    exact hab ((Finset.mem_filter.mp hza).2.trans (Finset.mem_filter.mp hzb).2.symm)
  rw [Finset.card_union_of_disjoint hdis]
  rw [Fintype.card_filter_piFinset_const s i a,
    Fintype.card_filter_piFinset_const s i b]
  simp [s, hd]

private theorem complement_omitted_bound {d : ℕ} (hd : 2 ≤ d) (t : ℕ)
    (S : Finset (Word d))
    (hS : IsWeakResolving d (kappa d - t) S)
    (hkt : t ≤ kappa d) :
    (complement S).card ≤ omittedCapacity t := by
  apply adjacent_pair_bound (by omega) (complement S)
  intro a b hab
  let i : Fin d := ⟨0, by omega⟩
  let x := Function.update (constantWord 0) i a
  let y := Function.update (constantWord 0) i b
  have hxy : x ≠ y := by
    intro h
    have hh := congrArg (fun z => z i) h
    exact hab (by simpa [x, y] using hh)
  have hs := hS x y hxy
  have hc := separation_complement S x y
  have hu := adjacent_separation i a b hab (Finset.univ : Finset (Word d))
  have hcard := univ_coordinate_card (by omega) i a b hab
  rw [hu, hcard] at hc
  unfold kappa at hc hs ⊢
  omega

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

private theorem dist_sum_le {α : Type*} (s : Finset α) (f g : α → ℕ) :
    Nat.dist (∑ a ∈ s, f a) (∑ a ∈ s, g a) ≤
      ∑ a ∈ s, Nat.dist (f a) (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have h := Nat.dist.triangle_inequality (f a + ∑ x ∈ s, f x)
        (g a + ∑ x ∈ s, f x) (g a + ∑ x ∈ s, g x)
      rw [Nat.dist_add_add_right, Nat.dist_add_add_left] at h
      calc
        Nat.dist (f a + ∑ x ∈ s, f x) (g a + ∑ x ∈ s, g x) ≤
            Nat.dist (f a) (g a) +
              Nat.dist (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by simpa [add_comm] using h
        _ ≤ Nat.dist (f a) (g a) + ∑ x ∈ s, Nat.dist (f x) (g x) :=
          Nat.add_le_add_left ih _

private theorem orbit_coordinate_bound {d : ℕ} (u : Word d) (i : Fin d)
    (a b : Fin 3) :
    (∑ z ∈ orbit u,
      Nat.dist (if a = z i then 0 else 1) (if b = z i then 0 else 1)) ≤
      2 * (if a = b then 0 else 1) := by
  classical
  have h01 : u ≠ fun j => ⟨((u j).val + 1) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    have hx := (u i).isLt
    omega
  have h02 : u ≠ fun j => ⟨((u j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    have hx := (u i).isLt
    omega
  have h12 : (fun j => ⟨((u j).val + 1) % 3, by omega⟩ : Word d) ≠
      fun j => ⟨((u j).val + 2) % 3, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val (congr_fun h i)
    have hx := (u i).isLt
    omega
  rw [show orbit u = {u, fun j => ⟨((u j).val + 1) % 3, by omega⟩,
      fun j => ⟨((u j).val + 2) % 3, by omega⟩} by rfl]
  simp only [Finset.sum_insert h01, Finset.sum_insert h02, Finset.sum_singleton]
  fin_cases ha : a <;> fin_cases hb : b <;> fin_cases hu : u i <;>
    simp [ha, hb, hu] <;> omega

private theorem orbit_separation_le {d : ℕ} (hd : 1 ≤ d) (u x y : Word d) :
    separation (orbit u) x y ≤ 2 * distance x y := by
  classical
  have hcard : (orbit u).card = 3 := orbit_card hd u
  calc
    separation (orbit u) x y ≤
        ∑ z ∈ orbit u, ∑ i : Fin d,
          Nat.dist (if x i = z i then 0 else 1) (if y i = z i then 0 else 1) := by
      apply Finset.sum_le_sum
      intro z hz
      exact dist_sum_le Finset.univ
        (fun i => if x i = z i then 0 else 1)
        (fun i => if y i = z i then 0 else 1)
    _ = ∑ i : Fin d, ∑ z ∈ orbit u,
          Nat.dist (if x i = z i then 0 else 1) (if y i = z i then 0 else 1) := by
      simp_rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin d, 2 * (if x i = y i then 0 else 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact orbit_coordinate_bound u i (x i) (y i)
    _ = 2 * distance x y := by
      simp [distance, Finset.mul_sum, Nat.mul_comm]

private theorem singleton_separation_le {d : ℕ} (z x y : Word d) :
    separation {z} x y ≤ distance x y := by
  have hxy : distance x z ≤ distance x y + distance y z := by
    simpa [distance_eq_hammingDist] using hammingDist_triangle x y z
  have hyx : distance y z ≤ distance x y + distance x z := by
    have := hammingDist_triangle y x z
    simpa [distance_eq_hammingDist, hammingDist_comm] using this
  simp only [separation, Finset.sum_insert, Finset.sum_singleton, Finset.not_mem_empty]
  unfold Nat.dist
  omega

private theorem base_separation_le {d : ℕ} (hd : 1 ≤ d) (x y : Word d) :
    separation (baseOmitted (d := d)) x y ≤ 4 * distance x y := by
  rw [baseOmitted]
  have h₁ := orbit_separation_le hd (constantWord 0) x y
  have h₂ := orbit_separation_le hd mixedWord x y
  rw [separation, Finset.sum_union (orbit_disjoint_constant_mixed (by omega))] at *
  omega

private theorem odd_separation_le {d : ℕ} (hd : 2 ≤ d) (x y : Word d) :
    separation (oddOmitted hd) x y ≤ 5 * distance x y := by
  rw [oddOmitted]
  have h₁ := base_separation_le (by omega) x y
  have h₂ := singleton_separation_le (extraWord hd) x y
  rw [separation, Finset.sum_insert] at *
  · omega
  · intro h
    exact (by
      unfold extraWord baseOmitted orbit
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h | h | h | h
      all_goals
        have h0 := congrArg Fin.val (congr_fun h ⟨0, by omega⟩)
        have h1 := congrArg Fin.val (congr_fun h ⟨1, by omega⟩)
        simp [constantWord, mixedWord] at h0 h1
        omega)
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

private def d2S_four : Finset (Word 2) :=
  {(fun _ => 0), (fun i => if i = 0 then 0 else 1),
    (fun i => if i = 0 then 1 else 0), (fun _ => 1)}

private def d2S_five : Finset (Word 2) :=
  {(fun _ => 0), (fun i => if i = 0 then 0 else 1),
    (fun i => if i = 0 then 1 else 0)}

private theorem d2S_four_card : d2S_four.card = 4 := by native_decide
private theorem d2S_five_card : d2S_five.card = 3 := by native_decide

private theorem d2S_four_resolves : IsWeakResolving 2 2 d2S_four := by
  native_decide

private theorem d2S_five_resolves : IsWeakResolving 2 1 d2S_five := by
  native_decide

private theorem d2_lower_four :
    ∀ S : Finset (Word 2), IsWeakResolving 2 2 S → 4 ≤ S.card := by
  native_decide

private theorem d2_lower_five :
    ∀ S : Finset (Word 2), IsWeakResolving 2 1 S → 3 ≤ S.card := by
  native_decide

private theorem base_complement_resolves_d3 :
    IsWeakResolving 3 (kappa 3 - 4) (complement (baseOmitted (d := 3))) := by
  native_decide

private theorem odd_complement_resolves_d3 :
    IsWeakResolving 3 (kappa 3 - 5) (complement (oddOmitted (by decide : 2 ≤ 3))) := by
  native_decide

private theorem base_complement_resolves_d4 :
    IsWeakResolving 4 (kappa 4 - 4) (complement (baseOmitted (d := 4))) := by
  native_decide

private theorem odd_complement_resolves_d4 :
    IsWeakResolving 4 (kappa 4 - 5) (complement (oddOmitted (by decide : 2 ≤ 4))) := by
  native_decide

theorem d2_metricDimension_four : metricDimension 2 (kappa 2 - 4) = 4 := by
  have hk : kappa 2 - 4 = 2 := by decide
  rw [hk]
  apply le_antisymm
  · exact csInf_le' ⟨d2S_four, d2S_four_resolves, d2S_four_card⟩
  · apply le_csInf
    · exact ⟨4, d2S_four, d2S_four_resolves, d2S_four_card⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d2_lower_four S hS

theorem d2_metricDimension_five : metricDimension 2 (kappa 2 - 5) = 3 := by
  have hk : kappa 2 - 5 = 1 := by decide
  rw [hk]
  apply le_antisymm
  · exact csInf_le' ⟨d2S_five, d2S_five_resolves, d2S_five_card⟩
  · apply le_csInf
    · exact ⟨3, d2S_five, d2S_five_resolves, d2S_five_card⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d2_lower_five S hS

private theorem d3_lower_four :
    ∀ S : Finset (Word 3), IsWeakResolving 3 (kappa 3 - 4) S → 21 ≤ S.card := by
  intro S hS
  have ht := complement_omitted_bound (by decide : 2 ≤ 3) 4 S hS (by decide)
  have hc := complement_card S
  omega

private theorem d3_lower_five :
    ∀ S : Finset (Word 3), IsWeakResolving 3 (kappa 3 - 5) S → 20 ≤ S.card := by
  intro S hS
  have ht := complement_omitted_bound (by decide : 2 ≤ 3) 5 S hS (by decide)
  have hc := complement_card S
  omega

private theorem d4_lower_four :
    ∀ S : Finset (Word 4), IsWeakResolving 4 (kappa 4 - 4) S → 75 ≤ S.card := by
  intro S hS
  have ht := complement_omitted_bound (by decide : 2 ≤ 4) 4 S hS (by decide)
  have hc := complement_card S
  omega

private theorem d4_lower_five :
    ∀ S : Finset (Word 4), IsWeakResolving 4 (kappa 4 - 5) S → 74 ≤ S.card := by
  intro S hS
  have ht := complement_omitted_bound (by decide : 2 ≤ 4) 5 S hS (by decide)
  have hc := complement_card S
  omega

theorem d3_metricDimension_four : metricDimension 3 (kappa 3 - 4) = 21 := by
  apply le_antisymm
  · have hc := complement_card (baseOmitted (d := 3))
    have hcard := baseOmitted_card (by decide : 2 ≤ 3)
    have hres := base_complement_resolves_d3
    exact (csInf_le' ⟨complement (baseOmitted (d := 3)), hres, rfl⟩).trans_eq (by omega)
  · apply le_csInf
    · exact ⟨21, complement (baseOmitted (d := 3)), base_complement_resolves_d3, by
        have hc := complement_card (baseOmitted (d := 3))
        have hcard := baseOmitted_card (by decide : 2 ≤ 3)
        omega⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d3_lower_four S hS

theorem d3_metricDimension_five : metricDimension 3 (kappa 3 - 5) = 20 := by
  apply le_antisymm
  · exact (csInf_le' ⟨complement (oddOmitted (by decide : 2 ≤ 3)), odd_complement_resolves_d3, rfl⟩).trans_eq (by
      have hc := complement_card (oddOmitted (by decide : 2 ≤ 3))
      have hcard := oddOmitted_card (by decide : 2 ≤ 3)
      omega)
  · apply le_csInf
    · exact ⟨20, complement (oddOmitted (by decide : 2 ≤ 3)), odd_complement_resolves_d3, by
        have hc := complement_card (oddOmitted (by decide : 2 ≤ 3))
        have hcard := oddOmitted_card (by decide : 2 ≤ 3)
        omega⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d3_lower_five S hS

theorem d4_metricDimension_four : metricDimension 4 (kappa 4 - 4) = 75 := by
  apply le_antisymm
  · exact (csInf_le' ⟨complement (baseOmitted (d := 4)), base_complement_resolves_d4, rfl⟩).trans_eq (by
      have hc := complement_card (baseOmitted (d := 4))
      have hcard := baseOmitted_card (by decide : 2 ≤ 4)
      omega)
  · apply le_csInf
    · exact ⟨75, complement (baseOmitted (d := 4)), base_complement_resolves_d4, by
        have hc := complement_card (baseOmitted (d := 4))
        have hcard := baseOmitted_card (by decide : 2 ≤ 4)
        omega⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d4_lower_four S hS

theorem d4_metricDimension_five : metricDimension 4 (kappa 4 - 5) = 74 := by
  apply le_antisymm
  · exact (csInf_le' ⟨complement (oddOmitted (by decide : 2 ≤ 4)), odd_complement_resolves_d4, rfl⟩).trans_eq (by
      have hc := complement_card (oddOmitted (by decide : 2 ≤ 4))
      have hcard := oddOmitted_card (by decide : 2 ≤ 4)
      omega)
  · apply le_csInf
    · exact ⟨74, complement (oddOmitted (by decide : 2 ≤ 4)), odd_complement_resolves_d4, by
        have hc := complement_card (oddOmitted (d := 4) (by decide : 2 ≤ 4))
        have hcard := oddOmitted_card (by decide : 2 ≤ 4)
        omega⟩
    · rintro n ⟨S, hS, rfl⟩
      exact d4_lower_five S hS

end D5.S3.Combinatorics.Hamming.TernaryWeakMetricStability
