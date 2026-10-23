/- GID: D5/S1/Words/Sequenceability/RowOrbitLift
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/RowOrbitLift
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Affine row orbits yield the two characteristic-five lifted cycles and exact labels. -/

import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Affine return orbits and the four-column characteristic-five lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.RowOrbitLift

open Equiv

/-- Row return after one complete round of columns. -/
def rowReturn {K : Type*} [Field K] (r : Kˣ) (c : K) : Perm K where
  toFun h := c + (r : K) * (h - c)
  invFun h := c + (↑r⁻¹ : K) * (h - c)
  left_inv h := by simp
  right_inv h := by simp

private theorem row_power {K : Type*} [Field K] (r : Kˣ) (c h : K) (n : ℕ) :
    (rowReturn r c ^ n) h = c + (r : K) ^ n * (h - c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih]
    change c + (r : K) * (c + (r : K) ^ n * (h - c) - c) = _
    rw [pow_succ']
    ring

/-- A primitive row multiplier has one fixed row and one orbit of all other rows. -/
theorem row_same_cycle_iff {K : Type*} [Field K] [Finite K]
    (r : Kˣ) (hr : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (c a b : K) :
    (rowReturn r c).SameCycle a b ↔ (a = c ↔ b = c) := by
  constructor
  · intro h
    have hc : rowReturn r c c = c := by simp [rowReturn]
    constructor
    · intro ha
      subst a
      exact (h.eq_of_left hc).symm
    · intro hb
      subst b
      exact h.eq_of_right hc
  · intro hab
    by_cases ha : a = c
    · have hb := hab.mp ha
      rw [ha, hb]
    · have hb : b ≠ c := fun h => ha (hab.mpr h)
      let z : Kˣ := Units.mk0 ((b - c) / (a - c))
        (div_ne_zero (sub_ne_zero.mpr hb) (sub_ne_zero.mpr ha))
      obtain ⟨n, hn⟩ := hr z
      have hn' : (r : K) ^ n = (b - c) / (a - c) := by
        simpa [z] using congrArg (fun t : Kˣ => (t : K)) hn
      refine ⟨(n : ℤ), ?_⟩
      rw [zpow_natCast, row_power, hn', div_mul_cancel₀ _ (sub_ne_zero.mpr ha)]
      ring

/-- Four quotient columns in their traversal order. -/
def column : Fin 4 → ZMod 5 := ![1, 2, 4, 3]

/-- Actual lifted successor: three reflections followed by the closing affine matching. -/
def lift {K : Type*} [Field K] (r : Kˣ) (c : K) : Perm (Fin 4 × K) where
  toFun v := if v.1 = 0 then (1, -v.2)
    else if v.1 = 1 then (2, -v.2)
    else if v.1 = 2 then (3, -v.2)
    else (0, -(r : K) * v.2 + (1 - (r : K)) * c)
  invFun v := if v.1 = 0 then
      (3, -(↑r⁻¹ : K) * (v.2 - (1 - (r : K)) * c))
    else if v.1 = 1 then (0, -v.2)
    else if v.1 = 2 then (1, -v.2)
    else (2, -v.2)
  left_inv := by
    rintro ⟨i, h⟩
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨i, h⟩
    fin_cases i <;> simp

/-- The row at the first column from which a vertex's round begins. -/
def initialRow {K : Type*} [Field K] (v : Fin 4 × K) : K :=
  if v.1 = 0 ∨ v.1 = 2 then v.2 else -v.2

/-- Vertices and differences are in the actual product additive group. -/
def vertex {K : Type*} (v : Fin 4 × K) : ZMod 5 × K := (column v.1, v.2)

def edgeLabel {K : Type*} [Field K] (r : Kˣ) (c : K) (v : Fin 4 × K) :
    ZMod 5 × K := vertex (lift r c v) - vertex v

private theorem lift_round {K : Type*} [Field K] (r : Kˣ) (c h : K) :
    (lift r c ^ 4) (0, h) = (0, rowReturn r c h) := by
  simp [pow_succ, Perm.mul_apply, lift, rowReturn]
  ring

private theorem lift_rounds {K : Type*} [Field K] (r : Kˣ) (c h : K) (n : ℕ) :
    (lift r c ^ (4 * n)) (0, h) = (0, (rowReturn r c ^ n) h) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, Perm.mul_apply, lift_round, ih]
    rw [pow_succ, Perm.mul_apply]

private theorem base_to_vertex {K : Type*} [Field K] (r : Kˣ) (c : K)
    (v : Fin 4 × K) : (lift r c).SameCycle (0, initialRow v) v := by
  rcases v with ⟨i, h⟩
  fin_cases i
  · exact Perm.SameCycle.refl _ _
  · exact ⟨1, by simp [lift, initialRow]⟩
  · exact ⟨2, by norm_num [lift, initialRow, pow_succ, Perm.mul_apply]⟩
  · exact ⟨3, by norm_num [lift, initialRow, pow_succ, Perm.mul_apply]⟩

private theorem lift_invariant {K : Type*} [Field K] (r : Kˣ) (c : K)
    (v : Fin 4 × K) : initialRow (lift r c v) = c ↔ initialRow v = c := by
  rcases v with ⟨i, h⟩
  fin_cases i <;> simp [lift, initialRow]
  constructor <;> intro he
  · have hz : (r : K) * (h + c) = 0 := by linear_combination -he
    have := (mul_eq_zero.mp hz).resolve_left r.ne_zero
    linear_combination -this
  · rw [show h = -c by linear_combination -he]
    ring

private theorem lift_same_cycle {K : Type*} [Field K] [Finite K]
    (r : Kˣ) (hr : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (c : K)
    (v w : Fin 4 × K) :
    (lift r c).SameCycle v w ↔ (initialRow v = c ↔ initialRow w = c) := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [pow_succ', Perm.mul_apply, lift_invariant] using ih
  · intro h
    have hrw := (row_same_cycle_iff r hr c (initialRow v) (initialRow w)).mpr h
    obtain ⟨n, hn⟩ := hrw.exists_nat_pow_eq
    have hb : (lift r c).SameCycle (0, initialRow v) (0, initialRow w) := by
      refine ⟨((4 * n : ℕ) : ℤ), ?_⟩
      rw [zpow_natCast, lift_rounds, hn]
    exact (base_to_vertex r c v).symm.trans (hb.trans (base_to_vertex r c w))

private theorem vertices_bijective (K : Type*) :
    Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} := by
  constructor
  · rintro ⟨i, h⟩ _
    exact (by decide : ∀ i : Fin 4, column i ≠ 0) i
  constructor
  · rintro ⟨i, h⟩ _ ⟨j, k⟩ _ he
    have hc := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    have hcol : Function.Injective column := by decide
    exact Prod.ext (hcol hc) hh
  · rintro ⟨d, h⟩ hd
    fin_cases d
    · exact (hd rfl).elim
    · exact ⟨(0, h), trivial, rfl⟩
    · exact ⟨(1, h), trivial, rfl⟩
    · exact ⟨(3, h), trivial, rfl⟩
    · exact ⟨(2, h), trivial, rfl⟩

private theorem labels_bijective {K : Type*} [Field K] [CharP K 5] (r : Kˣ)
    (hr : (r : K) + 1 ≠ 0) (c : K) :
    Set.BijOn (edgeLabel r c) Set.univ {v | v.1 ≠ 0} := by
  have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 5 2).not.mpr (by decide)
  have hcol : Function.Injective column := by decide
  have hcform : ∀ (i : Fin 4) (h : K), (edgeLabel r c (i, h)).1 = column i := by
    intro i h
    fin_cases i <;> norm_num [edgeLabel, lift, vertex, column] <;> decide
  constructor
  · rintro ⟨i, h⟩ _
    change (edgeLabel r c (i, h)).1 ≠ 0
    rw [hcform]
    exact (by decide : ∀ i : Fin 4, column i ≠ 0) i
  constructor
  · rintro ⟨i, h⟩ _ ⟨j, k⟩ _ he
    have hc := congrArg Prod.fst he
    have hi : i = j := hcol (by simpa only [hcform] using hc)
    subst j
    have hh := congrArg Prod.snd he
    suffices h = k by simp [this]
    fin_cases i <;> simp [edgeLabel, lift, vertex] at hh
    all_goals first
      | have hz : (2 : K) * (h - k) = 0 := by linear_combination -hh
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left htwo)
      | have hz : ((r : K) + 1) * (h - k) = 0 := by linear_combination -hh
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hr)
  · rintro ⟨d, h⟩ hd
    fin_cases d
    · exact (hd rfl).elim
    · refine ⟨(0, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]
        change column 0 = (1 : ZMod 5)
        decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr]
        <;> ring
    · refine ⟨(1, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]
        change column 1 = (2 : ZMod 5)
        decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr]
        <;> ring
    · refine ⟨(3, ((1 - (r : K)) * c - h) / ((r : K) + 1)), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]
        change column 3 = (3 : ZMod 5)
        decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr]
        <;> ring
    · refine ⟨(2, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]
        change column 2 = (4 : ZMod 5)
        decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr]
        <;> ring

/-- Every finite characteristic-five rowfield admits the actual two-cycle lift with
all outside-column edge labels, including the closing matching, exactly once. -/
theorem exists_characteristic_five_lift (K : Type*) [Field K] [Finite K] [CharP K 5]
    (c : K) : ∃ r : Kˣ,
      (r : K) + 1 ≠ 0 ∧
      (∀ v w : Fin 4 × K, (lift r c).SameCycle v w ↔
        (initialRow v = c ↔ initialRow w = c)) ∧
      Set.BijOn (edgeLabel r c) Set.univ {v | v.1 ≠ 0} ∧
      Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} ∧
      (∀ h : K, (lift r c ^ 4) (0, h) = (0, rowReturn r c h)) := by
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hn : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z := by
    intro z
    exact (Submonoid.mem_powers_iff z r).mp (mem_powers_iff_mem_zpowers.mpr (hr z))
  have hrn : (r : K) + 1 ≠ 0 := by
    intro he
    have he' : (r : K) = -1 := by linear_combination he
    have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 5 2).not.mpr (by decide)
    have hthree : (3 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 5 3).not.mpr (by decide)
    obtain ⟨n, h⟩ := hn (Units.mk0 2 htwo)
    have h' : (-1 : K) ^ n = 2 := by
      simpa [he'] using congrArg (fun z : Kˣ => (z : K)) h
    have hpall : ∀ m : ℕ, (-1 : K) ^ m = 1 ∨ (-1 : K) ^ m = -1 := by
      intro m
      induction m with
      | zero => exact Or.inl (by simp)
      | succ m ih => rcases ih with ih | ih <;> simp [pow_succ, ih]
    rcases hpall n with hp | hp
    · apply one_ne_zero (α := K)
      linear_combination hp - h'
    · apply hthree
      linear_combination hp - h'
  exact ⟨r, hrn, lift_same_cycle r hn c, labels_bijective r hrn c,
    vertices_bijective K, lift_round r c⟩

end D5.S1.Words.Sequenceability.RowOrbitLift
