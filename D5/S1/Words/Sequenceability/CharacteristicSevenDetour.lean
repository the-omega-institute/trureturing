/- GID: D5/S1/Words/Sequenceability/CharacteristicSevenDetour
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/CharacteristicSevenDetour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Six-column affine lift and the characteristic-seven relative path construction.
-/

import D5.S1.Words.Sequenceability.RowOrbitLift
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The characteristic-seven six-column lift.  The generic affine row-orbit
supplier is reused from `RowOrbitLift`; the six phases, their actual cycle
merger, and the path inventory are new content. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.CharacteristicSevenDetour

open Equiv
open D5.S1.Words.Sequenceability.RowOrbitLift

def column : Fin 6 → ZMod 7 := ![1, 3, 2, 6, 4, 5]

def lift {K : Type*} [Field K] (r : Kˣ) (c : K) : Perm (Fin 6 × K) where
  toFun v := if v.1 = 0 then (1, -v.2)
    else if v.1 = 1 then (2, -v.2)
    else if v.1 = 2 then (3, -v.2)
    else if v.1 = 3 then (4, -v.2)
    else if v.1 = 4 then (5, -v.2)
    else (0, -(r : K) * v.2 + (1 - (r : K)) * c)
  invFun v := if v.1 = 0 then
      (5, -(↑r⁻¹ : K) * (v.2 - (1 - (r : K)) * c))
    else if v.1 = 1 then (0, -v.2)
    else if v.1 = 2 then (1, -v.2)
    else if v.1 = 3 then (2, -v.2)
    else if v.1 = 4 then (3, -v.2)
    else (4, -v.2)
  left_inv := by
    rintro ⟨i, h⟩
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨i, h⟩
    fin_cases i <;> simp

def initialRow {K : Type*} [Field K] (v : Fin 6 × K) : K :=
  if v.1 = 0 ∨ v.1 = 2 ∨ v.1 = 4 then v.2 else -v.2

def vertex {K : Type*} (v : Fin 6 × K) : ZMod 7 × K := (column v.1, v.2)

def edgeLabel {K : Type*} [Field K] (r : Kˣ) (c : K) (v : Fin 6 × K) :
    ZMod 7 × K := vertex (lift r c v) - vertex v

def labelColumn : Fin 6 → ZMod 7 := ![2, 6, 4, 5, 1, 3]

private theorem lift_round {K : Type*} [Field K] (r : Kˣ) (c h : K) :
    (lift r c ^ 6) (0, h) = (0, rowReturn r c h) := by
  simp [pow_succ, Perm.mul_apply, lift, rowReturn]
  ring

private theorem lift_rounds {K : Type*} [Field K] (r : Kˣ) (c h : K) (n : ℕ) :
    (lift r c ^ (6 * n)) (0, h) = (0, (rowReturn r c ^ n) h) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, Perm.mul_apply, lift_round, ih]
    rw [pow_succ, Perm.mul_apply]

private theorem base_to_vertex {K : Type*} [Field K] (r : Kˣ) (c : K)
    (v : Fin 6 × K) : (lift r c).SameCycle (0, initialRow v) v := by
  rcases v with ⟨i, h⟩
  fin_cases i
  · exact Perm.SameCycle.refl _ _
  · exact ⟨1, by simp [lift, initialRow]⟩
  · exact ⟨2, by norm_num [lift, initialRow, pow_succ, Perm.mul_apply]⟩
  · exact ⟨3, by norm_num [lift, initialRow, pow_succ, Perm.mul_apply]⟩
  · exact ⟨4, by norm_num [lift, initialRow, pow_succ, Perm.mul_apply]⟩
  · exact ⟨5, by norm_num [lift, initialRow, pow_succ, Perm.mul_apply]⟩

private theorem lift_invariant {K : Type*} [Field K] (r : Kˣ) (c : K)
    (v : Fin 6 × K) : initialRow (lift r c v) = c ↔ initialRow v = c := by
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
    (v w : Fin 6 × K) :
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
      refine ⟨((6 * n : ℕ) : ℤ), ?_⟩
      rw [zpow_natCast, lift_rounds, hn]
    exact (base_to_vertex r c v).symm.trans (hb.trans (base_to_vertex r c w))

private theorem vertices_bijective (K : Type*) :
    Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} := by
  constructor
  · rintro ⟨i, h⟩ _
    exact (by decide : ∀ i : Fin 6, column i ≠ 0) i
  constructor
  · rintro ⟨i, h⟩ _ ⟨j, k⟩ _ he
    have hc := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    have hcol : Function.Injective column := by decide
    exact Prod.ext (hcol hc) hh
  · rintro ⟨d, h⟩ hd
    fin_cases d
    · exact (hd rfl).elim
    · exact ⟨(0, h), trivial, by norm_num [vertex, column] <;> rfl⟩
    · exact ⟨(2, h), trivial, by norm_num [vertex, column] <;> rfl⟩
    · exact ⟨(1, h), trivial, by norm_num [vertex, column] <;> rfl⟩
    · exact ⟨(4, h), trivial, by norm_num [vertex, column] <;> rfl⟩
    · exact ⟨(5, h), trivial, by norm_num [vertex, column] <;> rfl⟩
    · exact ⟨(3, h), trivial, by norm_num [vertex, column] <;> rfl⟩

private theorem labels_bijective {K : Type*} [Field K] [CharP K 7] (r : Kˣ)
    (hr : (r : K) + 1 ≠ 0) (c : K) :
    Set.BijOn (edgeLabel r c) Set.univ {v | v.1 ≠ 0} := by
  have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)
  have hcol : Function.Injective labelColumn := by decide
  have hcform : ∀ (i : Fin 6) (h : K),
      (edgeLabel r c (i, h)).1 = labelColumn i := by
    intro i h
    fin_cases i <;> norm_num [edgeLabel, lift, vertex, column, labelColumn] <;> decide
  constructor
  · rintro ⟨i, h⟩ _
    change (edgeLabel r c (i, h)).1 ≠ 0
    rw [hcform]
    exact (by decide : ∀ i : Fin 6, labelColumn i ≠ 0) i
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
    · refine ⟨(4, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]; change labelColumn 4 = (1 : ZMod 7); decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr] <;> ring
    · refine ⟨(0, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]; change labelColumn 0 = (2 : ZMod 7); decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr] <;> ring
    · refine ⟨(5, ((1 - (r : K)) * c - h) / ((r : K) + 1)), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]; change labelColumn 5 = (3 : ZMod 7); decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr] <;> ring
    · refine ⟨(2, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]; change labelColumn 2 = (4 : ZMod 7); decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr] <;> ring
    · refine ⟨(3, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]; change labelColumn 3 = (5 : ZMod 7); decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr] <;> ring
    · refine ⟨(1, -h / 2), trivial, ?_⟩
      apply Prod.ext
      · rw [hcform]; change labelColumn 1 = (6 : ZMod 7); decide
      · simp [edgeLabel, lift, vertex]
        field_simp [htwo, hr] <;> ring

/-- The six-column lift has the exact two-cycle row criterion and the complete
nonzero-column vertex and edge-label inventories. -/
theorem exists_characteristic_seven_lift (K : Type*) [Field K] [Finite K] [CharP K 7]
    (c : K) : ∃ r : Kˣ,
      (r : K) + 1 ≠ 0 ∧
      (∀ v w : Fin 6 × K, (lift r c).SameCycle v w ↔
        (initialRow v = c ↔ initialRow w = c)) ∧
      Set.BijOn (edgeLabel r c) Set.univ {v | v.1 ≠ 0} ∧
      Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} ∧
      (∀ h : K, (lift r c ^ 6) (0, h) = (0, rowReturn r c h)) := by
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hn : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z := by
    intro z
    exact (Submonoid.mem_powers_iff z r).mp (mem_powers_iff_mem_zpowers.mpr (hr z))
  have hrn : (r : K) + 1 ≠ 0 := by
    intro he
    have he' : (r : K) = -1 := by linear_combination he
    have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)
    have hthree : (3 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 3).not.mpr (by decide)
    obtain ⟨n, h⟩ := hn (Units.mk0 2 htwo)
    have h' : (-1 : K) ^ n = 2 := by
      simpa [he'] using congrArg (fun z : Kˣ => (z : K)) h
    have hpall : ∀ m : ℕ, (-1 : K) ^ m = 1 ∨ (-1 : K) ^ m = -1 := by
      intro m
      induction m with
      | zero => exact Or.inl (by simp)
      | succ m ih => rcases ih with ih | ih <;> simp [pow_succ, ih]
    rcases hpall n with hp | hp
    · apply one_ne_zero (α := K); linear_combination hp - h'
    · apply hthree; linear_combination hp - h'
  exact ⟨r, hrn, lift_same_cycle r hn c, labels_bijective r hrn c,
    vertices_bijective K, lift_round r c⟩

section RelativePathData

variable {K : Type*} [Field K] [CharP K 7]

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def alpha (r : Kˣ) (u : K) : K := ((r : K) + 1) * u / (3 * (r : K))

def beta (r : Kˣ) (u : K) : K := u - alpha r u

def carrier := (Fin 6 × K) ⊕ Fin 2

def source : carrier (K := K) := Sum.inr 0

def target : carrier (K := K) := Sum.inr 1

def headOne (r : Kˣ) (u : K) : carrier (K := K) := Sum.inl (1, alpha r u)

def headTwo (r : Kˣ) (u : K) : carrier (K := K) := Sum.inl (0, beta r u)

def predecessorOne (r : Kˣ) (u : K) : carrier (K := K) := Sum.inl (0, -alpha r u)

def predecessorTwo (r : Kˣ) (u : K) : carrier (K := K) :=
  Sum.inl (5, u - 2 * alpha r u)

def liftWithEndpoints (r : Kˣ) (c : K) : Perm (carrier (K := K)) :=
  Equiv.sumCongr (lift r c) (Equiv.refl (Fin 2))

def vertexWithEndpoints (u : K) : carrier (K := K) → ZMod 7 × K
  | Sum.inl v => vertex v
  | Sum.inr i => if i = 0 then (0, 0) else (0, u)

def splice (r : Kˣ) (u : K) : Perm (carrier (K := K)) :=
  Equiv.swap (headOne r u) source *
    (Equiv.swap (headOne r u) target *
      (Equiv.swap (headOne r u) (headTwo r u) *
        liftWithEndpoints r (-alpha r u)))

private theorem char7_three_ne_zero : (3 : K) ≠ 0 :=
  (CharP.cast_eq_zero_iff K 7 3).not.mpr (by decide)

private theorem alpha_den_ne_zero (r : Kˣ) : (3 * (r : K)) ≠ 0 :=
  mul_ne_zero char7_three_ne_zero r.ne_zero

private theorem alpha_equation (r : Kˣ) (u : K) :
    3 * (r : K) * alpha r u = ((r : K) + 1) * u := by
  unfold alpha
  field_simp [alpha_den_ne_zero r, char7_three_ne_zero]

private theorem alpha_beta_sum (r : Kˣ) (u : K) : alpha r u + beta r u = u := by
  simp [beta]

private theorem lift_predecessor_two (r : Kˣ) (u : K) :
    lift r (-alpha r u) (5, u - 2 * alpha r u) = (0, beta r u) := by
  apply Prod.ext
  · rfl
  · change -(r : K) * (u - 2 * alpha r u) +
        (1 - (r : K)) * (-alpha r u) = u - alpha r u
    have h := alpha_equation r u
    linear_combination h

private theorem lift_second_head (r : Kˣ) (u : K) :
    liftWithEndpoints r (-alpha r u) (predecessorTwo r u) = headTwo r u := by
  change Sum.inl (lift r (-alpha r u) (5, u - 2 * alpha r u)) =
    Sum.inl (0, beta r u)
  rw [lift_predecessor_two]

private theorem splice_key_apply (r : Kˣ) (u : K) (hu : u ≠ 0) :
    splice r u (predecessorOne r u) = headTwo r u ∧
    splice r u (predecessorTwo r u) = target ∧
    splice r u source = headOne r u ∧
    splice r u target = source := by
  have h₁ : headOne r u ≠ source := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have h₂ : headOne r u ≠ target := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have h₃ : headOne r u ≠ headTwo r u := by
    intro h
    have h' := congrArg (fun z => (z : Fin 6 × K).1) (Sum.inl.inj h)
    norm_num [headOne, headTwo] at h'
  have hp₁ : predecessorOne r u ≠ predecessorTwo r u := by
    intro h
    have h' := congrArg (fun z => (z : Fin 6 × K).1) (Sum.inl.inj h)
    norm_num [predecessorOne, predecessorTwo] at h'
  have hp₁h₁ : predecessorOne r u ≠ headOne r u := by
    intro h
    have h' := congrArg (fun z => (z : Fin 6 × K).1) (Sum.inl.inj h)
    norm_num [predecessorOne, headOne] at h'
  have hp₁h₂ : predecessorOne r u ≠ headTwo r u := by
    intro h
    change (Sum.inl (0, -alpha r u) : carrier (K := K)) =
      Sum.inl (0, beta r u) at h
    have h' := congrArg Prod.snd (Sum.inl.inj h)
    simp [beta] at h'
    have hz : u = 0 := by
      calc
        u = (u - alpha r u) - (-alpha r u) := by ring
        _ = 0 := by rw [← h']; ring
    exact hu hz
  have hp₂h₁ : predecessorTwo r u ≠ headOne r u := by
    intro h
    have h' := congrArg (fun z => (z : Fin 6 × K).1) (Sum.inl.inj h)
    norm_num [predecessorTwo, headOne] at h'
  have hp₂h₂ : predecessorTwo r u ≠ headTwo r u := by
    intro h
    have h' := congrArg (fun z => (z : Fin 6 × K).1) (Sum.inl.inj h)
    norm_num [predecessorTwo, headTwo] at h'
  have hs : source ≠ headTwo r u := by
    change Sum.inr _ ≠ Sum.inl _
    exact Sum.inr_ne_inl
  have ht : target ≠ headTwo r u := by
    change Sum.inr _ ≠ Sum.inl _
    exact Sum.inr_ne_inl
  have hs' : source (K := K) ≠ target (K := K) := by
    change (Sum.inr (0 : Fin 2) : carrier (K := K)) ≠ Sum.inr 1
    intro h
    have h' := congrArg (fun z : carrier (K := K) =>
      match z with | Sum.inl _ => (0 : Fin 2) | Sum.inr i => i) h
    norm_num at h'
  have hpre₁ : liftWithEndpoints r (-alpha r u) (predecessorOne r u) = headOne r u := by
    change Sum.inl (lift r (-alpha r u) (0, -alpha r u)) =
      Sum.inl (1, alpha r u)
    simp [lift]
  have hpre₂ : liftWithEndpoints r (-alpha r u) (predecessorTwo r u) = headTwo r u :=
    lift_second_head r u
  have hfixs : liftWithEndpoints r (-alpha r u) (source (K := K)) = source := by rfl
  have hfixt : liftWithEndpoints r (-alpha r u) (target (K := K)) = target := by rfl
  refine ⟨?_, ?_⟩
  · simp only [splice, Equiv.Perm.mul_apply]
    rw [hpre₁, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne h₃.symm ht.symm]
    rw [Equiv.swap_apply_of_ne_of_ne h₃.symm hs.symm]
  · refine ⟨?_, ?_⟩
    · simp only [splice, Equiv.Perm.mul_apply]
      rw [hpre₂, Equiv.swap_apply_right, Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne h₂.symm hs'.symm]
    · refine ⟨?_, ?_⟩
      · simp only [splice, Equiv.Perm.mul_apply]
        rw [hfixs]
        rw [Equiv.swap_apply_of_ne_of_ne h₁.symm hs]
        rw [Equiv.swap_apply_of_ne_of_ne h₁.symm hs']
        rw [Equiv.swap_apply_right]
      · simp only [splice, Equiv.Perm.mul_apply]
        rw [hfixt]
        rw [Equiv.swap_apply_of_ne_of_ne h₂.symm ht]
        rw [Equiv.swap_apply_right, Equiv.swap_apply_left]

/-- The affine equations behind the two-head splice.  The theorem records the
actual four seams and their vector labels before the closing endpoint edge is
deleted. -/
theorem six_column_splice_seams (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hr : (r : K) + 1 ≠ 0) :
    (splice r u (predecessorOne r u) = headTwo r u) ∧
    (splice r u (predecessorTwo r u) = target) ∧
    (splice r u source = headOne r u) ∧
    (splice r u target = source) ∧
    (vertexWithEndpoints u (headTwo r u) -
        vertexWithEndpoints u (predecessorOne r u) = (0, u)) ∧
    (vertexWithEndpoints u target -
        vertexWithEndpoints u (predecessorTwo r u) = (2, 2 * alpha r u)) ∧
    (vertexWithEndpoints u (headOne r u) -
        vertexWithEndpoints u source = (3, alpha r u)) ∧
    (vertexWithEndpoints u source -
        vertexWithEndpoints u target = (0, -u)) := by
  have hkey := splice_key_apply r u hu
  refine ⟨hkey.1, hkey.2.1, hkey.2.2.1, hkey.2.2.2, ?_, ?_, ?_, ?_⟩
  · simp [vertexWithEndpoints, predecessorOne, headTwo, vertex, column, beta,
      alpha_beta_sum]
  · have hneg : (-5 : ZMod 7) = 2 := by decide
    simp [vertexWithEndpoints, predecessorTwo, target, vertex, column, hneg]
  · simp [vertexWithEndpoints, headOne, source, vertex, column]
  · simp [vertexWithEndpoints, source, target]

end

end RelativePathData

end D5.S1.Words.Sequenceability.CharacteristicSevenDetour
