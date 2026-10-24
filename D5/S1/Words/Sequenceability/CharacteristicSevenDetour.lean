/- GID: D5/S1/Words/Sequenceability/CharacteristicSevenDetour
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/CharacteristicSevenDetour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Six-column affine lift and the characteristic-seven relative path construction.
-/

import D5.S1.Words.Sequenceability.RowOrbitLift
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import D5.S3.Combinatorics.PerfectMatchings.FiniteReturnTowers
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
open D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
open D5.S3.Combinatorics.PerfectMatchings.FiniteReturnTowers

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

section FullPath

variable {K : Type*} [Field K] [Finite K] [CharP K 7]

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def markedPoint (r : Kˣ) (u : K) : Fin 4 → carrier (K := K) :=
  ![headOne r u, headTwo r u, target, source]

def markedSet (r : Kˣ) (u : K) : Set (carrier (K := K)) :=
  Set.range (markedPoint r u)

private theorem markedPoint_injective (r : Kˣ) (u : K) :
    Function.Injective (markedPoint r u) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | (have hc := congrArg (fun z : carrier (K := K) =>
          match z with
          | Sum.inl (a, _) => a.val
          | Sum.inr i => i.val + 6) h
       norm_num [markedPoint, headOne, headTwo, source, target] at hc
       try omega)

def markedEquiv (r : Kˣ) (u : K) : Fin 4 ≃ {x // x ∈ markedSet r u} := by
  classical
  apply Equiv.ofBijective (fun i =>
    ⟨markedPoint r u i, ⟨i, rfl⟩⟩)
  constructor
  · intro i j h
    exact markedPoint_injective r u (Subtype.ext_iff.mp h)
  · intro x
    rcases x.2 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    exact Subtype.ext hi

def markedCycle : Perm (Fin 4) :=
  swap 0 1 * swap 1 2 * swap 2 3

private theorem markedCycle_apply :
    markedCycle 0 = 1 ∧ markedCycle 1 = 2 ∧ markedCycle 2 = 3 ∧
      markedCycle 3 = 0 := by
  norm_num [markedCycle, Perm.mul_apply, swap_apply_def]

private theorem markedCycle_sameCycle (i j : Fin 4) :
    markedCycle.SameCycle i j := by
  have h01 : markedCycle.SameCycle 0 1 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.1
  have h12 : markedCycle.SameCycle 1 2 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.2.1
  have h23 : markedCycle.SameCycle 2 3 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.2.2.1
  have h30 : markedCycle.SameCycle 3 0 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.2.2.2
  fin_cases i <;> fin_cases j
  all_goals first
    | exact Perm.SameCycle.refl _ _
    | exact h01
    | exact h12
    | exact h23
    | exact h30
    | exact h01.symm
    | exact h12.symm
    | exact h23.symm
    | exact h30.symm
    | exact h01.trans h12
    | exact h01.trans (h12.trans h23)
    | exact h01.trans (h12.trans (h23.trans h30))
    | exact h12.trans h23
    | exact h12.trans (h23.trans h30)
    | exact h23.trans h30
    | exact h30.trans h01

private theorem q_same_cycle_head (r : Kˣ)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (u : K)
    (v : Fin 6 × K) :
    (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (Sum.inl v : carrier (K := K))
      (headOne r u) ↔ initialRow v = -alpha r u := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (carrier (K := K)) := by
    change Fintype ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p := liftWithEndpoints r (-alpha r u)
  change p⁻¹.SameCycle (Sum.inl v : carrier (K := K)) (headOne r u) ↔ _
  constructor
  · intro h
    have h' : p.SameCycle (Sum.inl v : carrier (K := K)) (headOne r u) :=
      (Equiv.Perm.sameCycle_inv).mp h
    obtain ⟨n, hn⟩ := h'.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    rw [hp n] at hn
    change Sum.inl ((lift r (-alpha r u) ^ n) v) =
      Sum.inl (1, alpha r u) at hn
    have hn' := Sum.inl.inj hn
    have hcycle : (lift r (-alpha r u)).SameCycle v (1, alpha r u) :=
      ⟨(n : ℤ), hn'⟩
    have hiff := (lift_same_cycle r hrgen (-alpha r u) v (1, alpha r u)).mp hcycle
    exact hiff.mpr (by simp [initialRow])
  · intro h
    have hhead : initialRow (1, alpha r u) = -alpha r u := by
      simp [initialRow]
    have hbase := (lift_same_cycle r hrgen (-alpha r u) v (1, alpha r u)).mpr
      ⟨(fun _ => hhead), (fun _ => h)⟩
    obtain ⟨n, hn⟩ := hbase.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    refine (Equiv.Perm.sameCycle_inv).mpr ?_
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, hp n, hn]
    rfl

def markedRepair (r : Kˣ) (u : K) :
    Perm {x // x ∈ markedSet r u} :=
  (markedEquiv r u).permCongr markedCycle⁻¹

private theorem marked_repair_extension (r : Kˣ) (u : K) :
    (markedRepair r u).ofSubtype =
      Equiv.swap (headOne r u) (headTwo r u) *
        (Equiv.swap (headOne r u) target *
          Equiv.swap (headOne r u) source) := by
  classical
  ext x
  have hAB : headOne r u ≠ headTwo r u := by
    intro h
    have h' := congrArg (fun z : carrier (K := K) =>
      match z with | Sum.inl (a, _) => a | Sum.inr _ => 0) h
    norm_num [headOne, headTwo] at h'
  have hAS : headOne r u ≠ source := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hAT : headOne r u ≠ target := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hBS : headTwo r u ≠ source := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hBT : headTwo r u ≠ target := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hST : source (K := K) ≠ target (K := K) := by
    change (Sum.inr (0 : Fin 2) : carrier (K := K)) ≠ Sum.inr 1
    intro h
    have h' := congrArg (fun z : carrier (K := K) =>
      match z with | Sum.inl _ => (0 : Fin 2) | Sum.inr i => i) h
    norm_num at h'
  by_cases hx : x ∈ markedSet r u
  · obtain ⟨i, rfl⟩ := hx
    have hi : markedPoint r u i ∈ markedSet r u := ⟨i, rfl⟩
    rw [Equiv.Perm.ofSubtype_apply_of_mem (markedRepair r u) hi]
    have heq : (markedEquiv r u).symm
        ⟨markedPoint r u i, hi⟩ = i := by
      calc
        (markedEquiv r u).symm ⟨markedPoint r u i, hi⟩ =
            (markedEquiv r u).symm ((markedEquiv r u) i) := by
              congr 1
        _ = i := (markedEquiv r u).symm_apply_apply i
    simp only [markedRepair, Equiv.permCongr_apply]
    rw [heq]
    fin_cases i
    · change source =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) (headOne r u)))
      rw [Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne hAS.symm hST]
      rw [Equiv.swap_apply_of_ne_of_ne hAS.symm hBS.symm]
    · change headOne r u =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) (headTwo r u)))
      rw [Equiv.swap_apply_of_ne_of_ne hAB.symm hBS]
      rw [Equiv.swap_apply_of_ne_of_ne hAB.symm hBT]
      rw [Equiv.swap_apply_right]
    · change headTwo r u =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) target))
      rw [Equiv.swap_apply_of_ne_of_ne hAT.symm hST.symm]
      rw [Equiv.swap_apply_right]
      rw [Equiv.swap_apply_left]
    · change target =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) source))
      rw [Equiv.swap_apply_right]
      rw [Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne hAT.symm hBT.symm]
  · have h₁ : x ≠ headOne r u := by
      intro h
      apply hx
      exact ⟨0, h.symm⟩
    have h₂ : x ≠ headTwo r u := by
      intro h
      apply hx
      exact ⟨1, h.symm⟩
    have hs : x ≠ source := by
      intro h
      apply hx
      exact ⟨3, h.symm⟩
    have ht : x ≠ target := by
      intro h
      apply hx
      exact ⟨2, h.symm⟩
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun z => z ∈ markedSet r u)
      (markedRepair r u) hx]
    simp only [Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h₁ hs,
      Equiv.swap_apply_of_ne_of_ne h₁ ht,
      Equiv.swap_apply_of_ne_of_ne h₁ h₂]

private theorem splice_inverse_reattach (r : Kˣ) (u : K) :
    (splice r u)⁻¹ =
      (liftWithEndpoints r (-alpha r u))⁻¹ * (markedRepair r u).ofSubtype := by
  rw [marked_repair_extension]
  simp only [splice, mul_inv_rev, Equiv.swap_inv]
  group

private theorem reattached_all_same_cycle {X : Type*} [Finite X]
    (p : Perm X) (S : Set X) [DecidablePred (· ∈ S)] (J : Perm S)
    (hmeet : ∀ x : X, ∃ z : S, p.SameCycle x z)
    (hreturn : ∀ z : S, ∃ n : ℕ,
      FirstVisit p S z n ∧ (p ^ n) z = z)
    (hJcycle : ∀ x y : S, J.SameCycle x y) :
    ∀ x y : X, (p * J.ofSubtype).SameCycle x y := by
  classical
  let f : Perm X := p * J.ofSubtype
  have hjump : ∀ z : S, ∃ n : ℕ,
      FirstVisit p S (J z) n ∧ (p ^ n) (J z) = J z := by
    intro z
    obtain ⟨n, hn, hend⟩ := hreturn (J z)
    exact ⟨n, hn, hend⟩
  have hmarked : ∀ x y : S, f.SameCycle x y := by
    intro x y
    rw [show f = p * J.ofSubtype from rfl]
    rw [same_cycle_of_first_visit (p * J.ofSubtype) S J]
    · exact hJcycle x y
    · intro z
      obtain ⟨n, hn, hend⟩ := hreturn (J z)
      obtain ⟨hfirst, hjump⟩ := first_visit_reattach p S J z n hn
      exact ⟨n, hfirst, hjump.trans hend⟩
  have hto : ∀ x : X, ∃ z : S, f.SameCycle x z := by
    intro x
    obtain ⟨z, hz⟩ := hmeet x
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    let H : ℕ → Prop := fun k => (p ^ k) x ∈ S
    have hHex : ∃ k, H k := by
      refine ⟨n, ?_⟩
      change (p ^ n) x ∈ S
      rw [hn]
      exact z.property
    let m := Nat.find hHex
    have hm : H m := Nat.find_spec hHex
    have hmS : (p ^ m) x ∈ S := hm
    by_cases hm0 : m = 0
    · subst m
      have hxS : x ∈ S := by
        have hmzero : (p ^ 0) x ∈ S := by simpa [hm0] using hmS
        simpa using hmzero
      refine ⟨⟨x, hxS⟩, ?_⟩
      exact Perm.SameCycle.refl f x
    · have hx0 : x ∉ S := by
        intro hx
        have hle : m ≤ 0 := Nat.find_min' hHex (by simpa [H, hx])
        omega
      have hmin : ∀ k, k < m → (p ^ k) x ∉ S := by
        intro k hkm hk
        have hle : m ≤ k := Nat.find_min' hHex (by simpa [H] using hk)
        omega
      have hseg : ∀ k, k ≤ m →
          (f ^ k) x = (p ^ k) x := by
        intro k hk
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ', Perm.mul_apply, ih (by omega)]
          have hnot : (p ^ k) x ∉ S := by
            by_cases hk0 : k = 0
            · simpa [hk0] using hx0
            · exact hmin k (by omega)
          simp only [f, Perm.mul_apply]
          rw [Perm.ofSubtype_apply_of_not_mem J hnot]
          rw [pow_succ']
          simp only [Perm.mul_apply]
      refine ⟨⟨(p ^ m) x, hm⟩, ?_⟩
      refine ⟨(m : ℤ), ?_⟩
      simpa only [f, zpow_natCast, hseg m le_rfl]
  intro x y
  obtain ⟨zx, hx⟩ := hto x
  obtain ⟨zy, hy⟩ := hto y
  exact hx.trans ((hmarked zx zy).trans hy.symm)

private theorem q_same_cycle_head_two (r : Kˣ)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (u : K) (hu : u ≠ 0)
    (v : Fin 6 × K) :
    (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (Sum.inl v : carrier (K := K))
      (headTwo r u) ↔ initialRow v ≠ -alpha r u := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (carrier (K := K)) := by
    change Fintype ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p := liftWithEndpoints r (-alpha r u)
  change p⁻¹.SameCycle (Sum.inl v : carrier (K := K)) (headTwo r u) ↔ _
  constructor
  · intro h
    have h' : p.SameCycle (Sum.inl v : carrier (K := K)) (headTwo r u) :=
      (Equiv.Perm.sameCycle_inv).mp h
    obtain ⟨n, hn⟩ := h'.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    rw [hp n] at hn
    have hcycle : (lift r (-alpha r u)).SameCycle v (0, beta r u) :=
      ⟨(n : ℤ), Sum.inl.inj hn⟩
    have hiff := (lift_same_cycle r hrgen (-alpha r u) v (0, beta r u)).mp hcycle
    have hb : initialRow (0, beta r u) ≠ -alpha r u := by
      simpa [initialRow] using (show beta r u ≠ -alpha r u from by
        intro he
        have hu0 : u = 0 := by
          dsimp [beta] at he
          linear_combination he
        exact hu hu0)
    exact fun hv => hb (hiff.mp hv)
  · intro h
    have hhead : ¬ initialRow (0, beta r u) = -alpha r u := by
      simpa [initialRow] using (show beta r u ≠ -alpha r u from by
        intro he
        have hu0 : u = 0 := by
          dsimp [beta] at he
          linear_combination he
        exact hu hu0)
    have hbase := (lift_same_cycle r hrgen (-alpha r u) v (0, beta r u)).mpr
      ⟨(fun hv => (h hv).elim), (fun hw => (hhead hw).elim)⟩
    obtain ⟨n, hn⟩ := hbase.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    refine (Equiv.Perm.sameCycle_inv).mpr ?_
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, hp n, hn]
    rfl

private theorem marked_cycle_injective (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (i j : Fin 4)
    (h : (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (markedPoint r u i) (markedPoint r u j)) : i = j := by
  letI : Finite (carrier (K := K)) := by
    change Finite ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p : Perm (carrier (K := K)) := (liftWithEndpoints r (-alpha r u))⁻¹
  have h12 : ¬ (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (headOne r u) (headTwo r u) := by
    intro hh
    have hb := (q_same_cycle_head_two r hrgen u hu (1, alpha r u)).mp hh
    exact hb (by simp [initialRow])
  have h21 : ¬ (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (headTwo r u) (headOne r u) := by
    intro hh
    exact h12 (Equiv.Perm.SameCycle.symm hh)
  have hsource : ∀ y : carrier (K := K),
      (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle source y → y = source := by
    intro y hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    have hs : (p ^ n) source = source := by
      exact Function.IsFixedPt.perm_pow (show Function.IsFixedPt p source by
        rfl) n
    have hs' : ((liftWithEndpoints r (-alpha r u))⁻¹ ^ n) source = source := by
      simpa [p] using hs
    rw [hs'] at hn
    exact hn.symm
  have htarget : ∀ y : carrier (K := K),
      (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle target y → y = target := by
    intro y hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    have hs : (p ^ n) target = target := by
      exact Function.IsFixedPt.perm_pow (show Function.IsFixedPt p target by
        rfl) n
    have hs' : ((liftWithEndpoints r (-alpha r u))⁻¹ ^ n) target = target := by
      simpa [p] using hs
    rw [hs'] at hn
    exact hn.symm
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h12 (by simpa [markedPoint] using h)).elim
  · exact (htarget _ (by simpa [markedPoint] using h)).elim
  · exact (hsource _ (by simpa [markedPoint] using h)).elim
  · exact (h21 (by simpa [markedPoint] using h)).elim
  · rfl
  · exact (htarget _ (by simpa [markedPoint] using h)).elim
  · exact (hsource _ (by simpa [markedPoint] using h)).elim
  · exact (htarget _ (by simpa [markedPoint] using h)).elim
  · exact (htarget _ (by simpa [markedPoint] using h)).elim
  · rfl
  · exact (htarget _ (by simpa [markedPoint] using h)).elim
  · exact (hsource _ (by simpa [markedPoint] using h)).elim
  · exact (hsource _ (by simpa [markedPoint] using h)).elim
  · exact (hsource _ (by simpa [markedPoint] using h)).elim
  · rfl

private theorem marked_return_data (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) :
    ∀ z : {x // x ∈ markedSet r u}, ∃ n : ℕ,
      FirstVisit (liftWithEndpoints r (-alpha r u))⁻¹
        (markedSet r u) (z : carrier (K := K)) n ∧
      (((liftWithEndpoints r (-alpha r u))⁻¹ ^ n) (z : carrier (K := K))) = z := by
  intro z
  letI : Finite (carrier (K := K)) := by
    change Finite ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p : Perm (carrier (K := K)) := (liftWithEndpoints r (-alpha r u))⁻¹
  let n := orbitPeriod p (z : carrier (K := K))
  have hn : 0 < n ∧ (p ^ n) (z : carrier (K := K)) = z :=
    (orbit_period_spec p (z : carrier (K := K))).1
  refine ⟨n, ?_, hn.2⟩
  refine ⟨hn.1, ?_, ?_⟩
  · rw [hn.2]
    exact z.property
  · intro k hk hkn hmem
    obtain ⟨j, hj⟩ := hmem
    obtain ⟨i, hi⟩ := z.property
    have hpow : (p ^ k) (markedPoint r u i) = markedPoint r u j := by
      calc
        (p ^ k) (markedPoint r u i) = (p ^ k) (z : carrier (K := K)) :=
          congrArg (p ^ k) hi
        _ = markedPoint r u j := by simpa [p] using hj.symm
    have hij := marked_cycle_injective r u hu hrgen i j
      (show p.SameCycle (markedPoint r u i) (markedPoint r u j) from
        ⟨(k : ℤ), by simpa [zpow_natCast] using hpow⟩)
    have hret : (p ^ k) (z : carrier (K := K)) = z := by
      calc
        (p ^ k) (z : carrier (K := K)) = (p ^ k) (markedPoint r u i) :=
          congrArg (p ^ k) hi.symm
        _ = markedPoint r u j := hpow
        _ = markedPoint r u i := by rw [hij]
        _ = z := hi
    have hle := (orbit_period_spec p (z : carrier (K := K))).2 ⟨hk, hret⟩
    exact (Nat.not_lt_of_ge hle) hkn

private theorem splice_is_cycle (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) :
    ∀ x y : carrier (K := K), (splice r u).SameCycle x y := by
  letI : Finite (carrier (K := K)) := by
    change Finite ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p : Perm (carrier (K := K)) := liftWithEndpoints r (-alpha r u)
  let S : Set (carrier (K := K)) := markedSet r u
  let J : Perm S := markedRepair r u
  have hmeet : ∀ x : carrier (K := K), ∃ z : S, p⁻¹.SameCycle x z := by
    intro x
    rcases x with v | i
    · by_cases hv : initialRow v = -alpha r u
      · exact ⟨⟨headOne r u, ⟨0, rfl⟩⟩,
          (q_same_cycle_head r hrgen u v).2 hv⟩
      · exact ⟨⟨headTwo r u, ⟨1, rfl⟩⟩,
          (q_same_cycle_head_two r hrgen u hu v).2 hv⟩
    · fin_cases i
      · exact ⟨⟨source, ⟨3, rfl⟩⟩, Perm.SameCycle.refl _ _⟩
      · exact ⟨⟨target, ⟨2, rfl⟩⟩, Perm.SameCycle.refl _ _⟩
  have hreturn : ∀ z : S, ∃ n : ℕ,
      FirstVisit p⁻¹ S (z : carrier (K := K)) n ∧
        ((p⁻¹ ^ n) (z : carrier (K := K))) = z := by
    intro z
    simpa only [p, S] using marked_return_data r u hu hrgen z
  have hJcycle : ∀ x y : S, J.SameCycle x y := by
    intro x y
    obtain ⟨i, hi⟩ := x.property
    obtain ⟨j, hj⟩ := y.property
    have hxi : x = markedEquiv r u i := by
      apply Subtype.ext
      exact hi.symm
    have hyj : y = markedEquiv r u j := by
      apply Subtype.ext
      exact hj.symm
    rw [hxi, hyj]
    have hsc : (markedCycle⁻¹).SameCycle i j :=
      (Equiv.Perm.sameCycle_inv).mpr (markedCycle_sameCycle i j)
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        ((markedEquiv r u).permCongr (markedCycle⁻¹) ^ n)
          ((markedEquiv r u) i) = (markedEquiv r u) ((markedCycle⁻¹ ^ n) i) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        simp [pow_succ', Perm.mul_apply, Equiv.permCongr_apply, ih]
    refine ⟨(n : ℤ), ?_⟩
    change ((markedEquiv r u).permCongr (markedCycle⁻¹) ^ n)
      ((markedEquiv r u) i) = (markedEquiv r u) j
    rw [hp n, hn]
  have hfull : ∀ x y : carrier (K := K),
      (p⁻¹ * J.ofSubtype).SameCycle x y := by
    exact reattached_all_same_cycle p⁻¹ S J hmeet hreturn hJcycle
  intro x y
  have hinv : (splice r u)⁻¹ = p⁻¹ * J.ofSubtype := by
    simpa [p, J] using splice_inverse_reattach r u
  have hxy : (splice r u)⁻¹.SameCycle x y := by
    rw [hinv]
    exact hfull x y
  exact (Equiv.Perm.sameCycle_inv).mp hxy

end

end FullPath

end D5.S1.Words.Sequenceability.CharacteristicSevenDetour
