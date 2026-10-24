/- GID: D5/S1/Words/Sequenceability/UniformRelativePath
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/UniformRelativePath
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A whole-carrier cycle with exact coordinate and label inventories yields the actual relative path, all prefixes, intervals, and total. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic
import D5.S1.Words.Sequenceability.RotationalColumnTriple
import D5.S3.Combinatorics.PerfectMatchings.CharacteristicFiveDetour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.UniformRelativePath

open Equiv
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! The affine lift used by the universal `p ≥ 7` branch.  The phase is the
cyclic nonzero-column index and the row changes sign at every edge; the final
edge also multiplies by a primitive row unit.  This keeps every ordinary row
label affine with slope `-2`, while the closing slope is `-(r+1)`. -/

def roundStep {n : ℕ} [NeZero n] {K : Type*} [Field K] (r : Kˣ) :
    Perm (ZMod n × K) where
  toFun v := if v.1 + 1 = 0 then (v.1 + 1, -(r : K) * v.2) else (v.1 + 1, -v.2)
  invFun v := if v.1 = 0 then (v.1 - 1, -(↑r⁻¹ : K) * v.2) else (v.1 - 1, -v.2)
  left_inv := by
    rintro ⟨i, x⟩
    by_cases hi : i + 1 = 0 <;> simp [hi, roundStep, r.ne_zero]
  right_inv := by
    rintro ⟨i, x⟩
    by_cases hi : i = 0 <;> simp [hi, roundStep, r.ne_zero]

def chartCoord {n p : ℕ} {K : Type*} (d : ZMod n → ZMod p)
    (b : ZMod n → K) : ZMod n × K → ZMod p × K
  | (j, x) => (d j, x + b j)

def affineLabel {n p : ℕ} {K : Type*} [Field K] (r : Kˣ)
    (d : ZMod n → ZMod p) (b : ZMod n → K) (v : ZMod n × K) : ZMod p × K :=
  chartCoord d b (roundStep r v) - chartCoord d b v

private theorem round_phase {n : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (x : K) (i : ZMod n) :
    (roundStep r ^ i.val) (0, x) = (i, (-1 : K) ^ i.val * x) := by
  have hphase : ∀ m : ℕ, m < n →
      (roundStep r ^ m) (0, x) = ((m : ZMod n), (-1 : K) ^ m * x) := by
    intro m
    induction m with
    | zero => intro; simp [roundStep]
    | succ m ih =>
        intro hm
        rw [pow_succ', Perm.mul_apply, ih (by omega)]
        simp [roundStep, show ¬ ((m : ZMod n) + 1 = 0) by
          intro h
          have hz := (ZMod.val_eq_zero _).mp h
          rw [ZMod.val_add_of_lt (by simpa using (show m + 1 < n from hm))] at hz
          omega]
        ring
  simpa only [ZMod.natCast_zmod_val] using hphase i.val i.isLt

private theorem round_one {n : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (heven : Even n) (x : K) :
    (roundStep r ^ n) (0, x) = (0, (r : K) * x) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm : n - 1 < n := by omega
  have hw : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    rw [← Nat.cast_add]
    simp [show n - 1 + 1 = n by omega]
  rw [show n = (n - 1) + 1 by omega, pow_succ', Perm.mul_apply,
    round_phase r x ⟨n - 1, hm⟩]
  simp only [roundStep, hw]
  have hsign : (-1 : K) ^ n = 1 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk, pow_add]
    simp
  have hsign' : (-1 : K) ^ (n - 1) * (-1 : K) = 1 := by
    rw [← pow_succ, show n - 1 + 1 = n by omega, hsign]
  rw [hsign']
  ring

private theorem round_rounds {n : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (heven : Even n) (x : K) (m : ℕ) :
    (roundStep r ^ (n * m)) (0, x) = (0, (r : K) ^ m * x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, pow_add, Perm.mul_apply, round_one r heven,
        ih, pow_succ]
      ring

private theorem round_same_cycle {n : ℕ} [NeZero n] {K : Type*} [Field K] [Finite K]
    (r : Kˣ) (hr : ∀ z : Kˣ, ∃ m : ℕ, r ^ m = z) (heven : Even n)
    (v w : ZMod n × K) :
    (roundStep r).SameCycle v w ↔ (v.2 = 0 ↔ w.2 = 0) := by
  have hinv (z : ZMod n × K) : (roundStep r z).2 = 0 ↔ z.2 = 0 := by
    dsimp [roundStep]
    split_ifs <;> simp [r.ne_zero]
  constructor
  · intro h
    obtain ⟨m, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction m with
    | zero => rfl
    | succ m ih =>
        simpa only [pow_succ', Perm.mul_apply, hinv] using ih
  · intro h
    let v₀ : K := (-1 : K) ^ v.1.val * v.2
    let w₀ : K := (-1 : K) ^ w.1.val * w.2
    have hrow : ∃ m : ℕ, (r : K) ^ m * v₀ = w₀ := by
      by_cases hv : v.2 = 0
      · have hw : w.2 = 0 := h.mp hv
        exact ⟨0, by simp [v₀, w₀, hv, hw]⟩
      · have hw : w.2 ≠ 0 := fun hw => hv (h.mpr hw)
        let z : Kˣ := Units.mk0 (w₀ / v₀)
          (div_ne_zero (by simp [w₀, hw]) (by simp [v₀, hv]))
        obtain ⟨m, hm⟩ := hr z
        refine ⟨m, ?_⟩
        have hm' : (r : K) ^ m = w₀ / v₀ := by
          simpa [z] using congrArg (fun q : Kˣ => (q : K)) hm
        rw [hm']
        field_simp [v₀, w₀, hv]
        ring
    obtain ⟨m, hm⟩ := hrow
    have hpow : (roundStep r ^ (n * m)) (0, v₀) =
        (0, (r : K) ^ m * v₀) := round_rounds r heven v₀ m
    have hto0 : (roundStep r).SameCycle (0, v₀) (0, w₀) :=
      ⟨(n * m : ℕ), by rw [zpow_natCast, hpow, hm]⟩
    have hv : (roundStep r).SameCycle (0, v₀) v := by
      refine ⟨(v.1.val : ℕ), ?_⟩
      rw [zpow_natCast, round_phase]
      apply Prod.ext rfl
      simp [v₀]
    have hw : (roundStep r).SameCycle (0, w₀) w := by
      refine ⟨(w.1.val : ℕ), ?_⟩
      rw [zpow_natCast, round_phase]
      apply Prod.ext rfl
      simp [w₀]
    exact hv.symm.trans (hto0.trans hw)

private theorem primitive_not_neg_one {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    {K : Type*} [Field K] [Finite K] [CharP K p] (r : Kˣ)
    (hr : ∀ z : Kˣ, ∃ m : ℕ, r ^ m = z) : (r : K) + 1 ≠ 0 := by
  intro hneg
  have htwo : (2 : K) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff K p 2).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) hd
  have hthree : (3 : K) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff K p 3).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)) hd
  have hrneg : (r : K) = -1 := by linear_combination hneg
  obtain ⟨m, hm⟩ := hr (Units.mk0 2 htwo)
  have hm' : (-1 : K) ^ m = 2 := by
    simpa [hrneg] using congrArg (fun z : Kˣ => (z : K)) hm
  have hpm : ∀ k : ℕ, (-1 : K) ^ k = 1 ∨ (-1 : K) ^ k = -1 := by
    intro k
    induction k with
    | zero => exact Or.inl (by simp)
    | succ k ih => rcases ih with ih | ih <;> simp [pow_succ, ih]
  rcases hpm m with h | h
  · exact htwo (by linear_combination h - hm')
  · exact hthree (by linear_combination h - hm')

theorem p_ge_seven_column_setup (K : Type*) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) [CharP K p] :
    ∃ (d : ZMod (p - 1) → ZMod p) (r : Kˣ),
      Set.BijOn d Set.univ {x | x ≠ 0} ∧
      Set.BijOn (fun i => d (i + 1) - d i) Set.univ {x | x ≠ 0} ∧
      d 1 = d 0 + d 2 ∧
      (∀ z : Kˣ, ∃ m : ℕ, r ^ m = z) ∧
      Even (p - 1) ∧ (r : K) + 1 ≠ 0 := by
  obtain ⟨d, hd, he, ht⟩ :=
    D5.S1.Words.Sequenceability.RotationalColumnTriple
      .exists_rotational_column_triple p hp h7
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgen : ∀ z : Kˣ, ∃ m : ℕ, r ^ m = z := by
    intro z
    exact (Submonoid.mem_powers_iff z r).mp
      (mem_powers_iff_mem_zpowers.mpr (hr z))
  have heven : Even (p - 1) := by
    have hodd := hp.eq_two_or_odd.resolve_left (by omega)
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  exact ⟨d, r, hd, he, ht, hgen, heven,
    primitive_not_neg_one hp h7 r hgen⟩

def pgeOffset {p : ℕ} {K : Type*} [Field K] (u : K) : ZMod (p - 1) → K :=
  fun j => if j = 2 then 2 * u else 0

abbrev pgeCarrier (p : ℕ) (K : Type*) := (ZMod (p - 1) × K) ⊕ Fin 2

def pgeCoordinate {p : ℕ} {K : Type*} [Field K]
    (d : ZMod (p - 1) → ZMod p) (u : K) : pgeCarrier p K → ZMod p × K
  | .inl (j, x) => (d j, x + pgeOffset u j)
  | .inr i => if i = 0 then (0, 0) else (0, u)

def pgeBasePerm {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    (r : Kˣ) : Perm (pgeCarrier p K) := (roundStep r).sumCongr 1

def pgeSurgery {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    (r : Kˣ) (u : K) : Perm (pgeCarrier p K) :=
  let h₁ : pgeCarrier p K := .inl (2, 0)
  let h₂ : pgeCarrier p K := .inl (1, u)
  let s : pgeCarrier p K := .inr 0
  let t : pgeCarrier p K := .inr 1
  swap h₁ s * swap h₁ t * swap h₁ h₂ * pgeBasePerm r

/-! The four arrows changed by `pgeSurgery` are recorded at the actual
carrier level.  The first-coordinate cancellation is exactly the published
column relation `d 1 = d 0 + d 2`; proving that these swaps merge the two
row-orbits and then inserting both endpoint singletons is the remaining
generic-cycle obligation. -/

theorem pge_head_coordinates {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    (d : ZMod (p - 1) → ZMod p) (u : K)
    (htriple : d 1 = d 0 + d 2) :
    pgeCoordinate d u (.inl (2, 0)) = (d 2, 2 * u) ∧
    pgeCoordinate d u (.inl (1, u)) = (d 1, u) ∧
    pgeCoordinate d u (.inl (1, 0)) = (d 1, 0) ∧
    pgeCoordinate d u (.inl (0, -u)) = (d 0, -u) := by
  simp [pgeCoordinate, pgeOffset]

theorem pge_removed_label_equations {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    (d : ZMod (p - 1) → ZMod p) (u : K)
    (htriple : d 1 = d 0 + d 2) :
    ((d 2, 2 * u) - (d 1, 0)) = (-d 0, 2 * u) ∧
    ((d 1, u) - (d 0, -u)) = (d 2, 2 * u) := by
  constructor
  · apply Prod.ext
    · rw [htriple]
      abel
    · ring
  · apply Prod.ext
    · rw [htriple]
      abel
    · ring


/-! The composition below is the exact finite-path part of the universal
relative-path construction.  The affine column lift and its endpoint surgery
provide the hypotheses in the characteristic-specific modules. -/

theorem compose_full_path {X G : Type*} [Fintype X] [AddCommGroup G]
    (Q : Perm X) (coord : X → G) (s t : X) (u : G) (M : ℕ)
    (B L : Set G)
    (hcard : Fintype.card X = M + 1)
    (hcycle : Q.IsCycleOn (Finset.univ : Finset X))
    (hqt : Q t = s)
    (hcoord : Function.Injective coord)
    (hs : coord s = 0)
    (ht : coord t = u)
    (hvertices : Set.BijOn coord {x | x ≠ s ∧ x ≠ t} B)
    (hlabels : Set.BijOn (fun x => coord (Q x) - coord x) {x | x ≠ t} L) :
    ∃ v : ℕ → G,
      v 0 = 0 ∧ v M = u ∧
      Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
      Set.BijOn v (Set.Ioo 0 M) B ∧
      Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M) L ∧
      Function.Injective (fun k : Fin (M + 1) =>
        ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
      (∀ a b : ℕ, a < b → b ≤ M →
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) ≠ 0) ∧
      (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = u := by
  let orbit : ℕ → X := fun n => (Q ^ n) s
  let v : ℕ → G := fun n => coord (orbit n)
  have hcard' : Fintype.card X = (M + 1) := hcard
  have hbound : Set.InjOn orbit (Set.Iio (M + 1)) := by
    simpa only [hcard'] using hcycle.injOn_pow_apply (Finset.mem_univ s)
  have horbit (z : X) : ∃ n < M + 1, orbit n = z := by
    simpa only [hcard'] using
      hcycle.exists_pow_eq (Finset.mem_univ s) (Finset.mem_univ z)
  have hzero : orbit 0 = s := by rfl
  have hlast : orbit M = t := by
    apply Q.injective
    rw [hqt]
    have hclose := hcycle.pow_card_apply (Finset.mem_univ s)
    simpa only [hcard', pow_succ', Perm.mul_apply] using hclose
  have hvinj : Function.Injective (fun n : Fin (M + 1) => v n.val) := by
    intro i j hij
    exact Fin.ext (hbound i.isLt j.isLt (hcoord hij))
  have hv0 : v 0 = 0 := by simp [v, orbit, hs]
  have hvM : v M = u := by simp [v, orbit, hlast, ht]
  have hinside : Set.BijOn orbit (Set.Ioo 0 M)
      {x | x ≠ s ∧ x ≠ t} := by
    constructor
    · intro n hn
      constructor
      · intro he
        have hn := hbound (x₁ := n) (x₂ := 0)
          (by change n < M + 1; omega) (by change 0 < M + 1; omega)
          (he.trans hzero.symm)
        omega
      · intro he
        have hn := hbound (x₁ := n) (x₂ := M)
          (by change n < M + 1; omega) (by change M < M + 1; omega)
          (he.trans hlast.symm)
        omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi.2)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj.2) hij
    · intro z hz
      obtain ⟨n, hn, heq⟩ := horbit z
      have hn0 : n ≠ 0 := by
        intro h
        subst n
        exact hz.1 (heq.symm.trans hzero)
      have hnM : n ≠ M := by
        intro h
        subst n
        exact hz.2 (heq.symm.trans hlast)
      exact ⟨n, ⟨by omega, by omega⟩, heq⟩
  have hpunctured : Set.BijOn orbit (Set.Iio M) {x | x ≠ t} := by
    constructor
    · intro n hn heq
      have hh := hbound (x₁ := n) (x₂ := M)
        (by change n < M + 1; omega) (by change M < M + 1; omega)
        (heq.trans hlast.symm)
      omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj) hij
    · intro z hz
      obtain ⟨n, hn, heq⟩ := horbit z
      have hnM : n ≠ M := by
        intro h
        subst n
        exact hz (heq.symm.trans hlast)
      exact ⟨n, (show n < M from by omega), heq⟩
  have hlabels' := hlabels.comp hpunctured
  have hstep (n : ℕ) : orbit (n + 1) = Q (orbit n) := by
    simp only [orbit, pow_succ', Perm.mul_apply]
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, (v (i + 1) - v i)) = v n - v 0 :=
    Finset.sum_range_sub v n
  refine ⟨v, hv0, hvM, hvinj, ?_, ?_, ?_, ?_, ?_⟩
  · exact hvertices.comp hinside
  · exact hlabels'.congr (fun n _ => by
      change coord (orbit (n + 1)) - coord (orbit n) =
        coord (Q (orbit n)) - coord (orbit n)
      rw [hstep])
  · intro i j heq
    apply hvinj
    simpa only [hsum, sub_left_inj] using heq
  · intro a b hab hb hzero'
    have hinterval :
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) = v b - v a := by
      rw [Finset.sum_Ico_eq_sub _ hab.le, hsum, hsum]
      abel
    have heq : v b = v a := sub_eq_zero.mp (hinterval.symm.trans hzero')
    have hij := hvinj (a₁ := ⟨b, by omega⟩) (a₂ := ⟨a, by omega⟩) heq
    have heqb : b = a := congrArg Fin.val hij
    omega
  · rw [hsum, hv0, hvM]
    simp

/-! The published characteristic-five telescope is re-exported here so the
universal file has an exact, checked small-prime branch while the generic
affine branch is completed. -/

theorem characteristic_five_case (K : Type*) [Field K] [Finite K] [CharP K 5]
    (u : K) (hu : u ≠ 0) :
    let M := 4 * Nat.card K + 1
    ∃ v : ℕ → ZMod 5 × K,
      v 0 = (0, 0) ∧ v M = (0, u) ∧
      Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
      Set.BijOn v (Set.Ioo 0 M) {z | z.1 ≠ 0} ∧
      Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M)
        ({z | z.1 ≠ 0} ∪ {(0, u)}) ∧
      Function.Injective (fun k : Fin (M + 1) =>
        ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
      (∀ a b : ℕ, a < b → b ≤ M →
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) ≠ 0) ∧
      (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = (0, u) := by
  simpa only using
    D5.S1.Words.Sequenceability.CharacteristicFiveDetour
      .exists_characteristic_five_relative_path K u hu

#print axioms compose_full_path

end D5.S1.Words.Sequenceability.UniformRelativePath
