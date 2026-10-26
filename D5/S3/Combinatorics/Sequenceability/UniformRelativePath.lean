/- GID: D5/S3/Combinatorics/Sequenceability/UniformRelativePath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/UniformRelativePath
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rotational columns and affine row dynamics give the universal finite-field relative path. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic
import D5.S1.Words.Sequenceability.RotationalColumnTriple
import D5.S3.Combinatorics.PerfectMatchings.CharacteristicFiveDetour

/-! Universal finite-field relative paths from rotational columns and affine
row dynamics. The signed row coordinate is y=(-1)^j x in the native chart
Phi(j,x)=(d_j,(-1)^j*x+b_j). Thus `chartCoord` is Phi after this involutive
change of row variable; `roundStep` is its advance-and-multiply action in y
coordinates. No coordinate change is applied to the final ambient path.

The construction follows the supplied native two-cut proof. The original
arbitrary-subset, same-M, Headley induction and odd-product problems remain open. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.UniformRelativePath

open Equiv
open D5.S1.Words.Sequenceability
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
    by_cases hi : i + 1 = 0
    · have hi' : i = -1 := (eq_neg_iff_add_eq_zero).mpr hi
      simp [hi, hi', r.ne_zero]
    · simp [hi, r.ne_zero]
  right_inv := by
    rintro ⟨i, x⟩
    by_cases hi : i = 0 <;> simp [hi, r.ne_zero]

def chartCoord {n p : ℕ} {K : Type*} [Add K] (d : ZMod n → ZMod p)
    (b : ZMod n → K) : ZMod n × K → ZMod p × K
  | (j, x) => (d j, x + b j)

def affineLabel {n p : ℕ} [NeZero n] {K : Type*} [Field K] (r : Kˣ)
    (d : ZMod n → ZMod p) (b : ZMod n → K) (v : ZMod n × K) : ZMod p × K :=
  chartCoord d b (roundStep r v) - chartCoord d b v

private theorem chart_vertices_bijective {n p : ℕ} {K : Type*} [Field K]
    (d : ZMod n → ZMod p) (b : ZMod n → K)
    (hd : Set.BijOn d Set.univ {x | x ≠ 0}) :
    Set.BijOn (chartCoord d b) Set.univ {z | z.1 ≠ 0} := by
  refine ⟨fun v _ => hd.1 (Set.mem_univ v.1), ?_, ?_⟩
  · rintro ⟨i, x⟩ _ ⟨j, y⟩ _ h
    have hi : i = j := hd.2.1 trivial trivial (congrArg Prod.fst h)
    subst j
    exact Prod.ext rfl (add_right_cancel (congrArg Prod.snd h))
  · rintro ⟨a, x⟩ ha
    obtain ⟨i, _, hi⟩ := hd.2.2 ha
    exact ⟨(i, x - b i), trivial, by simp [chartCoord, hi]⟩

private theorem affineLabel_formula {n p : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (d : ZMod n → ZMod p) (b : ZMod n → K)
    (i : ZMod n) (x : K) :
    affineLabel r d b (i, x) =
      (d (i + 1) - d i,
        if i + 1 = 0 then -((r : K) + 1) * x + b (i + 1) - b i
        else -2 * x + b (i + 1) - b i) := by
  by_cases hi : i + 1 = 0 <;>
    simp [affineLabel, roundStep, chartCoord, hi, Prod.sub_def] <;> ring

private theorem affine_labels_bijective {n p : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (d : ZMod n → ZMod p) (b : ZMod n → K)
    (he : Set.BijOn (fun i => d (i + 1) - d i) Set.univ {x | x ≠ 0})
    (htwo : (2 : K) ≠ 0) (hr : (r : K) + 1 ≠ 0) :
    Set.BijOn (affineLabel r d b) Set.univ {z | z.1 ≠ 0} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, x⟩ _
    change (affineLabel r d b (i, x)).1 ≠ 0
    rw [affineLabel_formula]
    exact he.1 (Set.mem_univ i)
  · rintro ⟨i, x⟩ _ ⟨j, y⟩ _ h
    have hi : i = j := he.2.1 trivial trivial (by
      simpa only [affineLabel_formula] using congrArg Prod.fst h)
    subst j
    have hrow := congrArg Prod.snd h
    simp only [affineLabel_formula] at hrow
    have hxy : x = y := by
      split_ifs at hrow
      · have hz : ((r : K) + 1) * (x - y) = 0 := by linear_combination -hrow
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hr)
      · have hz : (2 : K) * (x - y) = 0 := by linear_combination -hrow
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left htwo)
    exact Prod.ext rfl hxy
  · rintro ⟨a, x⟩ ha
    obtain ⟨i, _, hi⟩ := he.2.2 ha
    change d (i + 1) - d i = a at hi
    by_cases hclose : i + 1 = 0
    · refine ⟨(i, (b (i + 1) - b i - x) / ((r : K) + 1)), trivial, ?_⟩
      rw [affineLabel_formula, if_pos hclose, hi]
      refine Prod.ext (by rfl) ?_
      field_simp
      ring
    · refine ⟨(i, (b (i + 1) - b i - x) / 2), trivial, ?_⟩
      rw [affineLabel_formula, if_neg hclose, hi]
      refine Prod.ext (by rfl) ?_
      field_simp
      ring

private theorem round_nat_phase {n : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (x : K) (m : ℕ) (hm : m < n) :
    (roundStep (n := n) r ^ m) (0, x) = ((m : ZMod n), (-1 : K) ^ m * x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hnext : (m : ZMod n) + 1 ≠ 0 := by
        have hc : ((m + 1 : ℕ) : ZMod n) ≠ 0 :=
          (ZMod.natCast_eq_zero_iff (m + 1) n).not.mpr
            (Nat.not_dvd_of_pos_of_lt (by omega) hm)
        simpa only [Nat.cast_add, Nat.cast_one] using hc
      rw [pow_succ', Perm.mul_apply, ih (by omega)]
      change (if (m : ZMod n) + 1 = 0 then _ else _) = _
      rw [ite_eq_right hnext]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]

      congr 1
      ring

private theorem round_phase {n : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (x : K) (i : ZMod n) :
    (roundStep (n := n) r ^ i.val) (0, x) = (i, (-1 : K) ^ i.val * x) := by
  simpa only [ZMod.natCast_zmod_val] using round_nat_phase r x i.val i.val_lt

private theorem round_one {n : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (heven : Even n) (x : K) :
    (roundStep (n := n) r ^ n) (0, x) = (0, (r : K) * x) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm : n - 1 < n := by omega
  have hw : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    have hc : ((n - 1 + 1 : ℕ) : ZMod n) = 0 := by
      simp [show n - 1 + 1 = n by omega]
    simpa only [Nat.cast_add, Nat.cast_one] using hc
  have hpow := congrArg (fun k : ℕ => roundStep (n := n) r ^ k)
    (show n = (n - 1) + 1 by omega)
  rw [hpow, pow_succ', Perm.mul_apply, round_nat_phase r x (n - 1) hm]
  change (if ((n - 1 : ℕ) : ZMod n) + 1 = 0 then _ else _) = _
  rw [ite_eq_left hw]
  have hsign : (-1 : K) ^ n = 1 := heven.neg_one_pow
  have hsign' : (-1 : K) ^ (n - 1) * (-1 : K) = 1 := by
    rw [← pow_succ, show n - 1 + 1 = n by omega, hsign]
  have heq : (-1 : K) ^ (n - 1) = -1 := by linear_combination -hsign'
  rw [heq]
  congr 1
  ring

private theorem round_rounds {n : ℕ} [NeZero n] {K : Type*} [Field K]
    (r : Kˣ) (heven : Even n) (x : K) (m : ℕ) :
    (roundStep (n := n) r ^ (n * m)) (0, x) = (0, (r : K) ^ m * x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, pow_add, Perm.mul_apply, round_one r heven, ih, pow_succ]
      congr 1
      ring

private theorem round_same_cycle {n : ℕ} [NeZero n] {K : Type*} [Field K] [Finite K]
    (r : Kˣ) (hr : ∀ z : Kˣ, ∃ m : ℕ, r ^ m = z) (heven : Even n)
    (v w : ZMod n × K) :
    (roundStep (n := n) r).SameCycle v w ↔ (v.2 = 0 ↔ w.2 = 0) := by
  have hinv (z : ZMod n × K) : (roundStep (n := n) r z).2 = 0 ↔ z.2 = 0 := by
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
        rw [hm', div_mul_cancel₀ _ (by simp [v₀, hv])]
    obtain ⟨m, hm⟩ := hrow
    have hpow : (roundStep (n := n) r ^ (n * m)) (0, v₀) =
        (0, (r : K) ^ m * v₀) := round_rounds r heven v₀ m
    have hto0 : (roundStep (n := n) r).SameCycle (0, v₀) (0, w₀) :=
      ⟨(n * m : ℕ), by rw [zpow_natCast, hpow, hm]⟩
    have hv : (roundStep (n := n) r).SameCycle (0, v₀) v := by
      refine ⟨(v.1.val : ℕ), ?_⟩
      rw [zpow_natCast, round_phase]
      refine Prod.ext (by rfl) ?_
      simp [v₀, ← mul_assoc, ← pow_add, ← two_mul]
    have hw : (roundStep (n := n) r).SameCycle (0, w₀) w := by
      refine ⟨(w.1.val : ℕ), ?_⟩
      rw [zpow_natCast, round_phase]
      refine Prod.ext (by rfl) ?_
      simp [w₀, ← mul_assoc, ← pow_add, ← two_mul]
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
  · exact one_ne_zero (by linear_combination h - hm')
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
    RotationalColumnTriple.exists_rotational_column_triple p hp h7
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgen : ∀ z : Kˣ, ∃ m : ℕ, r ^ m = z := by
    intro z
    exact (Submonoid.mem_powers_iff z r).mp
      (mem_powers_iff_mem_zpowers.mpr (hr z))
  have heven : Even (p - 1) := by
    have hodd := hp.eq_two_or_odd.resolve_left (by omega)
    exact ⟨(p - 1) / 2, by omega⟩
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

private theorem pgeBasePower {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    (r : Kˣ) (m : ℕ) (v : ZMod (p - 1) × K) :
    (pgeBasePerm r ^ m) (.inl v) = .inl ((roundStep r ^ m) v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
      rfl

private theorem pgeBaseSameCycle {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    [Finite K] (r : Kˣ) (hr : ∀ z : Kˣ, ∃ m : ℕ, r ^ m = z)
    (heven : Even (p - 1)) (v w : ZMod (p - 1) × K) :
    (pgeBasePerm r).SameCycle (.inl v) (.inl w) ↔
      (v.2 = 0 ↔ w.2 = 0) := by
  rw [← round_same_cycle r hr heven]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    rw [pgeBasePower] at hm
    exact ⟨(m : ℤ), by simpa only [zpow_natCast] using Sum.inl.inj hm⟩
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    exact ⟨(m : ℤ), by rw [zpow_natCast, pgeBasePower, hm]⟩

theorem pge_whole_carrier_cycle {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    [Finite K] (hp : p.Prime) (h7 : 7 ≤ p) (r : Kˣ)
    (hr : ∀ z : Kˣ, ∃ m : ℕ, r ^ m = z) (heven : Even (p - 1))
    (u : K) (hu : u ≠ 0) :
    (pgeSurgery r u).IsCycleOn (Set.univ : Set (pgeCarrier p K)) := by
  let P := pgeBasePerm (p := p) r
  let h₁ : pgeCarrier p K := .inl (2, 0)
  let h₂ : pgeCarrier p K := .inl (1, u)
  let s : pgeCarrier p K := .inr 0
  let t : pgeCarrier p K := .inr 1
  let A : Set (pgeCarrier p K) := {z | P.SameCycle h₁ z}
  let B : Set (pgeCarrier p K) := {z | P.SameCycle h₂ z}
  let U : Set (pgeCarrier p K) := Set.range Sum.inl
  have hA : P.IsCycleOn A :=
    ⟨P.bijOn (fun z => Perm.sameCycle_apply_right),
      fun x hx y hy => hx.symm.trans hy⟩
  have hB : P.IsCycleOn B :=
    ⟨P.bijOn (fun z => Perm.sameCycle_apply_right),
      fun x hx y hy => hx.symm.trans hy⟩
  have hdis : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    have hh := hzA.trans hzB.symm
    have he := (pgeBaseSameCycle r hr heven (2, 0) (1, u)).mp hh
    exact hu (he.mp rfl)
  have hU : A ∪ B = U := by
    ext z
    cases z with
    | inl v =>
        simp only [Set.mem_union, Set.mem_ofPred_eq, A, B]
        rw [pgeBaseSameCycle r hr heven, pgeBaseSameCycle r hr heven]
        simpa [U, hu] using em (v.2 = 0)
    | inr i =>
        have hfix : P (.inr i) = .inr i := rfl
        have hna : ¬ P.SameCycle h₁ (.inr i) := fun h =>
          by simpa only [h₁, reduceCtorEq] using h.eq_of_right hfix
        have hnb : ¬ P.SameCycle h₂ (.inr i) := fun h =>
          by simpa only [h₂, reduceCtorEq] using h.eq_of_right hfix
        simp [A, B, hna, hnb, U]
  have hR : (swap h₁ h₂ * P).IsCycleOn U := by
    have hm := D5.S1.Words.Sequenceability.CharacteristicFiveDetour.merge_cycles
      P A B hA hB hdis (P⁻¹ h₁) (P⁻¹ h₂)
      ((Perm.SameCycle.refl P h₁).symm_apply_right)
      ((Perm.SameCycle.refl P h₂).symm_apply_right)
    simpa only [mul_swap_eq_swap_mul, Perm.inv_def, Equiv.apply_symm_apply, hU] using hm
  have hPs : P s = s := rfl
  have hPt : P t = t := rfl
  have hR_s : (swap h₁ h₂ * P) s = s := by simp [Perm.mul_apply, hPs, s, h₁, h₂, swap_apply_def]
  have hR_t : (swap h₁ h₂ * P) t = t := by simp [Perm.mul_apply, hPt, t, h₁, h₂, swap_apply_def]
  have hh₁ : h₁ ∈ U := ⟨(2, 0), rfl⟩
  have hT : (swap h₁ t * (swap h₁ h₂ * P)).IsCycleOn (U ∪ {t}) := by
    have hm := D5.S1.Words.Sequenceability.CharacteristicFiveDetour.merge_cycles
      (swap h₁ h₂ * P) U {t} hR (Perm.isCycleOn_singleton.mpr hR_t)
      (by simp [U, t, Set.disjoint_singleton_right])
      ((swap h₁ h₂ * P)⁻¹ h₁) t
      (hR.inv.1.1 hh₁) (by simp)
    simpa only [mul_swap_eq_swap_mul, Perm.inv_def, Equiv.apply_symm_apply, hR_t] using hm
  have hT_s : (swap h₁ t * (swap h₁ h₂ * P)) s = s := by
    simp only [Perm.mul_apply, hR_s]; simp [s, h₁, t, swap_apply_def]
  have hQ : (swap h₁ s * (swap h₁ t * (swap h₁ h₂ * P))).IsCycleOn
      ((U ∪ {t}) ∪ {s}) := by
    have hm := D5.S1.Words.Sequenceability.CharacteristicFiveDetour.merge_cycles
      (swap h₁ t * (swap h₁ h₂ * P)) (U ∪ {t}) {s} hT
      (Perm.isCycleOn_singleton.mpr hT_s)
      (by simp [U, s, t, Set.disjoint_singleton_right])
      ((swap h₁ t * (swap h₁ h₂ * P))⁻¹ h₁) s
      (hT.inv.1.1 (Or.inl hh₁)) (by simp)
    simpa only [mul_swap_eq_swap_mul, Perm.inv_def, Equiv.apply_symm_apply, hT_s] using hm
  have hfull : (U ∪ {t}) ∪ {s} = Set.univ := by
    ext z
    cases z with
    | inl v => simp [U]
    | inr i => fin_cases i <;> simp [U, s, t]
  simpa only [hfull, pgeSurgery, h₁, h₂, s, t, P, pgeBasePerm, mul_assoc] using hQ

/-! The four arrows changed by `pgeSurgery` are recorded at the actual
carrier level.  The first-coordinate cancellation is exactly the published
column relation `d 1 = d 0 + d 2`. The whole-cycle theorem merges both
row-orbits and inserts the endpoint singleton cycles. -/

private theorem small_phase_inj {p : ℕ} [NeZero (p - 1)] (h7 : 7 ≤ p)
    (a b : ℕ) (ha : a < p - 1) (hb : b < p - 1)
    (h : (a : ZMod (p - 1)) = (b : ZMod (p - 1))) : a = b := by
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv

private theorem pge_coordinate_injective {p : ℕ} {K : Type*} [Field K]
    (d : ZMod (p - 1) → ZMod p) (u : K) (hu : u ≠ 0)
    (hd : Set.BijOn d Set.univ {x | x ≠ 0}) :
    Function.Injective (pgeCoordinate d u) := by
  have hv := chart_vertices_bijective d (pgeOffset u) hd
  rintro (v | i) (w | j) h
  · exact congrArg Sum.inl (hv.2.1 trivial trivial h)
  · have hn := hv.1 (Set.mem_univ v)
    have hz := congrArg Prod.fst h
    fin_cases j <;> exact (hn hz).elim
  · have hn := hv.1 (Set.mem_univ w)
    have hz := congrArg Prod.fst h
    fin_cases i <;> exact (hn hz.symm).elim
  · fin_cases i <;> fin_cases j <;> simp_all [pgeCoordinate]

private theorem pge_surgery_labels {p : ℕ} [NeZero (p - 1)] {K : Type*} [Field K]
    (h7 : 7 ≤ p) (r : Kˣ) (d : ZMod (p - 1) → ZMod p) (u : K)
    (ht : d 1 = d 0 + d 2)
    (he : Set.BijOn (affineLabel r d (pgeOffset u)) Set.univ {z | z.1 ≠ 0}) :
    Set.BijOn (fun z => pgeCoordinate d u (pgeSurgery r u z) - pgeCoordinate d u z)
      {z | z ≠ Sum.inr 1} ({z | z.1 ≠ 0} ∪ {(0, u)}) := by
  let s : pgeCarrier p K := .inr 0
  let t : pgeCarrier p K := .inr 1
  let a : pgeCarrier p K := .inl (1, 0)
  let b : pgeCarrier p K := .inl (0, -u)
  let h₁ : pgeCarrier p K := .inl (2, 0)
  let h₂ : pgeCarrier p K := .inl (1, u)
  let ψ : Perm (pgeCarrier p K) := swap s a * swap s b
  let L : pgeCarrier p K → ZMod p × K := fun z =>
    match z with
    | .inl v => affineLabel r d (pgeOffset u) v
    | .inr _ => (0, u)
  have h01 : (0 : ZMod (p - 1)) ≠ 1 := by
    intro h
    have := small_phase_inj (p := p) h7 0 1 (by omega) (by omega) (by simpa using h)
    omega
  have h02 : (0 : ZMod (p - 1)) ≠ 2 := by
    intro h
    have := small_phase_inj (p := p) h7 0 2 (by omega) (by omega) (by simpa using h)
    omega
  have h12 : (1 : ZMod (p - 1)) ≠ 2 := by
    intro h
    have := small_phase_inj (p := p) h7 1 2 (by omega) (by omega) (by simpa using h)
    omega
  have hPa : pgeBasePerm r a = h₁ := by
    simp [pgeBasePerm, roundStep, a, h₁, one_add_one_eq_two, Ne.symm h02]
  have hPb : pgeBasePerm r b = h₂ := by
    simp [pgeBasePerm, roundStep, b, h₂, Ne.symm h01]
  have hψt : ψ t = t := by simp [ψ, s, t, a, b, swap_apply_def]
  have hψ : Set.BijOn ψ {z | z ≠ t} {z | z ≠ t} :=
    ψ.bijOn (fun z => by
      change ψ z ≠ t ↔ z ≠ t
      conv_lhs => rw [← hψt]
      exact not_congr ψ.injective.eq_iff)
  have hL : Set.BijOn L {z | z ≠ t} ({z | z.1 ≠ 0} ∪ {(0, u)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro (v | i) hi
      · exact Or.inl (he.1 trivial)
      · exact Or.inr rfl
    · rintro (v | i) hi (w | j) hj h
      · exact congrArg Sum.inl (he.2.1 trivial trivial h)
      · exact ((he.1 (Set.mem_univ v)) (congrArg Prod.fst h)).elim
      · exact ((he.1 (Set.mem_univ w)) (congrArg Prod.fst h).symm).elim
      · have hi0 : i = 0 := by fin_cases i <;> simp_all [t]
        have hj0 : j = 0 := by fin_cases j <;> simp_all [t]
        simp [hi0, hj0]
    · intro z hz
      rcases hz with hz | hz
      · obtain ⟨v, _, hv⟩ := he.2.2 hz
        exact ⟨.inl v, by simp [t], hv⟩
      · exact ⟨s, by simp [s, t], hz.symm⟩
  have hdiff (z : pgeCarrier p K) (hz : z ≠ t) :
      pgeCoordinate d u (pgeSurgery r u z) - pgeCoordinate d u z = L (ψ z) := by
    by_cases hza : z = a
    · subst z
      apply Prod.ext
      · simp [pgeSurgery, pgeCoordinate, pgeOffset, pgeBasePerm, roundStep,
          ψ, L, s, t, a, b, h₁, h₂, swap_apply_def, h01, h02, h12,
          Ne.symm h01, Ne.symm h02, Ne.symm h12, one_add_one_eq_two]
      · simp [pgeSurgery, pgeCoordinate, pgeOffset, pgeBasePerm, roundStep,
          ψ, L, s, t, a, b, h₁, h₂, swap_apply_def, h01, h02, h12,
          Ne.symm h01, Ne.symm h02, Ne.symm h12, one_add_one_eq_two]
    by_cases hzb : z = b
    · subst z
      apply Prod.ext
      · simp [pgeSurgery, pgeCoordinate, pgeOffset, pgeBasePerm, roundStep,
          affineLabel, chartCoord, ψ, L, s, t, a, b, h₁, h₂, swap_apply_def,
          h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
          one_add_one_eq_two, ht] <;> abel
      · simp [pgeSurgery, pgeCoordinate, pgeOffset, pgeBasePerm, roundStep,
          affineLabel, chartCoord, ψ, L, s, t, a, b, h₁, h₂, swap_apply_def,
          h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
          one_add_one_eq_two]
        ring
    by_cases hzs : z = s
    · subst z
      apply Prod.ext
      · simp [pgeSurgery, pgeCoordinate, pgeOffset, pgeBasePerm, roundStep,
          affineLabel, chartCoord, ψ, L, s, t, a, b, h₁, h₂, swap_apply_def,
          h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
          one_add_one_eq_two, ht] <;> abel
      · simp [pgeSurgery, pgeCoordinate, pgeOffset, pgeBasePerm, roundStep,
          affineLabel, chartCoord, ψ, L, s, t, a, b, h₁, h₂, swap_apply_def,
          h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12,
          one_add_one_eq_two]
        ring
    have hp₁ : pgeBasePerm r z ≠ h₁ := by
      rw [← hPa]
      exact (pgeBasePerm r).injective.ne hza
    have hp₂ : pgeBasePerm r z ≠ h₂ := by
      rw [← hPb]
      exact (pgeBasePerm r).injective.ne hzb
    have hps : pgeBasePerm r z ≠ s := by
      have hs : pgeBasePerm r s = s := rfl
      rw [← hs]
      exact (pgeBasePerm r).injective.ne hzs
    have hpt : pgeBasePerm r z ≠ t := by
      have ht : pgeBasePerm r t = t := rfl
      rw [← ht]
      exact (pgeBasePerm r).injective.ne hz
    have hψz : ψ z = z := by
      simp [ψ, Perm.mul_apply, swap_apply_of_ne_of_ne, hza, hzb, hzs]
    rw [hψz]
    have hQz : pgeSurgery r u z = pgeBasePerm r z := by
      simp only [pgeSurgery, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hp₁ hp₂,
        swap_apply_of_ne_of_ne hp₁ hpt, swap_apply_of_ne_of_ne hp₁ hps]
    rw [hQz]
    cases z with
    | inl v => rfl
    | inr i => fin_cases i <;> simp_all [s, t]
  exact (hL.comp hψ).congr (fun z hz => (hdiff z hz).symm)

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
    simpa only [Finset.card_univ, hcard'] using hcycle.injOn_pow_apply (Finset.mem_univ s)
  have horbit (z : X) : ∃ n < M + 1, orbit n = z := by
    simpa only [Finset.card_univ, hcard'] using
      hcycle.exists_pow_eq (Finset.mem_univ s) (Finset.mem_univ z)
  have hzero : orbit 0 = s := by rfl
  have hlast : orbit M = t := by
    apply Q.injective
    rw [hqt]
    have hclose := hcycle.pow_card_apply (Finset.mem_univ s)
    simpa only [Finset.card_univ, hcard', pow_succ', Perm.mul_apply] using hclose
  have hvinj : Function.Injective (fun n : Fin (M + 1) => v n.val) := by
    intro i j hij
    exact Fin.ext (hbound i.isLt j.isLt (hcoord hij))
  have hv0 : v 0 = 0 := by simp [v, orbit, hs]
  have hvM : v M = u := by
    change coord (orbit M) = u
    rw [hlast, ht]
  have hinside : Set.BijOn orbit (Set.Ioo 0 M)
      {x | x ≠ s ∧ x ≠ t} := by
    constructor
    · intro n hn
      rcases hn with ⟨hn0, hnM⟩
      constructor
      · intro he
        have heqn := hbound (x₁ := n) (x₂ := 0)
          (by change n < M + 1; omega) (by change 0 < M + 1; omega)
          (he.trans hzero.symm)
        omega
      · intro he
        have heqn := hbound (x₁ := n) (x₂ := M)
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
      change n < M at hn
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
      change coord (Q (orbit n)) - coord (orbit n) =
        coord (orbit (n + 1)) - coord (orbit n)
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

/-- The complete relative path for every finite field of prime characteristic
at least seven, including all actual vector-label inventories and bounded sums. -/
theorem exists_prime_ge_seven_relative_path (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (K : Type*) [Field K] [Finite K] [CharP K p] (u : K) (hu : u ≠ 0) :
    let M := (p - 1) * Nat.card K + 1
    ∃ v : ℕ → ZMod p × K,
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
  letI : NeZero (p - 1) := ⟨by omega⟩
  letI : NeZero p := ⟨by omega⟩
  letI := Fintype.ofFinite K
  obtain ⟨d, r, hd, he, ht, hr, heven, hrneg⟩ := p_ge_seven_column_setup K hp h7
  let Q := pgeSurgery (p := p) r u
  let coord := pgeCoordinate d u
  let s : pgeCarrier p K := .inr 0
  let t : pgeCarrier p K := .inr 1
  let M := (p - 1) * Nat.card K + 1
  have hcard : Fintype.card (pgeCarrier p K) = M + 1 := by
    simp [pgeCarrier, M, Nat.card_eq_fintype_card, ZMod.card]

  have hcycle : Q.IsCycleOn (Finset.univ : Finset (pgeCarrier p K)) := by
    simpa only [Finset.coe_univ] using pge_whole_carrier_cycle hp h7 r hr heven u hu
  have hqt : Q t = s := by
    simp [Q, pgeSurgery, t, s, pgeBasePerm, Perm.mul_apply, swap_apply_def]
  have hcoord : Function.Injective coord := pge_coordinate_injective d u hu hd
  have hinside : Set.BijOn coord {z | z ≠ s ∧ z ≠ t} {z | z.1 ≠ 0} := by
    have hv := chart_vertices_bijective d (pgeOffset u) hd
    have hset : {z : pgeCarrier p K | z ≠ s ∧ z ≠ t} = Set.range Sum.inl := by
      ext z
      cases z with
      | inl v => simp [s, t]
      | inr i => fin_cases i <;> simp [s, t]
    rw [hset]
    refine ⟨?_, hcoord.injOn, ?_⟩
    · rintro z ⟨v, rfl⟩
      exact hv.1 trivial
    · intro z hz
      obtain ⟨v, _, hv⟩ := hv.2.2 hz
      exact ⟨.inl v, ⟨v, rfl⟩, hv⟩
  have htwo : (2 : K) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
      ((CharP.cast_eq_zero_iff K p 2).mp hz)
  have hlabels := pge_surgery_labels h7 r d u ht
    (affine_labels_bijective r d (pgeOffset u) he htwo hrneg)
  exact compose_full_path Q coord s t (0, u) M _ _ hcard hcycle hqt hcoord
    (by simp [coord, pgeCoordinate, s]) (by simp [coord, pgeCoordinate, t])
    hinside hlabels

/-- Every prime at least five and every finite field of that characteristic
admit the universal relative path with complete full-vector inventories. -/
theorem exists_uniform_relative_path (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (K : Type*) [Field K] [Finite K] [CharP K p] (u : K) (hu : u ≠ 0) :
    let M := (p - 1) * Nat.card K + 1
    ∃ v : ℕ → ZMod p × K,
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
  by_cases h : p = 5
  · subst p
    exact CharacteristicFiveDetour.exists_characteristic_five_relative_path K u hu
  · have hodd := hp.eq_two_or_odd.resolve_left (by omega)
    exact exists_prime_ge_seven_relative_path p hp (by omega) K u hu

#print axioms compose_full_path
#print axioms exists_uniform_relative_path

end

end D5.S3.Combinatorics.Sequenceability.UniformRelativePath
