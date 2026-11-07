/- GID: D5/S3/Arith/CharacterSums/MercaQuadraticQuarter
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/MercaQuadraticQuarter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed finite quadratic quarter-sum formula at conductor four r. -/

import D5.S3.Analytic.Zeta.MercaImaginaryCharacter
import D5.S3.Analytic.Zeta.CatalanPrimeOddMoment
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Four literal representative blocks retain the sign in the finite quadratic sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.MercaQuadraticQuarter
open D5.S3.Analytic.Zeta MercaImaginaryCharacter

variable (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5)

private def block (x : ZMod r × ZMod 4) : ZMod (4 * r) :=
  ((x.1.val + r * x.2.val : ℕ) : ZMod (4 * r))

private lemma block_bound (x : ZMod r × ZMod 4) : x.1.val + r * x.2.val < 4 * r := by
  have hb := ZMod.val_lt x.1
  have hj := ZMod.val_lt x.2
  nlinarith

private lemma block_val (x : ZMod r × ZMod 4) :
    (block r x).val = x.1.val + r * x.2.val :=
  ZMod.val_natCast_of_lt (block_bound r x)

private def blockEquiv : ZMod r × ZMod 4 ≃ ZMod (4 * r) := by
  apply Equiv.ofBijective (block r)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y h
    have hh := congrArg (ZMod.castHom (dvd_mul_left r 4) (ZMod r)) h
    have hx : x.1 = y.1 := by
      simpa only [block, map_add, map_mul, map_natCast, Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val] using hh
    have hv := congrArg ZMod.val h
    rw [block_val, block_val, hx] at hv
    have hy : x.2 = y.2 := by
      apply ZMod.val_injective 4
      apply Nat.eq_of_mul_eq_mul_left (Fact.out : r.Prime).pos
      omega
    exact Prod.ext hx hy
  · simp [Nat.mul_comm]

include hr in
private lemma four_cast : (r : ZMod 4) = 1 := by
  rw [← ZMod.natCast_mod r 4, show r % 4 = 1 by omega]
  rfl

private lemma four_weight (b : ℕ) :
    (∑ j : ZMod 4, ((b : ℤ) + (r : ℤ) * j.val) *
      ZMod.χ₄ ((b : ZMod 4) + j)) =
      if b % 4 < 2 then -2 * (r : ℤ) else 2 * (r : ℤ) := by
  classical
  have hsum (f : ZMod 4 → ℤ) : ∑ j, f j = f 0 + f 1 + f 2 + f 3 := by
    exact Fin.sum_univ_four f
  rw [hsum]
  simp only [show (0 : ZMod 4).val = 0 by decide,
    show (1 : ZMod 4).val = 1 by decide,
    show (2 : ZMod 4).val = 2 by decide,
    show (3 : ZMod 4).val = 3 by decide]
  have hb : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  have hbcast : (b : ZMod 4) = (b % 4 : ℕ) := (ZMod.natCast_mod b 4).symm
  rcases hb with hb | hb | hb | hb <;>
    norm_num [hbcast, hb, ZMod.χ₄] <;> ring

private def residueSum (j : ℕ) : ℤ :=
  ∑ b : ZMod r, if b.val % 4 = j then quadraticChar (ZMod r) b else 0

include hr in
private lemma negative_even (b : ZMod r) :
    quadraticChar (ZMod r) (-b) = quadraticChar (ZMod r) b := by
  rw [← neg_one_mul, map_mul]
  have hn : quadraticChar (ZMod r) (-1) = 1 := by
    have hleg : legendreSym r (-1) = 1 := by
      rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_one_mod_four (by omega)]
    simpa only [legendreSym, Int.cast_neg, Int.cast_one] using hleg
  rw [hn, one_mul]

include hr in
private lemma residue_reflections :
    residueSum r 0 = residueSum r 1 ∧ residueSum r 2 = residueSum r 3 := by
  classical
  have he (j k : ℕ) (hjk : j + k = 1 ∨ j + k = 5)
      (hj : j < 4) (hk : k < 4) : residueSum r j = residueSum r k := by
    unfold residueSum
    rw [← Equiv.sum_comp (Equiv.neg (ZMod r))]
    apply Finset.sum_congr rfl
    intro b _
    change (if (-b).val % 4 = j then quadraticChar (ZMod r) (-b) else 0) = _
    rw [negative_even r hr]
    by_cases hb : b = 0
    · simp [hb, quadraticChar_zero]
    · letI : NeZero b := ⟨hb⟩
      rw [ZMod.val_neg_of_ne_zero]
      have hv := ZMod.val_lt b
      have hvpos := ZMod.val_pos.mpr hb
      have hmod : (r - b.val) % 4 = j ↔ b.val % 4 = k := by omega
      simp only [hmod]
  exact ⟨he 0 1 (Or.inl rfl) (by decide) (by decide),
    he 2 3 (Or.inr rfl) (by decide) (by decide)⟩

include hr in
private lemma residue_total :
    residueSum r 0 + residueSum r 1 + residueSum r 2 + residueSum r 3 = 0 := by
  classical
  have ht := quadraticChar_sum_zero ((ZMod.ringChar_zmod_n r).substr (by omega))
  rw [residueSum, residueSum, residueSum, residueSum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  convert ht using 1
  apply Finset.sum_congr rfl
  intro b _
  have hb : b.val % 4 = 0 ∨ b.val % 4 = 1 ∨ b.val % 4 = 2 ∨ b.val % 4 = 3 := by omega
  rcases hb with hb | hb | hb | hb <;> simp [hb]

include hr in
private lemma weighted_blocks :
    (∑ a : ZMod (4 * r), (a.val : ℂ) * character r a) =
      (-8 * (r : ℤ) * residueSum r 0 : ℤ) := by
  classical
  rw [← Equiv.sum_comp (blockEquiv r), Fintype.sum_prod_type]
  change (∑ b : ZMod r, ∑ j : ZMod 4,
    ((block r (b, j)).val : ℂ) * character r (block r (b, j))) = _
  have hterm (b : ZMod r) (j : ZMod 4) :
      ((block r (b, j)).val : ℂ) * character r (block r (b, j)) =
        (((b.val : ℤ) + (r : ℤ) * j.val) *
          ZMod.χ₄ ((b.val : ZMod 4) + j) * quadraticChar (ZMod r) b : ℤ) := by
    have he : block r (b, j) = ((b.val + r * j.val : ℕ) : ℤ) := by simp [block]
    rw [block_val, he, character_int]
    simp only [legendreSym, Int.cast_natCast, Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val,
      four_cast r hr, one_mul, Int.cast_mul, Int.cast_add]
    ring
  simp_rw [hterm]
  push_cast
  have hin (b : ZMod r) :
      (∑ j : ZMod 4, ((b.val : ℤ) + (r : ℤ) * j.val) *
        ZMod.χ₄ ((b.val : ZMod 4) + j) * quadraticChar (ZMod r) b) =
      (if b.val % 4 < 2 then -2 * (r : ℤ) else 2 * (r : ℤ)) *
        quadraticChar (ZMod r) b := by
    rw [← Finset.sum_mul, four_weight r b.val]
  have hs : (∑ b : ZMod r,
      (if b.val % 4 < 2 then -2 * (r : ℤ) else 2 * (r : ℤ)) *
        quadraticChar (ZMod r) b) =
      -2 * (r : ℤ) * (residueSum r 0 + residueSum r 1 - residueSum r 2 - residueSum r 3) := by
    unfold residueSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hb : b.val % 4 = 0 ∨ b.val % 4 = 1 ∨ b.val % 4 = 2 ∨ b.val % 4 = 3 := by omega
    rcases hb with hb | hb | hb | hb <;> simp [hb] <;> ring
  have hi : (∑ b : ZMod r, ∑ j : ZMod 4,
      ((b.val : ℤ) + (r : ℤ) * j.val) * ZMod.χ₄ ((b.val : ZMod 4) + j) *
        quadraticChar (ZMod r) b) = -8 * (r : ℤ) * residueSum r 0 := by
    simp_rw [hin]
    rw [hs]
    obtain ⟨h01, h23⟩ := residue_reflections r hr
    have ht := residue_total r hr
    rw [← h01, ← h23] at ht ⊢
    linear_combination 2 * (r : ℤ) * ht
  exact_mod_cast hi

/-- The source's literal positive quarter Legendre sum. -/
def quarterSum : ℤ :=
  ∑ a ∈ Finset.Icc 1 ((r - 1) / 4), legendreSym r (a : ℤ)

include hr in
private lemma residue_quarter : residueSum r 0 = quarterSum r := by
  classical
  let m := (r - 1) / 4
  have hrm : r = 4 * m + 1 := by dsimp [m]; omega
  have hfour : quadraticChar (ZMod r) (4 : ZMod r) = 1 := by
    have htwo := Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega))
    convert quadraticChar_sq_one' (F := ZMod r) htwo using 1 <;> norm_num
  have he : residueSum r 0 =
      ∑ a ∈ Finset.range (m + 1), legendreSym r (a : ℤ) := by
    unfold residueSum
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun b _ => b.val / 4)
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      have hlt := ZMod.val_lt b
      exact Finset.mem_range.mpr (by omega)
    · intro b hb c hc heq
      apply ZMod.val_injective r
      have hb' := (Finset.mem_filter.mp hb).2
      have hc' := (Finset.mem_filter.mp hc).2
      omega
    · intro a ha
      have ha' := Finset.mem_range.mp ha
      have har : 4 * a < r := by omega
      refine ⟨(4 * a : ℕ), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [ZMod.val_natCast_of_lt har]
        omega
      · rw [ZMod.val_natCast_of_lt har]
        omega
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      have hval : b.val = 4 * (b.val / 4) := by omega
      change quadraticChar (ZMod r) b =
        quadraticChar (ZMod r) (((b.val / 4 : ℕ) : ℤ) : ZMod r)
      simp only [Int.cast_natCast]
      conv_lhs => rw [← ZMod.natCast_zmod_val b, hval, Nat.cast_mul, Nat.cast_ofNat, map_mul, hfour, one_mul]
  rw [he]
  have hset : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext a
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp [quarterSum, m, legendreSym]

/-- The number of quadratic nonresidues in the literal positive quarter interval. -/
def nonresidueCount : ℕ :=
  ((Finset.Icc 1 ((r - 1) / 4) : Finset ℕ).filter
    (fun a : ℕ => legendreSym r (a : ℤ) = -1)).card

/-- The quarter character sum is the interval length minus twice its nonresidue count. -/
theorem quarter_nonresidue :
    quarterSum r = (((r - 1) / 4 : ℕ) : ℤ) - 2 * nonresidueCount r := by
  classical
  have hval (a : ℕ) (ha : a ∈ Finset.Icc 1 ((r - 1) / 4)) :
      legendreSym r (a : ℤ) = 1 ∨ legendreSym r (a : ℤ) = -1 := by
    have ha' := Finset.mem_Icc.mp ha
    have hrp : 0 < r := (Fact.out : r.Prime).pos
    have har : a < r := by omega
    have ha0 : (a : ZMod r) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt har, ZMod.val_zero] at hv
      omega
    simpa only [legendreSym, Int.cast_natCast] using quadraticChar_dichotomy ha0
  have hs : quarterSum r =
      ∑ a ∈ Finset.Icc 1 ((r - 1) / 4),
        (1 - 2 * (if legendreSym r (a : ℤ) = -1 then (1 : ℤ) else 0)) := by
    unfold quarterSum
    apply Finset.sum_congr rfl
    intro a ha
    rcases hval a ha with h | h <;> simp [h]
  rw [hs, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hc : (∑ a ∈ Finset.Icc 1 ((r - 1) / 4),
      if legendreSym r (a : ℤ) = -1 then (1 : ℤ) else 0) = nonresidueCount r := by
    rw [← Finset.sum_filter]
    simp [nonresidueCount]
  rw [hc]
  simp

include hr in
/-- The signed finite weighted-character bridge, before using any class number. -/
theorem LFunction_zero_quarter :
    DirichletCharacter.LFunction (character r) 0 = 2 * (quarterSum r : ℂ) := by
  have hne := (character_properties r hr).2.2.2
  rw [CatalanPrimeOddMoment.LFunction_zero_eq_neg_weighted_sum_general
    (4 * r) (by omega) (character r) hne, weighted_blocks r hr, residue_quarter r hr]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero]
  <;> ring

end D5.S3.Arith.CharacterSums.MercaQuadraticQuarter
