/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152MarkedSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152MarkedSeries
   mirror-E: none(waiver:marked-dyck-descent-counting)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: An arbitrary marked interior Dyck descent has the Catalan denominator identity. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Factor
import D5.S3.Combinatorics.InversionSeq.InversionSeq152Reflection
import Mathlib.RingTheory.PowerSeries.Catalan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152MarkedSeries

open DyckStep
open scoped BigOperators
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse
open D5.S3.Combinatorics.InversionSeq.InversionSeq152Factor
open D5.S3.Combinatorics.InversionSeq.InversionSeq152Reflection

set_option maxHeartbeats 2400000 in
theorem marked_interior_descent_enumeration {R : Type*} [CommRing R]
    (weight : ℕ → R) (hempty : weight 0 = 0) :
    let catalan := PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries
    let marked := PowerSeries.mk fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        (((((path.val.toList.splitOn U).map List.length).filter (· != 0)).dropLast.map
          weight).sum)
    let final := PowerSeries.mk fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        weight (path.val.toList.reverse.takeWhile (· == D)).length
    (2 - catalan) * marked = (catalan - 1) * final := by
  classical
  let C := PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries
  let initial (path : DyckWord) := (path.toList.takeWhile (· == U)).length
  let runs (path : DyckWord) :=
    ((path.toList.splitOn D).map List.length).filter (· != 0)
  let total (path : DyckWord) := ((runs path).map weight).sum
  let A := PowerSeries.mk fun size =>
    ∑ path : {path : DyckWord // path.semilength = size}, weight (initial path.val)
  let B := PowerSeries.mk fun size =>
    ∑ path : {path : DyckWord // path.semilength = size},
      (weight (initial path.val + 1) - weight (initial path.val))
  let T := PowerSeries.mk fun size =>
    ∑ path : {path : DyckWord // path.semilength = size}, total path.val
  let t := PowerSeries.X * C
  have hsizezero (path : DyckWord) (hsize : path.semilength = 0) : path = 0 := by
    apply DyckWord.toList_eq_nil.mp
    apply List.length_eq_zero_iff.mp
    rw [← DyckWord.two_mul_semilength_eq_length, hsize, mul_zero]
  have hnest (inner outer : DyckWord) :
      initial (inner.nest + outer) = initial inner + 1 := by
    have hguard : ∀ steps : List DyckStep,
        ((steps ++ D :: outer.toList).takeWhile (· == U)) =
          steps.takeWhile (· == U) := by
      intro steps
      induction steps with
      | nil => simp
      | cons step steps ih => cases step <;> simp [ih]
    change (([U] ++ inner.toList ++ [D] ++ outer.toList).takeWhile (· == U)).length = _
    simp [List.append_assoc, hguard, initial]
  obtain ⟨ascent, descent, hascent, hdescent, hparse, hparseDescent⟩ := runFactorization
  have hfactor (factors : List DyckWord) :
      total (ascentWord factors) = weight factors.length +
        ((factors.map total).sum) := by
    have hruns := (hascent factors).2.2.2.2
    rw [(hascent factors).1] at hruns
    dsimp only [total, runs]
    rw [hruns, List.map_append, List.sum_append, List.map_flatMap]
    have hflat : ∀ pieces : List DyckWord,
        (pieces.flatMap (fun path =>
          ((((path.toList.splitOn D).map List.length).filter (· != 0)).map weight))).sum =
          (pieces.map total).sum := by
      intro pieces
      induction pieces with
      | nil => rfl
      | cons path pieces ih => simp [ih, total, runs]
    rw [hflat]
    by_cases hnil : factors = []
    · simp [hnil, hempty]
    · simp [hnil, total, runs]
  have htotal (inner outer : DyckWord) :
      total (inner.nest + outer) = total inner + total outer +
        (weight (initial inner + 1) - weight (initial inner)) := by
    let factors := ascent.symm inner
    have hinner : ascentWord factors = inner := by
      rw [← (hascent factors).1]
      exact ascent.apply_symm_apply inner
    have hlength : initial inner = factors.length := by
      rw [← hinner, ← (hascent factors).1]
      exact (hascent factors).2.2.1
    have happend : ascentWord (factors ++ [outer]) = inner.nest + outer := by
      simp [ascentWord, List.foldl_append, ← hinner]
    rw [← happend, hfactor, ← hinner, hfactor]
    rw [hinner, hlength]
    simp only [List.length_append, List.length_singleton, List.map_append,
      List.map_singleton, List.sum_append, List.sum_singleton]
    ring
  have hsplit (degree : ℕ) :
      ∃ split : (Σ pair : {pair : ℕ × ℕ // pair ∈ Finset.antidiagonal degree},
        {path : DyckWord // path.semilength = pair.val.1} ×
          {path : DyckWord // path.semilength = pair.val.2}) ≃
        {path : DyckWord // path.semilength = degree + 1},
        ∀ choice, (split choice).val = choice.2.1.val.nest + choice.2.2.val := by
    let assemble : (Σ pair : {pair : ℕ × ℕ // pair ∈ Finset.antidiagonal degree},
        {path : DyckWord // path.semilength = pair.val.1} ×
          {path : DyckWord // path.semilength = pair.val.2}) →
        {path : DyckWord // path.semilength = degree + 1} := fun choice =>
      ⟨choice.2.1.val.nest + choice.2.2.val, by
        have hs := Finset.mem_antidiagonal.mp choice.1.property
        simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
          choice.2.1.property, choice.2.2.property]
        omega⟩
    have hinj : Function.Injective assemble := by
      rintro ⟨⟨⟨leftSize, rightSize⟩, hsize⟩,
          ⟨⟨inner, hinner⟩, ⟨outer, houter⟩⟩⟩
        ⟨⟨⟨otherLeft, otherRight⟩, hotherSize⟩,
          ⟨⟨otherInner, hotherInner⟩, ⟨otherOuter, hotherOuter⟩⟩⟩ heq
      have hi := congrArg (fun path => path.val.insidePart) heq
      have ho := congrArg (fun path => path.val.outsidePart) heq
      simp [assemble] at hi ho
      subst otherInner
      subst otherOuter
      have hl := hinner.symm.trans hotherInner
      have hr := houter.symm.trans hotherOuter
      change leftSize = otherLeft at hl
      change rightSize = otherRight at hr
      subst otherLeft
      subst otherRight
      rfl
    have hsurj : Function.Surjective assemble := by
      intro path
      have hne : path.val ≠ 0 := by
        intro heq
        simpa [heq] using path.property
      have hs : (path.val.insidePart.semilength, path.val.outsidePart.semilength) ∈
          Finset.antidiagonal degree := by
        apply Finset.mem_antidiagonal.mpr
        have hs := path.val.semilength_insidePart_add_semilength_outsidePart_add_one hne
        omega
      refine ⟨⟨⟨(_, _), hs⟩,
        ⟨⟨path.val.insidePart, rfl⟩, ⟨path.val.outsidePart, rfl⟩⟩⟩, ?_⟩
      apply Subtype.ext
      exact path.val.nest_insidePart_add_outsidePart hne
    exact ⟨Equiv.ofBijective assemble ⟨hinj, hsurj⟩, fun _ => rfl⟩
  have hcount (degree : ℕ) :
      (∑ _path : {path : DyckWord // path.semilength = degree}, (1 : R)) =
        PowerSeries.coeff degree C := by
    simp [C, DyckWord.card_dyckWord_semilength_eq_catalan]
  have hsum (degree : ℕ) (value : DyckWord → R) :
      (∑ path : {path : DyckWord // path.semilength = degree + 1}, value path.val) =
        ∑ pair ∈ Finset.antidiagonal degree,
          ∑ inner : {path : DyckWord // path.semilength = pair.1},
            ∑ outer : {path : DyckWord // path.semilength = pair.2},
              value (inner.val.nest + outer.val) := by
    obtain ⟨split, hword⟩ := hsplit degree
    rw [← split.sum_comp (fun path => value path.val)]
    simp only [Fintype.sum_sigma, Fintype.sum_prod_type, hword]
    exact Finset.sum_coe_sort (Finset.antidiagonal degree) (fun pair : ℕ × ℕ =>
      ∑ inner : {path : DyckWord // path.semilength = pair.1},
        ∑ outer : {path : DyckWord // path.semilength = pair.2},
          value (inner.val.nest + outer.val))
  have hAzero : PowerSeries.coeff 0 A = 0 := by
    simp only [A, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro path hpath
    rw [hsizezero path.val path.property]
    exact hempty
  have hTzero : PowerSeries.coeff 0 T = 0 := by
    simp only [T, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro path hpath
    rw [hsizezero path.val path.property]
    change (([0].filter (· != 0)).map weight).sum = 0
    rfl
  have hA : A = t * (A + B) := by
    ext degree
    cases degree with
    | zero => simp [t, hAzero]
    | succ degree =>
      rw [show t * (A + B) = PowerSeries.X * (C * (A + B)) by dsimp [t]; ring,
        PowerSeries.coeff_succ_X_mul, mul_comm C, PowerSeries.coeff_mul]
      simp only [A, PowerSeries.coeff_mk]
      rw [hsum degree (fun path => weight (initial path))]
      apply Finset.sum_congr rfl
      intro pair hpair
      simp only [hnest, map_add, B, PowerSeries.coeff_mk, ← Finset.sum_add_distrib]
      simp only [add_sub_cancel]
      rw [← hcount]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [← Finset.mul_sum]
      ring
  have hT : T = 2 * t * T + t * B := by
    ext degree
    cases degree with
    | zero => simp [t, hTzero]
    | succ degree =>
      have heq : 2 * t * T + t * B =
          PowerSeries.X * (T * C + C * T + B * C) := by dsimp [t]; ring
      rw [heq, PowerSeries.coeff_succ_X_mul]
      simp only [map_add, PowerSeries.coeff_mul]
      simp only [T, PowerSeries.coeff_mk]
      change (∑ path : {path : DyckWord // path.semilength = degree + 1},
        total path.val) = _
      rw [hsum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro pair hpair
      simp only [htotal, Finset.sum_add_distrib, B, PowerSeries.coeff_mk]
      rw [← hcount pair.1, ← hcount pair.2]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.sum_sub_distrib, mul_one]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
      ring
  have hC : C ^ 2 * PowerSeries.X + 1 = C := by
    simpa [C] using congrArg (PowerSeries.map (Nat.castRingHom R))
      PowerSeries.catalanSeries_sq_mul_X_add_one
  have hunit : C * (1 - t) = 1 := by
    calc
      C * (1 - t) = C - C ^ 2 * PowerSeries.X := by dsimp [t]; ring
      _ = 1 := by nth_rw 1 [← hC]; ring
  have hmarked : (2 - C) * T = A := by
    have hrelation : (1 - 2 * t) * T = (1 - t) * A := by
      calc
        (1 - 2 * t) * T = T - (2 * t * T + t * B) + t * B := by ring
        _ = t * B := by rw [← hT]; ring
        _ = A - t * A := by nth_rw 1 [hA]; ring
        _ = (1 - t) * A := by ring
    have hfactor : C * (1 - 2 * t) = 2 - C := by
      calc
        C * (1 - 2 * t) = 2 * (C * (1 - t)) - C := by ring
        _ = 2 - C := by rw [hunit]; ring
    calc
      (2 - C) * T = C * ((1 - 2 * t) * T) := by rw [← hfactor]; ring
      _ = C * ((1 - t) * A) := by rw [hrelation]
      _ = A := by rw [← mul_assoc, hunit, one_mul]
  have hreflect (path : DyckWord) :
      (reflection path).semilength = path.semilength ∧
        initial (reflection path) =
          (path.toList.reverse.takeWhile (· == D)).length := by
    let flip : DyckStep → DyckStep | U => D | D => U
    have hword : (reflection path).toList = path.toList.reverse.map flip := rfl
    have hcount : ∀ steps : List DyckStep,
        (steps.map flip).count U = steps.count D := by
      intro steps
      induction steps with
      | nil => rfl
      | cons step steps ih => cases step <;> simp [flip, ih]
    have htake : ∀ steps : List DyckStep,
        ((steps.map flip).takeWhile (· == U)).length =
          (steps.takeWhile (· == D)).length := by
      intro steps
      induction steps with
      | nil => rfl
      | cons step steps ih => cases step <;> simp [flip, ih]
    constructor
    · change ((reflection path).toList.count U) = path.toList.count U
      rw [hword, hcount, List.count_reverse, path.count_U_eq_count_D]
    · dsimp only [initial]
      rw [hword]
      exact htake path.toList.reverse
  have htotalReflect (path : DyckWord) : total (reflection path) =
      (((((path.toList.splitOn U).map List.length).filter (· != 0)).map weight).sum) := by
    dsimp only [total, runs]
    rw [reflection_runs, List.map_reverse, List.sum_reverse]
  have hfixed (size : ℕ) :
      ∃ reflected : {path : DyckWord // path.semilength = size} ≃
        {path : DyckWord // path.semilength = size},
        ∀ path, (reflected path).val = reflection path.val := by
    exact ⟨reflection.subtypeEquiv (fun path => by rw [(hreflect path).1]), fun _ => rfl⟩
  have hTdesc : T = PowerSeries.mk (fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        (((((path.val.toList.splitOn U).map List.length).filter (· != 0)).map
          weight).sum)) := by
    ext size
    obtain ⟨reflected, hword⟩ := hfixed size
    simp only [T, PowerSeries.coeff_mk]
    rw [← reflected.sum_comp (fun path => total path.val)]
    simp only [hword, htotalReflect]
  have hAfinal : A = PowerSeries.mk (fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        weight (path.val.toList.reverse.takeWhile (· == D)).length) := by
    ext size
    obtain ⟨reflected, hword⟩ := hfixed size
    simp only [A, PowerSeries.coeff_mk]
    rw [← reflected.sum_comp (fun path => weight (initial path.val))]
    simp only [hword, (hreflect _).2]
  have hhead (path : DyckWord) : (runs path).getD 0 0 = initial path := by
    let factors := ascent.symm path
    have hword : ascentWord factors = path := by
      rw [← (hascent factors).1]
      exact ascent.apply_symm_apply path
    have hruns := (hascent factors).2.2.2.2
    rw [(hascent factors).1] at hruns
    have hfirst : initial path = factors.length := by
      rw [← hword, ← (hascent factors).1]
      exact (hascent factors).2.2.1
    rw [hfirst]
    dsimp only [runs]
    rw [← hword, hruns]
    cases factors with
    | nil => rfl
    | cons path factors => simp
  have hlast (path : DyckWord) :
      (((((path.toList.splitOn U).map List.length).filter (· != 0)).reverse).getD 0 0) =
        (path.toList.reverse.takeWhile (· == D)).length := by
    have hh := hhead (reflection path)
    dsimp only [runs] at hh
    rwa [reflection_runs, (hreflect path).2] at hh
  have hremove (lengths : List ℕ) :
      ((lengths.dropLast).map weight).sum =
        (lengths.map weight).sum - weight (lengths.reverse.getD 0 0) := by
    induction lengths using List.reverseRecOn with
    | nil => simp [hempty]
    | append_singleton earlier last _ => simp
  have hH : PowerSeries.mk (fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        (((((path.val.toList.splitOn U).map List.length).filter (· != 0)).dropLast.map
          weight).sum)) = T - A := by
    rw [hTdesc, hAfinal]
    ext size
    simp only [PowerSeries.coeff_mk, map_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro path hpath
    rw [hremove, hlast]
  change (2 - C) * _ = (C - 1) * _
  rw [hH, ← hAfinal, mul_sub, hmarked]
  ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq152MarkedSeries
