/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152PenultimateSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152PenultimateSeries
   mirror-E: none(waiver:penultimate-dyck-descent-counting)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: The penultimate Dyck descent has the final-descent series times XC divided by 1-X. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Factor
import D5.S3.Combinatorics.InversionSeq.InversionSeq152Reflection
import Mathlib.RingTheory.PowerSeries.Catalan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152PenultimateSeries

open DyckStep
open scoped BigOperators
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse
open D5.S3.Combinatorics.InversionSeq.InversionSeq152Factor
open D5.S3.Combinatorics.InversionSeq.InversionSeq152Reflection

set_option maxHeartbeats 2400000 in
theorem penultimate_descent_enumeration {R : Type*} [CommRing R]
    (weight : ℕ → R) (hempty : weight 0 = 0) :
    let catalan := PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries
    let penultimate := PowerSeries.mk fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        weight (((((path.val.toList.splitOn U).map List.length).filter
          (· != 0)).reverse).getD 1 0)
    let final := PowerSeries.mk fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        weight (path.val.toList.reverse.takeWhile (· == D)).length
    (1 - PowerSeries.X) * penultimate = PowerSeries.X * catalan * final := by
  classical
  let C := PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries
  let initial (path : DyckWord) := (path.toList.takeWhile (· == U)).length
  let runs (path : DyckWord) :=
    ((path.toList.splitOn D).map List.length).filter (· != 0)
  let second (path : DyckWord) := (runs path).getD 1 0
  let A := PowerSeries.mk fun size =>
    ∑ path : {path : DyckWord // path.semilength = size}, weight (initial path.val)
  let J := PowerSeries.mk fun size =>
    ∑ path : {path : DyckWord // path.semilength = size}, weight (second path.val)
  let geometric : PowerSeries R := PowerSeries.mk fun _ => 1
  let t := PowerSeries.X * C
  obtain ⟨ascent, descent, hascent, hdescent, hparse, hparseDescent⟩ := runFactorization
  have hbuild (path : DyckWord) : ascentWord (ascent.symm path) = path := by
    rw [← (hascent _).1]
    exact ascent.apply_symm_apply path
  have hrun (factors : List DyckWord) :
      runs (ascentWord factors) =
        (if factors = [] then [] else [factors.length]) ++ factors.flatMap runs := by
    have hh := (hascent factors).2.2.2.2
    rwa [(hascent factors).1] at hh
  have hinitial (factors : List DyckWord) :
      initial (ascentWord factors) = factors.length := by
    rw [← (hascent factors).1]
    exact (hascent factors).2.2.1
  have hsize (factors : List DyckWord) :
      (ascentWord factors).semilength =
        factors.length + (factors.map DyckWord.semilength).sum := by
    rw [← (hascent factors).1]
    exact (hascent factors).2.2.2.1
  have hrunzero (path : DyckWord) : runs path = [] ↔ path = 0 := by
    constructor
    · intro h
      rw [← hbuild path, hrun] at h
      have hfirst := (List.append_eq_nil_iff.mp h).1
      have hfactors : ascent.symm path = [] := by
        by_contra hn
        simp [hn] at hfirst
      rw [← hbuild path, hfactors]
      rfl
    · rintro rfl
      rfl
  have hhead (path : DyckWord) : (runs path).getD 0 0 = initial path := by
    rw [← hbuild path, hrun, hinitial]
    cases ascent.symm path with
    | nil => rfl
    | cons head tail => simp
  let mountain (size : ℕ) := ascentWord (List.replicate size (0 : DyckWord))
  have hmountainSize (size : ℕ) : (mountain size).semilength = size := by
    simp [mountain, hsize, List.map_replicate]
  have hmountainRuns (size : ℕ) : (runs (mountain size)).length ≤ 1 := by
    have hflat : (List.replicate size (0 : DyckWord)).flatMap runs = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro path hpath
      obtain ⟨hpositive, rfl⟩ := List.mem_replicate.mp hpath
      rfl
    rw [show mountain size = ascentWord (List.replicate size 0) from rfl, hrun, hflat]
    simp
    split_ifs <;> simp
  have hsingle (path : DyckWord) :
      (runs path).length ≤ 1 ↔ path = mountain path.semilength := by
    constructor
    · intro h
      let factors := ascent.symm path
      have hword : ascentWord factors = path := hbuild path
      have hflat : factors.flatMap runs = [] := by
        rw [← hword, hrun] at h
        by_cases hn : factors = []
        · simp [hn]
        · simp only [hn, ite_false, List.length_append, List.length_singleton] at h
          apply List.length_eq_zero_iff.mp
          omega
      have hall : ∀ piece ∈ factors, piece = 0 := by
        intro piece hpiece
        exact (hrunzero piece).mp (List.flatMap_eq_nil_iff.mp hflat piece hpiece)
      have hrep : factors = List.replicate factors.length 0 :=
        List.eq_replicate_length.mpr hall
      have hs : path.semilength = factors.length := by
        rw [← hword, hsize]
        have hsum : (factors.map DyckWord.semilength).sum = 0 := by
          rw [hrep]
          simp
        omega
      rw [hs]
      change path = ascentWord (List.replicate factors.length 0)
      rw [← hword]
      exact congrArg ascentWord hrep
    · intro h
      rw [h]
      exact hmountainRuns _
  have hsingleCount (size : ℕ) :
      (∑ path : {path : DyckWord // path.semilength = size},
        if (runs path.val).length ≤ 1 then (1 : R) else 0) = 1 := by
    let peak : {path : DyckWord // path.semilength = size} :=
      ⟨mountain size, hmountainSize size⟩
    rw [Fintype.sum_eq_single peak]
    · simp [peak, hmountainRuns]
    · intro path hne
      have hn : ¬ (runs path.val).length ≤ 1 := by
        intro hsmall
        apply hne
        apply Subtype.ext
        rw [(hsingle path.val).mp hsmall, path.property]
      simp [hn]
  have hsecond (inner outer : DyckWord) :
      weight (second (inner.nest + outer)) = weight (second inner) +
        (if (runs inner).length ≤ 1 then weight (initial outer) else 0) := by
    let factors := ascent.symm inner
    have hword : ascentWord factors = inner := hbuild inner
    have happend : ascentWord (factors ++ [outer]) = inner.nest + outer := by
      simp [ascentWord, List.foldl_append, ← hword]
    have hnew : runs (inner.nest + outer) =
        (factors.length + 1) :: (factors.flatMap runs ++ runs outer) := by
      rw [← happend, hrun]
      simp
    have hold : runs inner =
        (if factors = [] then [] else [factors.length]) ++ factors.flatMap runs := by
      rw [← hword, hrun]
    dsimp only [second]
    rw [hnew, hold]
    cases hf : factors.flatMap runs with
    | nil =>
      by_cases hn : factors = []
      · simp [hn, hempty]
        exact congrArg weight (hhead outer)
      · simp [hn, hempty]
        exact congrArg weight (hhead outer)
    | cons head tail =>
      have hn : factors ≠ [] := by intro hn; simp [hn] at hf
      simp [hn]
  have hsizezero (path : DyckWord) (hsize : path.semilength = 0) : path = 0 := by
    apply DyckWord.toList_eq_nil.mp
    apply List.length_eq_zero_iff.mp
    rw [← DyckWord.two_mul_semilength_eq_length, hsize, mul_zero]
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
  have hJzero : PowerSeries.coeff 0 J = 0 := by
    simp only [J, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro path hpath
    rw [hsizezero path.val path.property]
    exact hempty
  have hJ : J = t * J + PowerSeries.X * (geometric * A) := by
    ext degree
    cases degree with
    | zero => simp [t, hJzero]
    | succ degree =>
      have heq : t * J + PowerSeries.X * (geometric * A) =
          PowerSeries.X * (J * C + geometric * A) := by dsimp [t]; ring
      rw [heq, PowerSeries.coeff_succ_X_mul]
      simp only [map_add, PowerSeries.coeff_mul, J, PowerSeries.coeff_mk]
      rw [hsum degree (fun path => weight (second path)), ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro pair hpair
      simp only [hsecond, Finset.sum_add_distrib]
      have hindicator (inner : {path : DyckWord // path.semilength = pair.1}) :
          (∑ outer : {path : DyckWord // path.semilength = pair.2},
            if (runs inner.val).length ≤ 1 then weight (initial outer.val) else 0) =
          (if (runs inner.val).length ≤ 1 then (1 : R) else 0) *
            PowerSeries.coeff pair.2 A := by
        by_cases hn : (runs inner.val).length ≤ 1
        · simp [hn, A]
        · simp [hn]
      simp only [hindicator]
      rw [← Finset.sum_mul, hsingleCount, one_mul, ← hcount]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        geometric, PowerSeries.coeff_mk, one_mul]
      rw [← Finset.mul_sum]
      ring
  have hU : (1 - PowerSeries.X) * geometric = 1 := by
    ext degree
    cases degree with
    | zero => simp [geometric]
    | succ degree =>
      rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul]
      simp [geometric]
  have hC : C ^ 2 * PowerSeries.X + 1 = C := by
    simpa [C] using congrArg (PowerSeries.map (Nat.castRingHom R))
      PowerSeries.catalanSeries_sq_mul_X_add_one
  have hunit : C * (1 - t) = 1 := by
    calc
      C * (1 - t) = C - C ^ 2 * PowerSeries.X := by dsimp [t]; ring
      _ = 1 := by nth_rw 1 [← hC]; ring
  have hmain : (1 - PowerSeries.X) * J = t * A := by
    have hrelation : (1 - t) * J = PowerSeries.X * (geometric * A) := by
      calc
        (1 - t) * J = J - t * J := by ring
        _ = PowerSeries.X * (geometric * A) := by nth_rw 1 [hJ]; ring
    calc
      (1 - PowerSeries.X) * J = C * ((1 - PowerSeries.X) * ((1 - t) * J)) := by
        rw [show C * ((1 - PowerSeries.X) * ((1 - t) * J)) =
          (C * (1 - t)) * ((1 - PowerSeries.X) * J) by ring, hunit, one_mul]
      _ = C * ((1 - PowerSeries.X) * (PowerSeries.X * (geometric * A))) := by
        rw [hrelation]
      _ = t * A := by
        rw [show C * ((1 - PowerSeries.X) * (PowerSeries.X * (geometric * A))) =
          t * (((1 - PowerSeries.X) * geometric) * A) by dsimp [t]; ring, hU, one_mul]
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
  have hfixed (size : ℕ) :
      ∃ reflected : {path : DyckWord // path.semilength = size} ≃
        {path : DyckWord // path.semilength = size},
        ∀ path, (reflected path).val = reflection path.val := by
    exact ⟨reflection.subtypeEquiv (fun path => by rw [(hreflect path).1]), fun _ => rfl⟩
  have hJdesc : J = PowerSeries.mk (fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        weight (((((path.val.toList.splitOn U).map List.length).filter
          (· != 0)).reverse).getD 1 0)) := by
    ext size
    obtain ⟨reflected, hword⟩ := hfixed size
    simp only [J, PowerSeries.coeff_mk]
    rw [← reflected.sum_comp (fun path => weight (second path.val))]
    simp only [hword, second, runs, reflection_runs]
  have hAfinal : A = PowerSeries.mk (fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        weight (path.val.toList.reverse.takeWhile (· == D)).length) := by
    ext size
    obtain ⟨reflected, hword⟩ := hfixed size
    simp only [A, PowerSeries.coeff_mk]
    rw [← reflected.sum_comp (fun path => weight (initial path.val))]
    simp only [hword, (hreflect _).2]
  change (1 - PowerSeries.X) * _ = t * _
  rw [← hJdesc, ← hAfinal]
  exact hmain

end D5.S3.Combinatorics.InversionSeq.InversionSeq152PenultimateSeries
