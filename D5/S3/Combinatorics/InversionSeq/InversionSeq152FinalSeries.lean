/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152FinalSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152FinalSeries
   mirror-E: none(waiver:dyck-final-descent-enumeration)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: The height-refined Dyck series is the geometric series in q times XC. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Factor
import Mathlib.RingTheory.PowerSeries.Catalan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152FinalSeries

open DyckStep
open scoped BigOperators
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse

set_option maxHeartbeats 1600000 in
theorem final_descent_enumeration {R : Type*} [CommRing R] (q : R) :
    let catalan := PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries
    let heights := PowerSeries.mk fun size =>
      ∑ path : {path : DyckWord // path.semilength = size},
        q ^ (path.val.toList.reverse.takeWhile (· == D)).length
    (1 - PowerSeries.C q * PowerSeries.X * catalan) * heights = 1 := by
  classical
  have hfixed (runs size : ℕ) :
      (∑ path : {path : DyckWord // path.semilength = size},
        if (path.val.toList.reverse.takeWhile (· == D)).length = runs then 1 else 0) =
        PowerSeries.coeff size
          ((PowerSeries.X * PowerSeries.catalanSeries) ^ runs) := by
    classical
    let initial (path : DyckWord) := (path.toList.takeWhile (· == U)).length
    let count (runs size : ℕ) : ℕ :=
      ∑ path : {path : DyckWord // path.semilength = size},
        if initial path.val = runs then 1 else 0
    have hsizezero (path : DyckWord) (hsize : path.semilength = 0) : path = 0 := by
      apply DyckWord.toList_eq_nil.mp
      apply List.length_eq_zero_iff.mp
      rw [← DyckWord.two_mul_semilength_eq_length, hsize, mul_zero]
    have hzero (path : DyckWord) : initial path = 0 ↔ path = 0 := by
      constructor
      · intro h
        by_contra hne
        have hlist := DyckWord.toList_ne_nil.mpr hne
        obtain ⟨step, rest, hword⟩ := List.exists_cons_of_ne_nil hlist
        have hhead := path.head_eq_U hlist
        simp only [hword, List.head_cons] at hhead
        subst step
        simp [initial, hword] at h
      · rintro rfl
        rfl
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
    have hrecurrence (runs degree : ℕ) :
        count (runs + 1) (degree + 1) =
          ∑ pair ∈ Finset.antidiagonal degree, count runs pair.1 * catalan pair.2 := by
      obtain ⟨split, hword⟩ := hsplit degree
      have hsum := (split.sum_comp (fun path =>
        if initial path.val = runs + 1 then (1 : ℕ) else 0)).symm
      dsimp only [count]
      rw [hsum]
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      simp only [hword, hnest, Nat.add_right_cancel_iff]
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ,
        DyckWord.card_dyckWord_semilength_eq_catalan, mul_comm (catalan _) (ite _ _ _),
        ← Finset.sum_mul]
      change (∑ pair : {pair : ℕ × ℕ // pair ∈ Finset.antidiagonal degree},
        count runs pair.val.1 * catalan pair.val.2) = _
      simpa only [count] using Finset.sum_coe_sort (Finset.antidiagonal degree)
        (fun pair => count runs pair.1 * catalan pair.2)
    have hbase (degree : ℕ) : count 0 degree = if degree = 0 then 1 else 0 := by
      simp only [count, hzero]
      by_cases hd : degree = 0
      · subst degree
        have hall : ∀ path : {path : DyckWord // path.semilength = 0}, path.val = 0 := by
          intro path
          exact hsizezero path.val path.property
        simp [hall, DyckWord.card_dyckWord_semilength_eq_catalan]
      · have hall : ∀ path : {path : DyckWord // path.semilength = degree},
            path.val ≠ 0 := by
          intro path heq
          exact hd (by simpa [heq] using path.property.symm)
        simp [hd, hall]
    have hcoeff : ∀ runs degree,
        count runs degree = PowerSeries.coeff degree
          ((PowerSeries.X * PowerSeries.catalanSeries) ^ runs) := by
      intro runs
      induction runs with
      | zero => intro degree; simp [hbase]
      | succ runs ih =>
        intro degree
        cases degree with
        | zero =>
          have hall : ∀ path : {path : DyckWord // path.semilength = 0},
              initial path.val ≠ runs + 1 := by
            intro path
            rw [hsizezero path.val path.property]
            change (0 : ℕ) ≠ runs + 1
            omega
          simp [count, hall, pow_succ]
        | succ degree =>
          rw [hrecurrence, pow_succ]
          rw [mul_left_comm _ PowerSeries.X PowerSeries.catalanSeries,
            PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
          apply Finset.sum_congr rfl
          intro pair hpair
          simp [ih]
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
    let reflected : {path : DyckWord // path.semilength = size} ≃
        {path : DyckWord // path.semilength = size} :=
      reflection.subtypeEquiv (fun path => by rw [(hreflect path).1])
    calc
      _ = ∑ path : {path : DyckWord // path.semilength = size},
          if initial (reflected path).val = runs then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro path hpath
        rw [show (reflected path).val = reflection path.val from rfl, (hreflect path.val).2]
      _ = count runs size := reflected.sum_comp (fun path =>
          if initial path.val = runs then (1 : ℕ) else 0)
      _ = _ := hcoeff runs size
  let catalan := PowerSeries.map (Nat.castRingHom R) PowerSeries.catalanSeries
  let t := PowerSeries.X * catalan
  let z := PowerSeries.C q * t
  let series := PowerSeries.mk fun size =>
    ∑ path : {path : DyckWord // path.semilength = size},
      q ^ (path.val.toList.reverse.takeWhile (· == D)).length
  have hheight (path : DyckWord) :
      (path.toList.reverse.takeWhile (· == D)).length ≤ path.semilength := by
    have hall := List.all_takeWhile (l := path.toList.reverse) (p := (· == D))
    have heq : (path.toList.reverse.takeWhile (· == D)).count D =
        (path.toList.reverse.takeWhile (· == D)).length := by
      apply List.count_eq_length.mpr
      intro value hv
      have hh := (List.all_eq_true.mp hall) value hv
      exact (beq_iff_eq.mp hh).symm
    rw [← heq, DyckWord.semilength_eq_count_D]
    simpa only [List.count_reverse] using
      (List.takeWhile_sublist (l := path.toList.reverse) (· == D)).count_le D
  have hcoeff (runs size : ℕ) : PowerSeries.coeff size (z ^ runs) =
      q ^ runs * (PowerSeries.coeff (R := ℕ) size
        ((PowerSeries.X * PowerSeries.catalanSeries) ^ runs) : R) := by
    have heq : z ^ runs = PowerSeries.C (q ^ runs) *
        PowerSeries.map (Nat.castRingHom R)
          ((PowerSeries.X * PowerSeries.catalanSeries) ^ runs) := by
      simp only [z, t, catalan, mul_pow, map_pow, map_mul, PowerSeries.map_X]
    rw [heq, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
    rfl
  have hweighted (size : ℕ) : PowerSeries.coeff size series =
      ∑ runs ∈ Finset.range (size + 1), PowerSeries.coeff size (z ^ runs) := by
    simp only [series, PowerSeries.coeff_mk]
    simp_rw [hcoeff, ← hfixed, Nat.cast_sum]
    simp_rw [Finset.mul_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro path _
    have hb : (path.val.toList.reverse.takeWhile (· == D)).length ∈
        Finset.range (size + 1) := Finset.mem_range.mpr (by
          have hh := hheight path.val
          rw [path.property] at hh
          omega)
    simpa only [eq_comm, Finset.sum_ite_eq', if_pos hb]
  have hvanish (degree runs : ℕ) (hlt : degree < runs) :
      PowerSeries.coeff degree (z ^ runs) = 0 := by
    have heq : z = PowerSeries.X * (PowerSeries.C q * catalan) := by
      dsimp [z, t]
      ring
    rw [heq, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hstable (degree bound : ℕ) (hle : degree ≤ bound) :
      PowerSeries.coeff degree series =
        PowerSeries.coeff degree (∑ runs ∈ Finset.range (bound + 1), z ^ runs) := by
    rw [hweighted, map_sum]
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro runs hr hn
      apply hvanish
      simp only [Finset.mem_range] at hn
      omega
  have hidentity : (1 - z) * series = 1 := by
    ext degree
    let truncated := ∑ runs ∈ Finset.range (degree + 1), z ^ runs
    have heq : PowerSeries.coeff degree ((1 - z) * series) =
        PowerSeries.coeff degree ((1 - z) * truncated) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro pair hp
      have hs := Finset.mem_antidiagonal.mp hp
      rw [hstable pair.2 degree (by omega)]
    rw [heq]
    dsimp only [truncated]
    have htelescope : (1 - z) * (∑ runs ∈ Finset.range (degree + 1), z ^ runs) =
        1 - z ^ (degree + 1) := by
      rw [Finset.mul_sum]
      calc
        _ = ∑ runs ∈ Finset.range (degree + 1), (z ^ runs - z ^ (runs + 1)) := by
          apply Finset.sum_congr rfl
          intro runs _
          rw [pow_succ]
          ring
        _ = _ := by
          simpa only [pow_zero] using
            Finset.sum_range_sub' (fun runs => z ^ runs) (degree + 1)
    rw [htelescope, map_sub, hvanish degree (degree + 1) (by omega), sub_zero]
  simpa only [z, t, mul_assoc] using hidentity

end D5.S3.Combinatorics.InversionSeq.InversionSeq152FinalSeries
