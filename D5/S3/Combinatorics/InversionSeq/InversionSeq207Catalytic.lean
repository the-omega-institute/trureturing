/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Catalytic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Catalytic
   mirror-E: none(waiver:formal-signed-catalytic-equations)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Exp]
   utility: none
   digest: Weighted root paths give formal catalytic equations and exact signed scalar counts. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Endpoints
import Mathlib.RingTheory.PowerSeries.Exp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Catalytic

open InversionSeq207Endpoints InversionSeq207LeftSigned InversionSeq207RightReduction

noncomputable def forwardSeries {R : Type*} [CommRing R] (isLeft : Bool) (x y : R) :
    PowerSeries R :=
  PowerSeries.mk fun depth =>
    Finsupp.linearCombination ℤ (fun label : ℕ × ℕ => x ^ label.1 * y ^ label.2)
      (walkEndpoints isLeft depth)

noncomputable def forwardMoment {R : Type*} [CommRing R] (x : R) : PowerSeries R :=
  PowerSeries.mk fun depth =>
    Finsupp.linearCombination ℤ (fun label : ℕ × ℕ => (label.2 : R) * x ^ label.1)
      (walkEndpoints false depth)
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

universe u

theorem forward_series_equations {R : Type u} [CommRing R] [IsDomain R]
    (isLeft : Bool) (depth : ℕ) :
    ((walkEndpoints isLeft depth).sum (fun _ weight => weight) =
      (if isLeft then leftSignedCount depth 0 0 else rightSignedCount depth 0 0) ∧
    (∀ terminal : ℕ × ℕ, (walkEndpoints isLeft depth) terminal ≠ 0 →
      terminal.1 + terminal.2 ≤ depth) ∧
    (isLeft = false → depth ≠ 0 → ∀ terminal : ℕ × ℕ,
      (walkEndpoints isLeft depth) terminal ≠ 0 → 0 < terminal.1) ∧
    (∀ x y : R,
      let full := forwardSeries isLeft x y
      let boundary := forwardSeries isLeft x 1
      if isLeft then
        PowerSeries.C ((1 - y) * (x - y)) * (full - 1) = PowerSeries.X *
          (PowerSeries.C (x * (x - y)) * (boundary - full) +
            PowerSeries.C (1 - y) *
              (PowerSeries.C x * full - PowerSeries.C y * forwardSeries isLeft y y) +
            PowerSeries.C ((1 - y) * (x - y)) *
              (PowerSeries.C x * boundary - forwardSeries isLeft 1 1))
      else
        PowerSeries.C ((1 - y) * (x - y)) * (full - 1) = PowerSeries.X *
          (PowerSeries.C ((1 - y) * (x - y)) *
              (PowerSeries.C x * boundary + PowerSeries.C (1 - x) * forwardMoment x) +
            PowerSeries.C (x * y * (1 - y)) *
              (boundary - forwardSeries isLeft y 1) +
            PowerSeries.C (x * y * (x - y)) * (boundary - full))) ∧
    (isLeft = false → forwardSeries isLeft (0 : R) 1 = 1) ∧
    (isLeft = false → ∀ x : R,
      PowerSeries.C (x - 1) * (forwardSeries isLeft x 1 - 1) = PowerSeries.X *
        (PowerSeries.C (x - 1) * forwardMoment x +
          PowerSeries.C (x ^ 2) * forwardSeries isLeft x 1 -
          PowerSeries.C x * forwardSeries isLeft 1 1))) ∧
    (isLeft = false → ∀ x : R,
      letI : UniformSpace R := ⊥
      letI : DiscreteUniformity R := ⟨rfl⟩
      let tau : PowerSeries R := PowerSeries.mk fun degree => x ^ degree
      let substituted := PowerSeries.eval₂ (RingHom.id (PowerSeries R)) PowerSeries.X
        (forwardSeries false tau 1)
      PowerSeries.X * tau * substituted =
        (1 - PowerSeries.C x + PowerSeries.X * PowerSeries.C x +
          PowerSeries.X * PowerSeries.C (x ^ 2)) * forwardSeries false x 1 +
        (PowerSeries.C x - tau) * (1 - PowerSeries.X * forwardSeries false 1 1)
    ) := by
  have hall {S : Type u} [CommRing S] (isLeft : Bool) (depth : ℕ) :
      (walkEndpoints isLeft depth).sum (fun _ weight => weight) =
        (if isLeft then leftSignedCount depth 0 0 else rightSignedCount depth 0 0) ∧
      (∀ terminal : ℕ × ℕ, (walkEndpoints isLeft depth) terminal ≠ 0 →
        terminal.1 + terminal.2 ≤ depth) ∧
      (isLeft = false → depth ≠ 0 → ∀ terminal : ℕ × ℕ,
        (walkEndpoints isLeft depth) terminal ≠ 0 → 0 < terminal.1) ∧
      (∀ x y : S,
        let full := forwardSeries isLeft x y
        let boundary := forwardSeries isLeft x 1
        if isLeft then
          PowerSeries.C ((1 - y) * (x - y)) * (full - 1) = PowerSeries.X *
            (PowerSeries.C (x * (x - y)) * (boundary - full) +
              PowerSeries.C (1 - y) *
                (PowerSeries.C x * full - PowerSeries.C y * forwardSeries isLeft y y) +
              PowerSeries.C ((1 - y) * (x - y)) *
                (PowerSeries.C x * boundary - forwardSeries isLeft 1 1))
        else
          PowerSeries.C ((1 - y) * (x - y)) * (full - 1) = PowerSeries.X *
            (PowerSeries.C ((1 - y) * (x - y)) *
                (PowerSeries.C x * boundary + PowerSeries.C (1 - x) * forwardMoment x) +
              PowerSeries.C (x * y * (1 - y)) *
                (boundary - forwardSeries isLeft y 1) +
              PowerSeries.C (x * y * (x - y)) * (boundary - full))) ∧
      (isLeft = false → forwardSeries isLeft (0 : S) 1 = 1) ∧
      (isLeft = false → ∀ x : S,
        PowerSeries.C (x - 1) * (forwardSeries isLeft x 1 - 1) = PowerSeries.X *
          (PowerSeries.C (x - 1) * forwardMoment x +
            PowerSeries.C (x ^ 2) * forwardSeries isLeft x 1 -
            PowerSeries.C x * forwardSeries isLeft 1 1)) := by
    classical
    let count (length : ℕ) (label : ℕ × ℕ) : ℤ :=
      if isLeft then leftSignedCount length label.1 label.2
      else rightSignedCount length label.1 label.2
    have hdual (length : ℕ) (label : ℕ × ℕ) :
        Finsupp.linearCombination ℤ (count length) (walkStep isLeft label) =
          count (length + 1) label := by
      cases isLeft with
      | false =>
          simp [count, walkStep, rightSignedCount, Finsupp.linearCombination_single]
          ring
      | true =>
          simp [count, walkStep, leftSignedCount, Finsupp.linearCombination_single]
    have hpairing (steps remaining : ℕ) :
        Finsupp.linearCombination ℤ (count remaining) (walkEndpoints isLeft steps) =
          count (steps + remaining) (0, 0) := by
      induction steps generalizing remaining with
      | zero => simp [walkEndpoints, Finsupp.linearCombination_single]
      | succ steps ih =>
          simp only [walkEndpoints]
          rw [Finsupp.apply_linearCombination]
          have hfunctions : (Finsupp.linearCombination ℤ (count remaining)) ∘ walkStep isLeft =
              count (remaining + 1) := by
            funext label
            exact hdual remaining label
          rw [hfunctions, ih]
          congr 1
          omega
    have hstepBound (label terminal : ℕ × ℕ)
        (hlarge : label.1 + label.2 + 1 < terminal.1 + terminal.2) :
        walkStep isLeft label terminal = 0 := by
      have hsingle (target : ℕ × ℕ) (weight : ℤ)
          (htarget : target.1 + target.2 ≤ label.1 + label.2 + 1) :
          Finsupp.single target weight terminal = 0 := by
        apply Finsupp.single_eq_of_ne
        intro heq
        subst terminal
        omega
      have hlow : (∑ index ∈ Finset.range label.2,
          Finsupp.single (label.1 + 1, index) (1 : ℤ)) terminal = 0 := by
        rw [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro index hi
        have hiBound := Finset.mem_range.mp hi
        exact hsingle _ _ (by dsimp; omega)
      have hhigh : (∑ distance ∈ Finset.range (label.1 + 1),
          Finsupp.single (label.1 - distance, label.2 + distance) (1 : ℤ)) terminal = 0 := by
        rw [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro distance hd
        have hdBound := Finset.mem_range.mp hd
        exact hsingle _ _ (by dsimp; omega)
      have hrightHigh : (∑ distance ∈ Finset.range label.1,
          Finsupp.single (label.1 - distance, distance + 1) (1 : ℤ)) terminal = 0 := by
        rw [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro distance hd
        have hdBound := Finset.mem_range.mp hd
        exact hsingle _ _ (by dsimp; omega)
      have hrightLow : (∑ distance ∈ Finset.range label.2,
          Finsupp.single (label.1 + 1, distance + 1) (1 : ℤ)) terminal = 0 := by
        rw [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro distance hd
        have hdBound := Finset.mem_range.mp hd
        exact hsingle _ _ (by dsimp; omega)
      cases isLeft <;>
        simp only [walkStep, Bool.false_eq_true, if_false, if_true, Finsupp.add_apply,
          Finsupp.sub_apply, hlow, hhigh, hrightHigh, hrightLow,
          hsingle (label.1 + 1, 0) _ (by dsimp; omega),
          hsingle (label.1, 0) _ (by dsimp; omega), hsingle (0, 0) _ (by simp)] <;> ring
    have hbound (steps : ℕ) (terminal : ℕ × ℕ)
        (hlarge : steps < terminal.1 + terminal.2) :
        walkEndpoints isLeft steps terminal = 0 := by
      induction steps generalizing terminal with
      | zero =>
          simp only [walkEndpoints]
          apply Finsupp.single_eq_of_ne
          intro heq
          subst terminal
          simp at hlarge
      | succ steps ih =>
          rw [walkEndpoints, Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
          apply Finset.sum_eq_zero
          intro label hlabel
          have hnonzero := Finsupp.mem_support_iff.mp hlabel
          have hlabelBound : label.1 + label.2 ≤ steps := by
            by_contra hnot
            exact hnonzero (ih label (by omega))
          rw [Finsupp.smul_apply, hstepBound label terminal (by omega)]
          simp
    have hpositiveStep (label terminal : ℕ × ℕ) (hlabel : 0 < label.1)
        (hzero : terminal.1 = 0) : walkStep false label terminal = 0 := by
      have hsingle (target : ℕ × ℕ) (weight : ℤ) (htarget : 0 < target.1) :
          Finsupp.single target weight terminal = 0 := by
        apply Finsupp.single_eq_of_ne
        intro heq
        have := congrArg Prod.fst heq
        omega
      have hhigh : (∑ distance ∈ Finset.range label.1,
          Finsupp.single (label.1 - distance, distance + 1) (1 : ℤ)) terminal = 0 := by
        rw [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro distance hd
        have hdBound := Finset.mem_range.mp hd
        exact hsingle _ _ (by dsimp; omega)
      have hlow : (∑ distance ∈ Finset.range label.2,
          Finsupp.single (label.1 + 1, distance + 1) (1 : ℤ)) terminal = 0 := by
        rw [Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro distance hd
        exact hsingle _ _ (by simp)
      simp only [walkStep, Bool.false_eq_true, if_false, Finsupp.add_apply,
        hsingle (label.1 + 1, 0) _ (by simp), hsingle (label.1, 0) _ hlabel, hhigh, hlow]
      ring
    have hpositive (steps : ℕ) (hsteps : steps ≠ 0) (terminal : ℕ × ℕ)
        (hzero : terminal.1 = 0) : walkEndpoints false steps terminal = 0 := by
      induction steps generalizing terminal with
      | zero => contradiction
      | succ steps ih =>
          cases steps with
          | zero =>
              have hfirst : walkEndpoints false 1 = Finsupp.single (1, 0) 1 := by
                simp [walkEndpoints, walkStep, Finsupp.linearCombination_single]
              rw [hfirst]
              apply Finsupp.single_eq_of_ne
              intro heq
              have := congrArg Prod.fst heq
              omega
          | succ steps =>
              rw [walkEndpoints, Finsupp.linearCombination_apply, Finsupp.sum_apply, Finsupp.sum]
              apply Finset.sum_eq_zero
              intro label hlabel
              have hnonzero := Finsupp.mem_support_iff.mp hlabel
              have hlabelPos : 0 < label.1 := by
                by_contra hnot
                exact hnonzero (ih (by omega) label (by omega))
              rw [Finsupp.smul_apply, hpositiveStep label terminal hlabelPos hzero]
              simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have htotal := hpairing depth 0
      simpa [count, leftSignedCount, rightSignedCount, Finsupp.linearCombination_apply] using htotal
    · intro terminal hnonzero
      by_contra hnot
      exact hnonzero (hbound depth terminal (by omega))
    · intro hright hdepth terminal hnonzero
      subst isLeft
      by_contra hnot
      exact hnonzero (hpositive depth hdepth terminal (by omega))
    · intro x y
      have hscale (scalar : S) (family : (ℕ × ℕ) → S) (weights : (ℕ × ℕ) →₀ ℤ) :
          Finsupp.linearCombination ℤ (fun label => scalar * family label) weights =
            scalar * Finsupp.linearCombination ℤ family weights := by
        simp only [Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro label hlabel
        ring
      have hadd (first second : (ℕ × ℕ) → S) (weights : (ℕ × ℕ) →₀ ℤ) :
          Finsupp.linearCombination ℤ (fun label => first label + second label) weights =
            Finsupp.linearCombination ℤ first weights +
              Finsupp.linearCombination ℤ second weights := by
        simp [Finsupp.linearCombination_apply, Finsupp.sum, smul_add,
          Finset.sum_add_distrib]
      have hsub (first second : (ℕ × ℕ) → S) (weights : (ℕ × ℕ) →₀ ℤ) :
          Finsupp.linearCombination ℤ (fun label => first label - second label) weights =
            Finsupp.linearCombination ℤ first weights -
              Finsupp.linearCombination ℤ second weights := by
        simp [Finsupp.linearCombination_apply, Finsupp.sum, smul_sub,
          Finset.sum_sub_distrib]
      have hleft (label : ℕ × ℕ) :
          (1 - y) * (x - y) *
              Finsupp.linearCombination ℤ (fun target : ℕ × ℕ =>
                x ^ target.1 * y ^ target.2) (walkStep true label) =
            x * (x - y) * (x ^ label.1 - x ^ label.1 * y ^ label.2) +
              (1 - y) * (x * (x ^ label.1 * y ^ label.2) -
                y * (y ^ label.1 * y ^ label.2)) +
              (1 - y) * (x - y) * (x * x ^ label.1 - 1) := by
        classical
        have hlow := mul_neg_geom_sum y label.2
        have hhigh : (x - y) *
            (∑ index ∈ Finset.range (label.1 + 1), x ^ (label.1 - index) * y ^ index) =
              x ^ (label.1 + 1) - y ^ (label.1 + 1) := by
          have h := geom_sum₂_mul y x (label.1 + 1)
          simp only [Nat.add_sub_cancel] at h
          simp_rw [mul_comm (y ^ _) (x ^ _)] at h
          linear_combination -h
        have hsum : (∑ index ∈ Finset.range (label.1 + 1),
            x ^ (label.1 - index) * y ^ (label.2 + index)) =
              y ^ label.2 * ∑ index ∈ Finset.range (label.1 + 1),
                x ^ (label.1 - index) * y ^ index := by
          simp only [pow_add, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index hi
          ring
        simp only [walkStep, if_true, map_sub, map_add, map_sum,
          Finsupp.linearCombination_single, one_smul, pow_zero, mul_one]
        rw [← Finset.mul_sum, hsum]
        linear_combination x ^ (label.1 + 1) * (x - y) * hlow +
          (1 - y) * y ^ label.2 * hhigh
      
      have hright (label : ℕ × ℕ) :
          (1 - y) * (x - y) *
              Finsupp.linearCombination ℤ (fun target : ℕ × ℕ =>
                x ^ target.1 * y ^ target.2) (walkStep false label) =
            (1 - y) * (x - y) *
                (x * x ^ label.1 + (1 - x) * ((label.2 : S) * x ^ label.1)) +
              x * y * (1 - y) * (x ^ label.1 - y ^ label.1) +
              x * y * (x - y) * (x ^ label.1 - x ^ label.1 * y ^ label.2) := by
        classical
        have hlow := mul_neg_geom_sum y label.2
        have hhigh : (x - y) *
            (∑ index ∈ Finset.range label.1, x ^ (label.1 - 1 - index) * y ^ index) =
              x ^ label.1 - y ^ label.1 := by
          have h := geom_sum₂_mul y x label.1
          simp_rw [mul_comm (y ^ _) (x ^ _)] at h
          linear_combination -h
        have hsum : (∑ index ∈ Finset.range label.1,
            x ^ (label.1 - index) * y ^ (index + 1)) =
              x * y * ∑ index ∈ Finset.range label.1,
                x ^ (label.1 - 1 - index) * y ^ index := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index hi
          have hindex := Finset.mem_range.mp hi
          have hexponent : label.1 - index = (label.1 - 1 - index) + 1 := by omega
          rw [hexponent, pow_succ, pow_succ]
          ring
        have hlowSum : (∑ index ∈ Finset.range label.2,
            x ^ (label.1 + 1) * y ^ (index + 1)) =
              x ^ (label.1 + 1) * y * ∑ index ∈ Finset.range label.2, y ^ index := by
          simp only [pow_succ, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index hi
          ring
        simp only [walkStep, Bool.false_eq_true, if_false, map_add, map_sum,
          Finsupp.linearCombination_single, one_smul, pow_zero, mul_one, zsmul_eq_mul]
        rw [hsum, hlowSum]
        simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast]
        linear_combination x * y * (1 - y) * hhigh +
          x ^ (label.1 + 1) * y * (x - y) * hlow
      cases isLeft <;> dsimp only
      · apply PowerSeries.ext
        intro degree
        cases degree with
        | zero =>
            simp [forwardSeries, walkEndpoints, Finsupp.linearCombination_single]
        | succ degree =>
            simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, Nat.succ_ne_zero,
              if_false, sub_zero, forwardSeries, forwardMoment, PowerSeries.coeff_mk,
              one_pow, mul_one]
            simp only [sub_mul, map_sub, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_mk, one_mul]
            rw [walkEndpoints, Finsupp.linearCombination_linearCombination]
            have hlift := congrArg
              (fun family => Finsupp.linearCombination ℤ family (walkEndpoints false degree))
              (funext hright)
            simp only [hadd, hsub, hscale] at hlift
            linear_combination hlift
      · apply PowerSeries.ext
        intro degree
        cases degree with
        | zero =>
            simp [forwardSeries, walkEndpoints, Finsupp.linearCombination_single]
        | succ degree =>
            simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, Nat.succ_ne_zero,
              if_false, sub_zero, forwardSeries, PowerSeries.coeff_mk, one_pow, mul_one]
            simp only [sub_mul, map_sub, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_mk, one_mul]
            rw [walkEndpoints, Finsupp.linearCombination_linearCombination]
            have hlift := congrArg
              (fun family => Finsupp.linearCombination ℤ family (walkEndpoints true degree))
              (funext hleft)
            simp only [hadd, hsub, hscale] at hlift
            linear_combination hlift
    · intro hright
      subst isLeft
      apply PowerSeries.ext
      intro degree
      cases degree with
      | zero => simp [forwardSeries, walkEndpoints, Finsupp.linearCombination_single]
      | succ degree =>
          simp only [forwardSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one,
            Nat.succ_ne_zero, if_false, Finsupp.linearCombination_apply, Finsupp.sum]
          apply Finset.sum_eq_zero
          intro label hlabel
          have hnonzero := Finsupp.mem_support_iff.mp hlabel
          have hfirst : label.1 ≠ 0 := by
            intro hzero
            exact hnonzero (hpositive (degree + 1) (by omega) label hzero)
          simp [zero_pow hfirst]
    · intro hright x
      subst isLeft
      have hstep (label : ℕ × ℕ) :
          (x - 1) * Finsupp.linearCombination ℤ
              (fun target : ℕ × ℕ => x ^ target.1) (walkStep false label) =
            (x - 1) * ((label.2 : S) * x ^ label.1) + x ^ 2 * x ^ label.1 - x := by
        have hhigh : (x - 1) *
            (∑ index ∈ Finset.range label.1, x ^ (label.1 - index)) =
              x ^ (label.1 + 1) - x := by
          have hsum : (∑ index ∈ Finset.range label.1, x ^ (label.1 - index)) =
              x * ∑ index ∈ Finset.range label.1, x ^ index := by
            rw [← Finset.sum_range_reflect, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro index hi
            have hindex := Finset.mem_range.mp hi
            have hexponent : label.1 - (label.1 - 1 - index) = index + 1 := by omega
            rw [hexponent, pow_succ']
          rw [hsum]
          have hgeom := mul_geom_sum x label.1
          linear_combination x * hgeom
        simp only [walkStep, Bool.false_eq_true, if_false, map_add, map_sum,
          Finsupp.linearCombination_single, one_smul, zsmul_eq_mul, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, Int.cast_sub, Int.cast_one, Int.cast_natCast]
        linear_combination hhigh
      apply PowerSeries.ext
      intro degree
      cases degree with
      | zero => simp [forwardSeries, walkEndpoints, Finsupp.linearCombination_single]
      | succ degree =>
          simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, Nat.succ_ne_zero,
            if_false, sub_zero, forwardSeries, forwardMoment, PowerSeries.coeff_mk,
            one_pow, mul_one, sub_mul, one_mul]
          rw [walkEndpoints, Finsupp.linearCombination_linearCombination]
          have hlift := congrArg
            (fun family => Finsupp.linearCombination ℤ family (walkEndpoints false degree))
            (funext hstep)
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul,
            mul_add, mul_sub, sub_mul, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum] at hlift ⊢
          simp only [mul_comm, mul_left_comm, mul_assoc, one_mul] at hlift ⊢
          exact hlift
  refine ⟨hall (S := R) isLeft depth, ?_⟩
  intro hright x
  subst isLeft
  let : UniformSpace R := ⊥
  let : DiscreteUniformity R := ⟨rfl⟩
  let tau : PowerSeries R := PowerSeries.mk fun degree => x ^ degree
  let collapse : PowerSeries (PowerSeries R) →+* PowerSeries R :=
    PowerSeries.eval₂Hom (φ := RingHom.id (PowerSeries R)) continuous_id
      PowerSeries.HasEval.X
  dsimp only
  rw [← PowerSeries.coe_eval₂Hom (φ := RingHom.id (PowerSeries R))
    continuous_id (PowerSeries.HasEval.X (R := R))]
  change PowerSeries.X * tau * collapse (forwardSeries false tau 1) =
    (1 - PowerSeries.C x + PowerSeries.X * PowerSeries.C x +
      PowerSeries.X * PowerSeries.C (x ^ 2)) * forwardSeries false x 1 +
    (PowerSeries.C x - tau) * (1 - PowerSeries.X * forwardSeries false 1 1)
  have hC (value : PowerSeries R) : collapse (PowerSeries.C value) = value := by
    simp [collapse, PowerSeries.coe_eval₂Hom]
  have hX : collapse PowerSeries.X = PowerSeries.X := by
    simp [collapse, PowerSeries.coe_eval₂Hom]
  have hembed (series : PowerSeries R) :
      collapse (PowerSeries.map PowerSeries.C series) = series := by
    have hsum := PowerSeries.hasSum_eval₂
      (φ := RingHom.id (PowerSeries R)) continuous_id
      (PowerSeries.HasEval.X (R := R)) (PowerSeries.map PowerSeries.C series)
    have hself := PowerSeries.hasSum_of_monomials_self series
    have hmonomial (degree : ℕ) (value : R) :
        PowerSeries.C value * PowerSeries.X ^ degree = PowerSeries.monomial degree value := by
      apply PowerSeries.ext
      intro index
      simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
        PowerSeries.coeff_monomial, eq_comm]
    simp only [PowerSeries.coeff_map, RingHom.id_apply, hmonomial] at hsum
    simpa only [collapse, PowerSeries.coe_eval₂Hom] using hsum.unique hself
  have hconstant (side : Bool) (x y : R) :
      collapse
        (forwardSeries side
          (PowerSeries.C x) (PowerSeries.C y)) =
        forwardSeries side x y := by
    rw [← hembed
      (forwardSeries side x y)]
    congr 1
    apply PowerSeries.ext
    intro degree
    simp only [PowerSeries.coeff_map,
      forwardSeries,
      PowerSeries.coeff_mk, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_intCast, zsmul_eq_mul, map_mul, map_pow]
  have hboundary (value : R) :
      collapse (forwardSeries false (PowerSeries.C value) 1) =
        forwardSeries false value 1 := by
    simpa only [map_one] using hconstant false value 1
  have hmoment : collapse (forwardMoment (PowerSeries.C x)) = forwardMoment x := by
    rw [← hembed (forwardMoment x)]
    congr 1
    apply PowerSeries.ext
    intro degree
    simp only [PowerSeries.coeff_map, forwardMoment, PowerSeries.coeff_mk,
      Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul, map_sum, map_mul,
      map_intCast, map_natCast, map_pow]
  have htau : (1 - PowerSeries.X * PowerSeries.C x) * tau = 1 := by
    apply PowerSeries.ext
    intro degree
    cases degree with
    | zero => simp [tau, sub_mul, mul_assoc]
    | succ degree =>
        simp only [sub_mul, one_mul, mul_assoc, map_sub, tau,
          PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false]
        rw [pow_succ]
        ring
  by_cases hx : x = 0
  · have htauZero : tau = 1 := by
      apply PowerSeries.ext
      intro degree
      cases degree <;> simp [tau, hx]
    have hroot := (hall (S := R) false 0).2.2.2.2.1 rfl
    rw [htauZero]
    have hscalar : collapse (forwardSeries false (1 : PowerSeries R) 1) =
        forwardSeries false (1 : R) 1 := by
      simpa only [map_one] using hconstant false (1 : R) 1
    rw [hscalar]
    simp only [hx, zero_pow (by decide : 2 ≠ 0), map_zero, mul_zero,
      add_zero, sub_zero, mul_one, zero_sub, neg_mul, hroot]
    ring
  · have hforward :=
      (hall (S := PowerSeries R) false 0).2.2.2.1
        (PowerSeries.C x) tau
    dsimp only at hforward
    have hcollapsed := congrArg collapse hforward
    simp only [map_mul, map_add, map_sub, map_one, hC, hX, hboundary, hmoment]
      at hcollapsed
    have hdifference := (hall (S := R) false 0).2.2.2.2.2 rfl x
    simp only [map_sub, map_one, map_pow] at hdifference
    have hproduct : (1 - tau) * PowerSeries.C x *
        (PowerSeries.X * tau * collapse (forwardSeries false tau 1) -
          (1 - PowerSeries.C x + PowerSeries.X * PowerSeries.C x +
            PowerSeries.X * PowerSeries.C x ^ 2) * forwardSeries false x 1 -
          (PowerSeries.C x - tau) * (1 - PowerSeries.X * forwardSeries false 1 1)) = 0 := by
      linear_combination hcollapsed +
        ((PowerSeries.C x - tau) *
          collapse (forwardSeries false (PowerSeries.C x) tau) +
          tau * (1 - PowerSeries.C x) * forwardSeries false x 1) * htau +
        (1 - tau) * (PowerSeries.C x - tau) * hdifference
    have hfirst : (PowerSeries.C x : PowerSeries R) ≠ 0 := by
      intro hzero
      exact hx (by simpa using congrArg PowerSeries.constantCoeff hzero)
    have hsecond : (1 - tau : PowerSeries R) ≠ 0 := by
      intro hzero
      have hcoeff := congrArg (PowerSeries.coeff 1) hzero
      simp only [map_sub, PowerSeries.coeff_one, one_ne_zero, if_false, tau,
        PowerSeries.coeff_mk, pow_one, map_zero, zero_sub, neg_eq_zero] at hcoeff
      exact hx hcoeff
    have hcancel := (mul_eq_zero.mp hproduct).resolve_left (mul_ne_zero hsecond hfirst)
    simp only [map_pow]
    linear_combination hcancel

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Catalytic
