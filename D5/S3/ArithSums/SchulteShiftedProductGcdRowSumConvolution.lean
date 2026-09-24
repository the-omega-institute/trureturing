/- GID: D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution
   generality: G
   mirror-B: D5/B/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Totient, mathlib/module/Mathlib.Logic.Equiv.Fin.Basic]
   utility: none
   digest: OEIS A347293's gcd row sum equals n squared convolved with totient squared. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
open Finset

noncomputable section

namespace D5.S3.ArithSums.SchulteShiftedProductGcdRowSumConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

def rowSum (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    Nat.gcd (1 + x * y) n

theorem result (n : ℕ) (hn : 0 < n) :
    rowSum n = ∑ d ∈ n.divisors, d ^ 2 * (Nat.totient (n / d)) ^ 2 := by
  have card_window_solutions (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
    Nat.card {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} =
      Nat.totient d * (n / d) ^ 2 := by
    letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
    let residue : Fin n ≃ ZMod d × Fin (n / d) :=
      (finCongr (Nat.div_mul_cancel hd).symm).trans
        (finProdFinEquiv.symm.trans
          ((Equiv.prodComm _ _).trans
            (Equiv.prodCongr (ZMod.finEquiv d).toEquiv (Equiv.refl _))))
    let window := (Equiv.prodCongr residue residue).subtypeEquiv (p :=
      fun p : Fin n × Fin n => d ∣ 1 + p.1.val * p.2.val) (q :=
      fun z : (ZMod d × Fin (n / d)) × (ZMod d × Fin (n / d)) =>
        1 + z.1.1 * z.2.1 = 0) (by
          intro p
          rw [← ZMod.natCast_eq_zero_iff]
          change ((1 + p.1.val * p.2.val : ℕ) : ZMod d) = 0 ↔
            1 + ZMod.finEquiv d ⟨p.1.val % d, Nat.mod_lt _ hd0⟩ *
              ZMod.finEquiv d ⟨p.2.val % d, Nat.mod_lt _ hd0⟩ = 0
          cases d with
          | zero => omega
          | succ d =>
            change ((1 + p.1.val * p.2.val : ℕ) : ZMod (d + 1)) = 0 ↔
              1 + (⟨p.1.val % (d + 1), Nat.mod_lt _ hd0⟩ : ZMod (d + 1)) *
                (⟨p.2.val % (d + 1), Nat.mod_lt _ hd0⟩ : ZMod (d + 1)) = 0
            rw [← ZMod.natCast_zmod_val (n := d + 1)
              (⟨p.1.val % (d + 1), Nat.mod_lt _ hd0⟩ : ZMod (d + 1)),
              ← ZMod.natCast_zmod_val (n := d + 1)
              (⟨p.2.val % (d + 1), Nat.mod_lt _ hd0⟩ : ZMod (d + 1))]
            simp only [ZMod.val, ZMod.natCast_mod,
              Nat.cast_add, Nat.cast_one, Nat.cast_mul]
            rfl)
    let units : (ZMod d)ˣ ≃ {p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} :=
      (unitsEquivProdSubtype (ZMod d)).trans
        ((Equiv.prodCongr (Equiv.refl _) (Equiv.neg _)).subtypeEquiv (by
          intro p
          change (p.1 * p.2 = 1 ∧ p.2 * p.1 = 1) ↔ 1 + p.1 * (-p.2) = 0
          rw [mul_comm p.2 p.1, and_self, mul_neg, ← sub_eq_add_neg,
            sub_eq_zero, eq_comm]))
    let shuffle : (ZMod d × ZMod d) × (Fin (n / d) × Fin (n / d)) ≃
        (ZMod d × Fin (n / d)) × (ZMod d × Fin (n / d)) :=
      (Equiv.prodAssoc _ _ _).trans
        ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _).symm)
      |>.trans ((Equiv.refl _).prodCongr
        ((Equiv.prodComm _ _).prodCongr (Equiv.refl _)))
      |>.trans ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _))
      |>.trans (Equiv.prodAssoc _ _ _).symm
    let split :
        ({p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} × Fin (n / d)) × Fin (n / d) ≃
          {z : (ZMod d × Fin (n / d)) × (ZMod d × Fin (n / d)) //
            1 + z.1.1 * z.2.1 = 0} :=
      (Equiv.prodAssoc _ _ _).trans
        (Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
          (shuffle.subtypeEquiv (by intro z; rfl)))
    calc
      Nat.card {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} =
          Nat.card (((ZMod d)ˣ × Fin (n / d)) × Fin (n / d)) :=
        Nat.card_congr (window.trans (split.symm.trans
          (Equiv.prodCongr (Equiv.prodCongr units.symm (Equiv.refl _))
            (Equiv.refl _))))
      _ = Nat.totient d * (n / d) ^ 2 := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card,
          ZMod.card_units_eq_totient, Nat.card_eq_fintype_card, Fintype.card_fin]
        ring
  have gcd_sum_totient_filter (a : ℕ) :
      Nat.gcd a n = ∑ d ∈ n.divisors, if d ∣ a then Nat.totient d else 0 := by
    have hzero : n ≠ 0 := Nat.ne_of_gt hn
    have hset : (Nat.gcd a n).divisors = n.divisors.filter (fun d => d ∣ a) := by
      ext d
      constructor
      · intro hd
        have hdg : d ∣ Nat.gcd a n := Nat.dvd_of_mem_divisors hd
        have hdn : d ∣ n := (Nat.dvd_gcd_iff).mp hdg |>.2
        have hda : d ∣ a := (Nat.dvd_gcd_iff).mp hdg |>.1
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdn, hzero⟩, hda⟩
      · intro hd
        rcases Finset.mem_filter.mp hd with ⟨hdn, hda⟩
        exact Nat.mem_divisors.mpr
          ⟨Nat.dvd_gcd hda (Nat.dvd_of_mem_divisors hdn), Nat.gcd_ne_zero_right hzero⟩
    rw [← Nat.sum_totient (Nat.gcd a n), hset]
    simp only [Finset.sum_filter]
  have rowSum_fin :
      rowSum n = ∑ x : Fin n, ∑ y : Fin n,
        Nat.gcd (1 + x.val * y.val) n := by
    unfold rowSum
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [← Fin.sum_univ_eq_sum_range]
  have sum_indicator_card (d : ℕ) :
      (∑ p : Fin n × Fin n,
        if d ∣ 1 + p.1.val * p.2.val then Nat.totient d else 0) =
        Nat.totient d * Nat.card {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} := by
    have hif :
        (fun p : Fin n × Fin n =>
          if d ∣ 1 + p.1.val * p.2.val then Nat.totient d else 0) =
        (fun p : Fin n × Fin n =>
          Nat.totient d * (if d ∣ 1 + p.1.val * p.2.val then 1 else 0)) := by
      funext p
      by_cases hp : d ∣ 1 + p.1.val * p.2.val <;> simp [hp]
    rw [hif, ← Finset.mul_sum]
    congr 1
    rw [← Finset.card_filter]
    rw [← Fintype.card_subtype (fun p : Fin n × Fin n => d ∣ 1 + p.1.val * p.2.val)]
    rw [Nat.card_eq_fintype_card]
  have weighted_solution_sum (d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
      (∑ x : Fin n, ∑ y : Fin n,
        if d ∣ 1 + x.val * y.val then Nat.totient d else 0) =
        Nat.totient d * (Nat.totient d * (n / d) ^ 2) := by
    calc
      (∑ x : Fin n, ∑ y : Fin n,
        if d ∣ 1 + x.val * y.val then Nat.totient d else 0) =
          ∑ p : Fin n × Fin n,
            if d ∣ 1 + p.1.val * p.2.val then Nat.totient d else 0 := by
        simpa [Finset.univ_product_univ] using
          (Finset.sum_product (Finset.univ : Finset (Fin n))
            (Finset.univ : Finset (Fin n))
            (fun p : Fin n × Fin n =>
              if d ∣ 1 + p.1.val * p.2.val then Nat.totient d else 0)).symm
      _ = Nat.totient d *
          Nat.card {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} :=
        sum_indicator_card d
      _ = Nat.totient d * (Nat.totient d * (n / d) ^ 2) := by
        rw [card_window_solutions n d hd hd0]
  have sum_three_reorder_finset {α β γ M : Type} [AddCommMonoid M]
      (sα : Finset α) (sβ : Finset β) (sγ : Finset γ)
      (term : α → β → γ → M) :
      (∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ, term a b c) =
        ∑ c ∈ sγ, ∑ a ∈ sα, ∑ b ∈ sβ, term a b c := by
    calc
      (∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ, term a b c) =
          ∑ a ∈ sα, ∑ c ∈ sγ, ∑ b ∈ sβ, term a b c := by
        apply Finset.sum_congr rfl
        intro a ha
        simpa using (Finset.sum_comm (s := sβ) (t := sγ)
          (f := fun b c => term a b c))
      _ = ∑ c ∈ sγ, ∑ a ∈ sα, ∑ b ∈ sβ, term a b c := by
        simpa using (Finset.sum_comm (s := sα) (t := sγ)
          (f := fun a c => ∑ b ∈ sβ, term a b c))
  have rowSum_weighted :
      rowSum n = ∑ d ∈ n.divisors,
        Nat.totient d * (Nat.totient d * (n / d) ^ 2) := by
    rw [rowSum_fin]
    simp_rw [gcd_sum_totient_filter]
    rw [sum_three_reorder_finset (Finset.univ : Finset (Fin n))
      (Finset.univ : Finset (Fin n)) n.divisors]
    apply Finset.sum_congr rfl
    intro d hd
    rw [weighted_solution_sum d (Nat.dvd_of_mem_divisors hd)
      (Nat.pos_of_mem_divisors hd)]
  let term : ℕ → ℕ := fun t => t ^ 2 * (Nat.totient (n / t)) ^ 2
  have hzero : n ≠ 0 := Nat.ne_of_gt hn
  calc
    rowSum n = ∑ d ∈ n.divisors,
        Nat.totient d * (Nat.totient d * (n / d) ^ 2) := rowSum_weighted
    _ = ∑ d ∈ n.divisors, term (n / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [term]
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hzero]
      ring
    _ = ∑ d ∈ n.divisors, term d := Nat.sum_div_divisors n term
    _ = ∑ d ∈ n.divisors, d ^ 2 * (Nat.totient (n / d)) ^ 2 := by rfl

end D5.S3.ArithSums.SchulteShiftedProductGcdRowSumConvolution
