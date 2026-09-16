/- GID: D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution
   generality: G
   mirror-B: D5/B/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Totient]
   utility: none
   digest: Schulte's gcd row sum equals n squared convolved with totient squared. -/

import Mathlib.Data.Nat.Totient

open scoped BigOperators
open Finset

noncomputable section

namespace D5.S3.ArithSums.SchulteShiftedProductGcdRowSumConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

private def residueFinEquiv (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
    Fin n ≃ ZMod d × Fin (n / d) := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
  let q := n / d
  have hn : d * q = n := by
    dsimp [q]
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hd)
  let e : Fin n ≃ ZMod d × Fin q :=
    { toFun := fun x =>
        (x.val, ⟨x.val / d, by
          apply (Nat.div_lt_iff_lt_mul hd0).2
          simpa [Nat.mul_comm, hn] using x.isLt⟩)
      invFun := fun p =>
        ⟨p.1.val + d * p.2.val, by
          have h1 : p.1.val + d * p.2.val < d + d * p.2.val :=
            Nat.add_lt_add_right p.1.val_lt _
          have h2 : d + d * p.2.val ≤ d * q := by
            have h := Nat.mul_le_mul_left d (Nat.succ_le_of_lt p.2.isLt)
            simpa [Nat.mul_succ, Nat.add_comm] using h
          rw [← hn]
          exact h1.trans_le h2⟩
      left_inv := by
        intro x
        apply Fin.ext
        simp only [ZMod.val_natCast]
        rw [Nat.mod_add_div]
      right_inv := by
        intro p
        apply Prod.ext
        · change ((p.1.val + d * p.2.val : ℕ) : ZMod d) = p.1
          simp [ZMod.natCast_val]
        · apply Fin.ext
          change (p.1.val + d * p.2.val) / d = p.2.val
          apply Nat.div_eq_of_lt_le
          · calc
              p.2.val * d = d * p.2.val := Nat.mul_comm _ _
              _ ≤ p.1.val + d * p.2.val := Nat.le_add_left _ _
          · calc
              p.1.val + d * p.2.val = p.1.val + p.2.val * d := by rw [Nat.mul_comm]
              _ < d + p.2.val * d := Nat.add_lt_add_right p.1.val_lt _
              _ = (p.2.val + 1) * d := by rw [Nat.succ_mul, Nat.add_comm] }
  simpa [q] using e

private def unitSolutionEquiv (d : ℕ) (_hd0 : 0 < d) :
    (ZMod d)ˣ ≃ {p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} := by
  letI : NeZero d := ⟨Nat.ne_of_gt _hd0⟩
  let hunit : ∀ p : {p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0}, IsUnit p.1.1 :=
    fun p => isUnit_iff_exists_inv.mpr ⟨-p.1.2, by
      have hp : p.1.1 * p.1.2 = -1 := by
        calc
          p.1.1 * p.1.2 = (1 + p.1.1 * p.1.2) - 1 := by ring
          _ = 0 - 1 := by rw [p.2]
          _ = -1 := by simp
      rw [mul_neg, hp]
      simp⟩
  refine
    { toFun := fun u => ⟨((u : ZMod d), -(u⁻¹ : ZMod d)), ?_⟩
      invFun := fun p => (hunit p).unit
      left_inv := by
        intro u
        apply Units.ext
        exact IsUnit.unit_spec _
      right_inv := by
        intro p
        let hu : IsUnit p.1.1 := hunit p
        have hpunit : (hu.unit : ZMod d) = p.1.1 := hu.unit_spec
        have hp : p.1.1 * p.1.2 = -1 := by
          calc
            p.1.1 * p.1.2 = (1 + p.1.1 * p.1.2) - 1 := by ring
            _ = 0 - 1 := by rw [p.2]
            _ = -1 := by simp
        have hmul : (hu.unit : ZMod d) * p.1.2 = -1 := by
          simpa [hpunit] using hp
        have hinv_mul : (hu.unit : ZMod d)⁻¹ * (hu.unit : ZMod d) = 1 := by
          exact ZMod.inv_mul_of_unit _ hu
        have hinv : (hu.unit : ZMod d)⁻¹ = -p.1.2 := by
          calc
            (hu.unit : ZMod d)⁻¹ = (hu.unit : ZMod d)⁻¹ * 1 := by simp
            _ = (hu.unit : ZMod d)⁻¹ * (-((hu.unit : ZMod d) * p.1.2)) := by
              rw [hmul]
              simp
            _ = -p.1.2 := by
              rw [mul_neg, ← mul_assoc, hinv_mul, one_mul]
        dsimp
        apply Subtype.ext
        change ((p.1.1, -(p.1.1)⁻¹) : ZMod d × ZMod d) = p.1
        apply Prod.ext
        · rfl
        · have hinv_p : p.1.1⁻¹ = -p.1.2 := by
            simpa [hpunit] using hinv
          rw [hinv_p]
          simp }
  · simp [mul_neg]

private def windowResidueEquiv (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
    {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} ≃
      {z : (ZMod d × Fin (n / d)) × (ZMod d × Fin (n / d)) //
        1 + z.1.1 * z.2.1 = 0} := by
  let e := Equiv.prodCongr (residueFinEquiv n d hd hd0) (residueFinEquiv n d hd hd0)
  letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
  refine
    { toFun := fun p => ⟨e p, ?_⟩
      invFun := fun z => ⟨e.symm z, ?_⟩
      left_inv := by
        intro p
        apply Subtype.ext
        change e.symm (e p.1) = p.1
        exact e.left_inv p.1
      right_inv := by
        intro z
        apply Subtype.ext
        change e (e.symm z.1) = z.1
        exact e.right_inv z.1 }
  · have hp : ((1 + p.1.1.val * p.1.2.val : ℕ) : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 p.2
    simpa [e, residueFinEquiv] using hp
  · rw [← ZMod.natCast_eq_zero_iff]
    simpa [e, residueFinEquiv, ZMod.natCast_mod] using z.2

private def solutionProductEquiv (d q : ℕ) :
    ({p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} × Fin q) × Fin q ≃
      {z : (ZMod d × Fin q) × (ZMod d × Fin q) //
        1 + z.1.1 * z.2.1 = 0} := by
  refine
    { toFun := fun a =>
        ⟨((a.1.1.1.1, a.1.2), (a.1.1.1.2, a.2)), a.1.1.2⟩
      invFun := fun z =>
        ⟨⟨⟨(z.1.1.1, z.1.2.1), z.2⟩, z.1.1.2⟩, z.1.2.2⟩
      left_inv := by
        intro a
        rcases a with ⟨⟨⟨a1, a2⟩, ha⟩, a3⟩
        rfl
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }

private theorem card_window_solutions (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
    Nat.card {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} =
      Nat.totient d * (n / d) ^ 2 := by
  let q := n / d
  have card_residue_solutions (d : ℕ) (hd0 : 0 < d) :
      Nat.card {p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} = Nat.totient d := by
    letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
    calc
      Nat.card {p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} = Nat.card (ZMod d)ˣ :=
        Nat.card_congr (unitSolutionEquiv d hd0).symm
      _ = Fintype.card (ZMod d)ˣ := Nat.card_eq_fintype_card
      _ = Nat.totient d := ZMod.card_units_eq_totient d
  calc
    Nat.card {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} =
        Nat.card {z : (ZMod d × Fin q) × (ZMod d × Fin q) //
          1 + z.1.1 * z.2.1 = 0} :=
      Nat.card_congr (windowResidueEquiv n d hd hd0)
    _ = Nat.card (({p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} × Fin q) × Fin q) :=
      Nat.card_congr (solutionProductEquiv d q).symm
    _ = Nat.card {p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} *
        Nat.card (Fin q) * Nat.card (Fin q) := by
      rw [Nat.card_prod, Nat.card_prod]
    _ = Nat.totient d * q ^ 2 := by
      rw [card_residue_solutions d hd0, Nat.card_eq_fintype_card, Fintype.card_fin]
      ring
    _ = Nat.totient d * (n / d) ^ 2 := by rfl

def rowSum (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    Nat.gcd (1 + x * y) n

theorem result (n : ℕ) (hn : 0 < n) :
    rowSum n = ∑ d ∈ n.divisors, d ^ 2 * (Nat.totient (n / d)) ^ 2 := by
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
