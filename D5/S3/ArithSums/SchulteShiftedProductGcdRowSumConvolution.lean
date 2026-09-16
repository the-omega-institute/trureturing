/- GID: D5/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution
   generality: G
   mirror-B: D5/B/S3/ArithSums/SchulteShiftedProductGcdRowSumConvolution
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Totient, mathlib/module/Mathlib.Logic.Equiv.Fin.Basic]
   utility: none
   digest: Schulte's gcd row sum equals n squared convolved with totient squared. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
open Finset

noncomputable section

namespace D5.S3.ArithSums.SchulteShiftedProductGcdRowSumConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem card_window_solutions (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
    Nat.card {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} =
      Nat.totient d * (n / d) ^ 2 := by
  let residueFinEquiv (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
      Fin n ≃ ZMod d × Fin (n / d) := by
    letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
    have hn : (n / d) * d = n := Nat.div_mul_cancel hd
    exact
      (finCongr hn.symm)
      |>.trans finProdFinEquiv.symm
      |>.trans (Equiv.prodComm _ _)
      |>.trans (Equiv.prodCongr (ZMod.finEquiv d).toEquiv (Equiv.refl _))
  let unitSolutionEquiv (d : ℕ) (hd0 : 0 < d) :
      (ZMod d)ˣ ≃ {p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} := by
    letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
    let negSecond : ZMod d × ZMod d ≃ ZMod d × ZMod d :=
      Equiv.prodCongr (Equiv.refl _) (Equiv.neg _)
    exact (unitsEquivProdSubtype (ZMod d)).trans
      (negSecond.subtypeEquiv (by
        intro p
        constructor
        · intro hp
          change 1 + p.1 * (-p.2) = 0
          rw [mul_neg, hp.1]
          simp
        · intro hp
          change 1 + p.1 * (-p.2) = 0 at hp
          have hneg : p.1 * (-p.2) = -1 := eq_neg_of_add_eq_zero_right hp
          have hmul : p.1 * p.2 = 1 := by
            apply neg_injective
            simpa only [mul_neg] using hneg
          exact ⟨hmul, by simpa only [mul_comm] using hmul⟩))
  let windowResidueEquiv (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) :
      {p : Fin n × Fin n // d ∣ 1 + p.1.val * p.2.val} ≃
        {z : (ZMod d × Fin (n / d)) × (ZMod d × Fin (n / d)) //
          1 + z.1.1 * z.2.1 = 0} := by
    let e := Equiv.prodCongr (residueFinEquiv n d hd hd0) (residueFinEquiv n d hd hd0)
    letI : NeZero d := ⟨Nat.ne_of_gt hd0⟩
    have finEquiv_natCast (x : Fin d) :
        ZMod.finEquiv d x = (x.val : ZMod d) := by
      rcases d with _ | d
      · exact Fin.elim0 x
      · exact (ZMod.natCast_zmod_val (n := d + 1) x).symm
    have finEquiv_symm_natCast (z : ZMod d) :
        (((ZMod.finEquiv d).symm z).val : ZMod d) = z := by
      calc
        (((ZMod.finEquiv d).symm z).val : ZMod d) =
            ZMod.finEquiv d ((ZMod.finEquiv d).symm z) :=
          (finEquiv_natCast _).symm
        _ = z := (ZMod.finEquiv d).apply_symm_apply z
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
      simpa [e, residueFinEquiv, finEquiv_natCast, ZMod.natCast_mod] using hp
    · rw [← ZMod.natCast_eq_zero_iff]
      simpa [e, residueFinEquiv, finEquiv_symm_natCast, ZMod.natCast_mod] using z.2
  let solutionProductEquiv (d q : ℕ) :
      ({p : ZMod d × ZMod d // 1 + p.1 * p.2 = 0} × Fin q) × Fin q ≃
        {z : (ZMod d × Fin q) × (ZMod d × Fin q) //
          1 + z.1.1 * z.2.1 = 0} := by
    let predicate : ZMod d × ZMod d → Prop := fun p => 1 + p.1 * p.2 = 0
    let extract : {z : (ZMod d × ZMod d) × (Fin q × Fin q) // predicate z.1} ≃
        {p : ZMod d × ZMod d // predicate p} × (Fin q × Fin q) :=
      Equiv.prodSubtypeFstEquivSubtypeProd
    let associate : ({p : ZMod d × ZMod d // predicate p} × Fin q) × Fin q ≃
        {p : ZMod d × ZMod d // predicate p} × (Fin q × Fin q) :=
      Equiv.prodAssoc _ _ _
    let shuffle : ((ZMod d × ZMod d) × (Fin q × Fin q)) ≃
        (ZMod d × Fin q) × (ZMod d × Fin q) :=
      (Equiv.prodAssoc (ZMod d) (ZMod d) (Fin q × Fin q)).trans
        ((Equiv.refl (ZMod d)).prodCongr
          (Equiv.prodAssoc (ZMod d) (Fin q) (Fin q)).symm)
      |>.trans ((Equiv.refl (ZMod d)).prodCongr
        ((Equiv.prodComm (ZMod d) (Fin q)).prodCongr (Equiv.refl (Fin q))))
      |>.trans ((Equiv.refl (ZMod d)).prodCongr
        (Equiv.prodAssoc (Fin q) (ZMod d) (Fin q)))
      |>.trans (Equiv.prodAssoc (ZMod d) (Fin q) (ZMod d × Fin q)).symm
    exact associate.trans (extract.symm.trans (shuffle.subtypeEquiv (by intro z; rfl)))
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
