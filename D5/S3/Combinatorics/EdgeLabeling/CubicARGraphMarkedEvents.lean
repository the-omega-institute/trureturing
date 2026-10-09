/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents
   mirror-E: none(waiver:helper-for-open-problem-resolution)
   anchors: []
   utility: none
   digest: Labelings with two marked edges and additive collision events. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphMarkedEvents

open scoped Classical

/-- Bijections with the first two labels fixed on the marked edges. -/
abbrev MarkedLabeling (E : Type) [Fintype E] [DecidableEq E] (m : ℕ) (hm : 2 ≤ m)
    (p q : E) :=
  {e : E ≃ Fin m // e p = ⟨0, by omega⟩ ∧ e q = ⟨1, hm⟩}

/-- Edge labels are the successor of the zero-based value of the finite equivalence. -/
def markLabel {E : Type} [Fintype E] [DecidableEq E] {m : ℕ} {hm : 2 ≤ m}
    {p q : E} (e : MarkedLabeling E m hm p q) (x : E) : ℕ := (e.val x).val + 1

/-- One of the three labels is the sum of the other two. -/
abbrev AdditiveTriple {E : Type} (f : E → ℕ) (a b c : E) : Prop :=
  f a + f b = f c ∨ f a + f c = f b ∨ f b + f c = f a

/-- The marked sample space has the factorial cardinality of its free edges. -/
theorem card_markedLabeling {E : Type} [Fintype E] [DecidableEq E]
    (m : ℕ) (hm : 2 ≤ m) (p q : E) (hpq : p ≠ q) (hcard : Fintype.card E = m) :
    Fintype.card (MarkedLabeling E m hm p q) = Nat.factorial (m - 2) := by
  classical
  let d : Fin 2 → E := ![p, q]
  let l : Fin 2 → Fin m := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
  have hd : Function.Injective d := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [d]
  have hl : Function.Injective l := by
    intro i j hij
    have hv := congrArg (fun x : Fin m => x.val) hij
    exact Fin.ext hv
  have hpred (e : E ≃ Fin m) :
      (e p = ⟨0, by omega⟩ ∧ e q = ⟨1, hm⟩) ↔ (∀ i, e (d i) = l i) := by
    constructor
    · intro h i
      fin_cases i
      · simpa [d, l] using h.1
      · simpa [d, l] using h.2
    · intro h
      exact ⟨by simpa [d, l] using h 0, by simpa [d, l] using h 1⟩
  change Fintype.card {e : E ≃ Fin m // _} = _
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hpred), ← Nat.card_eq_fintype_card]
  have hh := D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting.nat_card_equiv_constraints
    d l hd hl (by simpa using hcard)
  simpa [hcard] using hh

/-- At the common marked endpoint, the unique bad free label is three. -/
private theorem additive_marked_iff {E : Type} [Fintype E] [DecidableEq E]
    {m : ℕ} {hm : 2 ≤ m} {p q r : E} (hm3 : 3 ≤ m) (hpr : p ≠ r)
    (e : MarkedLabeling E m hm p q) :
    AdditiveTriple (markLabel e) p q r ↔ e.val r = ⟨2, by omega⟩ := by
  have hp : markLabel e p = 1 := by simp [markLabel, e.property.1]
  have hq : markLabel e q = 2 := by simp [markLabel, e.property.2]
  have hr0 : (e.val r).val ≠ 0 := by
    intro h
    have he : e.val r = e.val p := by
      apply Fin.ext
      simpa [e.property.1] using h
    exact hpr (e.val.injective he).symm
  unfold AdditiveTriple
  rw [hp, hq]
  change (1 + 2 = (e.val r).val + 1 ∨ 1 + ((e.val r).val + 1) = 2 ∨
    2 + ((e.val r).val + 1) = 1) ↔ e.val r = ⟨2, by omega⟩
  constructor
  · intro h
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_mk] at hv
    omega

/-- Bad labelings for a triple containing both marked edges are counted exactly. -/
theorem card_bad_both_marked {E : Type} [Fintype E] [DecidableEq E]
    (m : ℕ) (hm : 2 ≤ m) (hm3 : 3 ≤ m) (p q r : E)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hcard : Fintype.card E = m) :
    Fintype.card {e : MarkedLabeling E m hm p q //
      AdditiveTriple (markLabel e) p q r} = Nat.factorial (m - 3) := by
  classical
  let d : Fin 3 → E := ![p, q, r]
  let l : Fin 3 → Fin m := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hm3⟩
  have hd : Function.Injective d := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [d]
  have hl : Function.Injective l := by
    intro i j hij
    have hv := congrArg (fun x : Fin m => x.val) hij
    exact Fin.ext hv
  let eventEquiv : {e : MarkedLabeling E m hm p q //
      AdditiveTriple (markLabel e) p q r} ≃ {e : E ≃ Fin m // ∀ i, e (d i) = l i} :=
    { toFun := fun e => ⟨e.val.val, by
        intro i
        fin_cases i
        · simpa [d, l] using e.val.property.1
        · simpa [d, l] using e.val.property.2
        · simpa [d, l] using (additive_marked_iff hm3 hpr e.val).mp e.property⟩
      invFun := fun e => ⟨⟨e.val, by
        exact ⟨by simpa [d, l] using e.property 0,
          by simpa [d, l] using e.property 1⟩⟩, by
        apply (additive_marked_iff hm3 hpr _).mpr
        simpa [d, l] using e.property 2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr eventEquiv, ← Nat.card_eq_fintype_card]
  have hh := D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting.nat_card_equiv_constraints
    d l hd hl (by simpa using hcard)
  simpa [hcard] using hh

private theorem free_value_ge_two {E : Type} [Fintype E] [DecidableEq E]
    {m : ℕ} {hm : 2 ≤ m} {p q a : E} (hpa : p ≠ a) (hqa : q ≠ a)
    (e : MarkedLabeling E m hm p q) : 2 ≤ (e.val a).val := by
  have hzero : (e.val a).val ≠ 0 := by
    intro h
    have he : e.val a = e.val p := by
      apply Fin.ext
      simpa [e.property.1] using h
    exact hpa (e.val.injective he).symm
  have hone : (e.val a).val ≠ 1 := by
    intro h
    have he : e.val a = e.val q := by
      apply Fin.ext
      simpa [e.property.2] using h
    exact hqa (e.val.injective he).symm
  omega

private theorem card_two_assignments {E : Type} [Fintype E] [DecidableEq E]
    (m : ℕ) (hm : 2 ≤ m) (p q a b : E)
    (hpq : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b)
    (hqa : q ≠ a) (hqb : q ≠ b) (hab : a ≠ b) (hcard : Fintype.card E = m)
    (u v : Fin m) (hu : 2 ≤ u.val) (hv : 2 ≤ v.val) (huv : u ≠ v) :
    Fintype.card {e : MarkedLabeling E m hm p q // e.val a = u ∧ e.val b = v} =
      Nat.factorial (m - 4) := by
  classical
  let d : Fin 4 → E := ![p, q, a, b]
  let l : Fin 4 → Fin m := ![⟨0, by omega⟩, ⟨1, hm⟩, u, v]
  have hd : Function.Injective d := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [d]
  have hu0 : u ≠ (⟨0, by omega⟩ : Fin m) := by
    intro h
    have he := congrArg (fun x : Fin m => x.val) h
    change u.val = 0 at he
    omega
  have hu1 : u ≠ (⟨1, hm⟩ : Fin m) := by
    intro h
    have he := congrArg (fun x : Fin m => x.val) h
    change u.val = 1 at he
    omega
  have hv0 : v ≠ (⟨0, by omega⟩ : Fin m) := by
    intro h
    have he := congrArg (fun x : Fin m => x.val) h
    change v.val = 0 at he
    omega
  have hv1 : v ≠ (⟨1, hm⟩ : Fin m) := by
    intro h
    have he := congrArg (fun x : Fin m => x.val) h
    change v.val = 1 at he
    omega
  have hl : Function.Injective l := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [l]
  let eventEquiv : {e : MarkedLabeling E m hm p q // e.val a = u ∧ e.val b = v} ≃
      {e : E ≃ Fin m // ∀ i, e (d i) = l i} :=
    { toFun := fun e => ⟨e.val.val, by
        intro i
        fin_cases i
        · simpa [d, l] using e.val.property.1
        · simpa [d, l] using e.val.property.2
        · simpa [d, l] using e.property.1
        · simpa [d, l] using e.property.2⟩
      invFun := fun e => ⟨⟨e.val, by
        exact ⟨by simpa [d, l] using e.property 0,
          by simpa [d, l] using e.property 1⟩⟩,
        ⟨by simpa [d, l] using e.property 2, by simpa [d, l] using e.property 3⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr eventEquiv, ← Nat.card_eq_fintype_card]
  have hh := D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting.nat_card_equiv_constraints
    d l hd hl (by simpa using hcard)
  simpa [hcard] using hh

/-- The bad-event bound for an incident label fixed to one or two. The remaining
two labels differ by that fixed label, and each ordered pair fixes four edges. -/
theorem card_bad_single_marked_le {E : Type} [Fintype E] [DecidableEq E]
    (m : ℕ) (hm : 2 ≤ m) (hm6 : 6 ≤ m) (p q s a b : E)
    (hpq : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b)
    (hqa : q ≠ a) (hqb : q ≠ b) (hab : a ≠ b) (hcard : Fintype.card E = m)
    (delta : ℕ) (hdelta : 1 ≤ delta ∧ delta ≤ 2)
    (hs : ∀ e : MarkedLabeling E m hm p q, markLabel e s = delta) :
    Fintype.card {e : MarkedLabeling E m hm p q //
      AdditiveTriple (markLabel e) s a b} ≤
        2 * (m - 2 - delta) * Nat.factorial (m - 4) := by
  classical
  let I := Fin (m - 2 - delta) × Fin 2
  let lower : Fin (m - 2 - delta) → Fin m := fun k => ⟨k.val + 2, by omega⟩
  let upper : Fin (m - 2 - delta) → Fin m := fun k => ⟨k.val + 2 + delta, by omega⟩
  let u : I → Fin m := fun i => if i.2 = 0 then lower i.1 else upper i.1
  let v : I → Fin m := fun i => if i.2 = 0 then upper i.1 else lower i.1
  have hu (i : I) : 2 ≤ (u i).val := by
    by_cases h : i.2 = 0 <;> simp [u, lower, upper, h] <;> omega
  have hv (i : I) : 2 ≤ (v i).val := by
    by_cases h : i.2 = 0 <;> simp [v, lower, upper, h] <;> omega
  have huv (i : I) : u i ≠ v i := by
    intro h
    have he := congrArg (fun x : Fin m => x.val) h
    by_cases h : i.2 = 0
    all_goals simp [u, v, lower, upper, h] at he; omega
  let Target := Σ i : I, {e : MarkedLabeling E m hm p q //
    e.val a = u i ∧ e.val b = v i}
  let encode : (e : {e : MarkedLabeling E m hm p q //
      AdditiveTriple (markLabel e) s a b}) → {z : Target // z.2.val.val = e.val.val} :=
      fun e => by
    have ha := free_value_ge_two hpa hqa e.val
    have hb := free_value_ge_two hpb hqb e.val
    have hadd := e.property
    unfold AdditiveTriple at hadd
    rw [hs e.val] at hadd
    change delta + ((e.val.val a).val + 1) = (e.val.val b).val + 1 ∨
      delta + ((e.val.val b).val + 1) = (e.val.val a).val + 1 ∨
      ((e.val.val a).val + 1) + ((e.val.val b).val + 1) = delta at hadd
    have hcases : (e.val.val a).val + delta = (e.val.val b).val ∨
        (e.val.val b).val + delta = (e.val.val a).val := by omega
    by_cases h : (e.val.val a).val + delta = (e.val.val b).val
    · let k : Fin (m - 2 - delta) := ⟨(e.val.val a).val - 2, by
        have := (e.val.val b).isLt
        omega⟩
      refine ⟨⟨(k, 0), ⟨e.val, ?_, ?_⟩⟩, rfl⟩
      · apply Fin.ext
        simp only [u, k, lower, if_pos rfl, Fin.val_mk]
        omega
      · apply Fin.ext
        simp only [v, k, upper, if_pos rfl, Fin.val_mk]
        omega
    · let k : Fin (m - 2 - delta) := ⟨(e.val.val b).val - 2, by
        have h := hcases.resolve_left h
        have := (e.val.val a).isLt
        omega⟩
      have h := hcases.resolve_left h
      refine ⟨⟨(k, 1), ⟨e.val, ?_, ?_⟩⟩, rfl⟩
      · apply Fin.ext
        simp [u, k, upper]
        omega
      · apply Fin.ext
        simp [v, k, lower]
        omega
  have hinj : Function.Injective (fun e => (encode e).val) := by
    intro e f hef
    have hbase : e.val.val = f.val.val := by
      have h := congrArg (fun x : Target => x.2.val.val) hef
      simpa only [(encode e).property, (encode f).property] using h
    apply Subtype.ext
    exact Subtype.ext hbase
  have hsize (i : I) :
      Fintype.card {e : MarkedLabeling E m hm p q // e.val a = u i ∧ e.val b = v i} =
        Nat.factorial (m - 4) := by
    have h := card_two_assignments m hm p q a b hpq hpa hpb hqa hqb hab hcard
      (u i) (v i) (hu i) (hv i) (huv i)
    simpa only [← Nat.card_eq_fintype_card] using h
  calc
    _ ≤ Fintype.card Target := Fintype.card_le_of_injective (fun e => (encode e).val) hinj
    _ = 2 * (m - 2 - delta) * Nat.factorial (m - 4) := by
      rw [Fintype.card_sigma]
      simp_rw [hsize]
      simp [I, Fintype.card_prod, Nat.mul_comm]

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphMarkedEvents
