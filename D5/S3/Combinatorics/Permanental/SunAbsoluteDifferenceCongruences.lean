/- GID: D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both absolute-difference permanent congruences in Sun Conjecture 4.2(i). -/

/- Mathematical classification:
   weighted_fixed_sum: proof_shape: bind-only; escape_witness: none; consumer: permanent_circulant
   shiftPerm_iterate: proof_shape: bind-only; escape_witness: none; consumer: shiftPerm_order
   shiftPerm_order: proof_shape: bind-only; escape_witness: none; consumer: permanent_circulant
   shiftPerm_weight: proof_shape: bind-only; escape_witness: none; consumer: permanent_circulant
   shiftPerm_fixed: proof_shape: bind-only; escape_witness: none; consumer: fixedEquiv
   fixedEquiv: proof_shape: bind-only; escape_witness: none; consumer: permanent_circulant
   permanent_circulant: proof_shape: bind-only; escape_witness: none; consumer: permanent_fin_circulant
   A: proof_shape: bind-only; escape_witness: none; consumer: sign_entry, permanent_value, claim
   claim: proof_shape: bind-only; escape_witness: none; consumer: result
   permanent_reindex: proof_shape: bind-only; escape_witness: none; consumer: permanent_fin_circulant
   permanent_sign: proof_shape: bind-only; escape_witness: none; consumer: permanent_value
   sign_entry: proof_shape: bind-only; escape_witness: none; consumer: permanent_value
   alternating_sum: proof_shape: bind-only; escape_witness: none; consumer: permanent_value
   permanent_map: proof_shape: bind-only; escape_witness: none; consumer: permanent_value
   permanent_fin_circulant: proof_shape: bind-only; escape_witness: none; consumer: permanent_value
   permanent_value: proof_shape: bind-only; escape_witness: none; consumer: result
   result: proof_shape: bind-only; escape_witness: none; consumer: settling result
   admission_basis: open-problem-resolution (#22003; Proved)
   Direct frozen dependencies: none (all imported owners are pinned Mathlib).
   The source matrices use the literal one-based integer expression; the proof
   uses Mathlib conjugation directly, without a duplicate shift-action definition.
   The circulant ingredient is the Brualdi-Newman prime-order congruence.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22464
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
set_option maxHeartbeats 800000


open scoped BigOperators
namespace D5.S3.Combinatorics.Permanental.SunAbsoluteDifferenceCongruences

private theorem weighted_fixed_sum {p : ℕ} [Fact p.Prime]
    {α : Type*} [Fintype α] [DecidableEq α] (T : α → α) (w : α → ZMod p)
    (hw : ∀ x, w (T x) = w x) (hp : T^[p] = id) :
    (∑ x, w x) = ∑ x : Function.fixedPoints T, w x.val := by
  classical
  have hfiber (z : ZMod p) :
      (Fintype.card {x // w x = z} : ZMod p) =
      (Fintype.card {x : Function.fixedPoints T // w x.val = z} : ZMod p) := by
    let U : Function.End {x // w x = z} := fun x => ⟨T x.val, (hw x.val).trans x.property⟩
    have hcomm : Function.Semiconj (Subtype.val : {x // w x = z} → α) U T := fun _ => rfl
    have hiter (n : ℕ) (x : {x // w x = z}) :
        (U^[n] x).val = T^[n] x.val := hcomm.iterate_right n x
    have hU : U ^ p ^ 1 = 1 := by
      rw [pow_one]
      change U^[p] = id
      funext x
      apply Subtype.ext
      exact (hiter p x).trans (congrFun hp x.val)
    have hc := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hU
    have he : Function.fixedPoints U ≃ {x : Function.fixedPoints T // w x.val = z} :=
      { toFun := fun x => ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, x.val.property⟩
        invFun := fun x => ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [ZMod.natCast_eq_natCast_iff]
    simpa only [Fintype.card_congr he] using hc
  calc
    (∑ x, w x) = ∑ z : ZMod p, (Fintype.card {x // w x = z} : ZMod p) * z := by
      symm
      simpa using (Fintype.sum_fiberwise' w (fun z => z))
    _ = ∑ z : ZMod p,
        (Fintype.card {x : Function.fixedPoints T // w x.val = z} : ZMod p) * z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hfiber z]
    _ = ∑ x : Function.fixedPoints T, w x.val := by
      simpa using (Fintype.sum_fiberwise' (fun x : Function.fixedPoints T => w x.val) (fun z => z))

private theorem shiftPerm_iterate {p : ℕ} (n : ℕ) (σ : Equiv.Perm (ZMod p)) (x : ZMod p) :
    ((MulAut.conj (Equiv.addRight (1 : ZMod p)))^[n] σ) x = σ (x - n) + n := by
  let t : Equiv.Perm (ZMod p) := Equiv.addRight 1
  let c : Equiv.Perm (Equiv.Perm (ZMod p)) := MulAut.toPerm _ (MulAut.conj t)
  have hc : (MulAut.conj (Equiv.addRight (1 : ZMod p))) = (c : _ → _) := rfl
  rw [hc]
  change ((c^n) σ) x = _
  have hpow : c^n = MulAut.toPerm _ (MulAut.conj (t^n)) := by
    dsimp [c]
    rw [← map_pow, ← map_pow]
  rw [hpow]
  change (t^n) (σ ((t^n)⁻¹ x)) = _
  simp [t, Equiv.Perm.coe_pow, add_right_iterate, ← inv_pow, sub_eq_add_neg]

private theorem shiftPerm_order {p : ℕ} :
    (MulAut.conj (Equiv.addRight (1 : ZMod p)))^[p] = id := by
  funext σ
  ext x
  simp [shiftPerm_iterate]

private theorem shiftPerm_weight {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ZMod p) (σ : Equiv.Perm (ZMod p)) :
    (∏ x, f (((MulAut.conj (Equiv.addRight (1 : ZMod p))) σ) x - x)) = ∏ x, f (σ x - x) := by
  calc
    _ = ∏ x : ZMod p, f (((MulAut.conj (Equiv.addRight (1 : ZMod p))) σ) (x + 1) - (x + 1)) :=
      (Equiv.prod_comp (Equiv.addRight (1 : ZMod p)) _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro x _
      congr 1
      simp [MulAut.conj_apply, sub_eq_add_neg]

private theorem shiftPerm_fixed {p : ℕ} [Fact p.Prime]
    (σ : Function.fixedPoints (MulAut.conj (Equiv.addRight (1 : ZMod p)))) (x : ZMod p) :
    σ.val x = x + σ.val 0 := by
  have hs (y : ZMod p) : σ.val (y+1) = σ.val y + 1 := by
    have h := congrArg (fun τ : Equiv.Perm (ZMod p) => τ (y+1)) σ.property
    simpa [MulAut.conj_apply, Function.IsFixedPt, sub_eq_add_neg] using h.symm
  have hc : Function.Semiconj σ.val (fun y : ZMod p => y+1) (fun y => y+1) := hs
  have h := hc.iterate_right x.val 0
  simpa [add_right_iterate, add_comm] using h

private def fixedEquiv {p : ℕ} [Fact p.Prime] :
    Function.fixedPoints (MulAut.conj (Equiv.addRight (1 : ZMod p))) ≃ ZMod p where
  toFun σ := σ.val 0
  invFun a := ⟨Equiv.addRight a, by
    apply Equiv.ext
    intro x
    simp [MulAut.conj_apply, Equiv.Perm.mul_apply, add_assoc, add_left_comm, add_comm]⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact (shiftPerm_fixed σ x).symm
  right_inv a := by simp

private theorem permanent_circulant {p : ℕ} [Fact p.Prime] (f : ZMod p → ZMod p) :
    Matrix.permanent (fun i j : ZMod p => f (i-j)) = ∑ a, f a := by
  classical
  calc
    _ = ∑ σ : Equiv.Perm (ZMod p), ∏ x, f (σ x - x) := rfl
    _ = ∑ σ : Function.fixedPoints (MulAut.conj (Equiv.addRight (1 : ZMod p))), ∏ x, f (σ.val x - x) :=
      weighted_fixed_sum (MulAut.conj (Equiv.addRight (1 : ZMod p))) (fun σ => ∏ x, f (σ x - x))
        (shiftPerm_weight f) shiftPerm_order
    _ = ∑ a : ZMod p, ∏ x, f ((fixedEquiv.symm a).val x - x) :=
      (fixedEquiv.symm.sum_comp _).symm
    _ = ∑ a, f a := by
      apply Finset.sum_congr rfl
      intro a _
      simpa [fixedEquiv] using ZMod.pow_card (f a)

/-- Source labels j,k run through 1,...,p. Absolute value is taken in the integers. -/
def A (p : ℕ) (s : ℤ) : Matrix (Fin p) (Fin p) ℤ :=
  fun j k => |((j.val : ℤ) + 1) - ((k.val : ℤ) + 1) + s|

/-- Sun, Conjecture 4.2(i): both (4.3) and (4.4), with denominators cleared. -/
def claim : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ((p : ℤ) ∣ 2 * Matrix.permanent (A p 0) + 1) ∧
    ((p : ℤ) ∣ 2 * Matrix.permanent (A p 1) - 1)

open scoped BigOperators

private theorem permanent_reindex {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommSemiring R]
    (e : α ≃ β) (M : Matrix β β R) :
    Matrix.permanent (M.submatrix e e) = Matrix.permanent M := by
  classical
  unfold Matrix.permanent
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp

private theorem permanent_sign {p : ℕ} (M : Matrix (Fin p) (Fin p) (ZMod p)) :
    Matrix.permanent (fun i j => (-1) ^ (i.val+j.val) * M i j) = Matrix.permanent M := by
  classical
  unfold Matrix.permanent
  apply Finset.sum_congr rfl
  intro σ _
  simp only [pow_add, Finset.prod_mul_distrib]
  rw [Equiv.prod_comp σ (fun i : Fin p => (-1 : ZMod p)^i.val)]
  have hsq : (∏ i : Fin p, (-1 : ZMod p) ^ i.val) *
      (∏ i : Fin p, (-1 : ZMod p) ^ i.val) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp [← pow_add, ← two_mul, pow_mul]
  rw [hsq, one_mul]

private theorem sign_entry {p : ℕ} (ho : Odd p) (s : ℤ)
    (hs : s = 0 ∨ s = 1) (i j : Fin p) :
    (-1 : ZMod p) ^ (i.val+j.val) * (A p s i j : ZMod p) =
      (-1) ^ (i-j).val * ((i-j).val + s : ZMod p) := by
  have hbound_i := i.isLt
  have hbound_j := j.isLt
  have hs0 : 0 ≤ s := by rcases hs with rfl | rfl <;> norm_num
  have hs1 : s ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  by_cases hij : j.val ≤ i.val
  · have hv : (i-j).val = i.val-j.val := by
      exact Fin.sub_val_of_le hij
    have habs : A p s i j = (i.val : ℤ) - j.val + s := by
      unfold A
      rw [abs_of_nonneg]
      · ring
      · exact_mod_cast (show (0 : ℤ) ≤ (i.val : ℤ) + 1 - (j.val+1) + s by omega)
    have hpar : (-1 : ZMod p) ^ (i.val+j.val) = (-1) ^ (i.val-j.val) := by
      have he : i.val+j.val = (i.val-j.val)+2*j.val := by omega
      rw [he, pow_add, pow_mul]
      norm_num
    rw [hv, habs, hpar]
    push_cast
    rw [Nat.cast_sub hij]
  · have hij' : i.val < j.val := Nat.lt_of_not_le hij
    have hv : (i-j).val = p+i.val-j.val := by
      have h := Fin.intCast_val_sub_eq_sub_add_ite i j
      simp only [ite_eq_right (show ¬j ≤ i from hij)] at h
      omega
    have habs : A p s i j = -((i.val : ℤ) - j.val + s) := by
      unfold A
      rw [abs_of_nonpos]
      · ring
      · omega
    have he : (p+i.val-j.val) + (i.val+j.val) = p + 2*i.val := by omega
    have hpows : (-1 : ZMod p) ^ (p+i.val-j.val) *
        (-1) ^ (i.val+j.val) = -1 := by
      rw [← pow_add, he, pow_add, ho.neg_one_pow, pow_mul]
      norm_num
    have hsq : (-1 : ZMod p) ^ (i.val+j.val) *
        (-1) ^ (i.val+j.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hpar : (-1 : ZMod p) ^ (p+i.val-j.val) =
        -((-1) ^ (i.val+j.val)) := by
      have hh := congrArg (fun z : ZMod p => z * (-1)^(i.val+j.val)) hpows
      simpa only [mul_assoc, hsq, mul_one, neg_mul, one_mul] using hh
    rw [hv, habs, hpar]
    have hjle : j.val ≤ p+i.val := by omega
    rw [Nat.cast_sub hjle]
    push_cast
    simp only [ZMod.natCast_self, zero_add]
    ring

private theorem alternating_sum (m : ℕ) (s : ℤ) :
    (∑ r ∈ Finset.range (2*m+1), (-1 : ℤ)^r * ((r : ℤ)+s)) = (m : ℤ)+s := by
  let g : ℕ → ℤ := fun r => (-1)^r * (2*(r : ℤ)+2*s-1)
  have hstep (r : ℕ) : g (r+1) - g r = -4 * ((-1 : ℤ)^r * ((r : ℤ)+s)) := by
    dsimp [g]
    rw [pow_succ]
    push_cast
    ring
  have ht := Finset.sum_range_sub g (2*m+1)
  simp_rw [hstep] at ht
  rw [← Finset.mul_sum] at ht
  have hn : (-1 : ℤ)^(2*m+1) = -1 := by simp [pow_add, pow_mul]
  dsimp [g] at ht
  rw [hn] at ht
  push_cast at ht
  linarith

private theorem permanent_map {α R S : Type*} [Fintype α] [DecidableEq α]
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (M : Matrix α α R) :
    Matrix.permanent (fun i j => f (M i j)) = f (Matrix.permanent M) := by
  simp [Matrix.permanent, map_sum, map_prod]

private theorem permanent_fin_circulant {p : ℕ} [Fact p.Prime] (f : Fin p → ZMod p) :
    Matrix.permanent (fun i j : Fin p => f (i-j)) = ∑ a, f a := by
  classical
  let e := ZMod.finEquiv p
  let g : ZMod p → ZMod p := fun x => f (e.symm x)
  calc
    _ = Matrix.permanent (Matrix.submatrix (fun i j : ZMod p => g (i-j)) e e) := by
      congr 1
      funext i j
      change f (i-j) = f (e.symm (e i - e j))
      rw [← e.map_sub, e.symm_apply_apply]
    _ = Matrix.permanent (fun i j : ZMod p => g (i-j)) := permanent_reindex e.toEquiv _
    _ = ∑ a : ZMod p, g a := permanent_circulant g
    _ = ∑ a : Fin p, f a := by
      simpa [g] using e.symm.toEquiv.sum_comp f

private theorem permanent_value {p : ℕ} (hp : p.Prime) (ho : Odd p) (s : ℤ)
    (hs : s = 0 ∨ s = 1) :
    ((Matrix.permanent (A p s) : ℤ) : ZMod p) = ((p/2 : ℕ) : ZMod p) + s := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f : Fin p → ZMod p := fun r => (-1)^r.val * ((r.val : ZMod p)+s)
  have hA : (fun i j : Fin p => (-1 : ZMod p)^(i.val+j.val) * (A p s i j : ZMod p)) =
      (fun i j => f (i-j)) := by
    funext i j
    exact sign_entry ho s hs i j
  calc
    _ = Matrix.permanent (fun i j : Fin p => (A p s i j : ZMod p)) :=
      (permanent_map (Int.castRingHom (ZMod p)) (A p s)).symm
    _ = Matrix.permanent (fun i j : Fin p => f (i-j)) := by
      rw [← hA]
      exact (permanent_sign _).symm
    _ = ∑ r : Fin p, f r := permanent_fin_circulant f
    _ = ((p/2 : ℕ) : ZMod p) + s := by
      obtain ⟨m, hm⟩ := ho
      have hdiv : p/2 = m := by omega
      have hsum : (∑ r : Fin p, (-1 : ℤ)^r.val * ((r.val : ℤ)+s)) = (m : ℤ)+s := by
        calc
          _ = ∑ r ∈ Finset.range p, (-1 : ℤ)^r * ((r : ℤ)+s) :=
            Fin.sum_univ_eq_sum_range (fun r : ℕ => (-1 : ℤ)^r * ((r : ℤ)+s)) p
          _ = (m : ℤ)+s := by simpa only [hm] using alternating_sum m s
      have hc := congrArg (Int.castRingHom (ZMod p)) hsum
      simpa [f, hdiv] using hc

theorem result : D5.S3.Combinatorics.Permanental.SunAbsoluteDifferenceCongruences.claim := by
  intro p hp ho
  letI : Fact p.Prime := ⟨hp⟩
  have h0 := permanent_value hp ho 0 (Or.inl rfl)
  have h1 := permanent_value hp ho 1 (Or.inr rfl)
  have hmod : 2 * ((p/2 : ℕ) : ZMod p) + 1 = 0 := by
    have he : 2 * (p/2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd ho
    have hc := congrArg (fun n : ℕ => (n : ZMod p)) he
    simpa using hc
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [h0]
    simpa using hmod
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [h1]
    linear_combination hmod

end D5.S3.Combinatorics.Permanental.SunAbsoluteDifferenceCongruences
