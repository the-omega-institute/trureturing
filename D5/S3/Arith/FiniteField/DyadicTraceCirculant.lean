/- GID: D5/S3/Arith/FiniteField/DyadicTraceCirculant
   generality: G
   mirror-B: D5/B/S3/Arith/FiniteField/DyadicTraceCirculant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit dyadic trace-circulant consecutive sections over the binary field. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import D5.S3.Analytic.GoldenTomography.FinitePronyMatrixPencil

/-!
# Unit dyadic trace-circulant sections

The binary trace-one spectrum has exactly half the field cardinality. Its
root-sum kernel identifies the consecutive circulant section with a column
reversal of a square finite Prony Hankel matrix.
-/

namespace D5.S3.Arith.FiniteField.DyadicTraceCirculant

open scoped BigOperators

/-- Directed cyclic displacement; the endpoint casts precede subtraction. -/
def dyadicTraceCirculant (k t : ℕ) :
    Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) (ZMod 2) :=
  fun x y => ∑ i : Fin k,
    if ((y.val : ZMod (2 ^ k - 1)) - (x.val : ZMod (2 ^ k - 1))) =
        (t : ZMod (2 ^ k - 1)) * (2 : ZMod (2 ^ k - 1)) ^ i.val
    then 1 else 0


local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private abbrev BinaryField (k : ℕ) := GaloisField 2 k

noncomputable local instance (k : ℕ) : Fintype (BinaryField k) := Fintype.ofFinite _

open scoped Classical

private lemma binary_field_card {k : ℕ} (hk : k ≠ 0) :
    Fintype.card (BinaryField k) = 2 ^ k := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 k hk

private lemma binary_trace_fiber_card {k : ℕ} (hk : k ≠ 0) :
    Fintype.card {a : BinaryField k // Algebra.trace (ZMod 2) (BinaryField k) a = 1} =
      2 ^ (k - 1) := by
  classical
  let tr := (Algebra.trace (ZMod 2) (BinaryField k)).toAddMonoidHom
  have hsurj : Function.Surjective tr :=
    Algebra.trace_surjective (ZMod 2) (BinaryField k)
  have hker := AddSubgroup.card_ker_mul_card_of_surjective (f := tr) hsurj
  have hfiber := AddMonoidHom.card_fiber_eq_of_mem_range tr
    (hsurj 0) (hsurj 1)
  have hzero : (Finset.univ.filter fun a : BinaryField k => tr a = 0).card =
      Nat.card tr.ker := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hbase : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hbase, GaloisField.card 2 k hk, hpow] at hker
  rw [Fintype.card_subtype]
  change (Finset.univ.filter fun a : BinaryField k => tr a = 1).card = _
  rw [← hfiber, hzero]
  omega

private lemma trace_spectrum_card {k t : ℕ} (hk : k ≠ 0)
    (ht : Nat.Coprime t (2 ^ k - 1)) :
    Fintype.card {u : (BinaryField k)ˣ //
      Algebra.trace (ZMod 2) (BinaryField k) ((u : BinaryField k) ^ t) = 1} =
      2 ^ (k - 1) := by
  classical
  have hcop : (Nat.card (BinaryField k)ˣ).Coprime t := by
    rw [Nat.card_units, GaloisField.card 2 k hk]
    exact ht.symm
  let ep := powCoprime hcop
  let e₁ : {u : (BinaryField k)ˣ //
        Algebra.trace (ZMod 2) (BinaryField k) ((u : BinaryField k) ^ t) = 1} ≃
      {u : (BinaryField k)ˣ // Algebra.trace (ZMod 2) (BinaryField k) (u : BinaryField k) = 1} :=
    { toFun := fun u => ⟨ep u, by simpa [ep, powCoprime] using u.2⟩
      invFun := fun u => ⟨ep.symm u, by
        have h := u.2
        rw [← ep.apply_symm_apply u] at h
        simpa [ep, powCoprime] using h⟩
      left_inv := fun u => Subtype.ext (ep.symm_apply_apply u)
      right_inv := fun u => Subtype.ext (ep.apply_symm_apply u) }
  let e₂ : {u : (BinaryField k)ˣ //
        Algebra.trace (ZMod 2) (BinaryField k) (u : BinaryField k) = 1} ≃
      {a : BinaryField k // Algebra.trace (ZMod 2) (BinaryField k) a = 1} :=
    { toFun := fun u => ⟨u.1, u.2⟩
      invFun := fun a => ⟨Units.mk0 a.1 (by
        intro ha
        have h := a.2
        simp [ha] at h), a.2⟩
      left_inv := by intro u; apply Subtype.ext; apply Units.ext; rfl
      right_inv := by intro a; rfl }
  rw [Fintype.card_congr (e₁.trans e₂)]
  exact binary_trace_fiber_card hk

private lemma unit_inverse_power {k : ℕ} (hk : k ≠ 0)
    (u : (BinaryField k)ˣ) {y : ℕ} (hy : y ≤ 2 ^ k - 1) :
    ((u : BinaryField k) ^ y)⁻¹ = (u : BinaryField k) ^ (2 ^ k - 1 - y) := by
  have hN : (u : BinaryField k) ^ (2 ^ k - 1) = 1 := by
    simpa [Fintype.card_units, binary_field_card hk] using
      congrArg Units.val (pow_card_eq_one (x := u))
  apply (mul_right_injective₀ (pow_ne_zero y u.ne_zero))
  dsimp only
  rw [mul_inv_cancel₀ (pow_ne_zero y u.ne_zero), ← pow_add,
    Nat.add_sub_of_le hy, hN]

private lemma unit_root_sum {k : ℕ} (hk : k ≠ 0) (a : ℕ) :
    (∑ u : (BinaryField k)ˣ, (u : BinaryField k) ^ a) =
      if (2 ^ k - 1) ∣ a then 1 else 0 := by
  classical
  rw [FiniteField.sum_pow_units, binary_field_card hk]
  have hneg : (-1 : BinaryField k) = 1 := by
    have htwo : (2 : BinaryField k) = 0 := CharP.cast_eq_zero _ 2
    linear_combination -htwo
  rw [hneg]

private lemma binary_trace_indicator {k : ℕ} (a : BinaryField k) :
    (if Algebra.trace (ZMod 2) (BinaryField k) a = 1 then
      (1 : BinaryField k) else 0) =
      algebraMap (ZMod 2) (BinaryField k)
        (Algebra.trace (ZMod 2) (BinaryField k) a) := by
  generalize Algebra.trace (ZMod 2) (BinaryField k) a = b
  by_cases hb : b = 1
  · rw [hb, if_pos rfl, map_one]
  · have hb0 : b = 0 := by
      apply (ZMod.val_eq_zero b).mp
      have hlt := ZMod.val_lt b
      have hne : b.val ≠ 1 := fun h => hb ((ZMod.val_eq_one (by decide) b).mp h)
      omega
    rw [if_neg hb, hb0, map_zero]

private lemma trace_kernel_identity {k t x y : ℕ} (hk : k ≠ 0)
    (hy : y ≤ 2 ^ k - 1) :
    algebraMap (ZMod 2) (BinaryField k)
      (∑ i : Fin k, if ((y : ZMod (2 ^ k - 1)) - (x : ZMod (2 ^ k - 1))) =
        (t : ZMod (2 ^ k - 1)) * 2 ^ i.val then (1 : ZMod 2) else 0) =
    ∑ u ∈ (Finset.univ.filter fun u : (BinaryField k)ˣ =>
        Algebra.trace (ZMod 2) (BinaryField k) ((u : BinaryField k) ^ t) = 1),
      (u : BinaryField k) ^ x * ((u : BinaryField k) ^ y)⁻¹ := by
  classical
  have htrace (u : (BinaryField k)ˣ) :
      algebraMap (ZMod 2) (BinaryField k)
        (Algebra.trace (ZMod 2) (BinaryField k) ((u : BinaryField k) ^ t)) =
      ∑ i : Fin k, (u : BinaryField k) ^ (t * 2 ^ i.val) := by
    rw [FiniteField.algebraMap_trace_eq_sum_pow,
      GaloisField.finrank 2 hk]
    simp only [Nat.card_eq_fintype_card, ZMod.card, ← pow_mul]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have hdisplacement (i : Fin k) :
      (2 ^ k - 1) ∣ t * 2 ^ i.val + x + (2 ^ k - 1 - y) ↔
        ((y : ZMod (2 ^ k - 1)) - (x : ZMod (2 ^ k - 1))) =
          (t : ZMod (2 ^ k - 1)) * 2 ^ i.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hny : ((2 ^ k - 1 - y : ℕ) : ZMod (2 ^ k - 1)) =
        -(y : ZMod (2 ^ k - 1)) := by
      rw [Nat.cast_sub hy, ZMod.natCast_self, zero_sub]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hny]
    constructor <;> intro h <;> linear_combination -h
  symm
  calc
    _ = ∑ u : (BinaryField k)ˣ,
        algebraMap (ZMod 2) (BinaryField k)
          (Algebra.trace (ZMod 2) (BinaryField k) ((u : BinaryField k) ^ t)) *
          ((u : BinaryField k) ^ x * ((u : BinaryField k) ^ y)⁻¹) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      rw [← binary_trace_indicator]
      split_ifs <;> simp
    _ = ∑ u : (BinaryField k)ˣ, ∑ i : Fin k,
        (u : BinaryField k) ^ (t * 2 ^ i.val + x + (2 ^ k - 1 - y)) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [htrace, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [unit_inverse_power hk u hy]
      simp only [pow_add, mul_assoc]
    _ = ∑ i : Fin k, ∑ u : (BinaryField k)ˣ,
        (u : BinaryField k) ^ (t * 2 ^ i.val + x + (2 ^ k - 1 - y)) :=
      Finset.sum_comm
    _ = ∑ i : Fin k,
        if ((y : ZMod (2 ^ k - 1)) - (x : ZMod (2 ^ k - 1))) =
          (t : ZMod (2 ^ k - 1)) * 2 ^ i.val then (1 : BinaryField k) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [unit_root_sum hk, hdisplacement]
    _ = _ := by simp only [map_sum, apply_ite, map_one, map_zero]

/-- The consecutive half-size section of every unit dyadic circulant has determinant one. -/
theorem dyadic_trace_circulant_det_one {k t : ℕ} (hk : 2 ≤ k)
    (ht : Nat.Coprime t (2 ^ k - 1)) :
    Matrix.det (dyadicTraceCirculant k t) = 1 := by
  classical
  have hk0 : k ≠ 0 := by omega
  let M := 2 ^ (k - 1)
  let S : Finset (BinaryField k)ˣ := Finset.univ.filter fun u =>
    Algebra.trace (ZMod 2) (BinaryField k) ((u : BinaryField k) ^ t) = 1
  have hS : Fintype.card ↥S = M := by
    simpa [S, M, Fintype.card_subtype] using trace_spectrum_card hk0 ht
  let e : Fin M ≃ ↥S := (Fintype.equivFinOfCardEq hS).symm
  let nodes : Fin M → BinaryField k := fun i => ((e i).1 : BinaryField k)
  let weights : Fin M → BinaryField k := fun i => (nodes i ^ (M - 1))⁻¹
  have hn : Function.Injective nodes := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact Units.ext hij
  have hn0 (i : Fin M) : nodes i ≠ 0 := (e i).1.ne_zero
  have hw (i : Fin M) : weights i ≠ 0 := inv_ne_zero (pow_ne_zero _ (hn0 i))
  let B := (dyadicTraceCirculant k t).map (algebraMap (ZMod 2) (BinaryField k))
  have hMN : M ≤ 2 ^ k - 1 := by
    have hp : 0 < 2 ^ (k - 1) := pow_pos (by decide) _
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    dsimp [M]
    omega
  have hH : B.submatrix id Fin.revPerm =
      D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport.finitePronyShiftedHankel
        (n := M) nodes weights 0 := by
    ext x y
    change algebraMap (ZMod 2) (BinaryField k)
      (dyadicTraceCirculant k t x y.rev) =
      ∑ i : Fin M, weights i * nodes i ^ (0 + x.val + y.val)
    unfold dyadicTraceCirculant
    rw [trace_kernel_identity hk0 (le_trans (Nat.le_of_lt y.rev.isLt) hMN)]
    change (∑ u ∈ S, (u : BinaryField k) ^ x.val *
      ((u : BinaryField k) ^ y.rev.val)⁻¹) = _
    rw [← Finset.sum_coe_sort S]
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro i _
    change nodes i ^ x.val * (nodes i ^ y.rev.val)⁻¹ =
      (nodes i ^ (M - 1))⁻¹ * nodes i ^ (0 + x.val + y.val)
    have hrev : y.rev.val + y.val = M - 1 := by
      simp only [Fin.val_rev]
      omega
    field_simp [hn0 i]
    simp only [← pow_add]
    congr 1
    omega
  have hdet :=
    D5.S3.Analytic.GoldenTomography.FinitePronyMatrixPencil.finite_prony_square_hankel_det_ne_zero
      hn hw
  have hB : B.det ≠ 0 := by
    intro hzero
    apply hdet
    rw [← hH, Matrix.det_permute', hzero, mul_zero]
  have hA : (dyadicTraceCirculant k t).det ≠ 0 := by
    intro hzero
    apply hB
    exact ((algebraMap (ZMod 2) (BinaryField k)).map_det
      (dyadicTraceCirculant k t)).symm.trans (by rw [hzero, map_zero])
  apply ZMod.val_injective 2
  have hval := ZMod.val_lt (dyadicTraceCirculant k t).det
  have hnon : ((dyadicTraceCirculant k t).det).val ≠ 0 := by
    intro hz
    exact hA ((ZMod.val_eq_zero _).mp hz)
  change ((dyadicTraceCirculant k t).det).val = 1
  omega

end D5.S3.Arith.FiniteField.DyadicTraceCirculant
