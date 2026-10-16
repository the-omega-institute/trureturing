/- GID: D5/S3/Arith/Lattices/MinimalKernelPacking
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/MinimalKernelPacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimal nonnegative kernels satisfy a quantitative packing bound. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none; mathematical owners are pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17570.
floorWeights: proof_shape: bind-only; escape_witness: none; consumers: _proof_1_1, _proof_1_2, minimal_kernel_packing_bound, floorWeights_le, partialTotal, _proof_1_1, floorWeights_total_bound, floorWeights_mass_bounds, _proof_1_2, floorWeights_total_fiber.
floorWeights_mass_bounds: proof_shape: bind-only; escape_witness: none; consumers: minimal_kernel_packing_bound, floorWeights_total_fiber.
floorWeights_monotone: proof_shape: bind-only; escape_witness: none; consumers: floorWeights_total_fiber.
floorWeights_le: proof_shape: bind-only; escape_witness: none; consumers: floorWeights_total_fiber.
floorWeights_total_bound: proof_shape: bind-only; escape_witness: none; consumers: minimal_kernel_packing_bound.
partialTotal: proof_shape: bind-only; escape_witness: none; consumers: minimal_kernel_packing_bound, floorWeights_total_fiber.
floorWeights_total_fiber: proof_shape: bind-only; escape_witness: none; consumers: minimal_kernel_packing_bound.
minimal_kernel_packing_bound: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.MinimalKernelPacking.0.D5.S3.Arith.Lattices.MinimalKernelPacking.minimal_kernel_packing_bound; consumers: minimal_kernel_rank_deficient_bound.
rank_deficient_kernel_projection: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.MinimalKernelPacking.0.D5.S3.Arith.Lattices.MinimalKernelPacking.rank_deficient_kernel_projection; consumers: minimal_kernel_rank_deficient_bound.
minimal_kernel_rank_deficient_bound: proof_shape: content; escape_witness: _private.D5.S3.Arith.Lattices.MinimalKernelPacking.0.D5.S3.Arith.Lattices.MinimalKernelPacking.rank_deficient_kernel_projection; consumers: lengths_upper_bound.
transpose_injective_of_augmented_det: proof_shape: bind-only; escape_witness: none; consumers: exists_asymptotic_lower_family.
augmented_det_ne_zero_of_full_rank_positive: proof_shape: bind-only; escape_witness: none; consumers: lengths_upper_bound.
-/

import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.Int.Interval

noncomputable section
namespace D5.S3.Arith.Lattices.MinimalKernelPacking
open D5.S3.Arith.Lattices.CofactorKernel

open scoped BigOperators
open Matrix

private def floorWeights {k : ℕ} (x : Fin k → ℕ) (j : ℕ) : Fin k → ℕ :=
  fun i => j * x i / ∑ l, x l

private theorem floorWeights_mass_bounds {k : ℕ} (x : Fin k → ℕ)
    (hL : 0 < ∑ i, x i) (j : ℕ) :
    (∑ i, floorWeights x j i) ≤ j ∧ j < (∑ i, floorWeights x j i) + k := by
  let L := ∑ i, x i
  have hk : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    subst k
    simp at hL
  have hsum : L * (∑ i, floorWeights x j i) + ∑ i, (j*x i)%L = j*L := by
    calc
      L * (∑ i, floorWeights x j i) + ∑ i, (j*x i)%L =
          ∑ i, (L * floorWeights x j i + (j*x i)%L) := by
        rw [Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ i, j*x i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.div_add_mod (j*x i) L
      _ = j*L := by rw [← Finset.mul_sum]
  have hrem : ∑ i, (j*x i)%L ≤ k*(L-1) := by
    calc
      ∑ i, (j*x i)%L ≤ ∑ _i : Fin k, (L-1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.le_sub_one_of_lt (Nat.mod_lt _ hL)
      _ = k*(L-1) := by simp
  have hL' : 0 < L := hL
  have hm : (∑ i, floorWeights x j i) ≤ j := by
    by_contra hn
    have hlt := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hn) hL'
    have hle : L*(∑ i, floorWeights x j i) ≤ j*L := by omega
    rw [Nat.mul_comm j L] at hle
    exact (not_lt_of_ge hle) hlt
  constructor
  · exact hm
  · have hrem_lt : (∑ i, (j*x i)%L) < k*L := hrem.trans_lt
      (Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hL' (by decide)) hk)
    have hh : L*j < L*((∑ i, floorWeights x j i)+k) := by
      calc
        L*j = L*(∑ i, floorWeights x j i)+(∑ i, (j*x i)%L) := by
          simpa only [mul_comm j L] using hsum.symm
        _ < L*(∑ i, floorWeights x j i)+k*L := Nat.add_lt_add_left hrem_lt _
        _ = L*((∑ i, floorWeights x j i)+k) := by ring
    exact (Nat.mul_lt_mul_left hL').mp hh

private theorem floorWeights_monotone {k : ℕ} (x : Fin k → ℕ) :
    Monotone (floorWeights x) := by
  intro i j hij a
  exact Nat.div_le_div_right (Nat.mul_le_mul_right (x a) hij)

private theorem floorWeights_le {k : ℕ} (x : Fin k → ℕ) (j : ℕ)
    (hj : j ≤ ∑ i, x i) : floorWeights x j ≤ x := by
  intro i
  by_cases hL : ∑ l, x l = 0
  · simp [floorWeights, hL]
  · calc
      floorWeights x j i ≤ (∑ l, x l)*x i/(∑ l, x l) :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ hj)
      _ = x i := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hL)


private theorem floorWeights_total_bound {r k m : ℕ}
    (A : Matrix (Fin r) (Fin k) ℤ) (hA : ∀ i l, |A i l| ≤ m)
    (x : Fin k → ℕ) (hL : 0 < ∑ l, x l)
    (hx : ∀ i, ∑ l, A i l * (x l : ℤ) = 0) (j : ℕ) (i : Fin r) :
    |∑ l, A i l * (floorWeights x j l : ℤ)| ≤ k*m := by
  let L := ∑ l, x l
  have hLi : (0 : ℤ) < L := by exact_mod_cast hL
  have he (l : Fin k) : (L : ℤ) * floorWeights x j l =
      (j : ℤ)*x l - (j*x l%L : ℕ) := by
    have hh := Nat.div_add_mod (j*x l) L
    change L*floorWeights x j l+(j*x l)%L=j*x l at hh
    have hh' : (L : ℤ)*floorWeights x j l+(j*x l%L : ℕ)=(j : ℤ)*x l := by
      exact_mod_cast hh
    omega
  have ht : (L : ℤ)*(∑ l, A i l*(floorWeights x j l : ℤ)) =
      -∑ l, A i l*(j*x l%L : ℕ) := by
    calc
      (L : ℤ)*(∑ l, A i l*(floorWeights x j l : ℤ)) =
          ∑ l, A i l*((L : ℤ)*floorWeights x j l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = ∑ l, A i l*((j : ℤ)*x l-(j*x l%L : ℕ)) := by simp_rw [he]
      _ = (j : ℤ)*(∑ l, A i l*(x l : ℤ))-(∑ l, A i l*(j*x l%L : ℕ)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = -∑ l, A i l*(j*x l%L : ℕ) := by rw [hx i, mul_zero, zero_sub]
  have hb : |∑ l, A i l*(j*x l%L : ℕ)| ≤ (k : ℤ)*m*L := by
    calc
      |∑ l, A i l*(j*x l%L : ℕ)| ≤ ∑ l, |A i l*(j*x l%L : ℕ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin k, (m : ℤ)*L := by
        apply Finset.sum_le_sum
        intro l hl
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
        have hr : (j*x l%L : ℕ) ≤ (L : ℤ) := by exact_mod_cast (Nat.mod_lt (j*x l) hL).le
        exact mul_le_mul (hA i l) hr (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      _ = (k : ℤ)*m*L := by simp [mul_assoc]
  have hh := congrArg abs ht
  rw [abs_mul, abs_of_pos hLi, abs_neg] at hh
  have hmul : (L : ℤ)*|∑ l, A i l*(floorWeights x j l : ℤ)| ≤ (L : ℤ)*((k : ℤ)*m) := by
    rw [hh]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hb
  exact (mul_le_mul_iff_right₀ hLi).mp hmul


private def partialTotal {r k : ℕ} (A : Matrix (Fin r) (Fin k) ℤ) (x : Fin k → ℕ) (j : ℕ) :
    Fin r → ℤ := A *ᵥ fun l => (floorWeights x j l : ℤ)

private theorem floorWeights_total_fiber {r k : ℕ}
    (A : Matrix (Fin r) (Fin k) ℤ) (x : Fin k → ℕ) (hL : 0 < ∑ l, x l)
    (hmin : ∀ y : Fin k → ℕ, y ≤ x → A *ᵥ (fun l => (y l : ℤ)) = 0 → y=0 ∨ y=x)
    {j l : ℕ} (hj : j < ∑ a, x a) (hl : l < ∑ a, x a)
    (ht : partialTotal A x j = partialTotal A x l) : floorWeights x j = floorWeights x l := by
  have aux {j l : ℕ} (hjl : j ≤ l) (hl : l < ∑ a, x a)
      (ht : partialTotal A x j = partialTotal A x l) : floorWeights x j = floorWeights x l := by
    have hq := floorWeights_monotone x hjl
    let y : Fin k → ℕ := fun a => floorWeights x l a-floorWeights x j a
    have hyx : y ≤ x := fun a => (Nat.sub_le _ _).trans (floorWeights_le x l hl.le a)
    have hyker : A *ᵥ (fun a => (y a : ℤ)) = 0 := by
      have hcast : (fun a => (y a : ℤ)) =
          (fun a => (floorWeights x l a : ℤ))-(fun a => (floorWeights x j a : ℤ)) := by
        funext a
        exact Nat.cast_sub (hq a)
      rw [hcast, Matrix.mulVec_sub]
      change partialTotal A x l-partialTotal A x j=0
      rw [ht, sub_self]
    rcases hmin y hyx hyker with hy0 | hyall
    · funext a
      have h := congrFun hy0 a
      exact Nat.le_antisymm (hq a) (Nat.sub_eq_zero_iff_le.mp h)
    · have hm : ∑ a, y a ≤ l := by
        calc
          ∑ a, y a ≤ ∑ a, floorWeights x l a :=
            Finset.sum_le_sum (fun a ha => Nat.sub_le _ _)
          _ ≤ l := (floorWeights_mass_bounds x hL l).1
      rw [hyall] at hm
      omega
  rcases le_total j l with h | h
  · exact aux h hl ht
  · exact (aux h hj ht.symm).symm

private theorem minimal_kernel_packing_bound {r k m : ℕ}
    (A : Matrix (Fin r) (Fin k) ℤ) (hA : ∀ i l, |A i l| ≤ m)
    (x : Fin k → ℕ) (hL : 0 < ∑ l, x l)
    (hx : A *ᵥ (fun l => (x l : ℤ)) = 0)
    (hmin : ∀ y : Fin k → ℕ, y ≤ x → A *ᵥ (fun l => (y l : ℤ)) = 0 → y=0 ∨ y=x) :
    ∑ l, x l ≤ (2*k*m+1)^r*k := by
  classical
  let L := ∑ l, x l
  let I := Finset.Icc (-(k*m : ℤ)) (k*m : ℤ)
  have hp (j : Fin L) (i : Fin r) : partialTotal A x j.val i ∈ I := by
    apply Finset.mem_Icc.mpr
    exact abs_le.mp (floorWeights_total_bound A hA x hL
      (fun i => congrFun hx i) j.val i)
  have hr (j : Fin L) : j.val-(∑ a, floorWeights x j.val a) < k := by
    have h := floorWeights_mass_bounds x hL j.val
    omega
  let enc : Fin L → ((Fin r → I) × Fin k) := fun j =>
    (fun i => ⟨partialTotal A x j.val i,hp j i⟩,
      ⟨j.val-(∑ a, floorWeights x j.val a),hr j⟩)
  have hinj : Function.Injective enc := by
    intro j l h
    have ht : partialTotal A x j.val = partialTotal A x l.val := by
      funext i
      exact congrArg (fun z => ((z.1 i : I) : ℤ)) h
    have hq := floorWeights_total_fiber A x hL hmin j.isLt l.isLt ht
    have he : j.val-(∑ a, floorWeights x j.val a)=l.val-(∑ a, floorWeights x l.val a) :=
      congrArg (fun z => (z.2 : Fin k).val) h
    have hj := (floorWeights_mass_bounds x hL j.val).1
    have hl := (floorWeights_mass_bounds x hL l.val).1
    rw [hq] at he hj
    apply Fin.ext
    omega
  have hc : I.card=2*k*m+1 := by
    rw [Int.card_Icc]
    have hi : (k*m : ℤ)+1-(-(k*m : ℤ))=((2*k*m+1 : ℕ) : ℤ) := by push_cast; ring
    rw [hi, Int.toNat_natCast]
  have hb := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_pi, Fintype.card_coe,
    hc, Finset.prod_const, Finset.card_univ] using hb

open scoped BigOperators
open Matrix

private theorem rank_deficient_kernel_projection {r k : ℕ}
    (M : Matrix (Fin (r+1)) (Fin k) ℤ)
    (hM : ¬Function.Injective (fun z : Fin (r+1) → ℤ => M.transpose *ᵥ z)) :
    ∃ i : Fin (r+1), ∀ y : Fin k → ℤ,
      (M.submatrix i.succAbove id) *ᵥ y = 0 ↔ M *ᵥ y = 0 := by
  classical
  have hker : ∃ z : Fin (r+1) → ℤ, z ≠ 0 ∧ M.transpose *ᵥ z=0 := by
    by_contra hn
    apply hM
    intro a b hab
    change M.transpose *ᵥ a = M.transpose *ᵥ b at hab
    have hsub : M.transpose *ᵥ (a-b)=0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have hz : a-b=0 := by
      by_contra hz
      exact hn ⟨a-b,hz,hsub⟩
    exact sub_eq_zero.mp hz
  obtain ⟨z,hzn,hzk⟩ := hker
  obtain ⟨i,hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra hn
    apply hzn
    funext i
    by_contra hi
    exact hn ⟨i,hi⟩
  refine ⟨i, fun y => ⟨fun hy => ?_,fun hy => ?_⟩⟩
  · have hout (j : Fin r) : (M *ᵥ y) (i.succAbove j)=0 := congrFun hy j
    have hdot : z ⬝ᵥ M *ᵥ y=0 := by
      rw [← Matrix.dotProduct_transpose_mulVec, hzk, dotProduct_zero]
    change ∑ j, z j*(M *ᵥ y) j=0 at hdot
    rw [Fin.sum_univ_succAbove _ i] at hdot
    simp only [hout, mul_zero, Finset.sum_const_zero, add_zero] at hdot
    have hin : (M *ᵥ y) i=0 := (mul_eq_zero.mp hdot).resolve_left hi
    funext j
    exact Fin.succAboveCases i hin hout j
  · funext j
    exact congrFun hy (i.succAbove j)

theorem minimal_kernel_rank_deficient_bound {r k m : ℕ}
    (M : Matrix (Fin (r+1)) (Fin k) ℤ) (hM : ∀ i j, |M i j| ≤ m)
    (hdef : ¬Function.Injective (fun z : Fin (r+1) → ℤ => M.transpose *ᵥ z))
    (x : Fin k → ℕ) (hL : 0 < ∑ j, x j)
    (hx : M *ᵥ (fun j => (x j : ℤ))=0)
    (hmin : ∀ y : Fin k → ℕ, y ≤ x → M *ᵥ (fun j => (y j : ℤ))=0 → y=0 ∨ y=x) :
    ∑ j, x j ≤ (2*k*m+1)^r*k := by
  obtain ⟨i,hi⟩ := rank_deficient_kernel_projection M hdef
  apply minimal_kernel_packing_bound (M.submatrix i.succAbove id)
    (fun a b => hM (i.succAbove a) b) x hL ((hi _).mpr hx)
  intro y hy hyk
  exact hmin y hy ((hi _).mp hyk)

theorem transpose_injective_of_augmented_det {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ) (hdet : (augment M).det ≠ 0) :
    Function.Injective (fun z : Fin d → ℤ => M.transpose *ᵥ z) := by
  have hlin := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hs : LinearIndependent ℤ (fun i : Fin d => M i) := by
    have ht := hlin.comp Fin.succ (Fin.succ_injective d)
    change LinearIndependent ℤ (fun i : Fin d => (augment M) i.succ) at ht
    have he : (fun i : Fin d => (augment M) i.succ) = (fun i : Fin d => M i) := by
      funext i j
      rfl
    rw [he] at ht
    exact ht
  exact Matrix.mulVec_injective_iff.mpr hs

open scoped BigOperators
open Matrix

theorem augmented_det_ne_zero_of_full_rank_positive {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hM : Function.Injective (fun z : Fin d → ℤ => M.transpose *ᵥ z))
    (x : Fin (d+1) → ℤ) (hx : M *ᵥ x=0) (hsum : ∑ j, x j ≠ 0) :
    (augment M).det ≠ 0 := by
  have hker : ∀ z : Fin (d+1) → ℤ, (augment M).transpose *ᵥ z=0 → z=0 := by
    intro z hz
    have haug : augment M *ᵥ x = Pi.single 0 (∑ j, x j) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [Matrix.mulVec, dotProduct, augment_zero]
      · simpa [Matrix.mulVec, dotProduct, augment_succ] using congrFun hx i
    have hdot : z ⬝ᵥ (augment M *ᵥ x)=0 := by
      rw [← Matrix.dotProduct_transpose_mulVec, hz, dotProduct_zero]
    rw [haug] at hdot
    have hz0 : z 0=0 := by
      have he : z 0*(∑ j, x j)=0 := by simpa [dotProduct, Pi.single_apply] using hdot
      exact (mul_eq_zero.mp he).resolve_right hsum
    have htail : M.transpose *ᵥ (fun i => z i.succ)=0 := by
      funext j
      have he := congrFun hz j
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Fin.sum_univ_succ, augment_zero, augment_succ, hz0] using he
    have htail0 : (fun i : Fin d => z i.succ)=0 := hM (by simpa using htail)
    funext i
    refine Fin.cases hz0 (fun i => congrFun htail0 i) i
  have hinj : Function.Injective (fun z : Fin (d+1) → ℤ => (augment M).transpose *ᵥ z) := by
    intro a b hab
    change (augment M).transpose *ᵥ a=(augment M).transpose *ᵥ b at hab
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, hab, sub_self]
  have hn := Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hinj)
  simpa only [Matrix.det_transpose] using Matrix.nonsingular_iff_det_ne_zero.mp hn

end D5.S3.Arith.Lattices.MinimalKernelPacking
