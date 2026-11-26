/- GID: D5/S3/Quantum/Matrix/JacobiEndpointResolvent
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/JacobiEndpointResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: A tridiagonal Green column factors through bonds and leading tail resolvents. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
/-!
# Endpoint resolvent of a finite Jacobi matrix

The Green column transfers across each bond by solving the equation on the next tail.
Indices start at zero, and the bonds in the first column formula are the lower
off-diagonal entries of the tridiagonal matrix.
-/

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Matrix.JacobiEndpointResolvent

variable {K : Type*} [Field K] {n : ℕ}

/-- The sites retained by the principal compression starting at `i`. -/
abbrev Tail (i : Fin n) := {j : Fin n // i ≤ j}

/-- The first site of a compressed tail, expressed in its own index type. -/
def tailFirst (i : Fin n) : Tail i := ⟨i, le_rfl⟩

/-- Principal compression to the sites at and after `i`. -/
def tail (A : Matrix (Fin n) (Fin n) K) (i : Fin n) : Matrix (Tail i) (Tail i) K :=
  A.submatrix Subtype.val Subtype.val

/-- The matrix whose inverse is the resolvent at `z`. -/
def spectralShift (H : Matrix (Fin n) (Fin n) K) (z : K) :
    Matrix (Fin n) (Fin n) K :=
  z • (1 : Matrix (Fin n) (Fin n) K) - H

/-- Matrix entries at distance greater than one from the diagonal vanish. -/
def IsTridiagonal (H : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → H i j = 0

/-- The bond from site `j` to its successor. The terminal value is never used in a product. -/
def bond (H : Matrix (Fin n) (Fin n) K) (j : Fin n) : K :=
  if hj : j.val + 1 < n then H ⟨j.val + 1, hj⟩ j else 0

/-- The product of lower bonds strictly before the site `i`. -/
def bondProduct (H : Matrix (Fin n) (Fin n) K) (i : Fin n) : K :=
  ∏ j ∈ Finset.Iio i, bond H j

/-- The first diagonal entry of the inverse of the tail of the shifted matrix `A`. -/
noncomputable def tailDiagonal (A : Matrix (Fin n) (Fin n) K) (i : Fin n) : K :=
  (tail A i)⁻¹ (tailFirst i) (tailFirst i)

/-- The product of leading inverse entries of all tails through the tail starting at `i`. -/
noncomputable def tailDiagonalProduct (A : Matrix (Fin n) (Fin n) K) (i : Fin n) : K :=
  ∏ j ∈ Finset.Iic i, tailDiagonal A j

/-- The first column of the inverse of the shifted matrix `A`. -/
noncomputable def firstColumn [NeZero n] (A : Matrix (Fin n) (Fin n) K) : Fin n → K :=
  (A⁻¹).col 0

private theorem spectralShift_offDiagonal (H : Matrix (Fin n) (Fin n) K) (z : K)
    {r j : Fin n} (h : r ≠ j) : spectralShift H z r j = -H r j := by
  rw [spectralShift, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h,
    smul_zero, zero_sub]

private theorem tail_mulVec_add_prefix (A : Matrix (Fin n) (Fin n) K)
    (x : Fin n → K) (i : Fin n) (r : Tail i) :
    (tail A i *ᵥ (fun j : Tail i => x j.val)) r +
        (∑ j : {j : Fin n // ¬ i ≤ j}, A r.val j.val * x j.val) =
      (A *ᵥ x) r.val := by
  exact Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => i ≤ j)
    (fun j => A r.val j * x j)

private theorem tail_mulVec_of_zero_before (A : Matrix (Fin n) (Fin n) K)
    (x : Fin n → K) (i : Fin n) (hx : ∀ j < i, x j = 0) (r : Tail i) :
    (tail A i *ᵥ (fun j : Tail i => x j.val)) r = (A *ᵥ x) r.val := by
  have hprefix : (∑ j : {j : Fin n // ¬ i ≤ j}, A r.val j.val * x j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hx j.val (lt_of_not_ge j.property), mul_zero]
  simpa only [hprefix, add_zero] using tail_mulVec_add_prefix A x i r

private theorem inverse_column_equation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (hA : IsUnit A.det) (i : ι) :
    A *ᵥ (A⁻¹).col i = Pi.single i (1 : K) := by
  rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA,
    Matrix.one_mulVec]

private def tailZeroEquiv [NeZero n] : Tail (0 : Fin n) ≃ Fin n where
  toFun := Subtype.val
  invFun j := ⟨j, Fin.zero_le j⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

private theorem tail_zero_det [NeZero n] (A : Matrix (Fin n) (Fin n) K) :
    (tail A 0).det = A.det :=
  Matrix.det_submatrix_equiv_self tailZeroEquiv A

private theorem tailDiagonal_zero [NeZero n] (A : Matrix (Fin n) (Fin n) K) :
    tailDiagonal A 0 = firstColumn A 0 := by
  change ((A.submatrix tailZeroEquiv tailZeroEquiv)⁻¹) (tailFirst 0) (tailFirst 0) =
    (A⁻¹) 0 0
  rw [Matrix.inv_submatrix_equiv]
  rfl

/-- The actual equation on a noninitial tail. Its only input is through the
bond from the preceding site. -/
private theorem tail_equation [NeZero n] (H : Matrix (Fin n) (Fin n) K) (z : K)
    (hH : IsTridiagonal H) (p i : Fin n) (hpi : p.val + 1 = i.val)
    (g : Fin n → K) (hg : spectralShift H z *ᵥ g = Pi.single (0 : Fin n) 1) :
    tail (spectralShift H z) i *ᵥ (fun j : Tail i => g j.val) =
      (H i p * g p) • Pi.single (tailFirst i) (1 : K) := by
  have hp : p < i := by
    change p.val < i.val
    omega
  let prev : {j : Fin n // ¬ i ≤ j} := ⟨p, not_le_of_gt hp⟩
  funext r
  have hr : i.val ≤ r.val.val := r.property
  have hrp : r.val ≠ p := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hrzero : r.val ≠ 0 := by
    intro h
    have hval : r.val.val = 0 := (congrArg Fin.val h).trans (Fin.val_zero n)
    omega
  have hprefix :
      (∑ j : {j : Fin n // ¬ i ≤ j}, spectralShift H z r.val j.val * g j.val) =
        spectralShift H z r.val p * g p := by
    change (∑ j : {j : Fin n // ¬ i ≤ j}, spectralShift H z r.val j.val * g j.val) =
      spectralShift H z r.val prev.val * g prev.val
    refine Finset.sum_eq_single_of_mem prev (Finset.mem_univ _) ?_
    intro j _ hj
    have hjlt : j.val.val < i.val := lt_of_not_ge j.property
    have hjp : j.val.val ≠ p.val := fun h => hj (Subtype.ext (Fin.ext h))
    have hgap : j.val.val + 1 < r.val.val := by omega
    have hne : r.val ≠ j.val := fun h => by
      have hval := congrArg Fin.val h
      omega
    rw [spectralShift_offDiagonal H z hne, hH r.val j.val (Or.inr hgap), neg_zero, zero_mul]
  have hrow : (spectralShift H z *ᵥ g) r.val = 0 := by
    rw [hg, Pi.single_eq_of_ne hrzero]
  have hsplit := tail_mulVec_add_prefix (spectralShift H z) g i r
  rw [hprefix, hrow] at hsplit
  calc
    (tail (spectralShift H z) i *ᵥ (fun j : Tail i => g j.val)) r =
        -(spectralShift H z r.val p * g p) := eq_neg_of_add_eq_zero_left hsplit
    _ = H r.val p * g p := by rw [spectralShift_offDiagonal H z hrp, neg_mul, neg_neg]
    _ = ((H i p * g p) • Pi.single (tailFirst i) (1 : K)) r := by
      by_cases hri : r.val = i
      · have h : r = tailFirst i := Subtype.ext hri
        rw [h, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        rfl
      · have hrval : r.val.val ≠ i.val := fun h => hri (Fin.ext h)
        have hgap : p.val + 1 < r.val.val := by omega
        have hne : r ≠ tailFirst i := fun h => hri (congrArg Subtype.val h)
        rw [hH r.val p (Or.inr hgap), zero_mul, Pi.smul_apply, Pi.single_eq_of_ne hne,
          smul_zero]

/-- One step of the Green-column transfer, with the incoming bond as a factor. -/
theorem firstColumn_step [NeZero n] (H : Matrix (Fin n) (Fin n) K) (z : K)
    (hH : IsTridiagonal H) (hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (p i : Fin n) (hpi : p.val + 1 = i.val) :
    firstColumn (spectralShift H z) i =
      (bond H p * firstColumn (spectralShift H z) p) * tailDiagonal (spectralShift H z) i := by
  let A := spectralShift H z
  let g := firstColumn A
  let B := tail A i
  have hA : IsUnit A.det := by
    rw [← tail_zero_det A]
    exact hInv 0
  have hg : A *ᵥ g = Pi.single (0 : Fin n) 1 := inverse_column_equation A hA 0
  have hcut : B *ᵥ (fun j : Tail i => g j.val) =
      (H i p * g p) • Pi.single (tailFirst i) (1 : K) :=
    tail_equation H z hH p i hpi g hg
  have hsolve : (fun j : Tail i => g j.val) = (H i p * g p) • (B⁻¹).col (tailFirst i) := by
    calc
      (fun j : Tail i => g j.val) = B⁻¹ *ᵥ (B *ᵥ (fun j : Tail i => g j.val)) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (hInv i), Matrix.one_mulVec]
      _ = (H i p * g p) • (B⁻¹).col (tailFirst i) := by
        rw [hcut, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  have hcoord := congrFun hsolve (tailFirst i)
  have hp : p.val + 1 < n := by
    rw [hpi]
    exact i.isLt
  have hbond : bond H p = H i p := by
    rw [bond, dite_eq_left hp, show (⟨p.val + 1, hp⟩ : Fin n) = i from Fin.ext hpi]
  rw [hbond]
  exact hcoord

/-- The first resolvent column is the product of the intervening bonds times
the product of the first diagonal resolvents of all tails through site `i`. -/
theorem firstColumn_eq [NeZero n] (H : Matrix (Fin n) (Fin n) K) (z : K)
    (hH : IsTridiagonal H) (hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (i : Fin n) :
    firstColumn (spectralShift H z) i =
      bondProduct H i * tailDiagonalProduct (spectralShift H z) i := by
  suffices h : ∀ (m : ℕ) (i : Fin n), i.val = m →
      firstColumn (spectralShift H z) i =
        bondProduct H i * tailDiagonalProduct (spectralShift H z) i from h i.val i rfl
  intro m
  induction m with
  | zero =>
      intro i hi
      have hi0 : i = 0 := Fin.val_eq_zero_iff.mp hi
      subst i
      have hbefore : Finset.Iio (0 : Fin n) = ∅ := by
        apply Finset.Iio_eq_empty.mpr
        intro j _
        exact Fin.zero_le j
      simp only [bondProduct, tailDiagonalProduct, ← Finset.prod_Iio_mul_eq_prod_Iic,
        hbefore, Finset.prod_empty, one_mul, tailDiagonal_zero]
  | succ m ih =>
      intro i hi
      have hm : m < n := by
        have hn := i.isLt
        omega
      let p : Fin n := ⟨m, hm⟩
      have hpi : p.val + 1 = i.val := hi.symm
      have hinterval : Finset.Iio i = Finset.Iic p := by
        ext j
        simp only [Finset.mem_Iio, Finset.mem_Iic]
        change j.val < i.val ↔ j.val ≤ p.val
        omega
      have hb : bondProduct H i = bondProduct H p * bond H p := by
        unfold bondProduct
        rw [hinterval, Finset.prod_Iio_mul_eq_prod_Iic p]
      have hd : tailDiagonalProduct (spectralShift H z) i =
          tailDiagonalProduct (spectralShift H z) p * tailDiagonal (spectralShift H z) i := by
        unfold tailDiagonalProduct
        rw [← Finset.prod_Iio_mul_eq_prod_Iic i, hinterval]
      rw [firstColumn_step H z hH hInv p i hpi, ih p rfl, hb, hd]
      ac_rfl

/-- Invertibility of successive tails forces each leading inverse diagonal
entry to be nonzero. A zero entry would give a homogeneous equation on the
next tail and hence a zero column, contradicting the unit input. -/
theorem tailDiagonal_ne_zero (A : Matrix (Fin n) (Fin n) K)
    (hInv : ∀ j : Fin n, IsUnit (tail A j).det) (i : Fin n) : tailDiagonal A i ≠ 0 := by
  intro hdiag
  let u := ((tail A i)⁻¹).col (tailFirst i)
  have hu : tail A i *ᵥ u = Pi.single (tailFirst i) (1 : K) :=
    inverse_column_equation (tail A i) (hInv i) (tailFirst i)
  let x : Fin n → K := fun j => if hj : i ≤ j then u ⟨j, hj⟩ else 0
  have hbefore (j : Fin n) (hj : j < i) : x j = 0 := dite_eq_right (not_le_of_gt hj)
  have hxi : x i = 0 := by
    dsimp only [x]
    rw [dite_eq_left (le_refl i)]
    exact hdiag
  have hrestrict : (fun j : Tail i => x j.val) = u := by
    funext j
    simp only [x, dite_eq_left j.property]
  have hxresult (r : Tail i) : (A *ᵥ x) r.val = (Pi.single (tailFirst i) 1 : Tail i → K) r := by
    rw [← tail_mulVec_of_zero_before A x i hbefore r, hrestrict, hu]
  have hxall (j : Fin n) : x j = 0 := by
    rcases lt_trichotomy j i with hj | rfl | hj
    · exact hbefore j hj
    · exact hxi
    · have hjval : i.val < j.val := hj
      let next : Fin n := ⟨i.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hjval) j.isLt⟩
      have hnext : next.val = i.val + 1 := rfl
      have hxnextBefore (k : Fin n) (hk : k < next) : x k = 0 := by
        have hkval : k.val < next.val := hk
        by_cases hki : k < i
        · exact hbefore k hki
        · have hle : i.val ≤ k.val := le_of_not_gt hki
          have heq : k = i := Fin.ext (by omega)
          exact (congrArg x heq).trans hxi
      have hhom : tail A next *ᵥ (fun k : Tail next => x k.val) = 0 := by
        funext r
        have hr : next.val ≤ r.val.val := r.property
        have hri : i ≤ r.val := by
          change i.val ≤ r.val.val
          omega
        have hne : (⟨r.val, hri⟩ : Tail i) ≠ tailFirst i := by
          intro h
          have heq : r.val.val = i.val := congrArg (fun k : Tail i => k.val.val) h
          omega
        rw [tail_mulVec_of_zero_before A x next hxnextBefore r]
        exact (hxresult ⟨r.val, hri⟩).trans (Pi.single_eq_of_ne hne _)
      have hz : (fun k : Tail next => x k.val) = 0 :=
        Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (hInv next))
          (hhom.trans (Matrix.mulVec_zero _).symm)
      have hjnext : next ≤ j := by
        change next.val ≤ j.val
        omega
      exact congrFun hz ⟨j, hjnext⟩
  have hu0 : u = 0 := hrestrict.symm.trans (funext fun j => hxall j.val)
  have hunit := congrFun hu (tailFirst i)
  rw [hu0, Matrix.mulVec_zero, Pi.single_eq_same] at hunit
  exact zero_ne_one hunit

/-- Under tail invertibility, a coordinate vanishes exactly when a bond
strictly before it vanishes. -/
theorem firstColumn_eq_zero_iff [NeZero n] (H : Matrix (Fin n) (Fin n) K) (z : K)
    (hH : IsTridiagonal H) (hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (i : Fin n) :
    firstColumn (spectralShift H z) i = 0 ↔ ∃ j : Fin n, j < i ∧ bond H j = 0 := by
  have hd : tailDiagonalProduct (spectralShift H z) i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => tailDiagonal_ne_zero (spectralShift H z) hInv j
  rw [firstColumn_eq H z hH hInv i, mul_eq_zero, or_iff_left hd, bondProduct,
    Finset.prod_eq_zero_iff]
  simp only [Finset.mem_Iio]

/-- Applying a perturbation with input columns supported in the first `k`
sites gives a sum of those columns, weighted by the two resolvent factors.
The filter also handles a collar longer than the path or an empty collar. -/
theorem supported_mulVec_firstColumn [NeZero n] {ι : Type*}
    (H : Matrix (Fin n) (Fin n) K) (z : K)
    (hH : IsTridiagonal H) (hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (W : Matrix ι (Fin n) K) (k : ℕ) (hW : ∀ j : Fin n, k ≤ j.val → W.col j = 0) :
    W *ᵥ firstColumn (spectralShift H z) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
        tailDiagonalProduct (spectralShift H z) j • (bondProduct H j • W.col j) := by
  funext r
  simp only [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
  calc
    (∑ j : Fin n, W r j * firstColumn (spectralShift H z) j) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
          W r j * firstColumn (spectralShift H z) j := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro j _ hj
      have hj' : ¬ j.val < k := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hw : W r j = 0 := congrFun (hW j (Nat.le_of_not_gt hj')) r
      rw [hw, zero_mul]
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [firstColumn_eq H z hH hInv j]
      change W r j * (bondProduct H j * tailDiagonalProduct (spectralShift H z) j) =
        tailDiagonalProduct (spectralShift H z) j * (bondProduct H j * W r j)
      ac_rfl

end D5.S3.Quantum.Matrix.JacobiEndpointResolvent
