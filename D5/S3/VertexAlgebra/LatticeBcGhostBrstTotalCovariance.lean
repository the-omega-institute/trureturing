/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstTotalCovariance
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstTotalCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full original BRST charge has the rank-minus-26 total-stress anomaly. -/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.VertexAlgebra.BcGhostVirasoro
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Int.Cast.Field
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport BcGhostStressCurrent BcGhostStressTails
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

private def matterCentral (D : LatticeData) (m : ℤ) : ℂ :=
  (D.rank : ℂ) / 12 * ((m : ℂ) ^ 3 - m)

private def ghostCentral (m : ℤ) : ℂ :=
  -(13 : ℂ) / 6 * ((m : ℂ) ^ 3 - m)

private def matterRow (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) : Module.End ℂ (State D) :=
  C D (-n) * M D H (m + n)

private def ghostRow (D : LatticeData) (m n : ℤ) : Module.End ℂ (State D) :=
  if -1 ≤ n then C D (-n) * G D (m + n) else G D (m + n) * C D (-n)

private def ghostFirst (D : LatticeData) (m n : ℤ) : Module.End ℂ (State D) :=
  if -1 ≤ n then C D (m - n) * G D n else G D n * C D (m - n)

private def branchScalar (m n : ℤ) : ℂ :=
  if -1 ≤ n + m then
    if -1 ≤ n then 0 else (n - m : ℂ) * (2 * m + n)
  else
    if -1 ≤ n then -((n - m : ℂ) * (2 * m + n)) else 0

private def primitive (m n : ℤ) : ℂ :=
  (n : ℂ) * (n - 1) * (2 * n - 1) / 6 +
    (m : ℂ) * n * (n - 1) / 2 - 2 * (m : ℂ) ^ 2 * n

private theorem branch_window (m n : ℤ) :
    branchScalar m n =
      if 0 ≤ m then
        if n ∈ Finset.Ico (-m - 1) (-1) then (n - m : ℂ) * (2 * m + n) else 0
      else
        if n ∈ Finset.Ico (-1) (-m - 1) then -((n - m : ℂ) * (2 * m + n)) else 0 := by
  by_cases hm : 0 ≤ m
  · by_cases hwindow : n ∈ Finset.Ico (-m - 1) (-1)
    · have hb := Finset.mem_Ico.mp hwindow
      have hn : ¬ -1 ≤ n := by omega
      have hs : -1 ≤ n + m := by omega
      simp only [branchScalar, hm, hwindow, hn, hs, if_true, if_false]
    · have hsame : (-1 ≤ n + m) ↔ (-1 ≤ n) := by
        constructor
        · intro hs
          by_contra hn
          exact hwindow (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        · intro hn
          omega
      by_cases hn : -1 ≤ n
      · have hs := hsame.mpr hn
        simp only [branchScalar, hm, hwindow, hn, hs, if_true, if_false]
      · have hs : ¬ -1 ≤ n + m := fun h => hn (hsame.mp h)
        simp only [branchScalar, hm, hwindow, hn, hs, if_true, if_false]
  · by_cases hwindow : n ∈ Finset.Ico (-1) (-m - 1)
    · have hb := Finset.mem_Ico.mp hwindow
      have hn : -1 ≤ n := by omega
      have hs : ¬ -1 ≤ n + m := by omega
      simp only [branchScalar, hm, hwindow, hn, hs, if_true, if_false]
    · have hsame : (-1 ≤ n + m) ↔ (-1 ≤ n) := by
        constructor
        · intro hs
          omega
        · intro hn
          by_contra hs
          exact hwindow (Finset.mem_Ico.mpr ⟨hn, by omega⟩)
      by_cases hn : -1 ≤ n
      · have hs := hsame.mpr hn
        simp only [branchScalar, hm, hwindow, hn, hs, if_true, if_false]
      · have hs : ¬ -1 ≤ n + m := fun h => hn (hsame.mp h)
        simp only [branchScalar, hm, hwindow, hn, hs, if_true, if_false]

private theorem branch_finite (m : ℤ) : Function.HasFiniteSupport (branchScalar m) := by
  by_cases hm : 0 ≤ m
  · apply (Finset.Ico (-m - 1) (-1)).finite_toSet.subset
    intro n hn
    change n ∈ Finset.Ico (-m - 1) (-1)
    by_contra hout
    exact hn (by simp only [branch_window, hm, hout, if_true, if_false])
  · apply (Finset.Ico (-1) (-m - 1)).finite_toSet.subset
    intro n hn
    change n ∈ Finset.Ico (-1) (-m - 1)
    by_contra hout
    exact hn (by simp only [branch_window, hm, hout, if_true, if_false])

private theorem primitive_step (m n : ℤ) :
    primitive m (n + 1) - primitive m n = (n - m : ℂ) * (2 * m + n) := by
  simp only [primitive, Int.cast_add, Int.cast_one]
  ring

private theorem telescope (function : ℤ → ℂ) (lower upper : ℤ) (h : lower ≤ upper) :
    (∑ n ∈ Finset.Ico lower upper, (function (n + 1) - function n)) =
      function upper - function lower := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  change (∑ index ∈ Finset.range (upper - lower).toNat,
    (function (lower + (index : ℤ) + 1) - function (lower + (index : ℤ)))) = _
  have hend : lower + ((upper - lower).toNat : ℤ) = upper := by
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ upper - lower)]
    omega
  calc
    _ = function (lower + ((upper - lower).toNat : ℤ)) - function (lower + 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc] using
        (Finset.sum_range_sub (fun index : ℕ => function (lower + (index : ℤ)))
          (upper - lower).toNat)
    _ = _ := by rw [hend, add_zero]

private theorem branch_sum (m : ℤ) :
    (∑ᶠ n : ℤ, branchScalar m n) = ghostCentral m := by
  classical
  by_cases hm : 0 ≤ m
  · have hsupport : Function.support (branchScalar m) ⊆
        (Finset.Ico (-m - 1) (-1) : Set ℤ) := by
      intro n hn
      change n ∈ Finset.Ico (-m - 1) (-1)
      by_contra hout
      exact hn (by simp only [branch_window, hm, hout, if_true, if_false])
    rw [finsum_eq_sum_of_support_subset _ hsupport]
    calc
      _ = ∑ n ∈ Finset.Ico (-m - 1) (-1),
          (primitive m (n + 1) - primitive m n) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [branch_window, hm, hn, if_true, primitive_step]
      _ = primitive m (-1) - primitive m (-m - 1) :=
        telescope (primitive m) _ _ (by omega)
      _ = ghostCentral m := by
        simp only [primitive, ghostCentral, Int.cast_sub, Int.cast_neg, Int.cast_one]
        ring
  · have hsupport : Function.support (branchScalar m) ⊆
        (Finset.Ico (-1) (-m - 1) : Set ℤ) := by
      intro n hn
      change n ∈ Finset.Ico (-1) (-m - 1)
      by_contra hout
      exact hn (by simp only [branch_window, hm, hout, if_true, if_false])
    rw [finsum_eq_sum_of_support_subset _ hsupport]
    calc
      _ = -(∑ n ∈ Finset.Ico (-1) (-m - 1),
          (primitive m (n + 1) - primitive m n)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [branch_window, hm, hn, if_false, if_true, primitive_step]
      _ = -(primitive m (-m - 1) - primitive m (-1)) := by
        rw [telescope (primitive m) _ _ (by omega)]
      _ = ghostCentral m := by
        simp only [primitive, ghostCentral, Int.cast_sub, Int.cast_neg, Int.cast_one]
        ring

private theorem integral_central (m : ℤ) :
    ((-13 * (m ^ 3 - m) / 6 : ℤ) : ℂ) = ghostCentral m := by
  have hdiv : (6 : ℤ) ∣ m ^ 3 - m := by
    have hexisting := Nat.factorial_coe_dvd_prod 3 (m - 1)
    norm_num [Finset.prod_range_succ] at hexisting
    convert hexisting using 1 <;> ring
  rw [Int.cast_div (dvd_mul_of_dvd_right hdiv (-13)) (by norm_num : (6 : ℂ) ≠ 0)]
  simp only [ghostCentral, Int.cast_mul, Int.cast_sub, Int.cast_pow]
  norm_num
  ring

private theorem lift_mc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    M D H m * C D n = C D n * M D H m := by
  apply TensorProduct.ext'
  intro matter ghost
  simp [M, C, Module.End.mul_apply]

private theorem lift_mg (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    M D H m * G D n = G D n * M D H m := by
  apply TensorProduct.ext'
  intro matter ghost
  simp [M, G, Module.End.mul_apply]

private theorem lift_gc (D : LatticeData) (m n : ℤ) :
    G D m * C D n - C D n * G D m = (-2 * m - n : ℂ) • C D (m + n) := by
  have h := congrArg (LinearMap.lTensorHom (Carrier D))
    (L_c_commutator (K := ℂ) m n)
  simp only [map_sub, map_smul, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at h
  simpa only [G, C, LinearMap.lTensor_def] using h

private theorem lift_mm (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    M D H m * M D H n - M D H n * M D H m =
      (m - n : ℂ) • M D H (m + n) +
        (if m + n = 0 then matterCentral D m else 0) • 1 := by
  have h := congrArg (LinearMap.rTensorHom (Fock ℂ))
    (sugawaraMode_virasoro D H hHG hGH m n)
  simp only [map_sub, map_add, map_smul, LinearMap.coe_rTensorHom,
    LinearMap.rTensor_mul, Module.End.one_eq_id, LinearMap.rTensor_id] at h
  simpa only [M, matterCentral, LinearMap.rTensor_def, Module.End.one_eq_id,
    Int.cast_sub] using h

private theorem lift_gg (D : LatticeData) (m n : ℤ) :
    G D m * G D n - G D n * G D m =
      (m - n : ℂ) • G D (m + n) +
        (if m + n = 0 then ghostCentral m else 0) • 1 := by
  have h := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostVirasoro.L_virasoro (K := ℂ) m n)
  simp only [map_sub, map_add, map_smul, LinearMap.coe_lTensorHom,
    LinearMap.lTensor_mul, LinearMap.lTensor_id] at h
  simpa only [G, LinearMap.lTensor_def, Module.End.one_eq_id, integral_central] using h

private theorem comm_product {D : LatticeData} (operator left right : Module.End ℂ (State D)) :
    operator * (left * right) - (left * right) * operator =
      (operator * left - left * operator) * right +
        left * (operator * right - right * operator) := by
  simp only [sub_mul, mul_sub, mul_assoc]
  exact (sub_add_sub_cancel (operator * (left * right))
    (left * (operator * right)) (left * (right * operator))).symm

private theorem total_c (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    (M D H m + G D m) * C D n - C D n * (M D H m + G D m) =
      (-2 * m - n : ℂ) • C D (m + n) := by
  have h := lift_gc D m n
  rw [add_mul, mul_add, lift_mc]
  convert h using 1 <;> abel

private theorem total_m (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    (M D H m + G D m) * M D H n - M D H n * (M D H m + G D m) =
      (m - n : ℂ) • M D H (m + n) +
        (if m + n = 0 then matterCentral D m else 0) • 1 := by
  have h := lift_mm D H hHG hGH m n
  rw [add_mul, mul_add, ← lift_mg D H n m]
  convert h using 1 <;> abel

private theorem total_g (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    (M D H m + G D m) * G D n - G D n * (M D H m + G D m) =
      (m - n : ℂ) • G D (m + n) +
        (if m + n = 0 then ghostCentral m else 0) • 1 := by
  have h := lift_gg D m n
  rw [add_mul, mul_add, lift_mg]
  convert h using 1 <;> abel

private theorem matter_summand (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    (M D H m + G D m) * (C D (-n) * M D H n) -
      (C D (-n) * M D H n) * (M D H m + G D m) =
      (n - 2 * m : ℂ) • matterRow D H m (n - m) +
        (m - n : ℂ) • matterRow D H m n +
          (if n = -m then matterCentral D m • C D m else 0) := by
  rw [comm_product, total_c, total_m D H hHG hGH]
  have hcoefficient : (-2 * m - -n : ℂ) = (n - 2 * m : ℂ) := by ring
  simp only [smul_mul_assoc, mul_add, mul_smul_comm, mul_one, Int.cast_neg,
    hcoefficient, show m + -n = m - n by omega, matterRow,
    show -(n - m) = m - n by omega, show m + (n - m) = n by omega]
  by_cases hcentral : n = -m
  · have hsum : m + n = 0 := by omega
    have hindex : -n = m := by omega
    simp only [hcentral, hsum, hindex, if_true] <;> abel
  · have hsum : m + n ≠ 0 := by omega
    simp only [hcentral, hsum, if_false, zero_smul, add_zero] <;> abel

private theorem ghost_summand (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    (M D H m + G D m) * N D n - N D n * (M D H m + G D m) =
      (n - 2 * m : ℂ) • ghostFirst D m n +
        (m - n : ℂ) • ghostRow D m n +
          (if n = -m then ghostCentral m • C D m else 0) := by
  have hcoefficient : (-2 * m - -n : ℂ) = (n - 2 * m : ℂ) := by ring
  by_cases hn : -1 ≤ n
  · rw [N, if_pos hn, ← Module.End.mul_eq_comp, comm_product, total_c, total_g]
    simp only [smul_mul_assoc, mul_add, mul_smul_comm, mul_one, Int.cast_neg,
      hcoefficient, show m + -n = m - n by omega, ghostFirst, ghostRow, hn, if_true]
    by_cases hcentral : n = -m
    · have hsum : m + n = 0 := by omega
      have hindex : -n = m := by omega
      simp only [hcentral, hsum, hindex, if_true] <;> abel
    · have hsum : m + n ≠ 0 := by omega
      simp only [hcentral, hsum, if_false, zero_smul, add_zero] <;> abel
  · rw [N, if_neg hn, ← Module.End.mul_eq_comp, comm_product, total_g, total_c]
    simp only [add_mul, smul_mul_assoc, mul_smul_comm, one_mul, Int.cast_neg,
      hcoefficient, show m + -n = m - n by omega, ghostFirst, ghostRow, hn, if_false]
    by_cases hcentral : n = -m
    · have hsum : m + n = 0 := by omega
      have hindex : -n = m := by omega
      simp only [hcentral, hsum, hindex, add_neg_cancel, neg_neg, if_true]
      ac_rfl
    · have hsum : m + n ≠ 0 := by omega
      simp only [hcentral, hsum, if_false, zero_smul, add_zero]
      abel

private theorem A_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    (M D H m + G D m) * A D H n - A D H n * (M D H m + G D m) =
      ((n - 2 * m : ℂ) • matterRow D H m (n - m) +
        (m - n : ℂ) • matterRow D H m n +
          (if n = -m then matterCentral D m • C D m else 0)) +
      (2 : ℂ)⁻¹ • ((n - 2 * m : ℂ) • ghostFirst D m n +
        (m - n : ℂ) • ghostRow D m n +
          (if n = -m then ghostCentral m • C D m else 0)) := by
  have hsplit : (M D H m + G D m) * A D H n - A D H n * (M D H m + G D m) =
      ((M D H m + G D m) * (C D (-n) * M D H n) -
        (C D (-n) * M D H n) * (M D H m + G D m)) +
      (2 : ℂ)⁻¹ • ((M D H m + G D m) * N D n - N D n * (M D H m + G D m)) := by
    have hhalf_add (left right : Module.End ℂ (State D)) :=
      _root_.smul_add ((2 : ℂ)⁻¹) left right
    have hhalf_sub (left right : Module.End ℂ (State D)) :=
      _root_.smul_sub ((2 : ℂ)⁻¹) left right
    simp only [A, ← Module.End.mul_eq_comp, mul_add, add_mul,
      mul_smul_comm, smul_mul_assoc, hhalf_sub, hhalf_add]
    abel
  rw [hsplit, matter_summand D H hHG hGH, ghost_summand]

private theorem finite_add {D : LatticeData} {left right : ℤ → State D}
    (hleft : Function.HasFiniteSupport left) (hright : Function.HasFiniteSupport right) :
    Function.HasFiniteSupport (fun n => left n + right n) := by
  apply (hleft.union hright).subset
  intro n hn
  by_cases hzero : left n = 0
  · right
    intro hother
    exact hn (by simp [hzero, hother])
  · exact Or.inl hzero

private theorem finite_on_tensors (D : LatticeData) (family : ℤ → Module.End ℂ (State D))
    (htensor : ∀ (matter : Carrier D) (ghost : Fock ℂ),
      Function.HasFiniteSupport (fun n => family n (matter ⊗ₜ[ℂ] ghost)))
    (psi : State D) : Function.HasFiniteSupport (fun n => family n psi) := by
  induction psi using TensorProduct.induction_on with
  | zero => simp [Function.HasFiniteSupport]
  | tmul matter ghost => exact htensor matter ghost
  | add psi chi hpsi hchi =>
      simpa only [map_add] using finite_add hpsi hchi

private theorem matterRow_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (psi : State D) :
    Function.HasFiniteSupport (fun n => matterRow D H m n psi) := by
  apply finite_on_tensors D (matterRow D H m) _ psi
  intro matter ghost
  apply (Set.finite_Icc (-BcGhostBrstSupport.bound ghost - 2)
    (matterCutoff D H matter - m)).subset
  intro n hn
  have hzero (hout : n < -BcGhostBrstSupport.bound ghost - 2 ∨
      matterCutoff D H matter - m < n) :
      matterRow D H m n (matter ⊗ₜ[ℂ] ghost) = 0 := by
    rcases hout with hlo | hhi
    · have hc := BcGhostBrstSupport.c_vanish_below ghost n hlo
      simp [matterRow, M, C, Module.End.mul_apply, hc]
    · have hm : sugawaraMode D H (m + n) matter = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        dsimp [matterCutoff] at hhi
        omega
      simp [matterRow, M, C, Module.End.mul_apply, hm]
  constructor
  · by_contra hlo
    exact hn (hzero (Or.inl (lt_of_not_ge hlo)))
  · by_contra hhi
    exact hn (hzero (Or.inr (lt_of_not_ge hhi)))

private theorem ghostRow_finite (D : LatticeData) (m : ℤ) (psi : State D) :
    Function.HasFiniteSupport (fun n => ghostRow D m n psi) := by
  apply finite_on_tensors D (ghostRow D m) _ psi
  intro matter ghost
  apply (Set.finite_Icc (-BcGhostBrstSupport.bound ghost - 2)
    (max (-1) (2 * BcGhostBrstSupport.bound ghost + 4 - m))).subset
  intro n hn
  have hnonneg : 0 ≤ BcGhostBrstSupport.bound ghost := Int.natCast_nonneg _
  have hzero (hout : n < -BcGhostBrstSupport.bound ghost - 2 ∨
      max (-1) (2 * BcGhostBrstSupport.bound ghost + 4 - m) < n) :
      ghostRow D m n (matter ⊗ₜ[ℂ] ghost) = 0 := by
    rcases hout with hlo | hhi
    · have hbranch : ¬ -1 ≤ n := by omega
      have hc := BcGhostBrstSupport.c_vanish_below ghost n hlo
      simp [ghostRow, hbranch, C, G, Module.End.mul_apply, hc]
    · have hbranch : -1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hhi)
      have hstress := lt_of_le_of_lt (le_max_right _ _) hhi
      have hg : L (K := ℂ) (m + n) ghost = 0 :=
        L_high_mode _ _ (by simpa only [BcGhostBrstSupport.bound] using
          (show 2 * BcGhostBrstSupport.bound ghost + 4 < m + n by omega))
      simp [ghostRow, hbranch, C, G, Module.End.mul_apply, hg]
  constructor
  · by_contra hlo
    exact hn (hzero (Or.inl (lt_of_not_ge hlo)))
  · by_contra hhi
    exact hn (hzero (Or.inr (lt_of_not_ge hhi)))

private theorem ghostFirst_finite (D : LatticeData) (m : ℤ) (psi : State D) :
    Function.HasFiniteSupport (fun n => ghostFirst D m n psi) := by
  apply finite_on_tensors D (ghostFirst D m) _ psi
  intro matter ghost
  apply (Set.finite_Icc (min (-1) (m - BcGhostBrstSupport.bound ghost - 2))
    (max (-1) (2 * BcGhostBrstSupport.bound ghost + 4))).subset
  intro n hn
  have hzero (hout : n < min (-1) (m - BcGhostBrstSupport.bound ghost - 2) ∨
      max (-1) (2 * BcGhostBrstSupport.bound ghost + 4) < n) :
      ghostFirst D m n (matter ⊗ₜ[ℂ] ghost) = 0 := by
    rcases hout with hlo | hhi
    · have hbranch : ¬ -1 ≤ n := by
        have := lt_of_lt_of_le hlo (min_le_left _ _)
        omega
      have htail := lt_of_lt_of_le hlo (min_le_right _ _)
      have hc := BcGhostBrstSupport.c_vanish_below ghost (n - m) (by omega)
      have hindex : -(n - m) = m - n := by omega
      rw [hindex] at hc
      simp [ghostFirst, hbranch, C, G, Module.End.mul_apply, hc]
    · have hbranch : -1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hhi)
      have htail := lt_of_le_of_lt (le_max_right _ _) hhi
      have hg : L (K := ℂ) n ghost = 0 :=
        L_high_mode _ _ (by simpa only [BcGhostBrstSupport.bound] using htail)
      simp [ghostFirst, hbranch, C, G, Module.End.mul_apply, hg]
  constructor
  · by_contra hlo
    exact hn (hzero (Or.inl (lt_of_not_ge hlo)))
  · by_contra hhi
    exact hn (hzero (Or.inr (lt_of_not_ge hhi)))

private theorem weighted_finite {D : LatticeData} (family : ℤ → State D)
    (weight : ℤ → ℂ) (hfinite : Function.HasFiniteSupport family) :
    Function.HasFiniteSupport (fun n => weight n • family n) := by
  apply hfinite.subset
  intro n hn hzero
  exact hn (by simp only [hzero, smul_zero])

private theorem central_finite (D : LatticeData) (m : ℤ) (scalar : ℂ) (psi : State D) :
    Function.HasFiniteSupport
      (fun n : ℤ => if n = -m then scalar • C D m psi else 0) := by
  apply (Set.finite_singleton (-m)).subset
  intro n hn
  by_contra hne
  exact hn (by simp only [Set.mem_singleton_iff] at hne; simp only [hne, if_false])

private theorem central_sum (D : LatticeData) (m : ℤ) (scalar : ℂ) (psi : State D) :
    (∑ᶠ n : ℤ, if n = -m then scalar • C D m psi else 0) = scalar • C D m psi := by
  classical
  rw [finsum_eq_single _ (-m) (by intro n hn; simp only [hn, if_false])]
  simp only [if_true]

private theorem matter_cancel (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (psi : State D) :
    (∑ᶠ n : ℤ, (n - 2 * m : ℂ) • matterRow D H m (n - m) psi) +
      (∑ᶠ n : ℤ, (m - n : ℂ) • matterRow D H m n psi) = 0 := by
  have hbij : Function.Bijective (fun n : ℤ => n - m) := by
    constructor
    · intro left right heq
      change left - m = right - m at heq
      omega
    · intro n
      refine ⟨n + m, ?_⟩
      change n + m - m = n
      omega
  have hshift : (∑ᶠ n : ℤ, (n - 2 * m : ℂ) • matterRow D H m (n - m) psi) =
      ∑ᶠ n : ℤ, (n - m : ℂ) • matterRow D H m n psi := by
    apply finsum_eq_of_bijective (fun n : ℤ => n - m) hbij
    intro n
    simp only [Int.cast_sub]
    congr 1
    ring
  rw [hshift]
  have hneg : (∑ᶠ n : ℤ, (n - m : ℂ) • matterRow D H m n psi) =
      -(∑ᶠ n : ℤ, (m - n : ℂ) • matterRow D H m n psi) := by
    rw [← finsum_neg_distrib]
    apply finsum_congr
    intro n
    rw [← neg_smul, show -(m - n : ℂ) = (n - m : ℂ) by ring]
  rw [hneg, neg_add_cancel]

private theorem cross_current (D : LatticeData) (m n : ℤ) :
    C D (-n) * G D (m + n) - G D (m + n) * C D (-n) =
      (2 * m + n : ℂ) • C D m := by
  have h := lift_gc D (m + n) (-n)
  have hindex : m + n + -n = m := by omega
  have hscalar : -2 * ((m + n : ℤ) : ℂ) - ((-n : ℤ) : ℂ) = -(2 * m + n : ℂ) := by
    push_cast
    ring
  rw [hindex, hscalar] at h
  have hreverse : C D (-n) * G D (m + n) - G D (m + n) * C D (-n) =
      -(G D (m + n) * C D (-n) - C D (-n) * G D (m + n)) := by abel
  rw [hreverse, h, _root_.neg_smul (2 * m + n : ℂ) (C D m), neg_neg]

private theorem ghost_shift_change (D : LatticeData) (m n : ℤ) :
    (n - m : ℂ) • ghostFirst D m (n + m) +
      (m - n : ℂ) • ghostRow D m n = branchScalar m n • C D m := by
  have hsign : (m - n : ℂ) = -(n - m : ℂ) := by ring
  have hindex : m - (n + m) = -n := by omega
  have hmode : G D (n + m) = G D (m + n) := by rw [add_comm n m]
  have hneg (current : Module.End ℂ (State D)) :
      (-(n - m : ℂ)) • current = -((n - m : ℂ) • current) :=
    _root_.neg_smul (n - m : ℂ) current
  by_cases hn : -1 ≤ n <;> by_cases hs : -1 ≤ n + m
  · simp only [ghostFirst, ghostRow, branchScalar, hn, hs, if_true, hindex,
      hmode, hsign, hneg, add_neg_cancel, zero_smul]
  · simp only [ghostFirst, ghostRow, branchScalar, hn, hs, if_true, if_false,
      hindex, hmode, hsign]
    have hreverse : G D (m + n) * C D (-n) - C D (-n) * G D (m + n) =
        -(C D (-n) * G D (m + n) - G D (m + n) * C D (-n)) := by abel
    calc
      _ = (n - m : ℂ) • (G D (m + n) * C D (-n) -
          C D (-n) * G D (m + n)) := by
        rw [hneg]
        exact ((_root_.smul_sub (n - m : ℂ)
          (G D (m + n) * C D (-n)) (C D (-n) * G D (m + n))).trans
            (sub_eq_add_neg _ _)).symm
      _ = -((n - m : ℂ) • (C D (-n) * G D (m + n) -
          G D (m + n) * C D (-n))) := by
        rw [hreverse, _root_.smul_neg (n - m : ℂ)
          (C D (-n) * G D (m + n) - G D (m + n) * C D (-n))]
      _ = -(((n - m : ℂ) * (2 * m + n)) • C D m) := by
        rw [cross_current D m n, smul_smul]
      _ = _ := (_root_.neg_smul ((n - m : ℂ) * (2 * m + n)) (C D m)).symm
  · simp only [ghostFirst, ghostRow, branchScalar, hn, hs, if_true, if_false,
      hindex, hmode, hsign]
    calc
      _ = (n - m : ℂ) • (C D (-n) * G D (m + n) -
          G D (m + n) * C D (-n)) := by
        rw [hneg]
        exact ((_root_.smul_sub (n - m : ℂ)
          (C D (-n) * G D (m + n)) (G D (m + n) * C D (-n))).trans
            (sub_eq_add_neg _ _)).symm
      _ = _ := by rw [cross_current D m n, smul_smul]
  · simp only [ghostFirst, ghostRow, branchScalar, hn, hs, if_false, hindex,
      hmode, hsign, hneg, add_neg_cancel, zero_smul]

private theorem ghost_correction (D : LatticeData) (m : ℤ) (psi : State D) :
    (∑ᶠ n : ℤ, (n - 2 * m : ℂ) • ghostFirst D m n psi) +
      (∑ᶠ n : ℤ, (m - n : ℂ) • ghostRow D m n psi) =
        ghostCentral m • C D m psi := by
  have hbij : Function.Bijective (fun n : ℤ => n + m) := by
    constructor
    · intro left right heq
      change left + m = right + m at heq
      omega
    · intro n
      refine ⟨n - m, ?_⟩
      change n - m + m = n
      omega
  have hshift : (∑ᶠ n : ℤ, (n - 2 * m : ℂ) • ghostFirst D m n psi) =
      ∑ᶠ n : ℤ, (n - m : ℂ) • ghostFirst D m (n + m) psi := by
    calc
      _ = ∑ᶠ n : ℤ, ((n + m : ℤ) - 2 * m : ℂ) • ghostFirst D m (n + m) psi :=
        (finsum_comp (fun n : ℤ => n + m) hbij).symm
      _ = _ := by
        apply finsum_congr
        intro n
        simp only [Int.cast_add]
        congr 1
        ring
  have hfirst : Function.HasFiniteSupport
      (fun n : ℤ => (n - m : ℂ) • ghostFirst D m (n + m) psi) :=
    weighted_finite _ _ (Function.HasFiniteSupport.fun_comp_of_injective
      hbij.1 (ghostFirst_finite D m psi))
  have hsecond := weighted_finite _ (fun n : ℤ => (m - n : ℂ)) (ghostRow_finite D m psi)
  rw [hshift, ← finsum_add_distrib hfirst hsecond]
  calc
    _ = ∑ᶠ n : ℤ, branchScalar m n • C D m psi := by
      apply finsum_congr
      intro n
      have h := congrArg (fun operator : Module.End ℂ (State D) => operator psi)
        (ghost_shift_change D m n)
      simpa only [LinearMap.add_apply, LinearMap.smul_apply] using h
    _ = (∑ᶠ n : ℤ, branchScalar m n) • C D m psi :=
      (finsum_smul' (branch_finite m) (C D m psi)).symm
    _ = _ := by rw [branch_sum]

private theorem total_commutator_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m : ℤ) (psi : State D) :
    ((M D H m + G D m) * Q D H - Q D H * (M D H m + G D m)) psi =
      ((((D.rank : ℂ) - 26) / 12) * ((m : ℂ) ^ 3 - m)) • C D m psi := by
  let stress := M D H m + G D m
  let matterFirst := fun n : ℤ => (n - 2 * m : ℂ) • matterRow D H m (n - m) psi
  let matterSecond := fun n : ℤ => (m - n : ℂ) • matterRow D H m n psi
  let ghostFirstRow := fun n : ℤ => (n - 2 * m : ℂ) • ghostFirst D m n psi
  let ghostSecondRow := fun n : ℤ => (m - n : ℂ) • ghostRow D m n psi
  let matterDelta := fun n : ℤ => if n = -m then matterCentral D m • C D m psi else 0
  let ghostDelta := fun n : ℤ => if n = -m then ghostCentral m • C D m psi else 0
  have hpre := A_finite D H (stress psi)
  have hpost := (A_finite D H psi).fun_comp (map_zero stress)
  have hmap := stress.toAddMonoidHom.map_finsum (A_finite D H psi)
  simp only [LinearMap.toAddMonoidHom_coe] at hmap
  have hcomm : ((stress * Q D H - Q D H * stress) psi) =
      ∑ᶠ n : ℤ, (stress (A D H n psi) - A D H n (stress psi)) := by
    change stress (∑ᶠ n : ℤ, A D H n psi) - (∑ᶠ n : ℤ, A D H n (stress psi)) = _
    rw [hmap, finsum_sub_distrib hpost hpre]
  have hmatterFirst : Function.HasFiniteSupport matterFirst :=
    weighted_finite _ _ (Function.HasFiniteSupport.fun_comp_of_injective
      (show Function.Injective (fun n : ℤ => n - m) from by
        intro left right heq
        change left - m = right - m at heq
        omega)
      (matterRow_finite D H m psi))
  have hmatterSecond : Function.HasFiniteSupport matterSecond :=
    weighted_finite _ _ (matterRow_finite D H m psi)
  have hghostFirst : Function.HasFiniteSupport ghostFirstRow :=
    weighted_finite _ _ (ghostFirst_finite D m psi)
  have hghostSecond : Function.HasFiniteSupport ghostSecondRow :=
    weighted_finite _ _ (ghostRow_finite D m psi)
  have hmatterDelta : Function.HasFiniteSupport matterDelta :=
    central_finite D m (matterCentral D m) psi
  have hghostDelta : Function.HasFiniteSupport ghostDelta :=
    central_finite D m (ghostCentral m) psi
  have hghostRow := finite_add (finite_add hghostFirst hghostSecond) hghostDelta
  have hhalfGhost := weighted_finite _ (fun _ => (2 : ℂ)⁻¹) hghostRow
  have hterms : (∑ᶠ n : ℤ, (stress (A D H n psi) - A D H n (stress psi))) =
      (∑ᶠ n : ℤ, (matterFirst n + matterSecond n + matterDelta n)) +
        (2 : ℂ)⁻¹ • (∑ᶠ n : ℤ, (ghostFirstRow n + ghostSecondRow n + ghostDelta n)) := by
    calc
      _ = ∑ᶠ n : ℤ, ((matterFirst n + matterSecond n + matterDelta n) +
          (2 : ℂ)⁻¹ • (ghostFirstRow n + ghostSecondRow n + ghostDelta n)) := by
        apply finsum_congr
        intro n
        have h := congrArg (fun operator : Module.End ℂ (State D) => operator psi)
          (A_commutator D H hHG hGH m n)
        dsimp only [stress, matterFirst, matterSecond, matterDelta,
          ghostFirstRow, ghostSecondRow, ghostDelta]
        by_cases hcentral : n = -m
        · simpa only [if_pos hcentral, LinearMap.sub_apply, Module.End.mul_apply,
            LinearMap.add_apply, LinearMap.smul_apply] using h
        · simpa only [if_neg hcentral, LinearMap.sub_apply, Module.End.mul_apply,
            LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
            add_zero] using h
      _ = _ := by
        rw [finsum_add_distrib (finite_add (finite_add hmatterFirst hmatterSecond)
          hmatterDelta) hhalfGhost,
          ← smul_finsum' _ hghostRow]
  change ((stress * Q D H - Q D H * stress) psi) = _
  rw [hcomm, hterms,
    finsum_add_distrib (finite_add hmatterFirst hmatterSecond) hmatterDelta,
    finsum_add_distrib hmatterFirst hmatterSecond,
    finsum_add_distrib (finite_add hghostFirst hghostSecond) hghostDelta,
    finsum_add_distrib hghostFirst hghostSecond]
  change ((∑ᶠ n : ℤ, (n - 2 * m : ℂ) • matterRow D H m (n - m) psi) +
      (∑ᶠ n : ℤ, (m - n : ℂ) • matterRow D H m n psi) +
        (∑ᶠ n : ℤ, if n = -m then matterCentral D m • C D m psi else 0)) +
      (2 : ℂ)⁻¹ • ((∑ᶠ n : ℤ, (n - 2 * m : ℂ) • ghostFirst D m n psi) +
        (∑ᶠ n : ℤ, (m - n : ℂ) • ghostRow D m n psi) +
          (∑ᶠ n : ℤ, if n = -m then ghostCentral m • C D m psi else 0)) = _
  rw [matter_cancel, zero_add, ghost_correction, central_sum, central_sum]
  rw [← add_smul, smul_smul, ← add_smul]
  congr 1
  dsimp [matterCentral, ghostCentral]
  ring

theorem total_covariance (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m : ℤ) :
    Q D H * (M D H m + G D m) - (M D H m + G D m) * Q D H =
      -((((D.rank : ℂ) - 26) / 12) * ((m : ℂ) ^ 3 - (m : ℂ))) • C D m := by
  apply LinearMap.ext
  intro psi
  have h := total_commutator_apply D H hHG hGH m psi
  have hreverse :
      (Q D H * (M D H m + G D m) - (M D H m + G D m) * Q D H) psi =
        -(((M D H m + G D m) * Q D H - Q D H * (M D H m + G D m)) psi) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    abel
  rw [hreverse, h]
  simp only [LinearMap.smul_apply, neg_smul]

#print axioms total_covariance

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstTotalCovariance
