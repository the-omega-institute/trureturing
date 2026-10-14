/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstCAction
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstCAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full actual tensor BRST c-current variation is a statewise finite c-c row. -/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge BcGhostFockSupport
  BcGhostStressCurrent
open scoped BigOperators TensorProduct

noncomputable section

private theorem ghost_row_finite (p : ℤ) (g : Fock ℂ) :
    Function.HasFiniteSupport (fun n : ℤ => c (-n) (c (n + p) g)) := by
  let bound : ℤ := (((occupied g).sup id : ℕ) : ℤ) + (p.natAbs : ℤ) + 4
  apply (Set.finite_Icc (-bound) bound).subset
  intro n hn
  have hsup : (0 : ℤ) ≤ (((occupied g).sup id : ℕ) : ℤ) := Int.natCast_nonneg _
  have hp : -(p.natAbs : ℤ) ≤ p := by
    have hneg : -p ≤ (p.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -p))
    omega
  have hzero (houtside : n < -bound ∨ bound < n) : c (-n) (c (n + p) g) = 0 := by
    rcases houtside with hlow | hhigh
    · dsimp [bound] at hlow
      have hq : ¬ -n ≤ 1 := by omega
      have hnat : 0 ≤ -n - 2 := by omega
      have hcast := Int.toNat_of_nonneg hnat
      have hidx : (occupied g).sup id < 2 * (-n - 2).toNat := by omega
      have hc : c (K := ℂ) (-n) g = 0 := by
        simp only [c, if_neg hq, annihilate_eq_zero_of_sup_lt g _ hidx]
      have hcar := congrArg (fun operator : Module.End ℂ (Fock ℂ) => operator g)
        (c_c (K := ℂ) (-n) (n + p))
      simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
        hc, map_zero, add_zero] using hcar
    · dsimp [bound] at hhigh
      have hq : ¬ n + p ≤ 1 := by omega
      have hnat : 0 ≤ n + p - 2 := by omega
      have hcast := Int.toNat_of_nonneg hnat
      have hidx : (occupied g).sup id < 2 * (n + p - 2).toNat := by omega
      have hc : c (K := ℂ) (n + p) g = 0 := by
        simp only [c, if_neg hq, annihilate_eq_zero_of_sup_lt g _ hidx]
      simp only [hc, map_zero]
  constructor
  · by_contra hlow
    exact hn (hzero (Or.inl (lt_of_not_ge hlow)))
  · by_contra hhigh
    exact hn (hzero (Or.inr (lt_of_not_ge hhigh)))

private theorem row_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport (fun n : ℤ => (C D (-n) * C D (n + p)) psi) := by
  induction psi using TensorProduct.induction_on with
  | zero => simp [Function.HasFiniteSupport]
  | tmul matter ghost =>
      apply (ghost_row_finite p ghost).subset
      intro n hn hzero
      exact hn (by simp [C, Module.End.mul_apply, hzero])
  | add psi chi hpsi hchi =>
      apply (hpsi.union hchi).subset
      intro n hn
      by_cases hzero : (C D (-n) * C D (n + p)) psi = 0
      · right
        intro hother
        exact hn (by simp [map_add, hzero, hother])
      · exact Or.inl hzero

private theorem weighted_row_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport
      (fun n : ℤ => (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)) := by
  apply (row_finite D p psi).subset
  intro n hn hzero
  exact hn (by simp only [hzero, smul_zero])

def V (D : LatticeData) (p : ℤ) : Module.End ℂ (State D) where
  toFun psi := ∑ᶠ n : ℤ, (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)
  map_add' psi chi := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib (weighted_row_finite D p psi) (weighted_row_finite D p chi)
  map_smul' scalar psi := by
    simp only [map_smul, RingHom.id_apply]
    simp_rw [smul_comm (2 * _ + p : ℂ) scalar]
    exact (smul_finsum' scalar (weighted_row_finite D p psi)).symm

private theorem lift_cc (D : LatticeData) (p q : ℤ) :
    C D p * C D q + C D q * C D p = 0 := by
  have h := congrArg (LinearMap.lTensorHom (Carrier D)) (c_c (K := ℂ) p q)
  simp only [map_add, map_zero, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at h
  simpa only [C, LinearMap.lTensor_def] using h

private theorem lift_gc (D : LatticeData) (n p : ℤ) :
    G D n * C D p - C D p * G D n = (-2 * n - p : ℂ) • C D (n + p) := by
  have h := congrArg (LinearMap.lTensorHom (Carrier D)) (L_c_commutator (K := ℂ) n p)
  simp only [map_sub, map_smul, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at h
  simpa only [G, C, LinearMap.lTensor_def] using h

private theorem lift_mc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n p : ℤ) :
    M D H n * C D p = C D p * M D H n := by
  apply TensorProduct.ext'
  intro matter ghost
  simp [M, C, Module.End.mul_apply]

private theorem product_anti
    {D : LatticeData} (left middle current commutator anti : Module.End ℂ (State D))
    (hmiddle : middle * current - current * middle = commutator)
    (hleft : left * current + current * left = anti) :
    (left * middle) * current + current * (left * middle) =
      left * commutator + anti * middle := by
  rw [← hmiddle, ← hleft]
  simp only [mul_sub, add_mul, mul_assoc]
  abel

private theorem product_anti_rev
    {D : LatticeData} (left middle current anti commutator : Module.End ℂ (State D))
    (hmiddle : middle * current + current * middle = anti)
    (hleft : left * current - current * left = commutator) :
    (left * middle) * current + current * (left * middle) =
      left * anti - commutator * middle := by
  rw [← hmiddle, ← hleft]
  simp only [mul_add, sub_mul, mul_assoc]
  abel

private theorem lift_nc (D : LatticeData) (n p : ℤ) :
    N D n * C D p + C D p * N D n =
      -(2 * n + p : ℂ) • (C D (-n) * C D (n + p)) := by
  have hsign : (-2 * n - p : ℂ) = -(2 * n + p : ℂ) := by ring
  by_cases hn : -1 ≤ n
  · rw [N, if_pos hn, ← Module.End.mul_eq_comp]
    have h := product_anti (D := D) (C D (-n)) (G D n) (C D p)
      ((-2 * n - p : ℂ) • C D (n + p)) 0 (lift_gc D n p) (lift_cc D (-n) p)
    simpa only [mul_smul_comm, zero_mul, add_zero, hsign] using h
  · rw [N, if_neg hn, ← Module.End.mul_eq_comp]
    have h := product_anti_rev (D := D) (G D n) (C D (-n)) (C D p)
      0 ((-2 * n - p : ℂ) • C D (n + p)) (lift_cc D (-n) p) (lift_gc D n p)
    have hpair : C D (n + p) * C D (-n) = -(C D (-n) * C D (n + p)) :=
      eq_neg_of_add_eq_zero_left (lift_cc D (n + p) (-n))
    simpa only [mul_zero, smul_mul_assoc, zero_sub, hpair, smul_neg, neg_neg,
      hsign] using h

private theorem lift_ac (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n p : ℤ) :
    A D H n * C D p + C D p * A D H n =
      -(2 : ℂ)⁻¹ • ((2 * n + p : ℂ) • (C D (-n) * C D (n + p))) := by
  have hmatter : (C D (-n) * M D H n) * C D p +
      C D p * (C D (-n) * M D H n) = 0 := by
    have h := product_anti (D := D) (C D (-n)) (M D H n) (C D p)
      0 0 (by rw [lift_mc]; simp) (lift_cc D (-n) p)
    simpa only [mul_zero, zero_mul, zero_add] using h
  have heq : A D H n * C D p + C D p * A D H n =
      ((C D (-n) * M D H n) * C D p + C D p * (C D (-n) * M D H n)) +
        (2 : ℂ)⁻¹ • (N D n * C D p + C D p * N D n) := by
    simp only [A, ← Module.End.mul_eq_comp, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_add]
    abel
  rw [heq, hmatter, zero_add, lift_nc]
  simp only [smul_smul, mul_neg, neg_mul]

theorem c_action (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : ℤ) :
    Q D H * C D p + C D p * Q D H = -(2 : ℂ)⁻¹ • V D p := by
  apply LinearMap.ext
  intro psi
  have hpsi := A_finite D H psi
  have hCpsi := A_finite D H (C D p psi)
  have hpost := hpsi.fun_comp (map_zero (C D p))
  have hmap := (C D p).toAddMonoidHom.map_finsum hpsi
  simp only [LinearMap.toAddMonoidHom_coe] at hmap
  change (∑ᶠ n : ℤ, A D H n (C D p psi)) + C D p (∑ᶠ n : ℤ, A D H n psi) =
    -(2 : ℂ)⁻¹ • (∑ᶠ n : ℤ, (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi))
  rw [hmap, ← finsum_add_distrib hCpsi hpost]
  calc
    (∑ᶠ n : ℤ, (A D H n (C D p psi) + C D p (A D H n psi))) =
        ∑ᶠ n : ℤ, -(2 : ℂ)⁻¹ •
          ((2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)) := by
      apply finsum_congr
      intro n
      have h := congrArg (fun operator : Module.End ℂ (State D) => operator psi)
        (lift_ac D H n p)
      simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
        RingHom.id_apply] using h
    _ = -(2 : ℂ)⁻¹ •
        (∑ᶠ n : ℤ, (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)) :=
      (smul_finsum' _ (weighted_row_finite D p psi)).symm

#print axioms ghost_row_finite
#print axioms row_finite
#print axioms weighted_row_finite
#print axioms V
#print axioms lift_nc
#print axioms lift_ac
#print axioms c_action

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction
