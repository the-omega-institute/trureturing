/- GID: D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Original relative BRST finite perturbation and exact-energy cohomology. -/

import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeShellDegreeBounds
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeZeroMode
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
import D5.S3.HomologicalAlgebra.FinitePerturbation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeLightConeCoordinates
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock (b c)
open D5.S3.VertexAlgebra.LatticeQuartetContraction


noncomputable section


set_option backward.isDefEq.respectTransparency true

namespace D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising
open LatticeRelativeMassShell
variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

private theorem full_step_preserves_shell
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (x : State D) (hx : x ∈ relativeMassShell D H p) :
    (h F B p * (LatticeBRST.totalCharge D H - d0 F p)) x ∈
      relativeMassShell D H p := by
  have hQ := LatticeRelativeMassShell.totalCharge_mem_relativeMassShell
    D H hHG hGH p hx
  have hd := (Ground.shellD0 F H hHG hGH p ⟨x, hx⟩).property
  exact (Ground.shellH F B H hHG hGH p
    ⟨(LatticeBRST.totalCharge D H - d0 F p) x,
      (relativeMassShell D H p).sub_mem hQ hd⟩).property

/- Uniform finite nilpotence of the actual full-Q perturbation on the literal
original relative mass shell, for every integral charge, including zero. -/
theorem h_full_remainder_nilpotent_on_relativeMassShell
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) :
    ∀ x : State D, x ∈ relativeMassShell D H p →
      ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^
        (2 * LatticeRelativeMassShell.massShellCutoff D p + 1)) x = 0 := by
  classical
  let N := LatticeRelativeMassShell.massShellCutoff D p
  have hbound := LatticeRelativeShellDegreeBounds.actualBasis_coefficient_shell_degree_bound
    D F B H hHG hGH p
  have hN (x : State D) (hx : x ∈ relativeMassShell D H p)
      (i : StateIndex D t) (hi : (actualBasis F B).repr x i ≠ 0) :
      -(N : ℤ) ≤ degree i ∧ degree i ≤ (N : ℤ) :=
    (hbound x hx i hi).2.2.2
  intro x hx
  let A : Module.End ℂ (State D) :=
    h F B p * (LatticeBRST.totalCharge D H - d0 F p)
  have hiter (k : ℕ) :
      (A ^ k) x ∈ relativeMassShell D H p ∧
        ∀ j : StateIndex D t, (actualBasis F B).repr ((A ^ k) x) j ≠ 0 →
          -(N : ℤ) + (k : ℤ) ≤ degree j := by
    induction k with
    | zero =>
        constructor
        · simpa using hx
        · intro j hj
          have hj' : (actualBasis F B).repr x j ≠ 0 := by simpa using hj
          simpa using (hN x hx j hj').1
    | succ k ih =>
        constructor
        · rw [pow_succ', Module.End.mul_apply]
          exact full_step_preserves_shell F B H hHG hGH p ((A ^ k) x) ih.1
        · intro j hj
          have hj' : (actualBasis F B).repr (A ((A ^ k) x)) j ≠ 0 := by
            simpa only [pow_succ', Module.End.mul_apply] using hj
          have hs := (full_remainder_fixed_charge_vectors F B H hHG hGH p
            ((A ^ k) x) (fun i hi => (hbound ((A ^ k) x) ih.1 i hi).1)
            (-(N : ℤ) + (k : ℤ)) ih.2).2.2 j hj'
          omega
  obtain ⟨hpow, hlower⟩ := hiter (2 * N + 1)
  change (A ^ (2 * N + 1)) x = 0
  apply (actualBasis F B).repr.map_eq_zero_iff.mp
  ext j
  by_contra hj
  have hlo := hlower j hj
  have hhi := (hN ((A ^ (2 * N + 1)) x) hpow j hj).2
  omega

end D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology

namespace D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology.Number

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeQuartetContraction
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open LatticeRelativeMassShell LatticeBRST LatticeBRSTRelativeZeroMode
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge

abbrev State (D : LatticeData) := LatticeMatterGhostCoupling.State D

/- Exactly 1 tensor the signed ORIGINAL occupation number. -/
abbrev N (D : LatticeData) : Module.End ℂ (State D) :=
  D5.S3.Quantum.Fermionic.BcGhostChargeTensor.number (M := Carrier D)

section Algebra
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem comm_add (Z A B : Module.End ℂ V) :
    Z * (A + B) - (A + B) * Z = (Z * A - A * Z) + (Z * B - B * Z) := by
  noncomm_ring

private theorem comm_sub (Z A B : Module.End ℂ V) :
    Z * (A - B) - (A - B) * Z = (Z * A - A * Z) - (Z * B - B * Z) := by
  noncomm_ring

private theorem comm_mul (Z A B : Module.End ℂ V) :
    Z * (A * B) - (A * B) * Z = (Z * A - A * Z) * B + A * (Z * B - B * Z) := by
  noncomm_ring

private theorem comm_smul (Z A : Module.End ℂ V) (z : ℂ) :
    Z * (z • A) - (z • A) * Z = z • (Z * A - A * Z) := by
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

/- One actual bound captures BOTH x and Z x before either total is expanded. -/
private theorem family_degree (A : Family V) (Z : Module.End ℂ V) (z : ℂ)
    (ht : ∀ r, Z * A.term r - A.term r * Z = z • A.term r) :
    Z * A.total - A.total * Z = z • A.total := by
  classical
  apply LinearMap.ext
  intro x
  let k := max (A.bound x) (A.bound (Z x))
  change Z (A.total x) - A.total (Z x) = z • A.total x
  simp only [A.total_eq_sum x k (le_max_left _ _),
    A.total_eq_sum (Z x) k (le_max_right _ _), map_sum,
    ← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact LinearMap.congr_fun (ht r) x

private theorem commutes_pow (Z A : Module.End ℂ V) (hA : Z * A = A * Z) (r : ℕ) :
    Z * A ^ r = A ^ r * Z := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ']
    calc
      Z * (A * A ^ r) = (Z * A) * A ^ r := (mul_assoc _ _ _).symm
      _ = (A * Z) * A ^ r := by rw [hA]
      _ = A * (Z * A ^ r) := mul_assoc _ _ _
      _ = A * (A ^ r * Z) := by rw [ih]
      _ = (A * A ^ r) * Z := (mul_assoc _ _ _).symm

private theorem commutes_inversePolynomial (Z A : Module.End ℂ V)
    (hA : Z * A = A * Z) (n : ℕ) :
    Z * D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial A n =
      D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial A n * Z := by
  unfold D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  apply commutes_pow
  simpa only [mul_neg, neg_mul] using congrArg Neg.neg hA

private theorem zero_of_eq_two_smul (v : V) (hv : v = (2 : ℂ) • v) : v = 0 := by
  rw [two_smul] at hv
  have hz : v + 0 = v + v := by simpa only [add_zero] using hv
  exact (add_left_cancel hz).symm
end Algebra

variable {D : LatticeData}

private theorem original_number_ket (S : Finset ℕ) :
    ghostNumber (ket S) = (charge S : ℂ) • ket S := by
  simp only [ghostNumber, ket, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul]

private theorem number_tensor_commutator (A : Module.End ℂ (Carrier D))
    (G : Module.End ℂ Fock) :
    N D * tp A G - tp A G * N D = tp A (ghostNumber * G - G * ghostNumber) := by
  apply TensorProduct.ext'
  intro v w
  simp only [N, D5.S3.Quantum.Fermionic.BcGhostChargeTensor.number,
    D5.S3.Quantum.Fermionic.BcGhostChargeTensor.liftGhost, tp,
    LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.tmul_sub]

private theorem N_b (m : ℤ) :
    N D * LatticeMatterGhostCoupling.ghostB D m -
      LatticeMatterGhostCoupling.ghostB D m * N D =
        -LatticeMatterGhostCoupling.ghostB D m := by
  change N D * tp 1 (b m) - tp 1 (b m) * N D = -tp 1 (b m)
  rw [number_tensor_commutator, ghost_number_relations.2.1]
  apply TensorProduct.ext'
  intro v w
  simp [tp, TensorProduct.tmul_neg]

private theorem N_totalCharge (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    N D * totalCharge D H - totalCharge D H * N D = totalCharge D H := by
  change LatticeMatterGhostDegree.tensorNumber D * LatticeMatterGhostDegree.Q D H -
      LatticeMatterGhostDegree.Q D H * LatticeMatterGhostDegree.tensorNumber D =
        LatticeMatterGhostDegree.Q D H
  exact LatticeMatterGhostDegree.tensorNumber_Q D H

private theorem N_totalL0 (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    N D * totalL0 D H - totalL0 D H * N D = 0 := by
  change N D * (LatticeMatterGhostCoupling.matterMode D H 0 +
      LatticeMatterGhostCoupling.ghostVirasoro D 0) -
    (LatticeMatterGhostCoupling.matterMode D H 0 +
      LatticeMatterGhostCoupling.ghostVirasoro D 0) * N D = 0
  rw [← total_ward_b D H 0, comm_add, comm_mul, comm_mul,
    N_totalCharge, N_b]
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply, map_neg,
    LinearMap.zero_apply]
  abel

variable (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

private theorem N_dm (m : ℤ) : N D * dm F m - dm F m * N D = dm F m := by
  rw [dm, number_tensor_commutator, ghost_number_relations.2.2]

private theorem N_rr (m : ℤ) : N D * rr F m - rr F m * N D = -rr F m := by
  rw [rr, number_tensor_commutator, ghost_number_relations.2.1]
  apply TensorProduct.ext'
  intro v w
  simp [tp, TensorProduct.tmul_neg]

private theorem N_dTerm (r : ℕ) : N D * dTerm F r - dTerm F r * N D = dTerm F r := by
  rw [dTerm, comm_add, N_dm, N_dm]

private theorem N_rTerm (r : ℕ) : N D * rTerm F r - rTerm F r * N D = -rTerm F r := by
  rw [rTerm, comm_smul, comm_add, N_rr, N_rr]
  module

private theorem N_unscaledD : N D * unscaledD F - unscaledD F * N D = unscaledD F := by
  exact (by simpa only [unscaledD, one_smul] using (family_degree (dFamily F) (N D) 1
    (fun r => by simpa only [dFamily, one_smul] using N_dTerm F r)))

private theorem N_unscaledR : N D * unscaledR F - unscaledR F * N D = -unscaledR F := by
  have ht (r : ℕ) : N D * (rFamily F).term r - (rFamily F).term r * N D =
      (-1 : ℂ) • (rFamily F).term r := by
    change N D * rTerm F r - rTerm F r * N D = (-1 : ℂ) • rTerm F r
    rw [N_rTerm F r]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.neg_apply, LinearMap.smul_apply]
    module
  have hh := family_degree (rFamily F) (N D) (-1) ht
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hh x
  simpa only [unscaledR, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, neg_one_smul ℂ, LinearMap.neg_apply] using hx

private theorem N_d0 (p : Charge D) : N D * d0 F p - d0 F p * N D = d0 F p := by
  rw [d0, comm_smul, N_unscaledD]

private theorem N_quartet_R (p : Charge D) : N D * R F p - R F p * N D = -R F p := by
  rw [R, comm_smul, N_unscaledR, smul_neg]

private theorem N_actualBasis (i : StateIndex D t) :
    N D (actualBasis F B i) = (charge i.2 : ℂ) • actualBasis F B i := by
  rcases i with ⟨⟨p,m⟩,S⟩
  rw [actualBasis_apply]
  change tp 1 ghostNumber (sector F B p (MvPolynomial.monomial m 1) (ket S)) = _
  rw [ghost_sector, original_number_ket, sector_smul_right]

private theorem N_actual_diagonal :
    N D = diagonal (actualBasis F B) (fun i => (charge i.2 : ℂ)) := by
  apply (actualBasis F B).ext
  intro i
  rw [N_actualBasis, diagonal_basis]

private theorem N_actual_coefficient (x : State D) (i : StateIndex D t) :
    (actualBasis F B).repr (N D x) i =
      (charge i.2 : ℂ) * (actualBasis F B).repr x i := by
  rw [N_actual_diagonal F B, diagonal_coefficient]

private theorem N_invM : N D * invM F B - invM F B * N D = 0 := by
  classical
  apply sub_eq_zero.mpr
  apply (actualBasis F B).ext
  intro i
  have hinv : invM F B (actualBasis F B i) =
      (if totalCount i = 0 then (0 : ℂ) else (totalCount i : ℂ)⁻¹) •
        actualBasis F B i := by
    simp only [invM, inverseNumber, diagonal_basis]
  simp only [Module.End.mul_apply, hinv, N_actualBasis, map_smul, smul_smul]
  rw [mul_comm]

private theorem N_P0 : N D * P0 F B - P0 F B * N D = 0 := by
  apply sub_eq_zero.mpr
  apply (actualBasis F B).ext
  intro i
  simp only [Module.End.mul_apply, P0_basis, N_actualBasis, map_smul, smul_smul]
  rw [mul_comm]

private theorem N_h (p : Charge D) : N D * h F B p - h F B p * N D = -h F B p := by
  rw [h, comm_mul, N_quartet_R, N_invM]
  simp only [mul_zero, add_zero]
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.neg_apply]

private theorem N_original_basis (i : TensorLabel D) :
    N D (tensorBasis D i) = (charge i.2 : ℂ) • tensorBasis D i := by
  rw [tensorBasis_apply]
  simp only [N, D5.S3.Quantum.Fermionic.BcGhostChargeTensor.number,
    D5.S3.Quantum.Fermionic.BcGhostChargeTensor.liftGhost,
    TensorProduct.map_tmul, LinearMap.id_apply, original_number_ket,
    TensorProduct.tmul_smul]

private theorem N_original_coefficient (x : State D) (i : TensorLabel D) :
    coeff D (N D x) i = (charge i.2 : ℂ) * coeff D x i := by
  have hd : N D = diagonal (tensorBasis D) (fun j => (charge j.2 : ℂ)) := by
    apply (tensorBasis D).ext
    intro j
    rw [N_original_basis, diagonal_basis]
  change (tensorBasis D).repr (N D x) i =
    (charge i.2 : ℂ) * (tensorBasis D).repr x i
  rw [hd, diagonal_coefficient]

private theorem N_preserves_fixedMomentum (p : Charge D) (x : State D)
    (hx : x ∈ fixedMomentum D p) : N D x ∈ fixedMomentum D p := by
  apply (mem_fixedMomentum_iff D p _).mpr
  intro i hi
  rw [N_original_coefficient, (mem_fixedMomentum_iff D p x).mp hx i hi, mul_zero]

private theorem N_preserves_relativeMassShell
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) (x : State D)
    (hx : x ∈ relativeMassShell D H p) : N D x ∈ relativeMassShell D H p := by
  refine ⟨⟨N_preserves_fixedMomentum p x hx.1.1, ?_⟩, ?_⟩
  · change LatticeMatterGhostCoupling.ghostB D 0 (N D x) = 0
    have hb : LatticeMatterGhostCoupling.ghostB D 0 x = 0 := hx.1.2
    have he := LinearMap.congr_fun (N_b (D := D) 0) x
    have hn : -LatticeMatterGhostCoupling.ghostB D 0 (N D x) = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
        hb, map_zero, zero_sub, neg_zero] using he
    exact neg_eq_zero.mp hn
  · change totalL0 D H (N D x) = 0
    calc
      _ = N D (totalL0 D H x) :=
        (LinearMap.congr_fun (sub_eq_zero.mp (N_totalL0 H)) x).symm
      _ = 0 := by rw [hx.2, map_zero]

private theorem relative_zero_count_occupation (x : State D) (hb : ghostB0 x = 0)
    (i : StateIndex D t) (hi : totalCount i = 0)
    (hc : (actualBasis F B).repr x i ≠ 0) : i.2 = {1} ∧ charge i.2 = 1 := by
  have hS : i.2 = {1} := by
    rcases ((totalCount_zero_iff i).mp hi).2 with h1 | h13
    · exact h1
    · exact False.elim (hc ((b0_coefficients F B x).mp hb i (by simp [h13])))
  refine ⟨hS, ?_⟩
  norm_num [hS, charge, Finset.filter_singleton]

private theorem P0_actual_coefficient (x : State D) (i : StateIndex D t) :
    (actualBasis F B).repr (P0 F B x) i =
      (if totalCount i = 0 then (1 : ℂ) else 0) * (actualBasis F B).repr x i := by
  rw [P0, projectZero, diagonal_coefficient]

private theorem N_P0_of_literal_b0 (x : State D) (hb : ghostB0 x = 0) :
    N D (P0 F B x) = P0 F B x := by
  classical
  apply (actualBasis F B).repr.injective
  ext i
  simp only [N_actual_coefficient, P0_actual_coefficient]
  by_cases hi : totalCount i = 0
  · by_cases hc : (actualBasis F B).repr x i = 0
    · simp [hi, hc]
    · have hcharge := (relative_zero_count_occupation F B x hb i hi hc).2
      simp [hi, hcharge]
  · simp [hi]

private theorem N_P0_on_relativeMassShell
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) (x : State D)
    (hx : x ∈ relativeMassShell D H p) : N D (P0 F B x) = P0 F B x := by
  exact N_P0_of_literal_b0 F B x hx.1.2

private theorem P0_N_on_relativeMassShell
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) (x : State D)
    (hx : x ∈ relativeMassShell D H p) : P0 F B (N D x) = P0 F B x := by
  calc
    _ = N D (P0 F B x) :=
      (LinearMap.congr_fun (sub_eq_zero.mp (N_P0 F B)) x).symm
    _ = _ := N_P0_on_relativeMassShell F B H p x hx

def shellN (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) :
    Module.End ℂ (relativeMassShell D H p) where
  toFun x := ⟨N D x, N_preserves_relativeMassShell H p x x.property⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' z x := Subtype.ext (map_smul _ _ _)

def shellQ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) :
    Module.End ℂ (relativeMassShell D H p) where
  toFun x := ⟨totalCharge D H x,
    totalCharge_mem_relativeMassShell D H hHG hGH p x.property⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' z x := Subtype.ext (map_smul _ _ _)

def shellDelta (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) :
    Module.End ℂ (relativeMassShell D H p) :=
  shellQ H hHG hGH p - LatticeRelativeBRSTCohomology.Ground.shellD0 F H hHG hGH p

section Restricted
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D)

local notation "𝒏" => shellN H p
local notation "𝒅" => LatticeRelativeBRSTCohomology.Ground.shellD0 F H hHG hGH p
local notation "𝒉" => LatticeRelativeBRSTCohomology.Ground.shellH F B H hHG hGH p
local notation "𝜹" => shellDelta F H hHG hGH p
local notation "𝒊" => LatticeRelativeBRSTCohomology.Ground.inclusion F B H hHG hGH p
local notation "𝒑" => LatticeRelativeBRSTCohomology.Ground.projection F B H hHG hGH p

private theorem shell_d0_add_delta : 𝒅 + 𝜹 = shellQ H hHG hGH p := by
  unfold shellDelta
  abel

private theorem shell_N_Q :
    𝒏 * shellQ H hHG hGH p - shellQ H hHG hGH p * 𝒏 = shellQ H hHG hGH p := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change N D (totalCharge D H x) - totalCharge D H (N D x) = totalCharge D H x
  exact LinearMap.congr_fun (N_totalCharge H) x

private theorem shell_N_d0 : 𝒏 * 𝒅 - 𝒅 * 𝒏 = 𝒅 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change N D (d0 F p x) - d0 F p (N D x) = d0 F p x
  exact LinearMap.congr_fun (N_d0 F p) x

private theorem shell_N_h : 𝒏 * 𝒉 - 𝒉 * 𝒏 = -𝒉 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change N D (h F B p x) - h F B p (N D x) = -h F B p x
  exact LinearMap.congr_fun (N_h F B p) x

private theorem shell_N_delta : 𝒏 * 𝜹 - 𝜹 * 𝒏 = 𝜹 := by
  unfold shellDelta
  rw [comm_sub, shell_N_Q, shell_N_d0]

private theorem shell_N_hdelta : 𝒏 * (𝒉 * 𝜹) = (𝒉 * 𝜹) * 𝒏 := by
  apply sub_eq_zero.mp
  rw [comm_mul, shell_N_h F B H hHG hGH p, shell_N_delta F H hHG hGH p]
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.zero_apply]
  abel

private theorem shell_N_deltah : 𝒏 * (𝜹 * 𝒉) = (𝜹 * 𝒉) * 𝒏 := by
  apply sub_eq_zero.mp
  rw [comm_mul, shell_N_delta F H hHG hGH p, shell_N_h F B H hHG hGH p]
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.zero_apply, map_neg]
  abel

include H hHG hGH in
private theorem N_concrete_target (u : LatticeRelativeBRSTCohomology.Ground.target F B p) :
    N D (u : State D) = u := by
  have hb := (LatticeRelativeBRSTCohomology.Ground.inclusion F B H hHG hGH p u).property.1.2
  have he := N_P0_of_literal_b0 F B (u : State D) hb
  rwa [LatticeRelativeBRSTCohomology.Ground.target_projection_fix F B p u] at he

private theorem inclusion_N : (𝒏).comp 𝒊 = 𝒊 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact N_concrete_target F B H hHG hGH p u

private theorem projection_N : (𝒑).comp 𝒏 = 𝒑 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact P0_N_on_relativeMassShell F B H p x x.property

def K (n : ℕ) : Module.End ℂ (relativeMassShell D H p) :=
  D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial (𝒉 * 𝜹) n

def J (n : ℕ) : Module.End ℂ (relativeMassShell D H p) :=
  D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial (𝜹 * 𝒉) (n + 1)

def correctedI (n : ℕ) :
    LatticeRelativeBRSTCohomology.Ground.target F B p →ₗ[ℂ] relativeMassShell D H p :=
  (K F B H hHG hGH p n).comp 𝒊

def correctedP (n : ℕ) :
    relativeMassShell D H p →ₗ[ℂ] LatticeRelativeBRSTCohomology.Ground.target F B p :=
  (𝒑).comp (J F B H hHG hGH p n)

def correctedH (n : ℕ) : Module.End ℂ (relativeMassShell D H p) :=
  K F B H hHG hGH p n * 𝒉

def transferred (n : ℕ) : Module.End ℂ (LatticeRelativeBRSTCohomology.Ground.target F B p) :=
  (𝒑).comp ((𝜹).comp (correctedI F B H hHG hGH p n))

private theorem N_K (n : ℕ) : 𝒏 * K F B H hHG hGH p n = K F B H hHG hGH p n * 𝒏 := by
  exact commutes_inversePolynomial 𝒏 (𝒉 * 𝜹) (shell_N_hdelta F B H hHG hGH p) n

private theorem N_J (n : ℕ) : 𝒏 * J F B H hHG hGH p n = J F B H hHG hGH p n * 𝒏 := by
  exact commutes_inversePolynomial 𝒏 (𝜹 * 𝒉) (shell_N_deltah F B H hHG hGH p) (n + 1)

private theorem correctedI_N (n : ℕ) :
    (𝒏).comp (correctedI F B H hHG hGH p n) = correctedI F B H hHG hGH p n := by
  unfold correctedI
  calc
    (𝒏).comp ((K F B H hHG hGH p n).comp 𝒊) =
        (𝒏 * K F B H hHG hGH p n).comp 𝒊 := rfl
    _ = (K F B H hHG hGH p n * 𝒏).comp 𝒊 := by rw [N_K F B H hHG hGH p n]
    _ = (K F B H hHG hGH p n).comp ((𝒏).comp 𝒊) := rfl
    _ = _ := by rw [inclusion_N F B H hHG hGH p]

private theorem correctedP_N (n : ℕ) :
    (correctedP F B H hHG hGH p n).comp 𝒏 = correctedP F B H hHG hGH p n := by
  apply LinearMap.ext
  intro x
  change 𝒑 (J F B H hHG hGH p n (𝒏 x)) = 𝒑 (J F B H hHG hGH p n x)
  have he := LinearMap.congr_fun (N_J F B H hHG hGH p n) x
  change 𝒏 (J F B H hHG hGH p n x) = J F B H hHG hGH p n (𝒏 x) at he
  rw [← he]
  exact LinearMap.congr_fun (projection_N F B H hHG hGH p)
    (J F B H hHG hGH p n x)

private theorem correctedH_N (n : ℕ) :
    𝒏 * correctedH F B H hHG hGH p n - correctedH F B H hHG hGH p n * 𝒏 =
      -correctedH F B H hHG hGH p n := by
  unfold correctedH
  rw [comm_mul, sub_eq_zero.mpr (N_K F B H hHG hGH p n),
    shell_N_h F B H hHG hGH p]
  simp only [zero_mul, zero_add]
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]

private theorem finite_transfer_zero (n : ℕ) : transferred F B H hHG hGH p n = 0 := by
  apply LinearMap.ext
  intro u
  let v := correctedI F B H hHG hGH p n u
  have hv : 𝒏 v = v := LinearMap.congr_fun (correctedI_N F B H hHG hGH p n) u
  have hd : 𝒏 (𝜹 v) - 𝜹 v = 𝜹 v := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, hv] using
      LinearMap.congr_fun (shell_N_delta F H hHG hGH p) v
  have hd2 : 𝒏 (𝜹 v) = (2 : ℂ) • 𝜹 v := by
    rw [two_smul]
    exact sub_eq_iff_eq_add.mp hd
  change 𝒑 (𝜹 v) = 0
  apply zero_of_eq_two_smul
  calc
    𝒑 (𝜹 v) = 𝒑 (𝒏 (𝜹 v)) :=
      (LinearMap.congr_fun (projection_N F B H hHG hGH p) (𝜹 v)).symm
    _ = (2 : ℂ) • 𝒑 (𝜹 v) := by rw [hd2, map_smul]

end Restricted

end D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology.Number

namespace D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeQuartetContraction
open LatticeRelativeMassShell
open D5.S3.HomologicalAlgebra
open CategoryTheory

/- The shell differential is the original Q, using its proved literal-shell
invariance, not a replacement complex or an invariant-shell parameter. -/
private theorem original_shellQ_square {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hrank : D.rank = 26) :
    Number.shellQ H hHG hGH p *
      Number.shellQ H hHG hGH p = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change LatticeBRST.totalCharge D H (LatticeBRST.totalCharge D H x) = 0
  have hsq : LatticeBRST.totalCharge D H * LatticeBRST.totalCharge D H = 0 := by
    simpa [hrank, pow_two] using LatticeBRST.total_square_anomaly D H hHG hGH
  exact LinearMap.congr_fun hsq x

/- This is an actual short complex of original Q maps. Its standard ModuleCat
homology is canonically the genuine cycle/boundary quotient used below. -/
def originalComplex {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hrank : D.rank = 26) : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.moduleCatMk
    (Number.shellQ H hHG hGH p)
    (Number.shellQ H hHG hGH p)
    (original_shellQ_square H hHG hGH p hrank)

abbrev Cycles {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) : Submodule ℂ (relativeMassShell D H p) :=
  LinearMap.ker (Number.shellQ H hHG hGH p)

private instance cycles_add_comm_group {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) : AddCommGroup (Cycles H hHG hGH p) := by
  letI : AddCommGroup (relativeMassShell D H p) :=
    Submodule.addCommGroup (relativeMassShell D H p)
  exact Submodule.addCommGroup (Cycles H hHG hGH p)

/- Reuse Mathlib's actual image-to-kernel map, rather than specifying which
vectors ought to count as boundaries. -/
def boundaryMap {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hrank : D.rank = 26) :
    relativeMassShell D H p →ₗ[ℂ] Cycles H hHG hGH p :=
  (originalComplex H hHG hGH p hrank).moduleCatToCycles

def boundaries {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hrank : D.rank = 26) : Submodule ℂ (Cycles H hHG hGH p) :=
  LinearMap.range (boundaryMap H hHG hGH p hrank)

abbrev Cohomology {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hrank : D.rank = 26) :=
  (Cycles H hHG hGH p : Type) ⧸ boundaries H hHG hGH p hrank

private theorem mem_boundaries_iff {D : LatticeData}
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hrank : D.rank = 26) (x : Cycles H hHG hGH p) :
    x ∈ boundaries H hHG hGH p hrank ↔
      ∃ y : relativeMassShell D H p, Number.shellQ H hHG hGH p y = x := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

section OriginalContraction

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (p : Charge D)

private def length (D : LatticeData) (p : Charge D) : ℕ :=
  2 * LatticeRelativeMassShell.massShellCutoff D p + 1

include hHG hGH in
private theorem length_spec :
    1 ≤ length D p ∧
      ∀ x : State D, x ∈ relativeMassShell D H p →
        ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^
          length D p) x = 0 := by
  exact ⟨by unfold length; omega,
    h_full_remainder_nilpotent_on_relativeMassShell F B H hHG hGH p⟩

local notation "ℓ" => length D p
local notation "𝒱" => (relativeMassShell D H p : Type)
local notation "𝒰" => (Ground.target F B p : Type)
local notation "𝒬" => Number.shellQ H hHG hGH p
local notation "𝒩" => Number.shellN H p
local notation "𝒅" => Ground.shellD0 F H hHG hGH p
local notation "𝒉" => Ground.shellH F B H hHG hGH p
local notation "𝜹" => Number.shellDelta F H hHG hGH p
local notation "𝓘" => Number.correctedI F B H hHG hGH p ℓ
local notation "𝓟" => Number.correctedP F B H hHG hGH p ℓ
local notation "𝓗" => Number.correctedH F B H hHG hGH p ℓ

private theorem hdelta_coe (x : 𝒱) :
    ((𝒉 * 𝜹) x : State D) =
      (h F B p * (LatticeBRST.totalCharge D H - d0 F p)) (x : State D) := rfl

/- Apply exact on-shell equality at every intermediate restricted state.
The actual full-Q ambient word is the one used by the new nilpotence supplier. -/
private theorem hdelta_power_coe (r : ℕ) (x : 𝒱) :
    (((𝒉 * 𝜹) ^ r) x : State D) =
      ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^ r) (x : State D) := by
  let A : Module.End ℂ (State D) :=
    h F B p * (LatticeBRST.totalCharge D H - d0 F p)
  change (((𝒉 * 𝜹) ^ r) x : State D) = (A ^ r) (x : State D)
  induction r with
  | zero => rfl
  | succ r ih =>
    calc
      (((𝒉 * 𝜹) ^ (r + 1)) x : State D) =
          ((𝒉 * 𝜹) (((𝒉 * 𝜹) ^ r) x) : State D) := by
        rw [pow_succ', Module.End.mul_apply]
      _ = A ((((𝒉 * 𝜹) ^ r) x) : State D) :=
        hdelta_coe F B H hHG hGH p (((𝒉 * 𝜹) ^ r) x)
      _ = A ((A ^ r) (x : State D)) := congrArg A ih
      _ = (A ^ (r + 1)) (x : State D) := by
        rw [pow_succ']
        rfl

private theorem shell_hdelta_nilpotent : (𝒉 * 𝜹) ^ ℓ = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((𝒉 * 𝜹) ^ ℓ) x : State D) = 0
  rw [hdelta_power_coe F B H hHG hGH p]
  exact (length_spec F B H hHG hGH p).2 x x.property

variable (hrank : D.rank = 26) (hp : F.pPlus p ≠ 0)

/- Each field is discharged by an original source proof. No conclusion field,
zero transfer field, arbitrary retract, or external Q-square hypothesis occurs. -/
private def input : FinitePerturbation.Input (R := ℂ) (U := 𝒰) (V := 𝒱) where
  d0 := 𝒅
  h := 𝒉
  delta := 𝜹
  i := Ground.inclusion F B H hHG hGH p
  p := Ground.projection F B H hHG hGH p
  d0_sq := Ground.shell_d0_square F H hHG hGH p
  pi := Ground.projection_inclusion F B H hHG hGH p
  di := Ground.shell_d0_inclusion F B H hHG hGH p
  pd := Ground.projection_shell_d0 F B H hHG hGH p
  contraction := Ground.shell_contraction F B H hHG hGH p hp
  hh := Ground.shell_h_square F B H hHG hGH p
  hi := Ground.shell_h_inclusion F B H hHG hGH p
  ph := Ground.projection_shell_h F B H hHG hGH p
  perturbed_sq := by
    rw [Number.shell_d0_add_delta F H hHG hGH p]
    exact original_shellQ_square H hHG hGH p hrank

local notation "𝒄" => input F B H hHG hGH p hrank hp

/- This is the public theorem's primitive on the SAME original Q shell. -/
include hrank hp in
private theorem original_cycle_decomposition (x : 𝒱) (hx : 𝒬 x = 0) :
    x = 𝓘 (𝓟 x) + 𝒬 (𝓗 x) := by
  have out := 𝒄.finite_perturbation ℓ (length_spec F B H hHG hGH p).1
    (shell_hdelta_nilpotent F B H hHG hGH p)
  have hz : 𝒄.transferred ℓ = 0 :=
    Number.finite_transfer_zero F B H hHG hGH p ℓ
  have hD : 𝒄.D = 𝒬 := Number.shell_d0_add_delta F H hHG hGH p
  have hx' : 𝒄.D x = 0 := by rwa [hD]
  have he : x - 𝓘 (𝓟 x) = 𝒬 (𝓗 x) := by
    simpa only [hD, FinitePerturbation.Input.D, Number.shell_d0_add_delta F H hHG hGH p, FinitePerturbation.Input.I, FinitePerturbation.Input.P, FinitePerturbation.Input.H, FinitePerturbation.Input.K, FinitePerturbation.Input.J, input, Number.correctedI, Number.correctedP, Number.correctedH, Number.K, Number.J] using (out.representatives hz).2.1 x hx'
  calc
    x = 𝒬 (𝓗 x) + 𝓘 (𝓟 x) := sub_eq_iff_eq_add.mp he
    _ = 𝓘 (𝓟 x) + 𝒬 (𝓗 x) := add_comm _ _

/- Uniqueness means equality modulo the actual image of original Q, not
equality under the uncorrected P0. Used by exact_energy_representative. -/
include hrank hp in
private theorem corrected_representatives_unique (u v : 𝒰) :
    (∃ y : 𝒱, 𝒬 y = 𝓘 u - 𝓘 v) ↔ u = v := by
  have out := 𝒄.finite_perturbation ℓ (length_spec F B H hHG hGH p).1
    (shell_hdelta_nilpotent F B H hHG hGH p)
  have hz : 𝒄.transferred ℓ = 0 :=
    Number.finite_transfer_zero F B H hHG hGH p ℓ
  have hD : 𝒄.D = 𝒬 := Number.shell_d0_add_delta F H hHG hGH p
  have hPQ : ∀ y : 𝒱, 𝓟 (𝒬 y) = 0 := by
    intro y
    have he := LinearMap.congr_fun out.projection_chain y
    change (𝒄.P ℓ) (𝒄.D y) = (𝒄.transferred ℓ) ((𝒄.P ℓ) y) at he
    rw [hz, LinearMap.zero_apply] at he
    simpa only [hD, hz, LinearMap.comp_apply, LinearMap.zero_apply, map_zero, FinitePerturbation.Input.D, Number.shell_d0_add_delta F H hHG hGH p, FinitePerturbation.Input.I, FinitePerturbation.Input.P, FinitePerturbation.Input.H, FinitePerturbation.Input.K, FinitePerturbation.Input.J, input, Number.correctedI, Number.correctedP, Number.correctedH, Number.K, Number.J] using he
  have hPI (w : 𝒰) : 𝓟 (𝓘 w) = w := by
    have he := LinearMap.congr_fun out.retract w
    change 𝓟 (𝓘 w) = w at he
    exact he
  constructor
  · rintro ⟨y, hy⟩
    have he : (0 : 𝒰) = u - v := by
      simpa only [hPQ, map_sub, hPI] using congrArg 𝓟 hy
    exact sub_eq_zero.mp he.symm
  · intro he
    subst v
    exact ⟨0, by simp⟩

/- N I = I and P N = P come from the actual occupation-number supplier.
The scalar separation here is over C and works for EVERY integer q != 1. -/
private theorem corrected_projection_zero_of_charge_ne_one (q : ℤ) (hq : q ≠ 1)
    (x : 𝒱) (hx : 𝒩 x = (q : ℂ) • x) : 𝓟 x = 0 := by
  have hPN : 𝓟 (𝒩 x) = 𝓟 x := LinearMap.congr_fun
    (Number.correctedP_N F B H hHG hGH p ℓ) x
  have he : (q : ℂ) • 𝓟 x = 𝓟 x := by
    calc
      (q : ℂ) • 𝓟 x = 𝓟 ((q : ℂ) • x) := (map_smul 𝓟 (q : ℂ) x).symm
      _ = 𝓟 (𝒩 x) := congrArg 𝓟 hx.symm
      _ = 𝓟 x := hPN
  have hs : ((q : ℂ) - 1) • 𝓟 x = 0 := by
    calc
      ((q : ℂ) - 1) • 𝓟 x = (q : ℂ) • 𝓟 x - 𝓟 x := by module
      _ = 0 := by rw [he, sub_self]
  have hqC : (q : ℂ) ≠ 1 := by exact_mod_cast hq
  exact (smul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hqC)

/- The actual corrected homotopy lowers integer ghost charge by one. -/
private theorem corrected_homotopy_charge (q : ℤ) (x : 𝒱) (hx : 𝒩 x = (q : ℂ) • x) :
    𝒩 (𝓗 x) = ((q - 1 : ℤ) : ℂ) • 𝓗 x := by
  have he : 𝒩 (𝓗 x) - (q : ℂ) • 𝓗 x = -𝓗 x := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
      hx, map_smul] using LinearMap.congr_fun
        (Number.correctedH_N F B H hHG hGH p ℓ) x
  simp only [Int.cast_sub, Int.cast_one]
  calc
    𝒩 (𝓗 x) = -𝓗 x + (q : ℂ) • 𝓗 x := sub_eq_iff_eq_add.mp he
    _ = ((q : ℂ) - 1) • 𝓗 x := by module

/- Concentration is witnessed by an original boundary with a primitive of
the required ghost charge; no acyclicity or transfer conclusion is assumed. -/
include hrank hp in
theorem off_charge_one_exact (q : ℤ) (hq : q ≠ 1) (x : 𝒱)
    (hx : 𝒬 x = 0) (hNx : 𝒩 x = (q : ℂ) • x) :
    x = 𝒬 (𝓗 x) ∧ 𝒩 (𝓗 x) = ((q - 1 : ℤ) : ℂ) • 𝓗 x := by
  constructor
  · have he := original_cycle_decomposition F B H hHG hGH p hrank hp x hx
    simpa only [corrected_projection_zero_of_charge_ne_one F B H hHG hGH p q hq x hNx,
      map_zero, zero_add] using he
  · exact corrected_homotopy_charge F B H hHG hGH p q x hNx

/- The target coordinate of an original cycle uses corrected P = p0 J. -/
def cycleProjection : Cycles H hHG hGH p →ₗ[ℂ] 𝒰 :=
  (𝓟).comp (Cycles H hHG hGH p).subtype

/- Actual corrected representatives as elements of the original cycle space.
This supplies the concrete inverse on quotient classes below. -/
def representativeCycle (u : 𝒰) : Cycles H hHG hGH p :=
  ⟨𝓘 u, by
    have out := 𝒄.finite_perturbation ℓ (length_spec F B H hHG hGH p).1
      (shell_hdelta_nilpotent F B H hHG hGH p)
    have hz : 𝒄.transferred ℓ = 0 :=
      Number.finite_transfer_zero F B H hHG hGH p ℓ
    have hD : 𝒄.D = 𝒬 := Number.shell_d0_add_delta F H hHG hGH p
    change 𝒬 (𝓘 u) = 0
    simpa only [hD, FinitePerturbation.Input.D, Number.shell_d0_add_delta F H hHG hGH p, FinitePerturbation.Input.I, FinitePerturbation.Input.P, FinitePerturbation.Input.H, FinitePerturbation.Input.K, FinitePerturbation.Input.J, input, Number.correctedI, Number.correctedP, Number.correctedH, Number.K, Number.J] using ((out.representatives hz).1 u).1⟩

/- Original boundaries are exactly the kernel of corrected cycle projection.
The equivalence is consumed directly from the public representative API. -/
include hrank hp in
private theorem boundaries_eq_ker_cycleProjection :
    boundaries H hHG hGH p hrank = LinearMap.ker (cycleProjection F B H hHG hGH p) := by
  ext x
  rw [mem_boundaries_iff]
  change (∃ y : 𝒱, 𝒬 y = (x : 𝒱)) ↔ 𝓟 (x : 𝒱) = 0
  have out := 𝒄.finite_perturbation ℓ (length_spec F B H hHG hGH p).1
    (shell_hdelta_nilpotent F B H hHG hGH p)
  have hz : 𝒄.transferred ℓ = 0 :=
    Number.finite_transfer_zero F B H hHG hGH p ℓ
  have hD : 𝒄.D = 𝒬 := Number.shell_d0_add_delta F H hHG hGH p
  have hx : 𝒄.D (x : 𝒱) = 0 := by rw [hD]; exact x.property
  simpa only [hD, FinitePerturbation.Input.D, Number.shell_d0_add_delta F H hHG hGH p, FinitePerturbation.Input.I, FinitePerturbation.Input.P, FinitePerturbation.Input.H, FinitePerturbation.Input.K, FinitePerturbation.Input.J, input, Number.correctedI, Number.correctedP, Number.correctedH, Number.K, Number.J] using (out.representatives hz).2.2 (x : 𝒱) hx

include hrank hp in
private theorem cycleProjection_surjective : Function.Surjective (cycleProjection F B H hHG hGH p) := by
  have out := 𝒄.finite_perturbation ℓ (length_spec F B H hHG hGH p).1
    (shell_hdelta_nilpotent F B H hHG hGH p)
  have hz : 𝒄.transferred ℓ = 0 :=
    Number.finite_transfer_zero F B H hHG hGH p ℓ
  intro u
  refine ⟨representativeCycle F B H hHG hGH p hrank hp u, ?_⟩
  exact ((out.representatives hz).1 u).2

/- Use the existing first isomorphism theorem on the proved original kernel.
This is a genuine quotient of original cycles by actual original boundaries. -/
def cohomologyEquivTarget : Cohomology H hHG hGH p hrank ≃ₗ[ℂ] 𝒰 :=
  (Submodule.quotEquivOfEq (R := ℂ) (M := (Cycles H hHG hGH p : Type)) (boundaries H hHG hGH p hrank)
    (LinearMap.ker (cycleProjection F B H hHG hGH p))
    (boundaries_eq_ker_cycleProjection F B H hHG hGH p hrank hp)).trans
      ((cycleProjection F B H hHG hGH p).quotKerEquivOfSurjective
        (cycleProjection_surjective F B H hHG hGH p hrank hp))

private def polynomialTargetEquiv : Ground.energyTarget D t p ≃ₗ[ℂ] 𝒰 :=
  Submodule.equivMapOfInjective (groundMap F B p)
    (Ground.groundMap_injective F B p) (Ground.energyTarget D t p)

/- Exact transverse polynomial coordinates, with wt(nu)+chargeEnergy(D,p)=1
on every nonzero coefficient, not a cutoff or an arbitrary ground retract. -/
def cohomologyEquivEnergy :
    Cohomology H hHG hGH p hrank ≃ₗ[ℂ] Ground.energyTarget D t p :=
  (cohomologyEquivTarget F B H hHG hGH p hrank hp).trans
    (polynomialTargetEquiv F B p).symm

/- The inverse is the class of actual I applied to the supplied groundMap
image of the exact-energy polynomial, not a selected quotient representative. -/
/- Every original class has a unique exact-energy transverse coordinate, and
its corrected inclusion has actual ghost charge one. Uniqueness is modulo
actual original Q boundaries. When x has charge one, its actual Hcorr primitive
has charge zero, so the same statement uses degree-zero boundaries at q=1.
No desired cohomology isomorphism is input. -/
include hrank hp in
theorem exact_energy_representative (x : 𝒱) (hx : 𝒬 x = 0) :
    ∃! f : Ground.energyTarget D t p,
      (∃ y : 𝒱,
        𝒬 y = x - 𝓘 (polynomialTargetEquiv F B p f) ∧
          (𝒩 x = x → 𝒩 y = 0)) ∧
        𝒩 (𝓘 (polynomialTargetEquiv F B p f)) =
          𝓘 (polynomialTargetEquiv F B p f) := by
  let e := polynomialTargetEquiv F B p
  let f := e.symm (𝓟 x)
  have hf : e f = 𝓟 x := e.apply_symm_apply _
  have hd : 𝒬 (𝓗 x) = x - 𝓘 (e f) := by
    rw [hf]
    apply Eq.symm
    apply sub_eq_iff_eq_add.mpr
    exact (original_cycle_decomposition F B H hHG hGH p hrank hp x hx).trans (add_comm _ _)
  refine ⟨f, ⟨⟨𝓗 x, hd, ?_⟩, ?_⟩, ?_⟩
  · intro hNx
    have he := corrected_homotopy_charge F B H hHG hGH p 1 x (by simpa using hNx)
    simpa only [sub_self, Int.cast_zero, zero_smul] using he
  · exact LinearMap.congr_fun
      (Number.correctedI_N F B H hHG hGH p ℓ) (e f)
  · intro g hg
    obtain ⟨y, hy, _⟩ := hg.1
    have he : e f = e g :=
      (corrected_representatives_unique F B H hHG hGH p hrank hp (e f) (e g)).mp
        ⟨y - 𝓗 x, by rw [map_sub, hy, hd]; abel⟩
    exact (e.injective he).symm

end OriginalContraction

end D5.S3.VertexAlgebra.LatticeRelativeBRSTCohomology
