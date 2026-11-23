/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldLightConeDegreeBounds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldLightConeDegreeBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree bounds and finite perturbation length on the actual orbifold relative shell. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The orbifold-valued right coefficients of a relative state are
zero-mode eigenvectors. Their nonnegative weights bound the plane and
ghost energies and give a finite length for the original perturbation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldMatter (Orbifold mode eq_zero_of_weight_neg)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge Carrier bilinear)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticeSugawaraConformal (sugawaraMode_weighted_homogeneous)
open LatticePositiveEnergy (chargeEnergy chargeEnergy_complex_half)
open LatticeLightConeCoordinates (NullFrame PolynomialCoordinates frequencyWeight)
open LatticeLightConeCoordinates.NullFrame (Label)
open LatticeQuartetContraction (State StateIndex sector actualBasis actualBasis_apply
  ghostB0 b0_coefficients h)
open LatticeBRSTModeFiltration (degree exponentDegree)
open LatticeRelativeShellDegreeBounds (frameEnergy ghost_abs_charge_sub_one_le_count
  ghost_count_le_relativeEnergy abs_exponentDegree_le_frameEnergy)
open LatticeRelativeMassShell (massShellCutoff massShellCutoff_cast)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)
open D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
  (energy relativeEnergy relativeEnergy_nonneg L_zero_ket)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
  (diagonal diagonal_basis diagonal_coefficient)
open MvPolynomial (monomial IsWeightedHomogeneous isWeightedHomogeneous_monomial)

open private plane_inverse from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private originalEnergy from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
open private assocE_decomposition assocB0_eq rightLift_tmul rightSlice_tmul
  rightSlice_chargeProject from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone

variable (F : NullFrame hyperbolicPlane) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

private def rightBasisEnergy (i : StateIndex hyperbolicPlane t) : ℤ :=
  chargeEnergy hyperbolicPlane i.1.1 + (frameEnergy i.1.2 : ℤ) + relativeEnergy i.2 - 1

private theorem originalEnergy_diagonal :
    originalEnergy hyperbolicPlane (gramComplex hyperbolicPlane) =
      diagonal (actualBasis F B) (fun i => (rightBasisEnergy i : ℂ)) := by
  apply (actualBasis F B).ext
  rintro ⟨⟨q, m⟩, S⟩
  rw [diagonal_basis, actualBasis_apply]
  let P : PolynomialCoordinates (Label t) := monomial m 1
  have hP : IsWeightedHomogeneous frequencyWeight P (frameEnergy m) :=
    isWeightedHomogeneous_monomial frequencyWeight m 1 rfl
  have hP' := (F.frequency_grading B ((F.coordinateEquiv B).symm P) (frameEnergy m)).mp
    (by simpa only [AlgEquiv.apply_symm_apply] using hP)
  let v : Carrier hyperbolicPlane := Finsupp.single q ((F.coordinateEquiv B).symm P)
  have hm := sugawaraMode_weighted_homogeneous hyperbolicPlane (gramComplex hyperbolicPlane)
    plane_inverse plane_inverse q ((F.coordinateEquiv B).symm P) (frameEnergy m) hP'
  change (sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) 0 v ⊗ₜ[ℂ] ket S) +
    (v ⊗ₜ[ℂ] D5.S3.Quantum.Fermionic.BcGhostVirasoro.L 0 (ket S)) = _
  change sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) 0 v =
    ((frameEnergy m : ℂ) + (bilinear hyperbolicPlane q q : ℂ) / 2) • v at hm
  rw [hm, L_zero_ket, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← add_smul,
    ← chargeEnergy_complex_half]
  change ((frameEnergy m : ℂ) + (chargeEnergy hyperbolicPlane q : ℂ) + (energy S : ℂ)) •
      (v ⊗ₜ[ℂ] ket S) =
    (rightBasisEnergy ((⟨q, m⟩, S) : StateIndex hyperbolicPlane t) : ℂ) • (v ⊗ₜ[ℂ] ket S)
  congr 1
  simp only [rightBasisEnergy, relativeEnergy, Int.cast_sub, Int.cast_add, Int.cast_natCast,
    Int.cast_one]
  ring

private theorem rightSlice_assocE (i : StateIndex hyperbolicPlane t) (x : AssocState) :
    rightSlice F B i (assocE x) =
      mode 0 (rightSlice F B i x) + (rightBasisEnergy i : ℂ) • rightSlice F B i x := by
  rw [assocE_decomposition, originalEnergy_diagonal F B]
  induction x using TensorProduct.inductionOn with
  | tmul v y =>
    simp only [LinearMap.add_apply, map_add, LinearMap.rTensor_tmul, rightLift_tmul,
      rightSlice_tmul, diagonal_coefficient, map_smul, smul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]
    abel

/-- The total-energy kernel gives an exact orbifold zero-mode eigenvalue
at each right basis index, with the ghost vacuum shift included. -/
theorem rightSlice_eigen_of_assocE_eq_zero (x : AssocState) (hx : assocE x = 0)
    (i : StateIndex hyperbolicPlane t) :
    mode 0 (rightSlice F B i x) =
      ((1 - chargeEnergy hyperbolicPlane i.1.1 - (frameEnergy i.1.2 : ℤ) -
        relativeEnergy i.2 : ℤ) : ℂ) • rightSlice F B i x := by
  have he : mode 0 (rightSlice F B i x) +
      (rightBasisEnergy i : ℂ) • rightSlice F B i x = 0 := by
    rw [← rightSlice_assocE F B, hx, map_zero]
  have hw : -rightBasisEnergy i =
      1 - chargeEnergy hyperbolicPlane i.1.1 - (frameEnergy i.1.2 : ℤ) -
        relativeEnergy i.2 := by
    unfold rightBasisEnergy
    omega
  rw [← hw, Int.cast_neg, neg_smul]
  exact eq_neg_of_add_eq_zero_left he

private theorem rightSlice_eq_zero_of_assocB0_eq_zero (x : AssocState) (hx : assocB0 x = 0)
    (i : StateIndex hyperbolicPlane t) (hi : 3 ∈ i.2) :
    rightSlice F B i x = 0 := by
  classical
  -- A linear functional detecting the coefficient reduces to the plane-and-ghost kernel.
  by_contra hn
  let : Module.Free ℂ Orbifold := Module.Free.of_divisionRing ℂ Orbifold
  let : Module.Projective ℂ Orbifold := Module.Projective.of_free
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ hn
  let test : AssocState →ₗ[ℂ] State hyperbolicPlane :=
    (TensorProduct.lid ℂ (State hyperbolicPlane)).toLinearMap.comp
      (φ.rTensor (State hyperbolicPlane))
  have test_tmul (v : Orbifold) (y : State hyperbolicPlane) :
      test (v ⊗ₜ[ℂ] y) = φ v • y := by
    simp only [test, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul]
  have hcomm (y : AssocState) :
      test (rightLift ghostB0 y) = ghostB0 (test y) := by
    induction y using TensorProduct.inductionOn with
    | tmul v y => simp only [rightLift_tmul, test_tmul, map_smul]
    | add y z hy hz => simp only [map_add, hy, hz]
  have htest : ghostB0 (test x) = 0 := by
    rw [← hcomm, ← assocB0_eq, hx, map_zero]
  let coeff : State hyperbolicPlane →ₗ[ℂ] ℂ :=
    (Finsupp.lapply i).comp (actualBasis F B).repr.toLinearMap
  have hcoeff (y : AssocState) : coeff (test y) = φ (rightSlice F B i y) := by
    induction y using TensorProduct.inductionOn with
    | tmul v y =>
      rw [test_tmul, rightSlice_tmul, coeff.map_smul, φ.map_smul]
      exact mul_comm (φ v) (coeff y)
    | add y z hy hz =>
      rw [test.map_add, coeff.map_add, hy, hz, (rightSlice F B i).map_add, φ.map_add]
  exact hφ ((hcoeff x).symm.trans ((b0_coefficients F B (test x)).mp htest i hi))

/-- Every nonzero relative coefficient has the fixed momentum, omits the
zero-mode ghost site, and satisfies the excitation and degree bounds. -/
theorem relativeShell_rightSlice_bounds (p : Charge hyperbolicPlane)
    (x : AssocState) (hx : x ∈ relativeShell p)
    (i : StateIndex hyperbolicPlane t) (hi : rightSlice F B i x ≠ 0) :
    i.1.1 = p ∧ 3 ∉ i.2 ∧
      |degree i| ≤ (frameEnergy i.1.2 : ℤ) + relativeEnergy i.2 ∧
      (frameEnergy i.1.2 : ℤ) + relativeEnergy i.2 ≤ 1 - chargeEnergy hyperbolicPlane p := by
  obtain ⟨hp, hb, he⟩ := (mem_relativeShell_iff p x).mp hx
  have hq : i.1.1 = p := by
    by_contra hq
    have hs := congrArg (fun y => rightSlice F B i y) hp
    rw [rightSlice_chargeProject F B, ite_eq_right hq] at hs
    exact hi hs.symm
  have h3 : 3 ∉ i.2 := fun h3 => hi (rightSlice_eq_zero_of_assocB0_eq_zero F B x hb i h3)
  refine ⟨hq, h3, ?_, ?_⟩
  · calc
      |degree i| = |exponentDegree i.1.2 + (charge i.2 - 1)| := by
        congr 1
        unfold degree
        ring
      _ ≤ |exponentDegree i.1.2| + |charge i.2 - 1| := abs_add_le _ _
      _ ≤ (frameEnergy i.1.2 : ℤ) + relativeEnergy i.2 :=
        add_le_add (abs_exponentDegree_le_frameEnergy i.1.2)
          ((ghost_abs_charge_sub_one_le_count i.2 h3).trans (ghost_count_le_relativeEnergy i.2 h3))
  · by_contra hlevel
    let r : ℤ := 1 - chargeEnergy hyperbolicPlane p - (frameEnergy i.1.2 : ℤ) -
      relativeEnergy i.2
    have hr : r < 0 := by
      dsimp [r]
      omega
    have hre : (r : ℂ).re < 0 := by
      rw [Complex.intCast_re]
      exact_mod_cast hr
    have hs := rightSlice_eigen_of_assocE_eq_zero F B x he i
    rw [hq] at hs
    exact hi (eq_zero_of_weight_neg _ (r : ℂ) hre hs)

private theorem eq_zero_of_all_rightSlices (x : AssocState)
    (hx : ∀ i, rightSlice F B i x = 0) : x = 0 := by
  apply (rightSlices F B).map_eq_zero_iff.mp
  apply Finsupp.ext
  intro i
  change rightSlice F B i x = 0
  exact hx i

/-- Negative available level leaves only the zero vector in the relative shell. -/
theorem relativeShell_eq_bot_of_negative_level (p : Charge hyperbolicPlane)
    (hp : 1 - chargeEnergy hyperbolicPlane p < 0) : relativeShell p = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  apply (Submodule.mem_bot ℂ).mpr
  apply eq_zero_of_all_rightSlices planeFrame planeBasis
  intro i
  by_contra hi
  have hl := (relativeShell_rightSlice_bounds planeFrame planeBasis p x hx i hi).2.2.2
  have hg := relativeEnergy_nonneg i.2
  have hf : 0 ≤ (frameEnergy i.1.2 : ℤ) := Int.natCast_nonneg _
  omega

private theorem relativeShell_rightSlice_cutoff (p : Charge hyperbolicPlane)
    (x : relativeShell p) (i : StateIndex hyperbolicPlane t)
    (hi : rightSlice F B i x.val ≠ 0) :
    i.1.1 = p ∧ |degree i| ≤ (massShellCutoff hyperbolicPlane p : ℤ) := by
  obtain ⟨hq, _, hd, he⟩ := relativeShell_rightSlice_bounds F B p x.val x.property i hi
  have hg := relativeEnergy_nonneg i.2
  have hf : 0 ≤ (frameEnergy i.1.2 : ℤ) := Int.natCast_nonneg _
  rw [massShellCutoff_cast hyperbolicPlane p (by omega)]
  exact ⟨hq, hd.trans he⟩

/-- A uniform power of the literal restricted h(Q - d0) vanishes at every momentum. -/
theorem relative_h_remainder_pow_eq_zero (p : Charge hyperbolicPlane) :
    (relativeH F B p * relativeDelta F B p) ^
      (2 * (1 - chargeEnergy hyperbolicPlane p).toNat + 1) = 0 := by
  let N := massShellCutoff hyperbolicPlane p
  let A : Module.End ℂ (relativeShell p) := relativeH F B p * relativeDelta F B p
  change A ^ (2 * N + 1) = 0
  apply LinearMap.ext
  intro x
  have hiter (k : ℕ) :
      ((A ^ k) x).val ∈ momentumFiltration F B p (-(N : ℤ) + (k : ℤ)) := by
    induction k with
    | zero =>
      simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero]
      apply (mem_momentumFiltration_iff F B p _ x.val).mpr
      intro i hi
      obtain ⟨hq, hd⟩ := relativeShell_rightSlice_cutoff F B p x i hi
      exact ⟨hq, (abs_le.mp hd).1⟩
    | succ k ih =>
      have hs := (relative_remainder_raises F B p (-(N : ℤ) + (k : ℤ)) ((A ^ k) x) ih).2
      simpa only [A, pow_succ', Module.End.mul_apply, Nat.cast_succ, add_assoc] using hs
  apply Subtype.ext
  change ((A ^ (2 * N + 1)) x).val = 0
  apply eq_zero_of_all_rightSlices F B
  intro i
  by_contra hi
  have hlo := ((mem_momentumFiltration_iff F B p _ _).mp (hiter (2 * N + 1)) i hi).2
  have hhi := (abs_le.mp (relativeShell_rightSlice_cutoff F B p _ i hi).2).2
  omega

private theorem relative_h_remainder_pow_val (p : Charge hyperbolicPlane)
    (k : ℕ) (x : relativeShell p) :
    (((relativeH F B p * relativeDelta F B p) ^ k) x).val =
      ((rightLift (h F B p) * remainder F p) ^ k) x.val := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply]
    exact congrArg (fun y => rightLift (h F B p) (remainder F p y)) ih

/-- The same power of the ambient lifted word kills every vector of the literal shell. -/
theorem h_remainder_pow_apply_eq_zero (p : Charge hyperbolicPlane)
    (x : AssocState) (hx : x ∈ relativeShell p) :
    ((rightLift (h F B p) * remainder F p) ^
      (2 * (1 - chargeEnergy hyperbolicPlane p).toNat + 1)) x = 0 := by
  have hs := LinearMap.congr_fun (relative_h_remainder_pow_eq_zero F B p)
    (⟨x, hx⟩ : relativeShell p)
  have hv := congrArg (fun y : relativeShell p => y.val) hs
  rw [relative_h_remainder_pow_val F B] at hv
  exact hv

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
