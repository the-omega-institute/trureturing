/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedSourceBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedSourceBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original source BPZ pairing is invariant under the P48q lift and nondegenerate on each cubic fixed grade. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! Opposite charge sectors pair by the integer Wick form. The charge phases
cancel on those sectors, and the Gram covariance transports each Wick
contraction. The source grade projection and the cubic average preserve the
pairing against a fixed homogeneous vector. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedSourceBPZ

open scoped BigOperators Matrix
open LatticeGeneratingFieldLocality MvPolynomial
open LatticeActualAnnihilation (annihilate annihilationDerivation annihilation_apply annihilate_X)
open LatticeActualGeneratorLocality (paritySign_square)
open LatticePositiveEnergy (grade gradeProjection gradeProjection_mem actualL0_eigen_iff_grade)
open LatticeSugawaraCurrents (gramComplex)
open LatticeTwistedGroundRealization.SignQuotient (integral_cocycle_square)
open SourceBPZ.OriginalSourcePairing
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open D5.S3.VertexAlgebra.SignedOscillatorWick (wick_constant_left)
open IsometryLift (oscillator phase phase_law)
open ThirdTwistedChargeAction (N nativeStandardEta)
open NativeStandardThirdLift (standardLift standardLift_single)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qAllJetWickField (NativeStates)
open P48qNativeConformalSector (fixedStates)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)

open private mixingMatrix oscillator_X phase_zero from
  D5.S3.VertexAlgebra.Lattice.IsometryLift
open private mixing_gram from
  D5.S3.VertexAlgebra.Lattice.InvariantQuadraticConformalState
open private mem_fixedStates_iff lift_fixed fixedProjection fixedProjection_fixed
  sourceLZero_fixedProjection from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private left_grade_projection_pairing from
  D5.S3.VertexAlgebra.FixedGradedDuality

noncomputable section

private theorem epsilon_opposite (D : LatticeData) (a : Charge D) :
    epsilon D a (-a) = paritySign (bilinear D a a / 2) := by
  have hneg : lowerCocycleExponent D a (-a) = -lowerCocycleExponent D a a := by
    simp [lowerCocycleExponent, Finset.sum_neg_distrib, add_comm]
  rw [epsilon, hneg, integral_cocycle_square]
  simp only [paritySign, even_neg]

private theorem phase_opposite (D : LatticeData) (s : Charge D ≃+ Charge D)
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b) (a : Charge D) :
    phase D s a * phase D s (-a) = 1 := by
  have h := phase_law D s hs a (-a)
  simp only [add_neg_cancel, phase_zero, Units.val_one, one_mul, map_neg,
    epsilon_opposite, hs] at h
  have hsign : paritySign (bilinear D a a / 2) ≠ 0 := by
    intro hz
    have hsq := paritySign_square (bilinear D a a / 2)
    rw [hz, zero_mul] at hsq
    exact zero_ne_one hsq
  apply Units.ext
  simp only [Units.val_mul, Units.val_one]
  apply mul_right_cancel₀ hsign
  rw [one_mul]
  exact h.symm

private theorem nativePhase_opposite (D : LatticeData) (s : Charge D ≃+ Charge D)
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b) (a : Charge D) :
    nativeStandardEta D s a * nativeStandardEta D s (-a) = 1 := by
  simp only [nativeStandardEta, map_neg]
  calc
    _ = (phase D s a * phase D s (-a)) *
        ((phase D s (N D s a))⁻¹ * (phase D s (-(N D s a)))⁻¹) := by ac_rfl
    _ = 1 := by
      rw [phase_opposite D s hs a, one_mul, ← mul_inv_rev,
        mul_comm (phase D s (-(N D s a))) (phase D s (N D s a)),
        phase_opposite D s hs (N D s a), inv_one]

private theorem oscillator_constant (D : LatticeData) (s : Charge D ≃+ Charge D)
    (p : Oscillator D) :
    (oscillator D s p).coeff 0 = p.coeff 0 := by
  have h : (constantCoeff : Oscillator D →+* ℂ).comp (oscillator D s).toRingHom =
      constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change constantCoeff (oscillator D s (C c)) = constantCoeff (C c : Oscillator D)
      rw [show oscillator D s (C c) = C c from (oscillator D s).commutes c]
    · intro x
      change constantCoeff (oscillator D s (X x)) = constantCoeff (X x : Oscillator D)
      rw [oscillator_X]
      simp only [map_sum, constantCoeff_smul, constantCoeff_X, smul_zero,
        Finset.sum_const_zero]
  exact congrArg (fun f : Oscillator D →+* ℂ => f p) h

/-- A creation direction transported by the lift contracts with the same
Gram coefficient against a transported polynomial. -/
private theorem oscillator_annihilate (D : LatticeData) (s : Charge D ≃+ Charge D)
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b)
    (i : Fin D.rank) (k : ℕ) (q : Oscillator D) :
    (∑ j : Fin D.rank, mixingMatrix D s j i • annihilate D j k (oscillator D s q)) =
      oscillator D s (annihilate D i k q) := by
  let M := mixingMatrix D s
  let δ : Derivation ℂ (Oscillator D) (Oscillator D) :=
    ∑ j : Fin D.rank, M j i • annihilationDerivation D j k
  have δ_apply (p : Oscillator D) :
      δ p = ∑ j : Fin D.rank, M j i • annihilate D j k p := by
    change (Derivation.coeFnAddMonoidHom
      (∑ j : Fin D.rank, M j i • annihilationDerivation D j k)) p = _
    rw [map_sum]
    simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.coe_smul,
      Pi.smul_apply, annihilation_apply]
  have hGram (l : Fin D.rank) :
      (∑ r : Fin D.rank, M r l * ∑ j : Fin D.rank, M j i * (D.G j r : ℂ)) =
        (D.G i l : ℂ) := by
    have h := congrArg (fun A : Matrix (Fin D.rank) (Fin D.rank) ℂ => A i l)
      (mixing_gram D s hs)
    change (Mᵀ * gramComplex D * M) i l = (D.G i l : ℂ) at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, gramComplex, Matrix.map_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
  have hX (l : Fin D.rank) (m : ℕ) :
      δ (oscillator D s (X (l,m))) = oscillator D s (annihilate D i k (X (l,m))) := by
    rw [oscillator_X, map_sum]
    change (∑ r : Fin D.rank, δ (M r l • X (r,m))) = _
    simp only [Derivation.map_smul]
    simp only [δ_apply, annihilate_X]
    by_cases h : k = m
    · simp only [if_pos h, smul_smul, ← Finset.sum_smul, hGram, map_smul, map_one]
    · simp only [if_neg h, smul_zero, Finset.sum_const_zero, map_zero]
  rw [← δ_apply (oscillator D s q)]
  induction q using MvPolynomial.induction_on with
  | C c =>
      change δ (oscillator D s (algebraMap ℂ (Oscillator D) c)) =
        oscillator D s (annihilate D i k (algebraMap ℂ (Oscillator D) c))
      rw [(oscillator D s).commutes c, ← annihilation_apply]
      simp only [Derivation.map_algebraMap, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
      rcases x with ⟨l,m⟩
      rw [map_mul, δ.leibniz, hp, hX, LatticeActualAnnihilation.annihilate_mul]
      simp only [smul_eq_mul, map_add, map_mul] <;> ac_rfl

private theorem integerWick_oscillator (D : LatticeData) (s : Charge D ≃+ Charge D)
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b) (p q : Oscillator D) :
    integerWick D (oscillator D s p) (oscillator D s q) = integerWick D p q := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
      rw [show oscillator D s (C c) = C c from (oscillator D s).commutes c]
      simp only [integerWick_apply, show retune D (C c) = C c from (retune D).commutes c,
        wick_constant_left, oscillator_constant]
  | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr]
  | mul_X p x hp =>
      rcases x with ⟨i,k⟩
      rw [mul_comm p, map_mul, oscillator_X, Finset.sum_mul, integerWick_creation D i k p q]
      simp only [smul_mul_assoc, map_sum, LinearMap.sum_apply, LinearMap.BilinForm.smul_left,
        integerWick_creation]
      calc
        _ = integerWick D (oscillator D s p)
            (-((k : ℂ) + 1) •
              ∑ j : Fin D.rank, mixingMatrix D s j i • annihilate D j k (oscillator D s q)) := by
          simp only [Finset.smul_sum, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by
          rw [oscillator_annihilate D s hs i k q,
            ← map_smul (oscillator D s) (-((k : ℂ) + 1)) (annihilate D i k q), hp]

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "B" => sourcePairing lattice

/-- The standard lift preserves the actual original P48q source pairing. -/
theorem sourcePairing_standardLift (u v : NativeStates) :
    B (σ u) (σ v) = B u v := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  | single a p =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => simp only [map_add, hv, hw]
      | single b q =>
          rw [standardLift_single, standardLift_single, LinearMap.BilinForm.smul_left,
            LinearMap.BilinForm.smul_right, sourcePairing_single_single,
            sourcePairing_single_single]
          have hab : g b = -g a ↔ b = -a := by
            rw [← map_neg g]
            exact g.injective.eq_iff
          simp only [hab]
          by_cases h : b = -a
          · subst b
            have hη := congrArg (fun z : ℂˣ => (z : ℂ))
              (nativePhase_opposite lattice g g_isometry a)
            simp only [Units.val_mul, Units.val_one] at hη
            simp only [if_pos rfl, integerWick_oscillator lattice g g_isometry,
              ← mul_assoc, hη, one_mul]
          · simp only [if_neg h, mul_zero]

/-- The homogeneous submodule of the actual cubically fixed source. -/
abbrev fixedGrade (d : ℤ) : Submodule ℂ NativeStates :=
  fixedStates ⊓ grade lattice d

/-- The original BPZ form restricted to the cubic fixed grade. -/
def fixedGradeForm (d : ℤ) : LinearMap.BilinForm ℂ (fixedGrade d) :=
  B.restrict (fixedGrade d)

private theorem sourcePairing_fixedProjection (u : fixedStates) (v : NativeStates) :
    B u.val (fixedProjection v) = B u.val v := by
  have h (w : NativeStates) : B u.val (σ w) = B u.val w := by
    simpa only [lift_fixed u] using sourcePairing_standardLift u.val w
  change B u.val ((3 : ℂ)⁻¹ • (v + σ v + σ (σ v))) = _
  simp only [LinearMap.BilinForm.smul_right, LinearMap.BilinForm.add_right, h]
  ring

/-- The actual cubic fixed grade is nondegenerate for the restricted BPZ form. -/
theorem fixedGradeForm_nondegenerate (d : ℤ) : (fixedGradeForm d).Nondegenerate := by
  have left (u : fixedGrade d) (hu : ∀ v : fixedGrade d, fixedGradeForm d u v = 0) :
      u = 0 := by
    apply Subtype.ext
    change u.val = 0
    apply (sourcePairing_nondegenerate lattice gram_det_unit).1
    intro v
    let p := gradeProjection lattice d v
    have hL (w : NativeStates) :=
      actualL0_eigen_iff_grade lattice (actualInverse lattice)
        (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit) d w
    have hp := (hL p).mpr (gradeProjection_mem lattice d v)
    have hw : fixedProjection p ∈ grade lattice d := by
      apply (hL _).mp
      rw [sourceLZero_fixedProjection, hp, map_smul]
    let w : fixedGrade d :=
      ⟨fixedProjection p, (mem_fixedStates_iff _).mpr (fixedProjection_fixed p), hw⟩
    calc
      B u.val v = B u.val p :=
        (left_grade_projection_pairing lattice B
          (fun m n x y hx hy hne => sourcePairing_grade lattice m n hne x y hx hy)
          d u.val u.property.2 v).symm
      _ = B u.val (fixedProjection p) :=
        (sourcePairing_fixedProjection ⟨u.val, u.property.1⟩ p).symm
      _ = 0 := hu w
  refine ⟨left, ?_⟩
  intro v hv
  apply left v
  intro u
  change B v.val u.val = 0
  rw [sourcePairing_symmetric lattice v.val u.val]
  exact hv u

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedSourceBPZ
