/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldAllWeightDimension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldAllWeightDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact integer-weight dimensions from the assembled Leech stress mode. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeHalfFockParityT
import D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeTraceSplit

/-! The two actual stress operators give finite weight spaces at every integer.
The fixed dimension uses the full theta trace and the twisted dimension counts
the odd oscillator fiber with the genuine rank-24 ground multiplicity. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldAllWeightDimension

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef mode mode_apply)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeInvolution (fixedSpace)
open LatticeSugawaraCurrents (sugawaraMode)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockParityT (actualParity_on_actualGrade)
open LatticeHalfFockGradedTrace
  (actualTensorL0 actualGrade actualGrade_module_finite actualAmbientBasis
    actualTensorL0_repr oddWeight actual_grade_finrank_bRank bRank)
open LatticePositiveEnergy
  (grade gradeBasis grade_finiteDimensional EnergyFiber actualL0_eigenspace_eq_grade)
open LatticeThetaCharacter (fullThetaRestriction positiveFullThetaTrace
  positive_full_theta_character signedThetaCoefficient)
open SourceBPZ.ThetaGradeTraceSplit
  (plusGrade minusGrade gradeSplitEquiv gradeTheta grade_theta_trace_eq_fixed_minus_anti)

local notation "H" => actualInverse leechData
local notation "hHG" => actualInverse_left leechData leechUnit
local notation "hGH" => actualInverse_right leechData leechUnit

abbrev OrbifoldWeight (n : ℤ) : Submodule ℂ Orbifold :=
  (mode 0).eigenspace (n : ℂ)

abbrev UntwistedWeight (n : ℤ) : Submodule ℂ (Carrier leechData) :=
  (sugawaraMode leechData H 0).eigenspace (n : ℂ)

abbrev FixedWeight (n : ℤ) : Submodule ℂ (Carrier leechData) :=
  fixedSpace leechData ⊓ UntwistedWeight n

abbrev TwistedWeight (n : ℤ) : Submodule ℂ (ActualTensor leechData leechUnit) :=
  paritySpace leechData leechUnit (-1) ⊓ (actualTensorL0 leechData leechUnit).eigenspace (n : ℂ)

private theorem mem_orbifoldWeight_iff (n : ℤ) (x : Orbifold) :
    x ∈ OrbifoldWeight n ↔ x.1.val ∈ FixedWeight n ∧ x.2.val ∈ TwistedWeight n := by
  have hf : (mode 0 x).1.val = sugawaraMode leechData H 0 x.1.val :=
    congrArg Prod.fst (mode_apply 0 x)
  have ht : (mode 0 x).2.val = actualTensorL0 leechData leechUnit x.2.val :=
    congrArg Prod.snd (mode_apply 0 x)
  constructor
  · intro hx
    have he : mode 0 x = (n : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx
    refine ⟨⟨x.1.property, Module.End.mem_eigenspace_iff.mpr ?_⟩,
      ⟨x.2.property, Module.End.mem_eigenspace_iff.mpr ?_⟩⟩
    · exact hf.symm.trans (congrArg (fun y : Orbifold => y.1.val) he)
    · exact ht.symm.trans (congrArg (fun y : Orbifold => y.2.val) he)
  · rintro ⟨hfixed, htwisted⟩
    apply Module.End.mem_eigenspace_iff.mpr
    apply Prod.ext
    · apply Subtype.ext
      exact hf.trans (Module.End.mem_eigenspace_iff.mp hfixed.2)
    · apply Subtype.ext
      exact ht.trans (Module.End.mem_eigenspace_iff.mp htwisted.2)

/-- The literal assembled stress eigenspace is the product of its native sectors. -/
def weightEquiv (n : ℤ) : OrbifoldWeight n ≃ₗ[ℂ] (FixedWeight n × TwistedWeight n) where
  toFun x :=
    let hx := (mem_orbifoldWeight_iff n x.val).mp x.property
    (⟨x.val.1.val, hx.1⟩, ⟨x.val.2.val, hx.2⟩)
  invFun x :=
    let y : Orbifold := (⟨x.1.val, x.1.property.1⟩, ⟨x.2.val, x.2.property.1⟩)
    ⟨y, (mem_orbifoldWeight_iff n y).mpr ⟨x.1.property, x.2.property⟩⟩
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
  right_inv _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_add' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  map_smul' _ _ := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- The rank-24 twisted ground has weight 3/2, and every integer weight
at least two corresponds to an odd oscillator degree. -/
theorem twistedWeight_eq (n : ℤ) :
    TwistedWeight n =
      if 2 ≤ n then actualGrade leechData leechUnit (2 * n - 3).toNat else ⊥ := by
  by_cases hn : 2 ≤ n
  · rw [ite_eq_left hn]
    let N := (2 * n - 3).toNat
    have hN : (N : ℤ) = 2 * n - 3 := Int.toNat_of_nonneg (by omega)
    have hcast : (N : ℂ) = ((2 * n - 3 : ℤ) : ℂ) := by exact_mod_cast hN
    have henergy : (leechData.rank : ℂ) / 16 + (N : ℂ) / 2 = (n : ℂ) := by
      rw [leech_spec.1, hcast]
      push_cast
      ring
    have he : (actualTensorL0 leechData leechUnit).eigenspace (n : ℂ) =
        actualGrade leechData leechUnit N := by
      rw [Module.End.eigenspace_def, actualGrade, henergy, Module.End.one_eq_id]
    change paritySpace leechData leechUnit (-1) ⊓
      (actualTensorL0 leechData leechUnit).eigenspace (n : ℂ) = actualGrade leechData leechUnit N
    rw [he]
    apply inf_eq_right.mpr
    intro v hv
    have hodd : N % 2 = 1 := by omega
    have hp := actualParity_on_actualGrade leechData leechUnit N ⟨v, hv⟩
    rw [neg_one_pow_eq_pow_mod_two, hodd, pow_one] at hp
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hp
  · rw [ite_eq_right hn]
    apply le_antisymm _ bot_le
    intro v hv
    have he : actualTensorL0 leechData leechUnit v = (n : ℂ) • v :=
      Module.End.mem_eigenspace_iff.mp hv.2
    apply (Submodule.mem_bot ℂ).mpr
    let basis := actualAmbientBasis leechData leechUnit
    apply basis.repr.injective
    rw [map_zero]
    apply Finsupp.ext
    intro i
    rw [Finsupp.zero_apply]
    by_contra hcoeff
    have hc := congrArg (fun z => basis.repr z i) he
    change (actualAmbientBasis leechData leechUnit).repr
      (actualTensorL0 leechData leechUnit v) i = basis.repr ((n : ℂ) • v) i at hc
    rw [actualTensorL0_repr] at hc
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
    have hs := mul_right_cancel₀ hcoeff hc
    have hreal : (leechData.rank : ℂ) / 16 + (oddWeight leechData i.1 : ℂ) / 2 =
        ((24 / 16 + (oddWeight leechData i.1 : ℝ) / 2 : ℝ) : ℂ) := by
      simp [leech_spec.1]
    rw [hreal] at hs
    have hre := congrArg Complex.re hs
    rw [Complex.ofReal_re, Complex.intCast_re] at hre
    have hnonneg : (0 : ℝ) ≤ (oddWeight leechData i.1 : ℝ) := Nat.cast_nonneg _
    have hle : (n : ℝ) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
    linarith

private theorem untwistedWeight_eq_grade (n : ℤ) : UntwistedWeight n = grade leechData n :=
  actualL0_eigenspace_eq_grade leechData H hHG hGH n

instance untwistedWeight_finite (n : ℤ) : FiniteDimensional ℂ (UntwistedWeight n) := by
  rw [untwistedWeight_eq_grade n]
  exact grade_finiteDimensional leechData leechPosDef n

instance fixedWeight_finite (n : ℤ) : FiniteDimensional ℂ (FixedWeight n) :=
  Submodule.finiteDimensional_of_le (inf_le_right : FixedWeight n ≤ UntwistedWeight n)

instance twistedWeight_finite (n : ℤ) : FiniteDimensional ℂ (TwistedWeight n) := by
  by_cases hn : 2 ≤ n
  · rw [twistedWeight_eq n, ite_eq_left hn]
    exact actualGrade_module_finite leechData leechUnit _
  · rw [twistedWeight_eq n, ite_eq_right hn]
    infer_instance

instance orbifoldWeight_finite (n : ℤ) : FiniteDimensional ℂ (OrbifoldWeight n) :=
  Module.Finite.of_surjective (weightEquiv n).symm.toLinearMap (weightEquiv n).symm.surjective

/-- The ground factor multiplies the count of the actual odd oscillator fiber. -/
def twistedMultiplicity (n : ℤ) : ℕ :=
  if 2 ≤ n then 4096 * bRank 24 (2 * n - 3).toNat else 0

theorem twisted_weight_finrank (n : ℤ) :
    Module.finrank ℂ (TwistedWeight n) = twistedMultiplicity n := by
  by_cases hn : 2 ≤ n
  · simp only [twistedMultiplicity, ite_eq_left hn]
    rw [twistedWeight_eq n, ite_eq_left hn,
      actual_grade_finrank_bRank, leech_spec.1] <;> rfl
  · simp only [twistedMultiplicity, ite_eq_right hn]
    rw [twistedWeight_eq n, ite_eq_right hn, finrank_bot]

/-- Half the ambient finite dimension plus half the actual theta trace gives
the dimension of the fixed part of the Sugawara eigenspace. -/
theorem fixed_weight_finrank_eq_trace (n : ℤ) :
    (Module.finrank ℂ (FixedWeight n) : ℂ) =
      ((Module.finrank ℂ (UntwistedWeight n) : ℂ) +
        positiveFullThetaTrace leechData H hHG hGH leechPosDef n) / 2 := by
  let : FiniteDimensional ℂ (grade leechData n) :=
    grade_finiteDimensional leechData leechPosDef n
  let : FiniteDimensional ℂ (plusGrade leechData n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let : FiniteDimensional ℂ (minusGrade leechData n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hfixed : FixedWeight n = plusGrade leechData n := by
    change fixedSpace leechData ⊓ UntwistedWeight n = grade leechData n ⊓ fixedSpace leechData
    rw [untwistedWeight_eq_grade n, inf_comm]
  have htrace : positiveFullThetaTrace leechData H hHG hGH leechPosDef n =
      LinearMap.trace ℂ (grade leechData n) (gradeTheta leechData n) := by
    unfold positiveFullThetaTrace
    let e := LinearEquiv.ofEq _ _ (untwistedWeight_eq_grade n)
    have hc : e.conj (fullThetaRestriction leechData H hHG hGH n) = gradeTheta leechData n := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      rfl
    rw [← hc, LinearMap.trace_conj']
  have hsum := (gradeSplitEquiv leechData n).finrank_eq
  rw [Module.finrank_prod, ← untwistedWeight_eq_grade n, ← hfixed] at hsum
  have hsumC : (Module.finrank ℂ (UntwistedWeight n) : ℂ) =
      (Module.finrank ℂ (FixedWeight n) : ℂ) +
        (Module.finrank ℂ (minusGrade leechData n) : ℂ) := by
    simpa only [Nat.cast_add] using congrArg (fun d : ℕ => (d : ℂ)) hsum
  have hdiff := grade_theta_trace_eq_fixed_minus_anti leechData n leechPosDef
  rw [← htrace, ← hfixed] at hdiff
  rw [hsumC, hdiff]
  ring

/-- The fixed coefficient uses the actual charge/oscillator basis energy fiber
and the signed theta coefficient, extended by zero at negative indices. -/
theorem fixed_weight_finrank_eq_coefficients (n : ℤ) :
    (Module.finrank ℂ (FixedWeight n) : ℂ) =
      ((Nat.card (EnergyFiber leechData n) : ℂ) +
        (if 0 ≤ n then signedThetaCoefficient leechData n.toNat else 0)) / 2 := by
  have hcard : Module.finrank ℂ (UntwistedWeight n) = Nat.card (EnergyFiber leechData n) := by
    rw [untwistedWeight_eq_grade n]
    exact Module.finrank_eq_nat_card_basis (gradeBasis leechData n)
  have htheta := (positive_full_theta_character leechData H hHG hGH leechPosDef
    (q := 0) (by simp)).1 n
  rw [fixed_weight_finrank_eq_trace n, hcard, htheta]

/-- The coefficient formula shared by the orbifold and its relative BRST quotient. -/
def weightMultiplicity (n : ℤ) : ℂ :=
  ((Nat.card (EnergyFiber leechData n) : ℂ) +
    (if 0 ≤ n then signedThetaCoefficient leechData n.toNat else 0)) / 2 +
      (twistedMultiplicity n : ℂ)

/-- Exact finrank of the literal assembled stress eigenspace at every integer weight. -/
theorem weight_finrank (n : ℤ) :
    (Module.finrank ℂ (OrbifoldWeight n) : ℂ) = weightMultiplicity n := by
  rw [weightMultiplicity, (weightEquiv n).finrank_eq, Module.finrank_prod, Nat.cast_add,
    fixed_weight_finrank_eq_coefficients n, twisted_weight_finrank n]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldAllWeightDimension

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open ActualLeechOrbifoldAllWeightDimension (weightMultiplicity weight_finrank)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

local instance (p : Charge hyperbolicPlane) :
    AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup (GradedCycles planeFrame planeBasis p 1)

/-- At nonzero plane charge the native relative ghost-one quotient has the
orbifold multiplicity at the conformal weight selected by the charge. -/
theorem ghost_one_finrank_nonzero (p : Charge hyperbolicPlane) (hp : p ≠ 0) :
    (Module.finrank ℂ (GradedCohomology planeFrame planeBasis p 1) : ℂ) =
      weightMultiplicity (1 - p (0 : Fin 2) * p (1 : Fin 2)) := by
  rw [(ghostOneCohomologyEquivNonzero p hp).finrank_eq]
  exact weight_finrank (1 - p (0 : Fin 2) * p (1 : Fin 2))

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology
