/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFixedQuasiprimary
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFixedQuasiprimary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quasiprimary derivative strings span the actual fixed Leech vertex algebra. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction

/-! Graded spanning on the actual fixed source. The Virasoro commutator
constructs preimages for the positive-grade strings under the lowering mode.
The vacuum is killed by translation, and the actual weight-one space vanishes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldFixedQuasiprimary

open ActualLeechHyperbolic (leechData leechCoordinates leech_spec)
open FixedGradedDuality (fixedGradeSubmodule fixedGrades_iSup)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeInvolution (FixedCarrier fixedMode fixedSpace fixedTranslation fixedVacuum)
open LatticePositiveEnergy
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticeSugawaraVirasoro (sugawaraMode_virasoro)
open OriginalOrbifoldConformal (conformalVector L L_fixed_apply)
open OriginalOrbifoldField (Y_fixed_ncoeff_apply)
open SourceBPZ.ThetaReflectionAction (thetaRep_apply_one thetaRep_gradeProjection_commute)

open private no_roots from D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
open private fixedGrade_one_eq_bot from D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

open scoped VertexOperator

noncomputable section

local notation "D" => leechData
local notation "V" => FixedCarrier leechData
local notation "hu" => And.left (And.right leech_spec)
local notation "hD" => And.left (And.right (And.right leech_spec))

/-- The stress field's Virasoro modes on the actual fixed Leech carrier. -/
def fixedL (m : ℤ) : Module.End ℂ V :=
  fixedMode D (conformalVector D hu).1 (m + 1)

local notation "T" => fixedTranslation leechData
local notation "E" => fixedL 1
local notation "H" => fixedL 0

theorem fixedL_val (m : ℤ) (a : V) :
    (fixedL m a).val = sugawaraMode D (gramComplex D)⁻¹ m a.val := by
  rw [Matrix.inv_eq_left_inv (actualInverse_left D hu)]
  have h := L_fixed_apply D hu hD m (a, 0)
  simpa only [L, conformalVector, Y_fixed_ncoeff_apply, fixedL] using h

private theorem fixedL_commutator (m n : ℤ) (a : V) :
    fixedL m (fixedL n a) - fixedL n (fixedL m a) =
      ((m - n : ℤ) : ℂ) • fixedL (m + n) a +
        (if m + n = 0 then (leechData.rank : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) • a := by
  apply Subtype.ext
  have h := LinearMap.congr_fun
    (sugawaraMode_virasoro D (actualInverse D)
      (actualInverse_left D hu) (actualInverse_right D hu) m n) a.val
  rw [← Matrix.inv_eq_left_inv (actualInverse_left D hu)] at h
  simpa only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, fixedL_val,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] using h

theorem fixedL_minus_one : fixedL (-1) = T := by
  ext a : 1
  apply Subtype.ext
  rw [fixedL_val, Matrix.inv_eq_left_inv (actualInverse_left D hu),
    LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D
      (actualInverse D) (actualInverse_left D hu) (actualInverse_right D hu)]
  rfl

private theorem fixedL_zero_iff_grade (d : ℤ) (a : V) :
    H a = (d : ℂ) • a ↔ a.val ∈ grade D d := by
  rw [Subtype.ext_iff, fixedL_val, Submodule.coe_smul,
    Matrix.inv_eq_left_inv (actualInverse_left D hu)]
  exact actualL0_eigen_iff_grade D (actualInverse D)
    (actualInverse_left D hu) (actualInverse_right D hu) d a.val

private theorem fixedL_grade (m d : ℤ) (a : V) (ha : a.val ∈ grade D d) :
    (fixedL m a).val ∈ grade D (d - m) := by
  apply (fixedL_zero_iff_grade (d - m) _).mp
  have h := fixedL_commutator 0 m a
  have hc : (if m = 0 then (leechData.rank : ℂ) / 12 * ((0 : ℂ)^3 - 0) else 0) = 0 := by
    simp
  simp only [zero_sub, zero_add, Int.cast_neg, Int.cast_zero, hc, zero_smul, add_zero,
    (fixedL_zero_iff_grade d a).mpr ha, map_smul] at h
  rw [sub_eq_iff_eq_add, ← add_smul, ← Int.cast_neg, ← Int.cast_add] at h
  simpa only [sub_eq_add_neg, add_comm] using h

private theorem translation_grade (d : ℤ) (a : V) (ha : a.val ∈ grade D d) :
    (T a).val ∈ grade D (d + 1) := by
  simpa only [fixedL_minus_one, sub_neg_eq_add] using fixedL_grade (-1) d a ha

private theorem translation_pow_grade (d : ℤ) (b : V) (hb : b.val ∈ grade D d) (j : ℕ) :
    ((T ^ j) b).val ∈ grade D (d + j) := by
  induction j with
  | zero => simpa only [Nat.cast_zero, add_zero, pow_zero, Module.End.one_apply] using hb
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ, ← add_assoc]
    exact translation_grade (d + j) _ ih

private theorem lowering_translation (a : V) :
    E (T a) = T (E a) + (2 : ℂ) • H a := by
  have h := fixedL_commutator 1 (-1) a
  norm_num [fixedL_minus_one] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

/-- The exact lowering coefficient on each derivative of a homogeneous quasiprimary. -/
theorem lowering_translation_pow (d : ℤ) (b : V) (hb : b.val ∈ grade D d)
    (hE : E b = 0) (j : ℕ) :
    E ((T ^ (j + 1)) b) = ((j + 1 : ℂ) * (2 * (d : ℂ) + j)) • (T ^ j) b := by
  induction j with
  | zero =>
    simpa [hE, (fixedL_zero_iff_grade d b).mpr hb, smul_smul] using lowering_translation b
  | succ j ih =>
    have hT : T ((T ^ j) b) = (T ^ (j + 1)) b := by
      rw [pow_succ', Module.End.mul_apply]
    have hH : H ((T ^ (j + 1)) b) = ((d + (j + 1 : ℕ) : ℤ) : ℂ) • (T ^ (j + 1)) b :=
      (fixedL_zero_iff_grade _ _).mpr (translation_pow_grade d b hb (j + 1))
    rw [pow_succ' T (j + 1), Module.End.mul_apply, lowering_translation, ih, map_smul,
      hT, hH, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

private theorem negative_grade_zero (d : ℤ) (hd : d < 0) {a : V}
    (ha : a.val ∈ grade D d) : a = 0 := by
  apply Subtype.ext
  apply (carrierCoeffEquiv D).injective
  ext i
  have hcharge := chargeEnergy_nonneg D hD i.1
  have henergy : 0 ≤ energy D i := by
    change 0 ≤ chargeEnergy D i.1 + (oscillatorEnergy i.2 : ℤ)
    omega
  exact (mem_grade_iff D d _).mp ha i (by omega)

/-- The fixed degree-zero submodule is the line of the actual vacuum. -/
theorem fixed_grade_zero :
    fixedGradeSubmodule D 0 = Submodule.span ℂ {fixedVacuum D} := by
  apply le_antisymm
  · intro a ha
    change a.val ∈ grade D 0 at ha
    rw [grade_zero D hD, Submodule.mem_span_singleton] at ha
    obtain ⟨c, hc⟩ := ha
    exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc⟩
  · apply Submodule.span_le.mpr
    rintro _ rfl
    change (fixedVacuum D).val ∈ grade D 0
    rw [grade_zero D hD]
    exact Submodule.mem_span_singleton_self _

/-- The fixed degree-one submodule of the actual Leech lattice is zero. -/
theorem fixed_grade_one : fixedGradeSubmodule D 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have h := fixedGrade_one_eq_bot D hD (no_roots leechCoordinates leech_spec.2.2.2)
  change fixedSpace D ⊓ grade D 1 = ⊥ at h
  have hmem : a.val ∈ fixedSpace D ⊓ grade D 1 := ⟨a.property, ha⟩
  rw [h] at hmem
  have hz : a.val = 0 := by simpa only [Submodule.mem_bot] using hmem
  simpa only [Submodule.mem_bot] using (Subtype.ext hz : a = 0)

private theorem lowering_grade_zero (a : V) (ha : a.val ∈ grade D 0) : E a = 0 :=
  negative_grade_zero (0 - 1) (by omega) (fixedL_grade 1 0 a ha)

/-- The actual vacuum is quasiprimary and has no nonzero derivatives. -/
theorem fixed_vacuum_annihilation : E (fixedVacuum D) = 0 ∧ T (fixedVacuum D) = 0 := by
  constructor
  · apply lowering_grade_zero
    change fixedVacuum D ∈ fixedGradeSubmodule D 0
    rw [fixed_grade_zero]
    exact Submodule.mem_span_singleton_self _
  · apply Subtype.ext
    exact LatticeSugawaraConformal.translation_vacuum D

private theorem translation_grade_zero (b : V) (hb : b.val ∈ grade D 0) : T b = 0 := by
  change b ∈ fixedGradeSubmodule D 0 at hb
  rw [fixed_grade_zero, Submodule.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  rw [map_smul, fixed_vacuum_annihilation.2, smul_zero]

/-- A string generator of degree `n` is an iterated translation of an
actual fixed quasiprimary of nonnegative integral degree. -/
def quasiprimaryDerivatives (n : ℤ) : Set V :=
  {a | ∃ (d j : ℕ) (b : V), (d : ℤ) + j = n ∧ b.val ∈ grade D d ∧
    E b = 0 ∧ (T ^ j) b = a}

private theorem mem_derivative_span_of_quasiprimary (n : ℕ) (a : V)
    (ha : a.val ∈ grade D n) (he : E a = 0) :
    a ∈ Submodule.span ℂ (quasiprimaryDerivatives n) :=
  Submodule.subset_span ⟨n, 0, a, by simp, ha, he, by simp⟩

private theorem derivative_span_le_grade (n : ℤ) :
    Submodule.span ℂ (quasiprimaryDerivatives n) ≤ fixedGradeSubmodule D n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, j, b, hdeg, hb, _, rfl⟩
  change ((T ^ j) b).val ∈ grade D n
  rw [← hdeg]
  exact translation_pow_grade d b hb j

/-- In positive degree each generator lifts to the next string span under `L(1)`. -/
private theorem derivative_span_le_lowering_image (n : ℕ) (hn : 0 < n) :
    Submodule.span ℂ (quasiprimaryDerivatives n) ≤
      (Submodule.span ℂ (quasiprimaryDerivatives ((n : ℤ) + 1))).map E := by
  refine Submodule.span_le.mpr ?_
  rintro a ⟨d, j, b, hdeg, hb, hE, rfl⟩
  by_cases hd : d = 0
  · have hj : j ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hb0 : b.val ∈ grade D 0 := by simpa [hd] using hb
    rw [pow_succ, Module.End.mul_apply, translation_grade_zero b hb0, map_zero]
    exact Submodule.zero_mem _
  · let c : ℂ := (j + 1 : ℂ) * (2 * (d : ℂ) + j)
    have hc : c ≠ 0 := by
      have hnat : (j + 1) * (2 * d + j) ≠ 0 := by
        exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
      dsimp only [c]
      exact_mod_cast hnat
    refine Submodule.mem_map.mpr ⟨c⁻¹ • (T ^ (j + 1)) b, ?_, ?_⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨d, j + 1, b, by omega, hb, hE, rfl⟩
    · rw [map_smul, lowering_translation_pow d b hb hE j, Int.cast_natCast, smul_smul]
      change (c⁻¹ * c) • (T ^ j) b = (T ^ j) b
      rw [inv_mul_cancel₀ hc, one_smul]

private theorem fixed_grade_nat_le_span (n : ℕ) :
    fixedGradeSubmodule D n ≤ Submodule.span ℂ (quasiprimaryDerivatives n) := by
  induction n with
  | zero =>
    intro a ha
    exact mem_derivative_span_of_quasiprimary 0 a ha (lowering_grade_zero a ha)
  | succ n ih =>
    cases n with
    | zero =>
      change fixedGradeSubmodule D 1 ≤ _
      rw [fixed_grade_one]
      exact bot_le
    | succ n =>
      intro a ha
      have hlower : E a ∈ fixedGradeSubmodule D (n + 1 : ℕ) := by
        change (E a).val ∈ grade D _
        have h := fixedL_grade 1 ((n + 1 + 1 : ℕ) : ℤ) a ha
        rwa [show ((n + 1 + 1 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by omega] at h
      obtain ⟨y, hy, hyE⟩ := Submodule.mem_map.mp
        (derivative_span_le_lowering_image (n + 1) (Nat.succ_pos n) (ih hlower))
      have hy' : y ∈ Submodule.span ℂ (quasiprimaryDerivatives (n + 1 + 1 : ℕ)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hy
      have hygrade : y.val ∈ grade D (n + 1 + 1 : ℕ) := derivative_span_le_grade _ hy'
      have hresidual : E (a - y) = 0 := by rw [map_sub, hyE, sub_self]
      have hspan := mem_derivative_span_of_quasiprimary (n + 1 + 1) (a - y)
        ((grade D _).sub_mem ha hygrade) hresidual
      simpa only [sub_add_cancel] using Submodule.add_mem _ hspan hy'

/-- Each integer energy grade is exactly the span of the quasiprimary strings
of that total degree. This includes the vacuum, the empty weight one, and
all negative degrees. -/
theorem fixed_grade_eq_span (n : ℤ) :
    fixedGradeSubmodule D n = Submodule.span ℂ (quasiprimaryDerivatives n) := by
  apply le_antisymm
  · intro a ha
    by_cases hn : 0 ≤ n
    · have he := Int.toNat_of_nonneg hn
      rw [← he] at ha ⊢
      exact fixed_grade_nat_le_span n.toNat ha
    · rw [negative_grade_zero n (by omega) ha]
      exact Submodule.zero_mem _
  · exact derivative_span_le_grade n

/-- Every actual fixed state is a finite linear combination of homogeneous
quasiprimary derivative strings. -/
theorem span_quasiprimary_derivatives :
    Submodule.span ℂ (⋃ n : ℤ, quasiprimaryDerivatives n) = ⊤ := by
  apply top_unique
  have hgrade := fixedGrades_iSup D (by
    intro n a
    simpa only [thetaRep_apply_one] using thetaRep_gradeProjection_commute D n a)
  rw [← hgrade]
  apply iSup_le
  intro n
  rw [fixed_grade_eq_span]
  exact Submodule.span_mono (Set.subset_iUnion quasiprimaryDerivatives n)

#print axioms fixedL_val
#print axioms fixedL_minus_one
#print axioms lowering_translation_pow
#print axioms fixed_grade_zero
#print axioms fixed_grade_one
#print axioms fixed_vacuum_annihilation
#print axioms fixed_grade_eq_span
#print axioms span_quasiprimary_derivatives

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldFixedQuasiprimary
