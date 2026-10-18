import D5.S3.Geometry.Hyperideal.GramDomainContraction
import D5.S3.Geometry.Hyperideal.LengthGramBody
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set
open scoped Matrix
open D5.S3.Geometry.Hyperideal.GramDomainContraction
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

namespace CFMP80NativeDomainExactTransient

set_option autoImplicit false
set_option maxHeartbeats 2000000

-- Reuse the original frozen helper; do not copy its proof or alter its owner.
open private rad_positive from D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

#check @rad_positive
#check @Coordinates
#check @Delta
#check @rawDomain
#check @X
#check @gram
#check @delta
#check @frame
#check @rawNum
#check @leftRad
#check @rightRad
#check @rawCos
#check @lengthGram
#check @shared_radial_body
#check @full_domain_contractible
#check @Real.coshOpenPartialHomeomorph
#check @Real.cosh_arcosh
#check @Real.arcosh_cosh
#check @Real.arcosh_pos
#check @Real.one_lt_cosh
#check @OpenPartialHomeomorph.pi
#check @OpenPartialHomeomorph.homeomorphOfImageSubsetSource
#check @Homeomorph.setCongr
#check @Homeomorph.contractibleSpace
#check @Real.sqrt_pos
#check @Real.sq_sqrt
#check @sq_lt_sq'
#check @abs_lt_of_sq_lt_sq'
#check @mul_pos_iff_of_pos_left
#check @lt_div_iff₀
#check @div_lt_iff₀

/-- The literal six source frames, with one common vector x. -/
theorem frame_discriminant_identity (x : Coordinates) (q : Fin 6) :
    leftRad x q * rightRad x q - (rawNum x q)^2 =
      ((x q)^2 - 1) * Delta x := by
  fin_cases q <;>
    simp [leftRad, rightRad, rawNum, frame, Delta, delta, gram, rad, numerator,
      Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
      Matrix.det_fin_one, Matrix.det_fin_zero, Matrix.submatrix_apply,
      Fin.sum_univ_succ, Fin.succAbove] <;> ring

/-- The two original radicands and their actual positive square-root product. -/
theorem source_denominator_facts (x : Coordinates) (hx : ∀ i, 1 < x i)
    (q : Fin 6) :
    0 < leftRad x q ∧ 0 < rightRad x q ∧
      0 < Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q) ∧
      (Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q))^2 =
        leftRad x q * rightRad x q := by
  have hA : 0 < leftRad x q :=
    rad_positive _ _ _ (hx _) (hx _) (hx _)
  have hB : 0 < rightRad x q :=
    rad_positive _ _ _ (hx _) (hx _) (hx _)
  refine ⟨hA, hB, mul_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hB), ?_⟩
  rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]

/-- A chosen actual slot is strict precisely on the determinant-positive domain. -/
theorem delta_pos_iff_rawCos_strict (x : Coordinates) (hx : ∀ i, 1 < x i)
    (q : Fin 6) :
    0 < Delta x ↔ -1 < rawCos x q ∧ rawCos x q < 1 := by
  obtain ⟨hA, hB, hDpos, hDsquare⟩ := source_denominator_facts x hx q
  let D : ℝ := Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q)
  have hD : 0 < D := hDpos
  have hD2 : D^2 = leftRad x q * rightRad x q := hDsquare
  have hfactor : 0 < (x q)^2 - 1 := by
    nlinarith only [sq_nonneg (x q - 1), hx q]
  have hcos : rawCos x q = rawNum x q / D := by
    change rawNum x q / Real.sqrt (leftRad x q) / Real.sqrt (rightRad x q) = _
    rw [div_div]
  have hstrict_iff : (-1 < rawCos x q ∧ rawCos x q < 1) ↔
      (rawNum x q)^2 < D^2 := by
    rw [hcos]
    constructor
    · rintro ⟨hlo, hhi⟩
      apply sq_lt_sq'
      · simpa using (lt_div_iff₀ hD).mp hlo
      · simpa using (div_lt_iff₀ hD).mp hhi
    · intro hsquare
      obtain ⟨hlo, hhi⟩ := abs_lt_of_sq_lt_sq' hsquare hD.le
      constructor
      · apply (lt_div_iff₀ hD).mpr
        simpa using hlo
      · apply (div_lt_iff₀ hD).mpr
        simpa using hhi
  have hsquare_iff : (rawNum x q)^2 < D^2 ↔ 0 < Delta x := by
    rw [hD2]
    constructor
    · intro hsquare
      apply (mul_pos_iff_of_pos_left hfactor).mp
      rw [← frame_discriminant_identity x q]
      exact sub_pos.mpr hsquare
    · intro hdelta
      apply sub_pos.mp
      rw [frame_discriminant_identity x q]
      exact mul_pos hfactor hdelta
  exact (hstrict_iff.trans hsquare_iff).symm

/-- All six slots read that same x and that same determinant. -/
theorem delta_pos_iff_all_rawCos_strict (x : Coordinates) (hx : ∀ i, 1 < x i) :
    0 < Delta x ↔ ∀ q : Fin 6, -1 < rawCos x q ∧ rawCos x q < 1 := by
  constructor
  · intro hdelta q
    exact (delta_pos_iff_rawCos_strict x hx q).mp hdelta
  · intro hstrict
    exact (delta_pos_iff_rawCos_strict x hx 0).mpr (hstrict 0)

theorem mem_rawDomain_iff (x : Coordinates) :
    x ∈ rawDomain ↔ (∀ i, 1 < x i) ∧
      ∀ q : Fin 6, -1 < rawCos x q ∧ rawCos x q < 1 := by
  change ((∀ i, 1 < x i) ∧ 0 < Delta x) ↔ _
  constructor
  · rintro ⟨hx, hdelta⟩
    exact ⟨hx, (delta_pos_iff_all_rawCos_strict x hx).mp hdelta⟩
  · rintro ⟨hx, hstrict⟩
    exact ⟨hx, (delta_pos_iff_all_rawCos_strict x hx).mpr hstrict⟩

/-- A determinant preimage, without an independent geometric interpretation. -/
def lengthDeterminantDomain : Set Coordinates :=
  {l | (∀ i, 0 < l i) ∧ 0 < Delta (fun i => Real.cosh (l i))}

/-- The source-formula length domain, retaining all six strict inequalities. -/
def strictLengthDomain : Set Coordinates :=
  {l | (∀ i, 0 < l i) ∧
    ∀ q : Fin 6, -1 < rawCos (fun i => Real.cosh (l i)) q ∧
      rawCos (fun i => Real.cosh (l i)) q < 1}

def coordinateCosh : OpenPartialHomeomorph Coordinates Coordinates :=
  OpenPartialHomeomorph.pi (fun _ : Fin 6 => Real.coshOpenPartialHomeomorph)

/-- Restriction of the already existing product cosh/arcosh partial homeomorphism. -/
def determinantDomainHomeomorph : lengthDeterminantDomain ≃ₜ X :=
  coordinateCosh.homeomorphOfImageSubsetSource
    (by
      intro l hl
      change ∀ i ∈ (Set.univ : Set (Fin 6)), 0 < l i
      exact fun i _ => hl.1 i)
    (by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        change (∀ i, 1 < Real.cosh (l i)) ∧
          0 < Delta (fun i => Real.cosh (l i))
        exact ⟨fun i => Real.one_lt_cosh.mpr (hl.1 i).ne', hl.2⟩
      · intro hx
        change (∀ i, 1 < x i) ∧ 0 < Delta x at hx
        let l : Coordinates := fun i => Real.arcosh (x i)
        have hback : (fun i => Real.cosh (l i)) = x := by
          funext i
          exact Real.cosh_arcosh (hx.1 i).le
        refine ⟨l, ⟨fun i => Real.arcosh_pos (hx.1 i), ?_⟩, ?_⟩
        · change 0 < Delta (fun i => Real.cosh (l i))
          rw [hback]
          exact hx.2
        · change (fun i => Real.cosh (l i)) = x
          exact hback)

theorem delta_cosh_eq_lengthGram (l : Coordinates) :
    Delta (fun i => Real.cosh (l i)) = -(lengthGram l).det := rfl

theorem length_domains_eq : lengthDeterminantDomain = strictLengthDomain := by
  ext l
  change ((∀ i, 0 < l i) ∧ 0 < Delta (fun i => Real.cosh (l i))) ↔
    (∀ i, 0 < l i) ∧ ∀ q : Fin 6,
      -1 < rawCos (fun i => Real.cosh (l i)) q ∧
        rawCos (fun i => Real.cosh (l i)) q < 1
  constructor
  · rintro ⟨hl, hdelta⟩
    have hx : ∀ i, 1 < Real.cosh (l i) :=
      fun i => Real.one_lt_cosh.mpr (hl i).ne'
    exact ⟨hl, (delta_pos_iff_all_rawCos_strict _ hx).mp hdelta⟩
  · rintro ⟨hl, hstrict⟩
    have hx : ∀ i, 1 < Real.cosh (l i) :=
      fun i => Real.one_lt_cosh.mpr (hl i).ne'
    exact ⟨hl, (delta_pos_iff_all_rawCos_strict _ hx).mpr hstrict⟩

def strictLengthDomainHomeomorph : strictLengthDomain ≃ₜ X :=
  (Homeomorph.setCongr length_domains_eq).symm.trans determinantDomainHomeomorph

theorem lengthDeterminantDomain_contractible : ContractibleSpace lengthDeterminantDomain := by
  letI : ContractibleSpace X := full_domain_contractible
  exact determinantDomainHomeomorph.contractibleSpace

theorem strictLengthDomain_contractible : ContractibleSpace strictLengthDomain := by
  letI : ContractibleSpace X := full_domain_contractible
  exact strictLengthDomainHomeomorph.contractibleSpace

#check @frame_discriminant_identity
#check @source_denominator_facts
#check @delta_pos_iff_rawCos_strict
#check @delta_pos_iff_all_rawCos_strict
#check @mem_rawDomain_iff
#check @lengthDeterminantDomain
#check @strictLengthDomain
#check @coordinateCosh
#check @determinantDomainHomeomorph
#check @delta_cosh_eq_lengthGram
#check @length_domains_eq
#check @strictLengthDomainHomeomorph
#check @lengthDeterminantDomain_contractible
#check @strictLengthDomain_contractible

#print axioms rad_positive
#print axioms frame_discriminant_identity
#print axioms source_denominator_facts
#print axioms delta_pos_iff_rawCos_strict
#print axioms delta_pos_iff_all_rawCos_strict
#print axioms mem_rawDomain_iff
#print axioms lengthDeterminantDomain
#print axioms strictLengthDomain
#print axioms coordinateCosh
#print axioms determinantDomainHomeomorph
#print axioms delta_cosh_eq_lengthGram
#print axioms length_domains_eq
#print axioms strictLengthDomainHomeomorph
#print axioms lengthDeterminantDomain_contractible
#print axioms strictLengthDomain_contractible

end CFMP80NativeDomainExactTransient
