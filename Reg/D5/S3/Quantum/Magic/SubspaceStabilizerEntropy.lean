import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Subspace Stabilizer Entropy -/

namespace Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy

open scoped BigOperators Matrix
open _root_.D5.S3.Observer.WindowRegister
open _root_.D5.S3.Quantum.Algebra.WeylDisplacement
open _root_.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace FourthMomentCycleAndHermitianFormula

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d] {S : Type} [Fintype S],
    (Odd d → tau d = windowRoot d ^ ((d + 1) / 2)) ∧
    (∀ x y : ℕ, intPaperDisplacement d (x : ℤ) (y : ℤ) =
      tau d ^ (x * y) • (shiftMatrix d ^ x * clockMatrix d ^ y)) ∧
    (Odd d → ∀ x y : ℤ,
      intPaperDisplacement d x y = paperDisplacement d ((x : ZMod d), (y : ZMod d))) ∧
    (Odd d → ∀ x y : ℕ, tau d ^ (x * y) • (shiftMatrix d ^ x * clockMatrix d ^ y) =
      paperDisplacement d ((x : ZMod d), (y : ZMod d))) ∧
    (∀ (E : Matrix (ZMod d) S ℂ) (a : ZMod d × ZMod d),
      labelFourthMoment E a = Matrix.trace (alt (Eᴴ * displacement d a.1 a.2 * E) * A4 S)) ∧
    (∀ (E : Matrix (ZMod d) S ℂ),
      extrinsicScore E = (O.readout () () d : ℂ)⁻¹ *
        ∑ a : ZMod d × ZMod d, labelFourthMoment E a) ∧
    (∀ {H : Type} [Fintype H] [DecidableEq H] (A : Matrix H H ℂ), Aᴴ = A →
      ((Fintype.card H : ℂ) * ((Fintype.card H : ℂ) + 1) *
        ((Fintype.card H : ℂ) + 2) * ((Fintype.card H : ℂ) + 3)) * Matrix.trace (alt A * A4 H) =
        (Matrix.trace A) ^ 4 + 6 * (Matrix.trace A) ^ 2 * Matrix.trace (A ^ 2) +
          3 * (Matrix.trace (A ^ 2)) ^ 2 + 8 * Matrix.trace A * Matrix.trace (A ^ 3) +
          6 * Matrix.trace (A ^ 4))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let E1 : Matrix (ZMod 1) (ZMod 1) ℂ := 1
  have hbad : extrinsicScore E1 = 0 := by
    have hr := (@h 1 _ (ZMod 1) _).2.2.2.2.2.1 E1
    simpa [rejected, realize] using hr
  have hmom0 : labelFourthMoment E1 (0, 0) = 1 :=
    ((subspace_gap_isometry_invariance_and_twirl 1).2.1 E1 (by simp [E1])).1
  have hgood : extrinsicScore E1 = 1 := by
    rw [(fourth_moment_cycle_and_hermitian_formula 1 (S := ZMod 1)).2.2.2.2.2.1 E1]
    have huniv : (Finset.univ : Finset (ZMod 1 × ZMod 1)) = {(0, 0)} := by
      ext x; simp [Subsingleton.elim x (0, 0)]
    rw [huniv, Finset.sum_singleton, hmom0]; norm_num
  have h10 : (1 : ℂ) = 0 := hgood.symm.trans hbad
  norm_num at h10

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@fourth_moment_cycle_and_hermitian_formula)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fourth_moment_cycle_and_hermitian_formula, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@fourth_moment_cycle_and_hermitian_formula)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy.FourthMomentCycleAndHermitianFormula.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy.FourthMomentCycleAndHermitianFormula.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FourthMomentCycleAndHermitianFormula

namespace IntrinsicTermAndRankOneEntropy

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d],
    (∀ (k : ℕ) [NeZero k],
      (Odd k → intrinsicTerm k = (3 : ℂ) / ((k : ℂ) + 2)) ∧
      (Even k → intrinsicTerm k = (3 * ((k : ℂ) + 2)) / (((k : ℂ) + 1) * ((k : ℂ) + 3)))) ∧
    intrinsicTerm 1 = 1 ∧
    (∀ (ψ : ZMod d → ℂ), star ψ ⬝ᵥ ψ = 1 →
      let ρ := Matrix.vecMulVec ψ (star ψ)
      (linearStabilizerEntropy ψ : ℂ) = 1 - (d : ℂ)⁻¹ *
        ∑ a : ZMod d × ZMod d, (‖Matrix.trace ((paperDisplacement d a)ᴴ * ρ)‖ ^ 4 : ℂ) ∧
      (linearStabilizerEntropy ψ : ℂ) =
        1 - (O.readout () () d : ℂ) * Matrix.trace (Q d * power4 ρ)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [Unique S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ),
      Eᴴ * E = 1 → aseGap E = (linearStabilizerEntropy (fun j => E j default) : ℂ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let ψ1 : ZMod 1 → ℂ := fun _ => 1
  have hnorm : star ψ1 ⬝ᵥ ψ1 = 1 := by
    have huniv1 : (Finset.univ : Finset (ZMod 1)) = {0} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim x 0⟩
    simp [dotProduct, huniv1, ψ1]
  have hbad : (linearStabilizerEntropy ψ1 : ℂ) = 1 := by
    have hr := ((h 1).2.2.1 ψ1 hnorm).2
    simpa [rejected, realize] using hr
  let E1 : Matrix (ZMod 1) (ZMod 1) ℂ := 1
  have hcol : (fun j : ZMod 1 => E1 j default) = ψ1 :=
    funext fun j => by rw [Subsingleton.elim j default]; simp [E1, ψ1]
  have hgap : aseGap E1 = (linearStabilizerEntropy ψ1 : ℂ) := by
    rw [← hcol]
    exact (intrinsic_term_and_rank_one_entropy 1).2.2.2 (S := ZMod 1) E1 (by simp [E1])
  have hext : extrinsicScore E1 = 1 := by
    rw [(fourth_moment_cycle_and_hermitian_formula 1 (S := ZMod 1)).2.2.2.2.2.1 E1]
    have huniv : (Finset.univ : Finset (ZMod 1 × ZMod 1)) = {(0, 0)} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim x (0, 0)⟩
    rw [huniv, Finset.sum_singleton,
      ((subspace_gap_isometry_invariance_and_twirl 1).2.1 E1 (by simp [E1])).1]
    norm_num
  have hgood : (linearStabilizerEntropy ψ1 : ℂ) = 0 := by
    rw [← hgap]; unfold aseGap
    simp [(intrinsic_term_and_rank_one_entropy 1).2.1, hext]
  have h01 : (0 : ℂ) = 1 := hgood.symm.trans hbad
  norm_num at h01

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@intrinsic_term_and_rank_one_entropy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intrinsic_term_and_rank_one_entropy, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@intrinsic_term_and_rank_one_entropy)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy.IntrinsicTermAndRankOneEntropy.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy.IntrinsicTermAndRankOneEntropy.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "body", "body", "body", "arg", "arg",
        "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntrinsicTermAndRankOneEntropy

namespace SubspaceGapIsometryInvarianceAndTwirl

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O := ∀ (d : ℕ) [NeZero d],
    (∀ {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
        [NeZero (Fintype.card S₁)] [NeZero (Fintype.card S₂)]
        (E₁ : Matrix (ZMod d) S₁ ℂ) (E₂ : Matrix (ZMod d) S₂ ℂ),
      E₁ᴴ * E₁ = 1 → E₂ᴴ * E₂ = 1 →
        (LinearMap.range E₁.mulVecLin = LinearMap.range E₂.mulVecLin ↔ E₁ * E₁ᴴ = E₂ * E₂ᴴ) ∧
        (LinearMap.range E₁.mulVecLin = LinearMap.range E₂.mulVecLin →
          Fintype.card S₁ = Fintype.card S₂ ∧
          (∀ a : ZMod d × ZMod d, labelFourthMoment E₁ a = labelFourthMoment E₂ a) ∧
          extrinsicScore E₁ = extrinsicScore E₂ ∧ aseGap E₁ = aseGap E₂)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      labelFourthMoment E (0, 0) = 1 ∧
      (∀ (U : Matrix (ZMod d) (ZMod d) ℂ) (a b : ZMod d × ZMod d) (c : ℂ),
        Uᴴ * U = 1 → U * (E * Eᴴ) = (E * Eᴴ) * U →
        U * paperDisplacement d a * Uᴴ = c • paperDisplacement d b → c * star c = 1 →
          labelFourthMoment E a = labelFourthMoment E b)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      symTwirl4 d (power4 E * A4 S * (power4 E)ᴴ) = A4 (ZMod d) ∧
      (O.readout () () d : ℂ) * Matrix.trace (Q d * symTwirl4 d (power4 E * A4 S * (power4 E)ᴴ)) =
        intrinsicTerm d)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have : NeZero (Fintype.card (ZMod 1)) := ⟨by simp⟩
  let E1 : Matrix (ZMod 1) (ZMod 1) ℂ := 1
  have hr := ((h 1).2.2 (S := ZMod 1) E1 (by simp [E1])).2
  simp only [rejected, realize, Nat.cast_zero, zero_mul] at hr
  rw [(intrinsic_term_and_rank_one_entropy 1).2.1] at hr
  norm_num at hr

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, by decide⟩

def evidence : Registration arena
    (type_of% (@subspace_gap_isometry_invariance_and_twirl)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@subspace_gap_isometry_invariance_and_twirl, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@subspace_gap_isometry_invariance_and_twirl)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy.SubspaceGapIsometryInvarianceAndTwirl.unit
  realizationName := .str
    `Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy.SubspaceGapIsometryInvarianceAndTwirl
    "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SubspaceGapIsometryInvarianceAndTwirl

end
end Reg.D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
