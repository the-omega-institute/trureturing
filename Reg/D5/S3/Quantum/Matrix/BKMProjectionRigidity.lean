import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Matrix.BKMProjectionRigidity

/-! The negative spectral mass in the BKM projection leakage bound. -/

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse (inverse_identities)
open _root_.D5.S3.Quantum.Matrix.BKMProjectionRigidity
open _root_.D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction (omega)
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

noncomputable section

namespace Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity

universe u
private abbrev Mat (n : Type u) := Matrix n n ℂ

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Σ _ : Fintype n, Σ _ : DecidableEq n, Mat n)
    (fun p => Mat p.1) (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p P => by
    letI := p.2.1
    letI := p.2.2.1
    exact negTrace (omega p.2.2.2 P)) (fun e => nomatch e)

def zeroMass : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (D P : Mat n) (_hD : D.PosDef) (_hp : P.IsHermitian) (_hp2 : P * P = P)
    (l u : ℝ) (_hl : 0 < l) (_hu : 0 < u)
    (_hlD : l • (1 : Mat n) ≤ D) (_hDu : D ≤ u • (1 : Mat n)),
    RHLinalg.frobSq (P * D * (1 - P)) ≤
      (12 * u ^ 2 / l) * R.readout () ⟨n, inferInstance, inferInstance, D⟩ P

private abbrev I := ULift.{u} (Fin 2)
private def D : Mat I := diagonal (fun i => if i.down = 0 then (2 : ℂ) else 1)
private def P : Mat I := fun _ _ => 1 / 2

private theorem Dpos : (D : Mat I).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  split
  · exact_mod_cast (show (0 : ℝ) < 2 by norm_num)
  · exact_mod_cast (show (0 : ℝ) < 1 by norm_num)

private theorem Pherm : (P : Mat I).IsHermitian := by
  change (P : Mat I)ᴴ = P
  ext i j
  simp [P, Matrix.conjTranspose_apply]

private theorem Pproj : (P : Mat I) * P = P := by
  ext i j
  simp [P, Matrix.mul_apply]

private theorem corner_ne : (P : Mat I) * D * (1 - P) ≠ 0 := by
  intro h
  let i : I := ULift.up 0
  have hv : ((P : Mat I) * D * (1 - P)) i i = 0 :=
    congrArg (fun A : Mat I => A i i) h
  have hDiag (j : I) :
      ((P : Mat I) * D) i j = (1 / 2 : ℂ) * (if j.down = 0 then 2 else 1) := by
    simp [D, Matrix.mul_diagonal, P]
  let f : I → ℂ := fun j => ((1 / 2 : ℂ) * if j.down = 0 then 2 else 1) *
    ((1 - (P : Mat I)) j i)
  have hsum : ((P : Mat I) * D * (1 - P)) i i = ∑ j, f j := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z : ℂ => z * ((1 - (P : Mat I)) j i)) (hDiag j)
  rw [hsum, ← (Equiv.ulift : I ≃ Fin 2).symm.sum_comp f] at hv
  norm_num [f, i, Fin.sum_univ_two, Matrix.one_apply, P] at hv

private theorem corner_positive : 0 < RHLinalg.frobSq ((P : Mat I) * D * (1 - P)) := by
  let A : Mat I := P * D * (1 - P)
  have hps := Matrix.posSemidef_conjTranspose_mul_self A
  have hz : (Aᴴ * A).trace ≠ 0 :=
    fun h => corner_ne (Matrix.conjTranspose_mul_self_eq_zero.mp (hps.trace_eq_zero_iff.mp h))
  have ht := Complex.nonneg_iff.mp hps.trace_nonneg
  change 0 < (Aᴴ * A).trace.re
  refine lt_of_le_of_ne ht.1 ?_
  intro h
  exact hz (Complex.ext h.symm ht.2.symm)

private theorem lower_bound : (1 : ℝ) • (1 : Mat I) ≤ D := by
  rw [one_smul, ← Matrix.diagonal_one]
  apply Matrix.PosSemidef.diagonal_mono
  intro i
  change (1 : ℂ) ≤ (if i.down = 0 then (2 : ℂ) else 1)
  split <;> norm_num

private theorem upper_bound : (D : Mat I) ≤ (2 : ℝ) • (1 : Mat I) := by
  have hs : (2 : ℝ) • (1 : Mat I) = diagonal (fun _ => (2 : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Complex.real_smul]
  rw [hs]
  apply Matrix.PosSemidef.diagonal_mono
  intro i
  change (if i.down = 0 then (2 : ℂ) else 1) ≤ (2 : ℂ)
  split <;> norm_num

private theorem zeroMass_fails : ¬ arena.{u}.Law zeroMass := by
  intro h
  have hbad := h D P Dpos Pherm Pproj 1 2 (by norm_num) (by norm_num) lower_bound upper_bound
  have hz : RHLinalg.frobSq ((P : Mat I) * D * (1 - P)) ≤ 0 := by
    simpa [zeroMass, realize] using hbad
  exact (not_le_of_gt corner_positive) hz

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨I, inferInstance, inferInstance, D⟩, 1, P, ?_⟩
  change negTrace (omega (D : Mat I) 1) ≠ negTrace (omega D P)
  have hone : omega (D : Mat I) 1 = D := by
    rw [omega_of_commute D 1 Dpos (Commute.one_right D), mul_one]
  have hz : negTrace (D : Mat I) = 0 := by
    unfold negTrace
    rw [(CFC.negPart_eq_zero_iff D Dpos.isHermitian).mpr Dpos.posSemidef.nonneg]
    simp
  have h0 : negTrace (omega (D : Mat I) P) ≠ 0 := by
    intro he
    have hbound := omega_projection_leakage (D : Mat I) P Dpos Pherm Pproj 1 2
      (by norm_num) (by norm_num) lower_bound upper_bound
    rw [he, mul_zero] at hbound
    exact (not_le_of_gt corner_positive) hbound
  rw [hone, hz]
  exact Ne.symm h0

def family : Registration arena.{u} (type_of% (@omega_projection_leakage.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omega_projection_leakage.{u}, zeroMass, zeroMass_fails⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual zeroMass zeroMass_fails
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omega_projection_leakage.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.BKMProjectionRigidity
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Power

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Σ _ : Fintype n, Σ _ : DecidableEq n, Mat n)
    (fun p => Mat p.1) (fun p => Mat p.1)

def actual : Realization signature.{u} :=
  realize signature (fun _ p X => by
    letI := p.2.1
    letI := p.2.2.1
    exact omega p.2.2.2 X) (fun e => nomatch e)

def zero : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨I, inferInstance, inferInstance, D⟩, 0, 1, ?_⟩
  exact fun h => zero_ne_one ((inverse_identities (D : Mat I) Dpos).1.injective h)


namespace CommutingDirection

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (D X : Mat n) (_hD : D.PosDef) (_hDX : Commute D X),
    R.readout () ⟨n, inferInstance, inferInstance, D⟩ X = D * X

private theorem zero_fails : ¬ arena.{u}.Law zero := by
  intro h
  have hz := h (1 : Mat I) 1 Matrix.PosDef.one (Commute.refl _)
  change (0 : Mat I) = 1 * 1 at hz
  exact zero_ne_one (hz.trans (one_mul _))


def family : Registration arena.{u} (type_of% (@omega_of_commute.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omega_of_commute.{u}, zero, zero_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual zero zero_fails
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omega_of_commute.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity.Power.CommutingDirection.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity.Power.CommutingDirection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.BKMProjectionRigidity
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CommutingDirection

namespace Positivity

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (D P : Mat n) (_hD : D.PosDef) (_hp : P.IsHermitian) (_hp2 : P * P = P),
    (R.readout () ⟨n, inferInstance, inferInstance, D⟩ P).PosSemidef ↔ Commute D P

private theorem zero_fails : ¬ arena.{u}.Law zero := by
  intro h
  have hz := (h (D : Mat I) P Dpos Pherm Pproj).1 Matrix.PosSemidef.zero
  apply corner_ne
  rw [← hz.eq, mul_assoc, Matrix.mul_sub, mul_one, Pproj, sub_self, mul_zero]


def family : Registration arena.{u} (type_of% (@omega_projection_posSemidef_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omega_projection_posSemidef_iff.{u}, zero, zero_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual zero zero_fails
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omega_projection_posSemidef_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity.Power.Positivity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity.Power.Positivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.BKMProjectionRigidity
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positivity

end Power
end Reg.D5.S3.Quantum.Matrix.BKMProjectionRigidity
