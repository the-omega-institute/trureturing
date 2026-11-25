import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicParityCorrection

/-! Dependence of the cyclic certificates on the clipped quadratic and the split
of the mass transferred to the nearest neighbors. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

namespace Dual

def actual : Realization signature :=
  realize signature (fun _ _ x => max 0 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) [NeZero q] (t H Z a : ℝ)
    (_hH : 0 < H) (_hZ : 0 < Z)
    (_hC : -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q) < 1),
    let clip := R.readout () ()
    let C := -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q)
    let β := (t - H * (1 - C ^ 2)) / (1 - C)
    let ρ := -C - β / H
    let p := fun i : ZMod q =>
      (t - H * (1 - sample i ^ 2) - β * (1 - sample i)) / Z
    sample ((↑(q / 2) : ℤ) : ZMod q) = C ∧
    (∀ i, C ≤ sample i ∧ p i = H * (sample i - C) * (sample i - ρ) / Z ∧
      (0 < clip (p i) ↔ C < sample i ∧ ρ < sample i)) ∧
    ∀ v : ZMod q → ℝ, (∑ i, v i) = 1 →
      energy v =
        (2 * (t - (H / 2 + β) * (1 - a)) / Z - ∑ i, (clip (p i)) ^ 2) +
        (∑ i, (v i - clip (p i)) ^ 2) +
        2 * (∑ i, v i * (clip (p i) - p i)) +
        (2 * β / Z) * (cosineMoment 1 v - a) +
        (H / Z) * (cosineMoment 2 v - a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : -Real.cos ((↑(2 % 2 : ℕ) : ℝ) / 2 * mesh 2) < 1 := by norm_num
  obtain ⟨hrootSample, hroot, _⟩ := h 2 0 1 1 0 (by norm_num) (by norm_num) hc
  let i : ZMod 2 := ((↑(2 / 2 : ℕ) : ℤ) : ZMod 2)
  have hn := ((hroot i).2.2.mp (by norm_num [rejected, realize])).1
  change sample i = _ at hrootSample
  exact (lt_irrefl _ (hrootSample ▸ hn))

def evidence : Registration arena (type_of% @antipodal_dual_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@antipodal_dual_certificate, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@antipodal_dual_certificate) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Dual.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Dual.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicParityCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Dual

namespace Primal

def actual : Realization signature :=
  realize signature (fun _ _ x => x / 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) [NeZero q] (_hq : 4 ≤ q)
    (w : ZMod q → ℝ) (A : ℝ)
    (_hw : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ -1 → i ≠ ((↑(q / 2) : ℤ) : ZMod q) → 0 ≤ w i) (_hmass : ∑ i, w i = 1),
    let splitMass := R.readout () ()
    let C := -Real.cos ((↑(q % 2) : ℝ) / 2 * mesh q)
    let D₁ := 1 - cosineMoment 1 w
    let D₂ := 1 - cosineMoment 2 w
    let F := 1 - Real.cos (mesh q)
    let G := 1 - Real.cos (2 * mesh q)
    let U := 1 - C
    let V := 2 * (1 - C ^ 2)
    let δ := (A - D₂ - V * (A - D₁) / U) / (G - V * F / U)
    let μ := (A - D₁ - F * δ) / U
    0 ≤ w 0 - δ - μ → 0 ≤ w 1 + splitMass δ → 0 ≤ w (-1) + splitMass δ →
    0 ≤ w ((↑(q / 2) : ℤ) : ZMod q) + μ →
    let v := adjusted w δ μ (splitMass δ)
    v ∈ feasible q (1 - A) ∧ cosineMoment 1 v = 1 - A ∧ cosineMoment 2 v = 1 - A

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let w : ZMod 8 → ℝ := Pi.single 0 1
  have hw (i : ZMod 8) : 0 ≤ w i := by
    simp only [w, Pi.single_apply]
    split <;> norm_num
  have hm : ∑ i, w i = 1 := by simp [w, Pi.single_apply]
  have hM (r : ℕ) : cosineMoment r w = 1 := by
    unfold cosineMoment
    simp [w, Pi.single_apply, ite_mul, D5.S3.Fourier.Concentration.AggregateCosineBalance.mode]
  have hh := h 8 (by decide) w 0 (fun i _ _ _ _ => hw i) hm
  have hh' : adjusted w 0 0 1 ∈ feasible 8 1 ∧
      cosineMoment 1 (adjusted w 0 0 1) = 1 ∧ cosineMoment 2 (adjusted w 0 0 1) = 1 := by
    have h1 : 0 ≤ w 1 + 1 := by linarith only [hw 1]
    have hneg : 0 ≤ w (-1) + 1 := by linarith only [hw (-1)]
    simpa [hM, rejected, realize, show w 0 = 1 by simp [w], h1, hneg, hw] using hh
  have hsum : ∑ i, adjusted w 0 0 1 i = 3 := by
    norm_num [adjusted, w, Pi.single_apply, sum_add_distrib]
  linarith only [hh'.1.2.1, hsum]

def evidence : Registration arena (type_of% @adjusted_matches_moments) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjusted_matches_moments, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    norm_num [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@adjusted_matches_moments) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Primal.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Primal.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicParityCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Primal

namespace Mesh

abbrev meshSignature := UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization meshSignature :=
  realize meshSignature (fun _ _ => mesh) (fun e => nomatch e)

def rejected : Realization meshSignature :=
  realize meshSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem spacing_varies : actual.readout () () 1 ≠ actual.readout () () 2 := by
  simp [actual, realize, mesh]

namespace Positive

abbrev arena : Arena where
  signature := meshSignature
  Law R := ∀ {q : ℕ} [NeZero q],
    let spacing := R.readout () ()
    0 < spacing q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 : (0 : ℝ) < 0 := by simpa [rejected, realize] using h (q := 1)
  exact (lt_irrefl 0) h0

def evidence : Registration arena (type_of% @mesh_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mesh_pos, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨(), 1, 2, spacing_varies⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@mesh_pos) (Realization meshSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Mesh.Positive.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Mesh.Positive.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize meshSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicParityCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positive

namespace Centered

abbrev arena : Arena where
  signature := meshSignature
  Law R := ∀ {q : ℕ} (i : ZMod q),
    let spacing := R.readout () ()
    centeredAngle i = (i.valMinAbs : ℝ) * spacing q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi : (1 : ZMod 4).valMinAbs = 1 := by decide
  have hangle : centeredAngle (1 : ZMod 4) = 0 := by
    simpa [rejected, realize] using h (q := 4) (1 : ZMod 4)
  unfold centeredAngle at hangle
  norm_num [hi] at hangle

def evidence : Registration arena (type_of% @centeredAngle_eq_mesh) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@centeredAngle_eq_mesh, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨(), 1, 2, spacing_varies⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@centeredAngle_eq_mesh) (Realization meshSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Mesh.Centered.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection.Mesh.Centered.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize meshSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicParityCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Centered

end Mesh

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
