import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction

/-! Source family for the strict quadratic witness in the actual measurement theorem. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open LeanInformationAudit Matrix Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
noncomputable section

namespace Reg.D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction

universe u

private abbrev Mat (n : Type*) := Matrix n n ℂ
local notation "logDeriv" => _root_.D5.S3.Divergence.LogDerivTrace.logDeriv

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ q => q < 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (a : Matrix n n ℂ) (ha : a.PosDef)
    (htr : a.trace = 1) (hflat : ¬ ∃ c : ℝ, a = c • (1 : Matrix n n ℂ)),
    ∃ (i j : n) (hij : i ≠ j), ∃ (V : Matrix.unitaryGroup n ℂ)
      (Q : n → Matrix n n ℂ) (E : MatrixMap n n ℂ) (z : n → ℂ),
      let eigen := ha.isHermitian.eigenvalues
      let U := ha.isHermitian.eigenvectorUnitary
      let N := MatrixMap.of_kraus Q Q
      let τ := N a
      let P := Matrix.single i i (1 : ℂ)
      let w := fun t : ℝ => τ + t • (P - τ)
      let ρ := fun t : ℝ => a + t • ((V : Mat n) * (P - τ) * (V : Mat n)ᴴ)
      eigen j < eigen i ∧ V = U * rotation i j hij ∧ (∀ k, Q k = measurementKraus V k) ∧
      (∑ k, (Q k)ᴴ * Q k) = 1 ∧ N.IsCompletelyPositive ∧ N.IsTracePreserving ∧
      τ.PosDef ∧ τ.trace = 1 ∧ P.PosSemidef ∧ P.trace = 1 ∧
      (∀ X, (V : Mat n) * N X * (V : Mat n)ᴴ =
        ∑ k, (V : Mat n) * projector k * (V : Mat n)ᴴ * X *
          ((V : Mat n) * projector k * (V : Mat n)ᴴ)) ∧
      (∀ Y, measurementAdjoint V Y = ∑ k, (Q k)ᴴ * Y * Q k) ∧
      (∀ Y, E Y = omega a (measurementAdjoint V (logDeriv τ Y))) ∧
      (∀ Y, E (star Y) = star (E Y)) ∧ E.IsTracePreserving ∧ E τ = a ∧
      (∀ H Y, (Hᴴ * logDeriv a (E Y)).trace = ((N H)ᴴ * logDeriv τ Y).trace) ∧
      z = (U : Mat n) *ᵥ (Pi.single (M := fun _ : n => ℂ) i (Real.sqrt (eigen j) : ℂ) -
        Pi.single (M := fun _ : n => ℂ) j (Real.sqrt (eigen i) : ℂ)) ∧
      (∀ r s, (r = i ∨ r = j) → (s = i ∨ s = j) →
        (basisChange U).symm (E P) r s = (logMean (eigen r) (eigen s) / (eigen i + eigen j) : ℝ)) ∧
      quadratic z (E P) = (2 * eigen i * eigen j - 2 * logMean (eigen i) (eigen j) *
        Real.sqrt (eigen i * eigen j)) / (eigen i + eigen j) ∧ R.readout () () (quadratic z (E P)) ∧
      (∀ᶠ t : ℝ in 𝓝 0, (w t).PosDef ∧ (w t).trace = 1 ∧
        (ρ t).PosDef ∧ (ρ t).trace = 1 ∧ N (ρ t) = w t) ∧
      gibbs a τ V τ = a ∧ HasDerivAt (fun t : ℝ => gibbs a τ V (w t)) (E P - a) 0 ∧
      ¬ ∃ R : MatrixMap n n ℂ, (∀ X, X.PosSemidef → (R X).PosSemidef) ∧ R τ = a ∧
        ∃ ε > (0 : ℝ), ∀ t : ℝ, |t| < ε → (w t).PosDef →
          (R (w t) - gibbs a τ V (w t)).PosSemidef

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 2)
  let i : n := ULift.up 0
  let j : n := ULift.up 1
  let d : n → ℝ := fun k => if k.down = 0 then 3 / 4 else 1 / 4
  let a : Mat n := Matrix.diagonal (fun k => (d k : ℂ))
  have ha : a.PosDef := Matrix.posDef_diagonal_iff.mpr (fun k => by
    have hd : 0 < d k := by dsimp [d]; split <;> norm_num
    exact_mod_cast hd)
  have ht : a.trace = 1 := by
    have hs := (Equiv.ulift : n ≃ Fin 2).symm.sum_comp (fun k : n => (d k : ℂ))
    change (∑ k : n, (d k : ℂ)) = 1
    rw [← hs, Fin.sum_univ_two]
    norm_num [d]
  have hf : ¬ ∃ c : ℝ, a = c • (1 : Mat n) := by
    rintro ⟨c, hc⟩
    have hi := congrArg (fun X : Mat n => (X i i).re) hc
    have hj := congrArg (fun X : Mat n => (X j j).re) hc
    norm_num [a, d, i, j] at hi hj
    linarith
  obtain ⟨_, _, _, _, _, _, _, law⟩ := h a ha ht hf
  rcases law with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, impossible, _⟩
  exact impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), -1, 0, ?_⟩
  change ((-1 : ℝ) < 0) ≠ ((0 : ℝ) < 0)
  simp

def family : Registration arena.{u} (type_of% (@measurement_order_obstruction.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@measurement_order_obstruction.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@measurement_order_obstruction.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction.family
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
    owner := `D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction
