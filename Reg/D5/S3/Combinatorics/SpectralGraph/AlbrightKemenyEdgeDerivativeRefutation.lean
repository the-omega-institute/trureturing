import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation

/-! Observe the endpoint rate in the full weighted row-sum identity. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped BigOperators

noncomputable section

abbrev rateSignature : Signature :=
  signature (Σ n : ℕ, Σ _ : Fin n, Fin n) (fun p => Fin p.1) (fun _ => ℝ)

def actual : Realization rateSignature :=
  realize rateSignature (fun _ p i => edgeDegrees p.2.1 p.2.2 i) (fun e => nomatch e)

def rejected : Realization rateSignature :=
  realize rateSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := rateSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (d : Fin n → ℝ) (_ : ∀ i, ∑ j, G.adjMatrix ℝ i j = d i)
    (t : ℝ) (i : Fin n),
    ∑ j, paramAdj G a b t i j = d i + t * R.readout () ⟨n, a, b⟩ i

private theorem rate_zero : edgeDegrees (0 : Fin 2) 0 0 = 2 := by
  norm_num [edgeDegrees, Pi.single_apply]

private theorem rate_one : edgeDegrees (0 : Fin 2) 0 1 = 0 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [edgeDegrees, h]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  let G := SimpleGraph.pathGraph 2
  let d (i : Fin 2) : ℝ := ∑ j, G.adjMatrix ℝ i j
  have hbad := bad G 0 0 d (fun _ => rfl) 1 0
  change ∑ j, paramAdj G 0 0 1 0 j = d 0 + 1 * 0 at hbad
  have hactual := paramAdj_degrees G 0 0 d (fun _ => rfl) 1 0
  rw [rate_zero, hbad] at hactual
  linarith

def rateSource : Registration arena (type_of% @paramAdj_degrees) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@paramAdj_degrees, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨2, 0, 0⟩, 0, 1, ?_⟩
    change edgeDegrees (0 : Fin 2) 0 0 ≠ edgeDegrees (0 : Fin 2) 0 1
    rw [rate_zero, rate_one]
    norm_num

def rateRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@paramAdj_degrees) (Realization rateSignature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation.paramAdj_degrees.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation.rateSource
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨rateSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rateSignature (fun _ p i => edgeDegrees p.2.1 p.2.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation
