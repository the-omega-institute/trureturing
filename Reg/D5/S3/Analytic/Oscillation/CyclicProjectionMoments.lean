import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Analytic.Oscillation.CyclicProjectionMoments

namespace Reg.D5.S3.Analytic.Oscillation.CyclicProjectionMoments

open Finset Matrix ZMod
open _root_.D5.S3.Analytic.Oscillation.CyclicProjectionMoments
open _root_.D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.HMV
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support

noncomputable section

abbrev Params := Σ m : ℕ, Σ k : ℕ, Fin k ↪ ZMod m
abbrev signature := SingleDependentReadout.signature Params (fun p => ZMod p.1) (fun _ => ℂ)

def overlap : (p : Params) → ZMod p.1 → ℂ
  | ⟨_, _, a⟩, r => (((univ.map a).filter (fun b => b - r ∈ univ.map a)).card : ℂ)

def actual : Realization signature :=
  realize signature (fun _ p r => overlap p r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p r => overlap p r + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law v := ∀ {m : ℕ} [NeZero m] {k : ℕ} (a : Fin k ↪ ZMod m) (s : ℂ)
    (_hs : star s * s = (m : ℂ)⁻¹) (r : ZMod m),
    let U := selectedColumns a s
    (∑ S : {S : Finset (Fin m) // S.card = k},
      (prob U S : ℂ) * (Complex.normSq (∑ x ∈ S.1, stdAddChar (r * finEquiv m x)) : ℂ)) =
      (k : ℂ) + (if r = 0 then (k : ℂ)^2 else 0) - v.readout () ⟨m,k,a⟩ r

private def columns : Fin 2 ↪ ZMod 4 :=
  ⟨fun i => (i.val : ZMod 4), by decide⟩

private lemma half_normalization :
    star (1/2 : ℂ) * (1/2 : ℂ) = (4 : ℂ)⁻¹ := by
  norm_num [Complex.star_def]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law columns (1/2 : ℂ) half_normalization (1 : ZMod 4)
  have h0 := cyclic_projection_second_moment columns (1/2 : ℂ) half_normalization (1 : ZMod 4)
  dsimp only [rejected, realize, overlap] at h
  dsimp only at h0
  rw [h0] at h
  have hz : (1 : ℂ) = 0 := by linear_combination h
  exact one_ne_zero hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨4, 2, columns⟩, (0 : ZMod 4), (1 : ZMod 4), ?_⟩
  dsimp only [actual, realize, overlap]
  have hcard :
      ((univ.map columns).filter (fun b => b - 0 ∈ univ.map columns)).card ≠
      ((univ.map columns).filter (fun b => b - 1 ∈ univ.map columns)).card := by decide
  intro eq
  apply hcard
  exact_mod_cast eq

def evidence : Registration arena (type_of% @cyclic_projection_second_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_projection_second_moment, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def overlapRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cyclic_projection_second_moment) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.CyclicProjectionMoments.overlapUnit
  realizationName := `Reg.D5.S3.Analytic.Oscillation.CyclicProjectionMoments.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p r => overlap p r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.CyclicProjectionMoments
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms overlapRegistration

end
end Reg.D5.S3.Analytic.Oscillation.CyclicProjectionMoments
