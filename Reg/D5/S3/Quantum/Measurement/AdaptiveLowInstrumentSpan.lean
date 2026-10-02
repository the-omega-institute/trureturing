import D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
structure Model.{u,v} where
  a : Type u
  h : Type v
  finiteA : Fintype a
  decidableA : DecidableEq a
  nonemptyA : Nonempty a
  finiteH : Fintype h
  decidableH : DecidableEq h
  nonemptyH : Nonempty h
  clock : @CStarMatrix (a × h) (a × h) ℂ

@[reducible] def signature.{u,v} : Signature where
  Params := Model.{u,v}
  State p := @Event p.a p.finiteA p.decidableA
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := CStarMatrix (p.a × p.h) (p.a × p.h) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation.{u,v} (p : Model.{u,v})
    (e : @Event p.a p.finiteA p.decidableA) : CStarMatrix (p.a × p.h) (p.a × p.h) ℂ := by
  letI := p.finiteA
  letI := p.decidableA
  letI := p.finiteH
  letI := p.decidableH
  exact effect (tensorLow p.h) p.clock e

def actual.{u,v} : Realization signature.{u,v} :=
  realize signature (fun _ p e => observation p e) (fun e => nomatch e)

def rejected.{u,v} : Realization signature.{u,v} :=
  realize signature (fun _ p e => by
    letI := p.finiteA
    letI := p.decidableA
    letI := p.finiteH
    letI := p.decidableH
    exact observation p e + 1)
    (fun e => nomatch e)

def arena.{u,v} : Arena.{max (u+1) (v+1),u,0,max u v,0} where
  signature := signature.{u,v}
  Law R := ∀ {a : Type u} [Fintype a] [DecidableEq a]
    {h : Type v} [Fintype h] [DecidableEq h] [Nonempty a] [Nonempty h]
    (W : CStarMatrix (a × h) (a × h) ℂ)
    (_hW : star W * W = 1 ∧ W * star W = 1),
    let p : Model := ⟨a, h, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, W⟩
    (∀ e rho, Matrix.trace (eventState (tensorLow h) W e rho) =
      Matrix.trace (R.readout () p e * rho)) ∧
    (∀ e, 0 ≤ effect (tensorLow h) W e ∧ effect (tensorLow h) W e ≤ 1) ∧
    ∃ D : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ),
      D.toSubalgebra.toSubmodule = effectSpan (tensorLow h) W ∧
      (∀ K, tensorLow h K ∈ D) ∧
      (∀ X, X ∈ D ↔ star W * X * W ∈ D) ∧
      (∀ R : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ),
        (∀ K, tensorLow h K ∈ R) →
        (∀ X ∈ R, star W * X * W ∈ R) → D ≤ R)

theorem actual_law.{u,v} : arena.{u,v}.Law actual.{u,v} := by
  intro a _ _ h _ _ _ _ W hW
  exact actual_adaptive_span W hW

def singletonModel.{u,v} : Model.{u,v} :=
  { a := ULift.{u} (Fin 1)
    h := ULift.{v} (Fin 1)
    finiteA := inferInstance
    decidableA := inferInstance
    nonemptyA := inferInstance
    finiteH := inferInstance
    decidableH := inferInstance
    nonemptyH := inferInstance
    clock := 1 }

theorem rejected_law.{u,v} : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro hbad
  let W : CStarMatrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
    (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ := 1
  have hw : star W * W = 1 ∧ W * star W = 1 := by simp [W]
  have hz := (hbad (a := ULift.{u} (Fin 1)) (h := ULift.{v} (Fin 1)) W hw).1
    (.stop false) 1
  change Matrix.trace (0 : CStarMatrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
    (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) =
    Matrix.trace ((0 + 1) * 1 : CStarMatrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
      (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) at hz
  rw [zero_add, one_mul] at hz
  change Matrix.trace (0 : Matrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
    (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) =
    Matrix.trace (1 : Matrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
      (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) at hz
  have hz0 : (0 : ℂ) = 1 := by
    simpa [Matrix.trace_one, Fintype.card_prod] using hz
  exact zero_ne_one hz0

theorem sensitivity.{u,v} : Sensitivity arena.{u,v} actual.{u,v} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro k hki
    cases i
    cases k
    exact (hki rfl).elim
  · intro i
    exact nomatch i

theorem dependence.{u,v} : ObservationalDependence signature.{u,v} actual.{u,v} := by
  letI := singletonModel.finiteA
  letI := singletonModel.decidableA
  letI := singletonModel.finiteH
  letI := singletonModel.decidableH
  intro i
  cases i
  refine ⟨singletonModel, .stop true, .stop false, ?_⟩
  change (1 : CStarMatrix (singletonModel.a × singletonModel.h)
    (singletonModel.a × singletonModel.h) ℂ) ≠ 0
  intro heq
  have he := congrFun (congrFun heq (⟨0⟩, ⟨0⟩)) (⟨0⟩, ⟨0⟩)
  norm_num [singletonModel, CStarMatrix] at he

def registration.{u,v} : Registration arena.{u,v} (arena.{u,v}.Law actual.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem actual_adaptive_span in arena
  readout via (realize signature
    (fun _ p e => observation p e) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
    coordinates := #[0, 3, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity
#print axioms dependence

end Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
