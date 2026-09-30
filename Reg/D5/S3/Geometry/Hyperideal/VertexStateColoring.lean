import D5.S3.Geometry.Hyperideal.VertexStateColoring
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Geometry.Hyperideal.VertexStateColoring

open _root_.D5.S3.Geometry.Hyperideal.VertexStateColoring
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

inductive ReadoutRole where
  | balance
  | partition
  | angle
  deriving DecidableEq

instance : Fintype ReadoutRole :=
  ⟨{.balance, .partition, .angle}, by intro r; cases r <;> simp⟩

instance : Nonempty ReadoutRole := ⟨.balance⟩

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 4 → Bool
  Role := ReadoutRole
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output r _ := match r with
    | .balance => Bool
    | .partition => Fin 3 → Bool
    | .angle => Fin 4 → Fin 4 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun r _ b => match r with
      | .balance => balanced b
      | .partition => corresponds b
      | .angle => flatAngle b)
    (fun e => nomatch e)

def rejectedAt (target : ReadoutRole) : Realization signature :=
  realize signature
    (fun r _ b => match r with
      | .balance => if target = .balance then false else balanced b
      | .partition => if target = .partition then (fun _ => false) else corresponds b
      | .angle => if target = .angle then (fun _ _ => 0) else flatAngle b)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ k : Fin 3,
      R.readout .balance () (stateColor k) = true ∧
      R.readout .partition () (stateColor k) k = true) ∧
    (∀ b : Fin 4 → Bool, R.readout .balance () b = true →
      ((List.finRange 3).filter
        (fun k => R.readout .partition () b k)).length = 1) ∧
    (∀ (b : Fin 4 → Bool) (i j : Fin 4),
      R.readout .angle () b i j =
        Real.pi * (1 - ((crossing b i j).toNat : ℝ)))

theorem actual_law : arena.Law actual := by
  exact balanced_coloring_flat_angle_correspondence

theorem rejected_law (target : ReadoutRole) : ¬ arena.Law (rejectedAt target) := by
  intro h
  cases target with
  | balance =>
      have hh := (h.1 0).1
      change false = true at hh
      cases hh
  | partition =>
      have hh := (h.1 0).2
      change false = true at hh
      cases hh
  | angle =>
      have hh := h.2.2 (stateColor 0) 0 1
      norm_num [rejectedAt, realize, crossing, stateColor] at hh
      exact Real.pi_ne_zero hh.symm

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => false), stateColor 0, ?_⟩
  cases i with
  | balance =>
      intro h
      change balanced (fun _ : Fin 4 => false) = balanced (stateColor 0) at h
      have hfalse : balanced (fun _ : Fin 4 => false) = false := by decide
      have htrue : balanced (stateColor 0) = true := by decide
      rw [hfalse, htrue] at h
      cases h
  | partition =>
      intro h
      have hh := congrArg (fun f : Fin 3 → Bool => f 0) h
      change corresponds (fun _ : Fin 4 => false) 0 = corresponds (stateColor 0) 0 at hh
      have hfalse : corresponds (fun _ : Fin 4 => false) 0 = false := by decide
      have htrue : corresponds (stateColor 0) 0 = true := by decide
      rw [hfalse, htrue] at hh
      cases hh
  | angle =>
      intro h
      have hh := congrArg (fun f : Fin 4 → Fin 4 → ℝ => f 0 2) h
      change Real.pi = 0 at hh
      exact Real.pi_ne_zero hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedAt .balance, rejected_law .balance⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, rfl, rejected_law i⟩
      intro j h
      cases i <;> cases j <;> simp_all [actual, rejectedAt, realize]
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem balanced_coloring_flat_angle_correspondence in arena
  readout via (realize signature
    (fun r _ b => match r with
      | .balance => balanced b
      | .partition => corresponds b
      | .angle => flatAngle b)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.VertexStateColoring
    coordinates := #[]
    readouts := #[
      { path := #["fn", "arg", "body", "fn", "arg", "fn", "arg", "fn"],
        functionOperand := true },
      { path := #["fn", "arg", "body", "arg", "fn", "arg", "fn", "fn"],
        functionOperand := true },
      { path := #["arg", "arg", "body", "body", "body", "fn", "arg", "fn", "fn", "fn"],
        functionOperand := true }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let sourceName : Lean.Name :=
    `D5.S3.Geometry.Hyperideal.VertexStateColoring.balanced_coloring_flat_angle_correspondence
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == sourceName &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Vertex-state registration evidence is missing"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.bridgeKind == "source-equivalence" &&
          certificate.sourceBinding.isSome do
        throwError "Vertex-state registration lacks source-bound evidence"
  | .declaredUnresolved diagnostic =>
      throwError "Vertex-state registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "Vertex-state registration is undeclared"

#print axioms registration

end

end Reg.D5.S3.Geometry.Hyperideal.VertexStateColoring
