import D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open _root_.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
universe u v w

abbrev signature : Signature where
  Params := ℕ
  State d := EuclideanSpace ℝ (Fin d)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original law, varying only the final distance measurement. -/
def arena : Arena where
  signature := signature
  Law obs := ∀
    {S : Type u} {A : Type v} {Y : Type w} [Finite S] [Nonempty S] {d : ℕ}
    (δ : A → S → S) (y : S → Y) (c : S → EuclideanSpace ℝ (Fin d))
    (Δ ν r R : ℝ)
    (_hsep : ∀ i j, i ≠ j → Δ ≤ ‖c i - c j‖)
    (_hν : 0 ≤ ν) (_hνr : ν < r) (_hrR : r < R) (_hRΔ : R < Δ / 2),
    ∃ (T : A → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (decode : EuclideanSpace ℝ (Fin d) → S)
      (readout : EuclideanSpace ℝ (Fin d) → Y),
      (∀ a, ContDiff ℝ 1 (T a)) ∧
      (∀ a i h, ‖h - c i‖ ≤ r → T a h = c (δ a i)) ∧
      (∀ i h, ‖h - c i‖ ≤ r → decode h = i ∧ readout h = y i) ∧
      ∀ (w : List (A × EuclideanSpace ℝ (Fin d))),
        (∀ step ∈ w, ‖step.2‖ ≤ ν) →
        ∀ i h, ‖h - c i‖ ≤ r → ∀ n : ℕ,
          let pre := w.take n
          let s := symbolicRun δ i (pre.map Prod.fst)
          let x := noisyRun T h pre
          obs.readout () d (x - c s) ≤ r ∧ decode x = s ∧ readout x = y s

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  obtain ⟨T, dec, out, hsmooth, hplateau, hdecode, hrun⟩ :=
    h (S := ULift.{u} Bool) (A := ULift.{v} Unit) (Y := ULift.{w} Unit)
      (d := 1) (fun _ s => s) (fun _ => ⟨()⟩)
      (fun s => if s.down then EuclideanSpace.single 0 4 else 0)
      4 0 (1/2) 1 (by
        rintro ⟨i⟩ ⟨j⟩ hij
        cases i <;> cases j <;> simp_all)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have bad := (hrun [] (by simp) ⟨false⟩ 0 (by simp) 0).1
  change (1 : ℝ) ≤ 1/2 at bad
  norm_num at bad

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, 0, EuclideanSpace.single 0 (1 : ℝ), ?_⟩
  change ‖(0 : EuclideanSpace ℝ (Fin 1))‖ ≠ ‖EuclideanSpace.single 0 (1 : ℝ)‖
  simp

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@smooth_finite_machine_realization.{u,v,w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization.smooth_finite_machine_realization
  in arena
  readout via (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Observer.SymbolicStability.SmoothFiniteMachineRealization
