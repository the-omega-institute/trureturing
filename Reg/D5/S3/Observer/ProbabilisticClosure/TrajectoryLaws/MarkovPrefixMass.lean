import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal
noncomputable section
universe u

/-- The actual observation is the complete finite prefix of the infinite path. -/
abbrev signature : Signature where
  Params := (_ : Type u) × ℕ
  State p := ℕ → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2 + 1) → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [MeasurableSpace α]
    (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ] [IsProbabilityMeasure ν]
    [MeasurableSingletonClass α] (n : ℕ) (w : Fin (n + 1) → α),
    ((Kernel.trajMeasure (X := fun _ => α) ν
        (fun n => κ.comap (fun u : Iic n → α => u ⟨n, mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply _))).map (R.readout () ⟨α, n⟩)) {w}
      = ν {w 0} * ∏ i : Fin n, κ (w i.castSucc) {w i.succ}

def actual : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (p : (_ : Type u) × ℕ) (x : ℕ → p.1)
    (i : Fin (p.2 + 1)) => x i.1) (fun e => nomatch e)

/-- Repeating the initial state loses the transition recorded by a two-state prefix. -/
def rejected : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (p : (_ : Type u) × ℕ) (x : ℕ → p.1)
    (_ : Fin (p.2 + 1)) => x 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  let w : Fin 2 → ULift.{u} Bool := ![a, b]
  have hab : a ≠ b := by decide
  have hfibre : (fun (x : ℕ → ULift.{u} Bool) (_ : Fin 2) => x 0) ⁻¹' {w} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    exact hab (h0.symm.trans h1)
  have hh := h (Measure.dirac a) (Kernel.const _ (Measure.dirac b)) 1 w
  dsimp only [rejected, realize] at hh
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w), hfibre] at hh
  simpa [w, a, b, Kernel.const_apply] using hh

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro α m ν κ hκ hν hs n w
    exact markov_chain_law_map_prefix_apply_singleton ν κ n w,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 0⟩, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
    intro h
    have hh := congrArg (fun f => (f 0).down) h
    cases hh

register_information_theorem markov_chain_law_map_prefix_apply_singleton in arena
  readout via (realize signature.{u}
    (fun (_ : Unit) (p : (_ : Type u) × ℕ) (x : ℕ → p.1)
      (i : Fin (p.2 + 1)) => x i.1) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
    coordinates := #[0, 7]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg", "fn",
        "arg", "body"], stateBinder := 9 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
