import D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity

open Module LeanInformationAudit
open _root_.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity
open _root_.D5.S3.Observer.Hankel.HankelMinimalStateDimension
open _root_.D5.S3.Observer.Hankel.SequenceHankelRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := FiniteLinearRealization ℚ ℚ ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => r.stateDimension) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ N : ℕ,
    ∃ f g : FiniteLinearRealization ℚ ℚ ℚ,
      FiniteDimensional ℚ (tailSpace f.behavior) ∧
      FiniteDimensional ℚ (tailSpace g.behavior) ∧
      (∀ w : List Unit, w.length ≤ N → f.behavior w.length = g.behavior w.length) ∧
      f.behavior 0 1 = 1 ∧ g.behavior 0 1 = 1 ∧
      dataHankel f.behavior 1 1 ≠ 0 ∧ dataHankel g.behavior 1 1 ≠ 0 ∧
      R.readout () () f = 1 ∧ g.stateDimension = N + 3 ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = f.behavior → f.stateDimension ≤ r.stateDimension) ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = g.behavior → g.stateDimension ≤ r.stateDimension)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, g, hf, hg, hw, hf0, hg0, hbf, hbg, hdim, hrest⟩ := h 0
  change (0 : ℕ) = 1 at hdim
  cases hdim

def registration : Registration arena (∀ N : ℕ,
    ∃ f g : FiniteLinearRealization ℚ ℚ ℚ,
      FiniteDimensional ℚ (tailSpace f.behavior) ∧
      FiniteDimensional ℚ (tailSpace g.behavior) ∧
      (∀ w : List Unit, w.length ≤ N → f.behavior w.length = g.behavior w.length) ∧
      f.behavior 0 1 = 1 ∧ g.behavior 0 1 = 1 ∧
      dataHankel f.behavior 1 1 ≠ 0 ∧ dataHankel g.behavior 1 1 ≠ 0 ∧
      f.stateDimension = 1 ∧ g.stateDimension = N + 3 ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = f.behavior → f.stateDimension ≤ r.stateDimension) ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = g.behavior → g.stateDimension ≤ r.stateDimension)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_sample_rank_ambiguity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    obtain ⟨f, g, hf, hg, hw, hf0, hg0, hbf, hbg, hfd, hgd, hmin⟩ :=
      finite_sample_rank_ambiguity 0
    refine ⟨(), f, g, ?_⟩
    change f.stateDimension ≠ g.stateDimension
    omega

register_information_theorem finite_sample_rank_ambiguity in arena
  readout via (realize signature (fun _ _ r => r.stateDimension) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity
