/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeBoundary
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeBoundary
   mirror-E: none(waiver:occurrence-boundary-recovery)
   anchors: []
   utility: none
   digest: The prefix readout registers occurrence-based boundary recovery. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeBoundary
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange
open KAbelianLagrangeDefs
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeBoundary
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List Bool → List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => List.take) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ w => w) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ} {u v : List Bool} (_hnk : n < k) (_hnu : n ≤ u.length)
    (_huv : KAbelianEq k u v),
    R.readout () () n u = v.take n ∧ u.drop (u.length - n) = v.drop (v.length - n)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have heq : KAbelianEq 1 [true] [true] := fun _ _ _ => rfl
      have hh := (@h 1 0 [true] [true] (by omega) (by simp) heq).1
      simp [bad, realize] at hh
    exact ⟨kabelian_boundary_recovery, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have heq : KAbelianEq 1 [true] [true] := fun _ _ _ => rfl
      have hh := (@h 1 0 [true] [true] (by omega) (by simp) heq).1
      simp [bad, realize] at hh
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have hh := congrFun heq [true]
    simp [actual, realize] at hh

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeBoundary
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
    "fn", "arg", "fn", "arg", "fn", "fn"], functionOperand := true }] }

register_information_theorem kabelian_boundary_recovery in arena
  readout via (realize signature (fun _ _ => List.take) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeBoundary
