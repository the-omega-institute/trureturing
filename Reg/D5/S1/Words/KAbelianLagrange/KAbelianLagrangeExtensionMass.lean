/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeExtensionMass
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeExtensionMass
   mirror-E: none(waiver:extension-occurrence-mass)
   anchors: []
   utility: none
   digest: The original letter-count operand registers the extension-mass identity. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeExtensionMass
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange KAbelianLagrangeDefs
open D5.S1.Words.Mechanical
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeExtensionMass
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List Bool → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => List.count) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (alpha rho : ℝ) (m start n : ℕ) (b : Bool),
    ∑ z ∈ lowerMechanicalFactorSet alpha rho n,
      occurrences (lowerMechanicalFactor alpha rho m start) (z ++ [b]) =
        R.readout () () b ((lowerMechanicalFactor alpha rho m start).drop n)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hh := h 0 0 1 0 0 false
      have hm := mechanical_extension_mass 0 0 1 0 0 false
      have hw : lowerMechanicalFactor 0 0 1 0 = [false] := by
        simp [lowerMechanicalFactor, lowerMechanicalWord, lowerMechanicalLetter]
      rw [hw] at hh hm
      have hc := hm.symm.trans hh
      simp [bad, realize] at hc
    exact ⟨mechanical_extension_mass, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hh := h 0 0 1 0 0 false
      have hm := mechanical_extension_mass 0 0 1 0 0 false
      have hw : lowerMechanicalFactor 0 0 1 0 = [false] := by
        simp [lowerMechanicalFactor, lowerMechanicalWord, lowerMechanicalLetter]
      rw [hw] at hh hm
      have hc := hm.symm.trans hh
      simp [bad, realize] at hc
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), false, true, ?_⟩
    intro heq
    have hh := congrFun heq [false]
    simp [actual, realize] at hh

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeExtensionMass
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
    "arg", "fn", "fn"], functionOperand := true }] }

register_information_theorem mechanical_extension_mass in arena
  readout via (realize signature (fun _ _ => List.count) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeExtensionMass
