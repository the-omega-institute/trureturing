/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeClassification
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeClassification
   mirror-E: none(waiver:sturmian-extension-reconstruction)
   anchors: []
   utility: none
   digest: The original occurrence-equivalence operand registers count reconstruction. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeClassification
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange KAbelianLagrangeDefs
open D5.S1.Words.Mechanical
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeClassification
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List Bool → List Bool → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => KAbelianEq) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha rho : ℝ} (_h0 : 0 ≤ alpha) (_h1 : alpha < 1)
    (_hirr : Irrational alpha) (k m i j : ℕ)
    (_hab : KAbelianEq 1 (lowerMechanicalFactor alpha rho m i)
      (lowerMechanicalFactor alpha rho m j))
    (_hpre : (lowerMechanicalFactor alpha rho m i).take (k - 1) =
      (lowerMechanicalFactor alpha rho m j).take (k - 1))
    (_hsuf : (lowerMechanicalFactor alpha rho m i).drop (m - (k - 1)) =
      (lowerMechanicalFactor alpha rho m j).drop (m - (k - 1))),
    R.readout () () k (lowerMechanicalFactor alpha rho m i)
      (lowerMechanicalFactor alpha rho m j)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hx : Irrational (Real.sqrt 2 / 2) :=
        irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      exact @h (Real.sqrt 2 / 2) 0 (by positivity) (by linarith) hx
        0 0 0 0 (fun _ _ _ => rfl) rfl rfl
    exact ⟨mechanical_kabelian_of_boundaries, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hx : Irrational (Real.sqrt 2 / 2) :=
        irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      exact @h (Real.sqrt 2 / 2) 0 (by positivity) (by linarith) hx
        0 0 0 0 (fun _ _ _ => rfl) rfl rfl
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
    have hzero : KAbelianEq 0 [false] [] := by intro z hz hl; omega
    have hone : KAbelianEq 1 [false] [] :=
      (congrFun (congrFun heq [false]) []).mp hzero
    have hh := hone [false] (by simp) (by simp)
    simp [occurrences] at hh
    exact hh 0 (by omega) rfl rfl

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeClassification
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "body",
    "fn", "fn", "fn"], functionOperand := true }] }

register_information_theorem mechanical_kabelian_of_boundaries in arena
  readout via (realize signature (fun _ _ => KAbelianEq) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeClassification
