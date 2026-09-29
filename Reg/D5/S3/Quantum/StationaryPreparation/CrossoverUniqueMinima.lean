import D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum.RealSqrt

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ (z : ℝ) => 1 + (z^2 - Real.sqrt (z^4 + 4))/2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def arena : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena where
  signature := signature
  Law r := ∀ (c h γ : ℝ) (_hc : 12/5 < c) (_hh0 : 0 < h)
    (_hh : h < 31/20) (_hγ : 0 < γ),
    let g : ℝ → ℝ := fun z => r.readout () () z
    let F := fun j : ℕ => fun z : ℝ => (c+(h-z)^2)/(1-γ*g z)^j
    let S := {z : ℝ | 0 ≤ z ∧ z ≤ h ∧ 0 < 1-γ*g z}
    ∃ z2 z1 : ℝ, 0 < z2 ∧ z2 < z1 ∧ z1 < h ∧ z2 ∈ S ∧ z1 ∈ S ∧
      (∀ z ∈ S, z ≠ z2 → F 2 z2 < F 2 z) ∧
      (∀ z ∈ S, z ≠ z1 → F 1 z1 < F 1 z)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a2, a1, _, horder, _, hm2, hm1, hmin2, hmin1⟩ :=
    h 3 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hleft := hmin2 a1 hm1 (ne_of_gt horder)
  have hright := hmin1 a2 hm2 (ne_of_lt horder)
  change (3+(1-a2)^2)/(1-1*0)^2 < (3+(1-a1)^2)/(1-1*0)^2 at hleft
  change (3+(1-a1)^2)/(1-1*0)^1 < (3+(1-a2)^2)/(1-1*0)^1 at hright
  norm_num at hleft hright
  linarith

def registration : Registration arena (∀ (c h γ : ℝ) (_hc : 12/5 < c)
    (_hh0 : 0 < h) (_hh : h < 31/20) (_hγ : 0 < γ),
    let g := fun z : ℝ => 1+(z^2-Real.sqrt (z^4+4))/2
    let F := fun j : ℕ => fun z : ℝ => (c+(h-z)^2)/(1-γ*g z)^j
    let S := {z : ℝ | 0 ≤ z ∧ z ≤ h ∧ 0 < 1-γ*g z}
    ∃ z2 z1 : ℝ, 0 < z2 ∧ z2 < z1 ∧ z1 < h ∧ z2 ∈ S ∧ z1 ∈ S ∧
      (∀ z ∈ S, z ≠ z2 → F 2 z2 < F 2 z) ∧
      (∀ z ∈ S, z ≠ z1 → F 1 z1 < F 1 z)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result,
    rejected, rejected_law⟩
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
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change (1 : ℝ)+(0^2-Real.sqrt (0^4+4))/2 ≠ 1+(1^2-Real.sqrt (1^4+4))/2
    norm_num
    have hs := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
    intro he
    have heR : (1 : ℝ) + -1 = 1+(1-Real.sqrt 5)/2 := he
    have heq : Real.sqrt 5 = (3 : ℝ) := by linarith only [heR]
    rw [heq] at hs
    norm_num at hs

register_information_theorem _root_.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result
  in arena
  readout via (realize signature
    (fun _ _ (z : ℝ) => 1 + (z^2 - Real.sqrt (z^4 + 4))/2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value", "body"]
      stateBinder := 7 }] })
  escape continues (open)

end

end Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima
