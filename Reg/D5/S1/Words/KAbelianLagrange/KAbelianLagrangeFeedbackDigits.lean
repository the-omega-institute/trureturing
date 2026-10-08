/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeFeedbackDigits
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeFeedbackDigits
   mirror-E: none(waiver:prefix-dependent-feedback)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The original target readout registers the prefix-dependent digit construction. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeFeedbackDigits
import Reg.Support.DependentFamily
import Mathlib.Tactic

open D5.S1.Words.KAbelianLagrange
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeFeedbackDigits
noncomputable section

abbrev signature : Signature where
  Params := List ℕ → ℝ
  State := fun _ => List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ T p => T p) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (seed : List ℕ) (A B : ℕ)
    (_hseed : ∀ a ∈ seed, 0 < a ∧ a ≤ A) (T : List ℕ → ℝ)
    (_hT : ∀ p, 6 < T p ∧ T p ≤ (B : ℝ)),
    ∃ P : ℕ → List ℕ, ∃ d c : ℕ → ℕ, ∃ x y : ℕ → ℝ,
      ∃ u v : ℕ → ℕ → ℕ,
      P 0 = seed ∧
      (∀ j, P j = List.ofFn (fun i : Fin (P j).length => d i)) ∧
      StrictMono c ∧
      (∀ i, 0 < d i ∧ d i ≤ max A (max 4 B)) ∧
      (∀ i, seed.length ≤ i → (∀ j, i ≠ c j) → d i ≤ 4) ∧
      ∀ j, x j ∈ hallCantor ∧ y j ∈ hallCantor ∧
        R.readout () T (P j) = (d (c j) : ℝ) + x j + y j ∧
        5 ≤ d (c j) ∧ d (c j) ≤ B ∧ c j = (P j).length + (j + 1) ∧
        (∀ i, (0 < u j i ∧ u j i ≤ 4 ∧
          (GenContFract.of (x j)).s.get? i = some ⟨1, (u j i : ℝ)⟩) ∧
          (0 < v j i ∧ v j i ≤ 4 ∧
          (GenContFract.of (y j)).s.get? i = some ⟨1, (v j i : ℝ)⟩)) ∧
        P (j + 1) = P j ++ (List.ofFn (fun i : Fin (j + 1) => u j i)).reverse ++
          [d (c j)] ++ List.ofFn (fun i : Fin (j + 1) => v j i)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      obtain ⟨P, d, c, x, y, u, v, _, _, _, _, _, hstage⟩ :=
        h [] 0 7 (by simp) (fun _ => 7) (by intro p; norm_num)
      have hh := hstage 0
      have hd : (5 : ℝ) ≤ d (c 0) := by exact_mod_cast hh.2.2.2.1
      have he : (0 : ℝ) = (d (c 0) : ℝ) + x 0 + y 0 := hh.2.2.1
      linarith [hh.1.2.1, hh.2.1.2.1]
    exact ⟨feedback_digit_construction, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      obtain ⟨P, d, c, x, y, u, v, _, _, _, _, _, hstage⟩ :=
        h [] 0 7 (by simp) (fun _ => 7) (by intro p; norm_num)
      have hh := hstage 0
      have hd : (5 : ℝ) ≤ d (c 0) := by exact_mod_cast hh.2.2.2.1
      have he : (0 : ℝ) = (d (c 0) : ℝ) + x 0 + y 0 := hh.2.2.1
      linarith [hh.1.2.1, hh.2.1.2.1]
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(fun p => (p.length : ℝ)), [], [0], ?_⟩
    norm_num [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeFeedbackDigits
  coordinates := #[4]
  readouts := #[{ path := #[
    "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg",
    "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg",
    "arg", "arg", "body", "arg", "arg", "fn", "arg", "fn",
    "arg", "fn"], functionOperand := true }] }

register_information_theorem feedback_digit_construction in arena
  readout via (realize signature (fun _ T p => T p) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeFeedbackDigits
