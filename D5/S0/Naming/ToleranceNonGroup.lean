/- GID: D5/S0/Naming/ToleranceNonGroup
   generality: G
   mirror-B: D5/B/S0/Naming/ToleranceNonGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-base semantic tolerance for a partial monoid action always contains the identity when epsilon is nonnegative, but need not be closed under composition: two adjacent swaps of ABC are each zero-tolerant while their composite reaches CAB at positive semantic distance. In general, the triangle inequality leaves the second transformation's displacement at the moved sentence uncontrolled by its separate tolerance ticket at the original sentence. -/

/- Library-search audit trail (2026-08-12):
   * Repository queries for `toleranceSet`, `PartialAction`, fixed-base tolerance, composition
     triangles, and non-closure under composition found no matching declaration. The nearby
     `TranslationComposition.translation_composition` assumes semantically composable
     translations and proves an additive bound, so it is strictly stronger and not this claim.
   * Pinned-mathlib queries for `PartialAction`, tolerance sets, and non-closure under
     composition found no matching abstraction or theorem. The proof reuses `dist_triangle`.
   * Online capability was exercised after the local searches. Loogle query
     `"PartialAction"` returned zero declarations. Unauthenticated GitHub code search was
     unavailable (HTTP 401 and sign-in required), LeanSearch GET probes returned HTTP 405/404,
     and grep.app returned HTTP 429. No third-party Lean theorem was available to reuse through
     the working search endpoint.
-/

import Mathlib

namespace D5.S0.Naming.ToleranceNonGroup

universe u v w

/-- A monoid action whose value may be undefined at an individual sentence. -/
structure PartialAction (P : Type u) (S : Type v) [Monoid P] where
  act : P → S → Option S
  one_act : ∀ s, act 1 s = some s
  mul_act : ∀ p₂ p₁ s, act (p₂ * p₁) s = (act p₁ s).bind (act p₂)

/-- Transformations defined at `s` whose semantic displacement is at most `ε`. -/
def toleranceSet {P : Type u} {S : Type v} [Monoid P]
    {M : Type w} [PseudoMetricSpace M]
    (action : PartialAction P S) (meaning : S → M) (ε : ℝ) (s : S) : Set P :=
  {p | ∃ moved, action.act p s = some moved ∧ dist (meaning moved) (meaning s) ≤ ε}

/-- The identity is defined everywhere and lies in every nonnegative tolerance set. -/
theorem one_mem_toleranceSet {P : Type u} {S : Type v} [Monoid P]
    {M : Type w} [PseudoMetricSpace M]
    (action : PartialAction P S) (meaning : S → M) {ε : ℝ} (s : S)
    (hε : 0 ≤ ε) :
    1 ∈ toleranceSet action meaning ε s := by
  exact ⟨s, action.one_act s, by simpa using hε⟩

/-- Composition gets a triangle bound involving the second transformation at the moved sentence.
Its membership at the base sentence controls a separate displacement. -/
theorem tolerance_composition_triangle {P : Type u} {S : Type v} [Monoid P]
    {M : Type w} [PseudoMetricSpace M]
    (action : PartialAction P S) (meaning : S → M) {ε : ℝ} {s : S}
    {p₁ p₂ : P} (hp₁ : p₁ ∈ toleranceSet action meaning ε s)
    (hp₂ : p₂ ∈ toleranceSet action meaning ε s)
    {s₁ s₂ : S} (h₁ : action.act p₁ s = some s₁)
    (h₂ : action.act p₂ s₁ = some s₂) :
    action.act (p₂ * p₁) s = some s₂ ∧
      dist (meaning s₂) (meaning s) ≤ dist (meaning s₂) (meaning s₁) + ε ∧
      ∃ baseMoved,
        action.act p₂ s = some baseMoved ∧
          dist (meaning baseMoved) (meaning s) ≤ ε := by
  rcases hp₁ with ⟨s₁', h₁', hp₁dist⟩
  have hs₁ : s₁' = s₁ := Option.some.inj (h₁'.symm.trans h₁)
  subst s₁'
  constructor
  · rw [action.mul_act, h₁]
    exact h₂
  constructor
  · exact (dist_triangle (meaning s₂) (meaning s₁) (meaning s)).trans
      (add_le_add_right hp₁dist _)
  · exact hp₂

/-- Reordering positions by a permutation is a total special case of a partial action. -/
def permutationAction (A : Type*) : PartialAction (Equiv.Perm A) (A → A) where
  act p s := some (s ∘ p.symm)
  one_act _ := rfl
  mul_act _ _ _ := rfl

abbrev Sentence := Fin 3 → Fin 3

def abc : Sentence := ![0, 1, 2]
def acb : Sentence := ![0, 2, 1]
def bac : Sentence := ![1, 0, 2]
def cab : Sentence := ![2, 0, 1]

def swapLast : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def swapFirst : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def sentenceMeaning (sentence : Sentence) : ℝ := if sentence = cab then 1 else 0

/-- Data witnessing non-closure at one base sentence, including the moved-sentence gap. -/
def IsCompositionCounterexample {P : Type u} {S : Type v} [Monoid P]
    {M : Type w} [PseudoMetricSpace M]
    (action : PartialAction P S) (meaning : S → M) (ε : ℝ) (s : S)
    (p₁ p₂ : P) : Prop :=
  p₁ ≠ 1 ∧
    p₁ ∈ toleranceSet action meaning ε s ∧
    p₂ ∈ toleranceSet action meaning ε s ∧
    p₂ * p₁ ∉ toleranceSet action meaning ε s ∧
    ∃ s₁ s₂,
      action.act p₁ s = some s₁ ∧
      action.act p₂ s₁ = some s₂ ∧
      dist (meaning s₂) (meaning s₁) > ε

/-- ABC, ACB, and BAC have semantic value zero while CAB has value one. The two adjacent swaps
are each zero-tolerant at ABC, but their composite is not. -/
theorem tolerance_not_closed_counterexample :
    let action := permutationAction (Fin 3)
    action.act swapLast abc = some acb ∧
      action.act swapFirst abc = some bac ∧
      action.act swapFirst acb = some cab ∧
      sentenceMeaning abc = 0 ∧
      sentenceMeaning acb = 0 ∧
      sentenceMeaning bac = 0 ∧
      sentenceMeaning cab = 1 ∧
      swapLast ≠ 1 ∧
      swapLast ∈ toleranceSet action sentenceMeaning 0 abc ∧
      swapFirst ∈ toleranceSet action sentenceMeaning 0 abc ∧
      swapFirst * swapLast ∉ toleranceSet action sentenceMeaning 0 abc ∧
      dist (sentenceMeaning cab) (sentenceMeaning acb) > 0 := by
  dsimp only
  have hlast : (permutationAction (Fin 3)).act swapLast abc = some acb := by
    apply congrArg some
    funext i
    fin_cases i <;> rfl
  have hfirstBase : (permutationAction (Fin 3)).act swapFirst abc = some bac := by
    apply congrArg some
    funext i
    fin_cases i <;> rfl
  have hfirstMoved : (permutationAction (Fin 3)).act swapFirst acb = some cab := by
    apply congrArg some
    funext i
    fin_cases i <;> rfl
  have habc : sentenceMeaning abc = 0 := by
    rw [sentenceMeaning, if_neg (by decide : abc ≠ cab)]
  have hacb : sentenceMeaning acb = 0 := by
    rw [sentenceMeaning, if_neg (by decide : acb ≠ cab)]
  have hbac : sentenceMeaning bac = 0 := by
    rw [sentenceMeaning, if_neg (by decide : bac ≠ cab)]
  have hcab : sentenceMeaning cab = 1 := by simp [sentenceMeaning]
  have hnontrivial : swapLast ≠ 1 := by decide
  have hlastTol :
      swapLast ∈ toleranceSet (permutationAction (Fin 3)) sentenceMeaning 0 abc := by
    exact ⟨acb, hlast, by rw [hacb, habc]; norm_num⟩
  have hfirstTol :
      swapFirst ∈ toleranceSet (permutationAction (Fin 3)) sentenceMeaning 0 abc := by
    exact ⟨bac, hfirstBase, by rw [hbac, habc]; norm_num⟩
  have hcompNotTol :
      swapFirst * swapLast ∉
        toleranceSet (permutationAction (Fin 3)) sentenceMeaning 0 abc := by
    rintro ⟨moved, hmoved, hdist⟩
    have hmovedCab : moved = cab := by
      have hcomp :
          (permutationAction (Fin 3)).act (swapFirst * swapLast) abc = some cab := by
        rw [(permutationAction (Fin 3)).mul_act, hlast]
        exact hfirstMoved
      exact Option.some.inj (hmoved.symm.trans hcomp)
    subst moved
    rw [hcab, habc] at hdist
    norm_num at hdist
  have hmovedGap : dist (sentenceMeaning cab) (sentenceMeaning acb) > 0 := by
    rw [hcab, hacb]
    norm_num
  exact ⟨hlast, hfirstBase, hfirstMoved, habc, hacb, hbac, hcab, hnontrivial,
    hlastTol, hfirstTol, hcompNotTol, hmovedGap⟩

/-- Fixed-base semantic tolerance contains the identity but need not be closed under composition.
For two tolerated transformations, the triangle inequality leaves the second transformation's
displacement at the moved sentence as an uncontrolled term; its tolerance ticket at the original
sentence controls only a separate base-point displacement. -/
theorem tolerance_non_group {P : Type u} {S : Type v} [Monoid P]
    {M : Type w} [PseudoMetricSpace M]
    (action : PartialAction P S) (meaning : S → M) {ε : ℝ} (s : S)
    (hε : 0 ≤ ε) :
    1 ∈ toleranceSet action meaning ε s ∧
      (∃ p₁ p₂ : Equiv.Perm (Fin 3),
        IsCompositionCounterexample
          (permutationAction (Fin 3)) sentenceMeaning 0 abc p₁ p₂) ∧
      ∀ {p₁ p₂ : P} {s₁ s₂ : S},
        p₁ ∈ toleranceSet action meaning ε s →
        p₂ ∈ toleranceSet action meaning ε s →
        action.act p₁ s = some s₁ →
        action.act p₂ s₁ = some s₂ →
        action.act (p₂ * p₁) s = some s₂ ∧
          dist (meaning s₂) (meaning s) ≤ dist (meaning s₂) (meaning s₁) + ε ∧
          ∃ baseMoved,
            action.act p₂ s = some baseMoved ∧
              dist (meaning baseMoved) (meaning s) ≤ ε := by
  refine ⟨one_mem_toleranceSet action meaning s hε, ?_, ?_⟩
  · refine ⟨swapLast, swapFirst, ?_⟩
    have h := tolerance_not_closed_counterexample
    dsimp only at h
    rcases h with
      ⟨hlast, _hfirstBase, hfirstMoved, _habc, _hacb, _hbac, _hcab, hnontrivial,
        hlastTol, hfirstTol, hcompNotTol, hmovedGap⟩
    exact ⟨hnontrivial, hlastTol, hfirstTol, hcompNotTol, acb, cab,
      hlast, hfirstMoved, hmovedGap⟩
  · intro p₁ p₂ s₁ s₂ hp₁ hp₂ h₁ h₂
    exact tolerance_composition_triangle action meaning hp₁ hp₂ h₁ h₂

end D5.S0.Naming.ToleranceNonGroup
