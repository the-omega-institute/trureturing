import D5.S3.Combinatorics.Circle.SingleSmallSource
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ExpandingSourcePath
open _root_.D5.S3.Combinatorics.Circle.SingleSmallSource

/-! Typed whole-telescope family bridges. Contract source-selection and binding
evidence are unfinished under issue 22063; these are not declared_validated audits. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Combinatorics.Circle.SingleSmallSource

namespace rigidity
abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (a : Fin k)
    (ha : |actualSource k t a| < quarter k)
    (hL : ∀ i : Fin k, i ≠ a → Large k t i),
    k % 2 = 1 ∧ 3 * |actualSource k t a| = half k ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        let w := orient (decide (actualSource k t a < 0))
          (R.readout () (k, t) (phase (by omega) a j))
        (if j % 2 = 1 then 0 < w else w < 0) ∧
        3 * w = (if j % 2 = 1 then modulus k else -modulus k) -
          (2 : ℤ) ^ (j - 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : |actualSource 3 1 (0 : Fin 3)| < quarter 3 := by decide
  have hl : ∀ i : Fin 3, i ≠ 0 → Large 3 1 i := by decide
  have hh := h (by decide : 3 ≤ 3) 1 0 ha hl
  have ht := (hh.2.2 1 (by decide) (by decide)).1
  norm_num [rejected, realize, orient, actualSource, modulus, centered] at ht

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  refine ⟨(3, 1), 0, 1, ?_⟩
  change actualSource 3 1 (0 : Fin 3) ≠ actualSource 3 1 (1 : Fin 3)
  decide

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.SingleSmallSource.single_small_rigidity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@single_small_rigidity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence
end rigidity

namespace completion
abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Fin p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a =>
    path (by have := a.isLt; omega)
      (if 0 < actualSource p.1 p.2 a then a else phase (by have := a.isLt; omega) a 2)
      p.1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (a : Fin k)
    (ha : |actualSource k t a| < quarter k)
    (hL : ∀ i : Fin k, i ≠ a → Large k t i),
    let word := R.readout () (k, t) a
    word.Perm (List.finRange k) ∧ word.Nodup ∧ word.toFinset = Finset.univ ∧
      InStrip (actualSource k t) (half k) 0 word ∧
      (∀ n : ℕ, 0 ≤ ((word.take n).map (actualSource k t)).sum ∧
        ((word.take n).map (actualSource k t)).sum ≤ half k) ∧
      (word.map (actualSource k t)).sum = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : |actualSource 3 1 (0 : Fin 3)| < quarter 3 := by decide
  have hl : ∀ i : Fin 3, i ≠ 0 → Large 3 1 i := by decide
  have hh := h (by decide : 3 ≤ 3) 1 0 ha hl
  have ht := hh.1.length_eq
  norm_num [rejected, realize] at ht

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  refine ⟨(3, 1), 0, 1, ?_⟩
  decide

def source_registration : Registration arena
    (type_of%
      (@_root_.D5.S3.Combinatorics.Circle.SingleSmallSource.single_small_forward_completion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@single_small_forward_completion, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence
end completion

#print axioms rigidity.source_registration
#print axioms completion.source_registration
end Reg.D5.S3.Combinatorics.Circle.SingleSmallSource
