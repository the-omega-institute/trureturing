import D5.S3.TotalVariation.LocalLeafInverse
import D5.S3.Combinatorics.CircularWords.PairedDeletionLaw

noncomputable section
open scoped BigOperators
open D5.S3.TotalVariation.LocalLeafInverse
open D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope (pushMass)
open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.Combinatorics.CircularWords.PairedDeletionLaw

namespace LocalLeafInverseCheck

private def starF (x : Fin 5) : Fin 3 := if x = 3 then 1 else if x = 4 then 2 else 0
private def starG (x : Fin 5) : Fin 3 := if x = 1 then 1 else if x = 2 then 2 else 0

-- A double-star incidence component has degree three, so this checks a
-- non-cycle model beyond a degree-two short-path specialization.
example (p q : Fin 5 → ℝ) :
    totalVariation p q ≤ (3 / 2 : ℝ) *
      (totalVariation (pushMass starF p) (pushMass starF q) +
       totalVariation (pushMass starG p) (pushMass starG q)) := by
  have hfg : OppositeLeaves starF starG := by decide
  have hgf : OppositeLeaves starG starF := by decide
  exact total_variation_le_sum starF starG hfg hgf p q

section ActualCycles
variable {α : Type*} [DecidableEq α] {A : Finset α}
variable (hA : 4 ≤ A.card) {a b c : α}
variable (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
variable (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)

private def rawF (C : FixedCycles A) := paired a b C.val
private def rawG (C : FixedCycles A) := paired b c C.val

private noncomputable instance outF : Fintype (Set.range (rawF (A:=A) (a:=a) (b:=b))) :=
  (Set.finite_range _).fintype
private noncomputable instance outG : Fintype (Set.range (rawG (A:=A) (b:=b) (c:=c))) :=
  (Set.finite_range _).fintype

private def actualF (C : FixedCycles A) : Set.range (rawF (a:=a) (b:=b)) :=
  ⟨rawF C, ⟨C,rfl⟩⟩
private def actualG (C : FixedCycles A) : Set.range (rawG (b:=b) (c:=c)) :=
  ⟨rawG C, ⟨C,rfl⟩⟩

private lemma actual_fg : OppositeLeaves (actualF (A:=A) (a:=a) (b:=b))
    (actualG (A:=A) (b:=b) (c:=c)) := by
  classical
  intro x _ hgx y hxy hyx z hzy
  by_contra hne
  obtain ⟨k,hkx,hkn⟩ : ∃ k, actualG (b:=b) (c:=c) k = actualG (b:=b) (c:=c) x ∧ k ≠ x := by
    simpa only [IsLeaf, not_forall, not_imp] using hgx
  exact swap_has_leaf hA ha hb hc hab hbc hac
    x.property.1 y.property.1 k.property.1 z.property.1
    x.property.2 y.property.2 k.property.2 z.property.2
    (congrArg Subtype.val hxy).symm (fun h => hyx (Subtype.ext h))
    (congrArg Subtype.val hkx).symm (fun h => hkn (Subtype.ext h))
    (congrArg Subtype.val hzy).symm (fun h => hne (Subtype.ext h))

private lemma actual_gf : OppositeLeaves (actualG (A:=A) (b:=b) (c:=c))
    (actualF (A:=A) (a:=a) (b:=b)) := by
  classical
  intro x _ hfx y hxy hyx z hzy
  by_contra hne
  obtain ⟨k,hkx,hkn⟩ : ∃ k, actualF (a:=a) (b:=b) k = actualF (a:=a) (b:=b) x ∧ k ≠ x := by
    simpa only [IsLeaf, not_forall, not_imp] using hfx
  exact swap_has_leaf_swapped hA ha hb hc hab hbc hac
    x.property.1 y.property.1 k.property.1 z.property.1
    x.property.2 y.property.2 k.property.2 z.property.2
    (congrArg Subtype.val hxy).symm (fun h => hyx (Subtype.ext h))
    (congrArg Subtype.val hkx).symm (fun h => hkn (Subtype.ext h))
    (congrArg Subtype.val hzy).symm (fun h => hne (Subtype.ext h))

-- All legal cycles, no chosen finite subfamily and no desired estimate assumed.
example (p q : FixedCycles A → ℝ) :
    totalVariation p q ≤ (3 / 2 : ℝ) *
      (totalVariation (pushMass (actualF (a:=a) (b:=b)) p) (pushMass (actualF (a:=a) (b:=b)) q) +
       totalVariation (pushMass (actualG (b:=b) (c:=c)) p) (pushMass (actualG (b:=b) (c:=c)) q)) :=
  total_variation_le_sum _ _ (actual_fg hA ha hb hc hab hbc hac)
    (actual_gf hA ha hb hc hab hbc hac) p q

example (p q : FixedCycles A → ℝ) :
    totalVariation p q ≤ 3 *
      max (totalVariation (pushMass (actualF (a:=a) (b:=b)) p) (pushMass (actualF (a:=a) (b:=b)) q))
       (totalVariation (pushMass (actualG (b:=b) (c:=c)) p) (pushMass (actualG (b:=b) (c:=c)) q)) :=
  total_variation_le_max _ _ (actual_fg hA ha hb hc hab hbc hac)
    (actual_gf hA ha hb hc hab hbc hac) p q

end ActualCycles
end LocalLeafInverseCheck
