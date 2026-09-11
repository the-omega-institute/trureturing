import D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout
import D5.S3.ConceptDynamics.Spacetime.IntegerRepresentatives
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/- Validation only: finite typed presentations are transported to the existing HF archive.
   No declaration in this file is proposed as independent admission content. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LeafSquareBoundaryProbes
open D5.S0.History.Spacetime
open ArchiveCarrier HFEncoding SourceTreeEncoding
open D5.S3.ConceptDynamics.Spacetime
open ComplementCharge TaggedPresentation ProductNodes GeneratedProduct LeafSquareReadout
noncomputable section
attribute [local instance] Classical.propDecidable

def code4 : Fin 4 ↪ HF :=
  ⟨fun i => natCode i.val, fun _ _ h => Fin.ext (natCode_inj.mp h)⟩
def attr4 (src : Fin 4 → SourceTree) (i : Fin 4) : Attributes 3 where
  time := 0
  position := fun _ => 0
  positive := decide (i.val < 2)
  source := src i
def ctx (src : Fin 4 → SourceTree) : Context 3 :=
  contextOf code4 (attr4 src) (fun _ _ => False) (fun _ h => h)
    (fun _ _ _ h _ => h) (fun _ _ h => False.elim h) Finset.univ
def hist (src : Fin 4 → SourceTree) (s : Finset (Fin 4)) : BalancedRich 3 :=
  ⟨⟨ctx src, selectionOf code4 (attr4 src) (fun _ _ => False) (fun _ h => h)
    (fun _ _ _ h _ => h) (fun _ _ h => False.elim h) Finset.univ s
      (Finset.subset_univ _)⟩, by
    have h := charge_map code4 (attr4 src) (fun _ _ => False) (fun _ h => h)
      (fun _ _ _ h _ => h) (fun _ _ h => False.elim h) Finset.univ Finset.univ
    exact h.trans (by norm_num [attr4, Fin.sum_univ_succ])⟩

def cur (src : Fin 4 → SourceTree) : Fin 4 ↪ ↥(ctx src).current where
  toFun i := ⟨eventEquiv code4 i, by simp [ctx, contextOf]⟩
  inj' _ _ h := (eventEquiv code4).injective (congrArg Subtype.val h)

theorem selected_cur (src : Fin 4 → SourceTree) (s : Finset (Fin 4)) :
    selectedParents (hist src s).val.2 = s.map (cur src) := by
  ext e
  simp only [mem_selectedParents, hist, selectionOf, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, Subtype.ext he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, congrArg Subtype.val he⟩

def kept (src : Fin 4 → SourceTree) (s : Finset (Fin 4)) :=
  (s ×ˢ s).filter (fun p => FreeMagma.mul (src p.1) (src p.2) ∈ equalLeafSources)

theorem actual_selection (src : Fin 4 → SourceTree) (s : Finset (Fin 4)) :
    (sourceFilterBalanced equalLeafSources (productBalanced (hist src s) (hist src s))).val.2.val =
      ((kept src s).map ((cur src).prodMap (cur src))).map
        (generatedMap (ctx src) (ctx src)) := by
  change ((selectedParents (hist src s).val.2 ×ˢ selectedParents (hist src s).val.2).map
    (generatedMap (ctx src) (ctx src))).filter _ = _
  rw [Finset.filter_map, selected_cur, ← Finset.prodMap_map_product, Finset.filter_map]
  congr 2
  apply Finset.filter_congr
  intro p _
  change ((archive (ctx src) (ctx src)).attributes
    (generatedMap (ctx src) (ctx src) (cur src p.1, cur src p.2))).source ∈ _ ↔ _
  rw [GeneratedProduct.attributes_generated]
  simp [generatedAttributes, cur, ctx, contextOf, archiveOf, attr4]

theorem actual_readout (src : Fin 4 → SourceTree) (s : Finset (Fin 4)) :
    q (sourceFilterBalanced equalLeafSources (productBalanced (hist src s) (hist src s))).val =
      ∑ p ∈ kept src s,
        (if p.1.val < 2 then (1 : Int) else -1) * (if p.2.val < 2 then 1 else -1) := by
  change charge (context (ctx src) (ctx src)) _ = _
  rw [actual_selection, charge_generated, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  simp [contribution, cur, ctx, contextOf, attr4]

def same : Fin 4 → SourceTree := fun _ => .of 0
def mixed : Fin 4 → SourceTree := fun i =>
  if i = 0 then .of 0 else if i = 2 then .of 1 else .mul (.of 0) (.of 0)

theorem kept_same (s : Finset (Fin 4)) : kept same s = s ×ˢ s := by
  apply Finset.filter_true_of_mem
  intro _ _
  exact ⟨0, rfl⟩

-- Four actual selected ordered generated occurrences survive cancellation.
example : (sourceFilterBalanced equalLeafSources
    (productBalanced (hist same {0, 2}) (hist same {0, 2}))).val.2.val.card = 4 := by
  rw [actual_selection]
  simp [kept_same]

example : q (sourceFilterBalanced equalLeafSources
    (productBalanced (hist same {0, 2}) (hist same {0, 2}))).val = 0 := by
  rw [actual_readout, kept_same]
  simp only [Finset.sum_product, Finset.sum_insert (show (0 : Fin 4) ∉ {2} by decide),
    Finset.sum_singleton]
  norm_num

example : sourceCharge (hist same {0, 2}).val (.of 0) = 0 := by
  rw [(source_charge_apply _ _).1]
  change (∑ e ∈ ({0, 2} : Finset (Fin 4)).map (eventEquiv code4).toEmbedding
    with ((ctx same).archive.attributes e).source = .of 0, contribution (ctx same) e) = 0
  rw [Finset.filter_map, Finset.sum_map]
  simp only [Function.comp_apply, ctx, contextOf, contribution]
  simp [archiveOf, attr4, same, Finset.sum_insert (show (0 : Fin 4) ∉ {2} by decide)]

-- Distinct positive occurrences give four pairs, including both cross terms.
example : (sourceFilterBalanced equalLeafSources
    (productBalanced (hist same {0, 1}) (hist same {0, 1}))).val.2.val.card = 4 := by
  rw [actual_selection]
  simp [kept_same]

example : q (sourceFilterBalanced equalLeafSources
    (productBalanced (hist same {0, 1}) (hist same {0, 1}))).val = 4 := by
  rw [actual_readout, kept_same]
  norm_num [Finset.sum_product, Finset.sum_insert, Finset.sum_singleton]

-- Full Context preservation holds for arbitrary source predicates and histories.
example (L : Set SourceTree) (x : Rich 3) : (sourceFilter L x).1 = x.1 := rfl
example (L : Set SourceTree) (X : BalancedRich 3) :
    (sourceFilterBalanced L X).val.1 = X.val.1 := rfl

-- Empty selection over a nonempty archive and current region.
example : q (sourceFilterBalanced equalLeafSources
    (productBalanced (hist same ∅) (hist same ∅))).val = 0 := by
  rw [actual_readout]
  simp [kept]

-- Ordered contributions themselves, independently of the readout square theorem.
example :
    [contribution (context (ctx same) (ctx same))
      (generatedMap (ctx same) (ctx same) (cur same 0, cur same 0)),
     contribution (context (ctx same) (ctx same))
      (generatedMap (ctx same) (ctx same) (cur same 0, cur same 2)),
     contribution (context (ctx same) (ctx same))
      (generatedMap (ctx same) (ctx same) (cur same 2, cur same 0)),
     contribution (context (ctx same) (ctx same))
      (generatedMap (ctx same) (ctx same) (cur same 2, cur same 2))] = [1, -1, -1, 1] := by
  simp [contribution, context, GeneratedProduct.attributes_generated, generatedAttributes,
    cur, ctx, contextOf, archiveOf, attr4]

private theorem branch_injective (a b c d : SourceTree) :
    FreeMagma.mul a b = FreeMagma.mul c d ↔ a = c ∧ b = d := by
  constructor
  · intro h; injection h with h₁ h₂; exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl
private theorem of_injective (i j : Nat) : FreeMagma.of i = FreeMagma.of j ↔ i = j := by
  constructor
  · intro h; injection h
  · rintro rfl; rfl
private theorem of_ne_mul (i : Nat) (a b : SourceTree) :
    FreeMagma.of i ≠ FreeMagma.mul a b := by intro h; cases h

theorem mixed_kept : kept mixed {0, 1, 2} = {(0, 0), (2, 2)} := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num only [kept, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton, mixed, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Prod.mk.injEq,
      equalLeafSources, Set.mem_range, branch_injective, of_injective, of_ne_mul]
    <;> simp [of_injective]

example : (sourceFilterBalanced equalLeafSources
    (productBalanced (hist mixed {0, 1, 2}) (hist mixed {0, 1, 2}))).val.2.val.card = 2 := by
  rw [actual_selection, mixed_kept, Finset.card_map, Finset.card_map]
  norm_num [Finset.card_insert_of_notMem
    (show ((0, 0) : Fin 4 × Fin 4) ∉ {(2, 2)} by decide)]

example : q (sourceFilterBalanced equalLeafSources
    (productBalanced (hist mixed {0, 1, 2}) (hist mixed {0, 1, 2}))).val = 2 := by
  rw [actual_readout, mixed_kept]
  simp only [Finset.sum_insert (show ((0, 0) : Fin 4 × Fin 4) ∉ {(2, 2)} by decide),
    Finset.sum_singleton]
  norm_num

example : sourceCharge (hist mixed {0, 1, 2}).val (.mul (.of 0) (.of 0)) = 1 := by
  rw [(source_charge_apply _ _).1]
  change (∑ e ∈ ({0, 1, 2} : Finset (Fin 4)).map (eventEquiv code4).toEmbedding
    with ((ctx mixed).archive.attributes e).source = .mul (.of 0) (.of 0),
      contribution (ctx mixed) e) = 1
  rw [Finset.filter_map, Finset.sum_map]
  simp only [Function.comp_apply, ctx, contextOf, contribution]
  simp only [archiveOf, Equiv.toEmbedding_apply, Equiv.symm_apply_apply, attr4]
  simp only [Finset.sum_filter,
    Finset.sum_insert (show (0 : Fin 4) ∉ {1, 2} by decide),
    Finset.sum_insert (show (1 : Fin 4) ∉ {2} by decide), Finset.sum_singleton]
  norm_num only [mixed, Fin.ext_iff, Fin.coe_ofNat_eq_mod, of_ne_mul]
  simp

def retainedEmpty : BalancedRich 3 :=
  ⟨⟨⟨(ctx same).archive, ∅⟩, emptySelection _⟩,
    by simp [Balanced, background, charge]⟩

example : retainedEmpty.val.1.archive.events.card = 4 := by
  simp [retainedEmpty, ctx, contextOf, archiveOf]
example : retainedEmpty.val.1.current = ∅ := rfl
example : q (sourceFilterBalanced equalLeafSources
    (productBalanced retainedEmpty retainedEmpty)).val = 0 := by
  rw [leaf_product_fiber_readout]
  simp [retainedEmpty, emptySelection]

def emptyHistory : BalancedRich 3 :=
  ⟨IntegerRepresentatives.representative 3 0, IntegerRepresentatives.representative_balanced 3 0⟩
example : emptyHistory.val.1.archive.events = ∅ ∧ emptyHistory.val.1.current = ∅ ∧
    emptyHistory.val.2.val = ∅ := IntegerRepresentatives.representative_zero_empty 3
example : q (sourceFilterBalanced equalLeafSources
    (productBalanced emptyHistory emptyHistory)).val = 0 := by
  rw [leaf_product_fiber_readout]
  have he := (IntegerRepresentatives.representative_zero_empty 3).2.2
  change (∑ r ∈ ((IntegerRepresentatives.representative 3 0).2.val.image _).filter _, _) = 0
  rw [he]
  simp

end
end LeafSquareBoundaryProbes
