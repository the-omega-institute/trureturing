/- GID: D5/S3/HomologicalAlgebra/Solid/CoefficientLinearity
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/CoefficientLinearity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.BoundedMeasureNaturality
import D5.S3.HomologicalAlgebra.Solid.Supplier.ProfiniteCover

/-!
Additivity of the concrete bounded coefficient maps, by finite covers of
closed coefficient fibers. These maps must be additive before they can be
assembled into D : P tensor B_Z -> P. This argument uses actual condensed
descent; no injectivity of PToIntegerMeasures is assumed.

New proofs, Apache-2.0. The covering epimorphism supplier is reused from
root's immutable CWComparison.ProfiniteCover checkpoint, whose copyright
and Apache-2.0 attribution are preserved in its frozen source.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory
open scoped BigOperators

namespace LightCondensed.Solid
open IntProof

theorem freeOnMap_epi_of_surjective {T S : LightProfinite} (f : T ⟶ S)
    (hf : Function.Surjective f) :
    Epi ((lightProfiniteToLightCondSet ⋙ free ℤ).map f) := by
  let e := lightProfiniteToLightCondSetIsoTopCatToLightCondSet
  haveI : IsIso (e.hom.app T) := by dsimp [e]; infer_instance
  haveI : IsIso (e.hom.app S) := by dsimp [e]; infer_instance
  have hTop : Epi ((LightProfinite.toTopCat ⋙ topCatToLightCondSet).map f) :=
    CWComparison.profiniteCover_condensed_epi f.hom.hom hf
  haveI : Epi (lightProfiniteToLightCondSet.map f) := by
    apply (epi_comp_iff_of_isIso _ (e.hom.app S)).mp
    rw [e.hom.naturality f]
    exact epi_comp' (inferInstance : Epi (e.hom.app T)) hTop
  exact (free ℤ).map_epi _

/-- A closed fiber on which every finite row has coefficient k. Infinity
is included regardless of k, which is essential for compactness. -/
def measureCoefficientFiber (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (k : ℤ) : Set (NinfTensor S) :=
  {x | ∀ n : ℕ, x.1 = (n : ℕ∪{∞}) → c n x.2 = k}

theorem measureCoefficientFiber_closed (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) :
    IsClosed (measureCoefficientFiber S c k) := by
  have hs (n : ℕ) : IsClopen {(n : ℕ∪{∞})} := by
    constructor
    · exact isClosed_singleton
    · exact (OnePoint.isOpen_iff_of_notMem (by simp)).2 (isOpen_discrete _)
  have heq : measureCoefficientFiber S c k =
      ⋂ n : ℕ, ({x : NinfTensor S | x.1 = (n : ℕ∪{∞})}ᶜ ∪
        {x : NinfTensor S | c n x.2 = k}) := by
    ext x
    simp only [measureCoefficientFiber, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    exact forall_congr' fun _ => imp_iff_not_or
  rw [heq]
  exact isClosed_iInter fun n =>
    ((hs n).preimage continuous_fst).compl.isClosed.union
      (((isClopen_discrete ({k} : Set ℤ)).preimage
        ((c n).continuous.comp continuous_snd)).isClosed)

/-- The bounded coefficient map before the first protected quotient. -/
def measureCoefficientNumerator (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) : freeOn (NinfTensor S) ⟶ P :=
  ∑ k ∈ F, k • ((lightProfiniteToLightCondSet ⋙ free ℤ).map
    (coefficientSelector S c k) ≫ P_proj)

theorem measureCoefficientNumerator_on_fiber {S E : LightProfinite}
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (k : ℤ) (hk : k ∈ F)
    (a : E ⟶ NinfTensor S) (ha : ∀ x, a x ∈ measureCoefficientFiber S c k) :
    (lightProfiniteToLightCondSet ⋙ free ℤ).map a ≫
      measureCoefficientNumerator S c F =
        k • ((lightProfiniteToLightCondSet ⋙ free ℤ).map
          (a ≫ ConcreteCategory.ofHom ⟨Prod.fst, continuous_fst⟩) ≫ P_proj) := by
  let fst : NinfTensor S ⟶ ℕ∪{∞} :=
    ConcreteCategory.ofHom ⟨Prod.fst, continuous_fst⟩
  let z : E ⟶ LightProfinite.of PUnit.{1} :=
    ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  have hsel (l : ℤ) : a ≫ coefficientSelector S c l =
      if k = l then a ≫ fst else z ≫ ι := by
    ext x
    have hx := ha x
    by_cases hkl : k = l
    · subst l
      rw [if_pos rfl]
      change coefficientSelectorFun S c k ((a x).1, (a x).2) = (a x).1
      cases he : (a x).1 using OnePoint.rec
      · simp [coefficientSelectorFun, he]
      · rename_i n
        simp [coefficientSelectorFun, he, hx n he]
    · rw [if_neg hkl]
      change coefficientSelectorFun S c l ((a x).1, (a x).2) = ∞
      cases he : (a x).1 using OnePoint.rec
      · simp [coefficientSelectorFun, he]
      · rename_i n
        simp [coefficientSelectorFun, he, hx n he, hkl]
  simp only [measureCoefficientNumerator, Preadditive.comp_sum,
    Preadditive.comp_zsmul, ← Functor.map_comp_assoc, hsel]
  have hz : (lightProfiniteToLightCondSet ⋙ free ℤ).map (z ≫ ι) ≫ P_proj = 0 := by
    rw [Functor.map_comp]
    simp [Category.assoc, P_map, P_proj]
  simp only [apply_ite (fun g => (lightProfiniteToLightCondSet ⋙ free ℤ).map g),
    ite_comp, hz, smul_ite, smul_zero]
  simpa [fst] using (Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl])
    (fun h => (h hk).elim) :
    (∑ l ∈ F, if k = l then l •
      ((lightProfiniteToLightCondSet ⋙ free ℤ).map (a ≫ fst) ≫ P_proj) else 0) = _)

/-- Actual additivity, proved after a finite surjective closed-fiber cover. -/
theorem measureCoefficientNumerator_add (S : LightProfinite)
    (c d : ℕ → LocallyConstant S ℤ) (F G H : Finset ℤ)
    (hF : ∀ n s, c n s ∈ F) (hG : ∀ n s, d n s ∈ G)
    (hH : ∀ k ∈ F, ∀ l ∈ G, k + l ∈ H) :
    measureCoefficientNumerator S (c + d) H =
      measureCoefficientNumerator S c F + measureCoefficientNumerator S d G := by
  let I := F × G
  let E : I → LightProfinite := fun i => by
    let C := measureCoefficientFiber S c i.1.val ∩ measureCoefficientFiber S d i.2.val
    letI : CompactSpace C := isCompact_iff_compactSpace.mp
      ((measureCoefficientFiber_closed S c i.1.val).inter
        (measureCoefficientFiber_closed S d i.2.val)).isCompact
    exact LightProfinite.of C
  let a : (i : I) → E i ⟶ NinfTensor S := fun _ =>
    ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let T := CompHausLike.finiteCoproduct E
  let p : T ⟶ NinfTensor S := CompHausLike.finiteCoproduct.desc E a
  have hp : Function.Surjective p := by
    rintro ⟨t, s⟩
    cases t using OnePoint.rec
    · let i : I := (⟨c 0 s, hF 0 s⟩, ⟨d 0 s, hG 0 s⟩)
      refine ⟨⟨i, ⟨(∞, s), ?_⟩⟩, rfl⟩
      constructor <;> intro n hn <;> simp at hn
    · rename_i n
      let i : I := (⟨c n s, hF n s⟩, ⟨d n s, hG n s⟩)
      refine ⟨⟨i, ⟨((n : ℕ∪{∞}), s), ?_⟩⟩, rfl⟩
      constructor <;> intro m hm
      all_goals have hnm : n = m := OnePoint.coe_injective hm
      all_goals subst m; rfl
  haveI := freeOnMap_epi_of_surjective p hp
  apply (cancel_epi ((lightProfiniteToLightCondSet ⋙ free ℤ).map p)).1
  apply (isColimitOfPreserves (lightProfiniteToLightCondSet ⋙ free ℤ)
    (CompHausLike.finiteCoproduct.isColimit E)).hom_ext
  rintro ⟨i⟩
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (CompHausLike.finiteCoproduct.ι E i) ≫
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫
          measureCoefficientNumerator S (c + d) H) =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (CompHausLike.finiteCoproduct.ι E i) ≫
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫
          (measureCoefficientNumerator S c F + measureCoefficientNumerator S d G))
  simp only [Preadditive.comp_add, ← Functor.map_comp_assoc]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (a i) ≫
      measureCoefficientNumerator S (c + d) H =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (a i) ≫
      measureCoefficientNumerator S c F +
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (a i) ≫
      measureCoefficientNumerator S d G
  have hc : ∀ x, a i x ∈ measureCoefficientFiber S c i.1.val := fun x => x.property.1
  have hd : ∀ x, a i x ∈ measureCoefficientFiber S d i.2.val := fun x => x.property.2
  have hcd : ∀ x, a i x ∈ measureCoefficientFiber S (c + d) (i.1.val + i.2.val) := by
    intro x n hn
    exact congrArg₂ (· + ·) (hc x n hn) (hd x n hn)
  rw [measureCoefficientNumerator_on_fiber _ _ _ (hH _ i.1.property _ i.2.property) _ hcd,
    measureCoefficientNumerator_on_fiber _ _ _ i.1.property _ hc,
    measureCoefficientNumerator_on_fiber _ _ _ i.2.property _ hd, add_smul]

theorem measureCoefficientNumerator_prequotient (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) :
    (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫ (P_proj ▷ freeOn S) ≫
      boundedCoefficientMap S c F = measureCoefficientNumerator S c F := by
  simp only [boundedCoefficientMap, Preadditive.comp_sum, Preadditive.comp_zsmul,
    P_proj_coefficientSelectorMap, coefficientSelectorNumerator,
    Iso.inv_hom_id_assoc, measureCoefficientNumerator]

/-- The actual coefficient map is additive, before ordinary or derived
solidification. This supplies the linearity required for descent to B_Z. -/
theorem boundedCoefficientMap_add (S : LightProfinite)
    (c d : ℕ → LocallyConstant S ℤ) (F G H : Finset ℤ)
    (hF : ∀ n s, c n s ∈ F) (hG : ∀ n s, d n s ∈ G)
    (hH : ∀ k ∈ F, ∀ l ∈ G, k + l ∈ H) :
    boundedCoefficientMap S (c + d) H =
      boundedCoefficientMap S c F + boundedCoefficientMap S d G := by
  haveI : Epi (P_proj ▷ freeOn S) := by
    rw [← tensorCokerIsoInt_π_inv (C := freeOn S)]
    infer_instance
  apply (cancel_epi (P_proj ▷ freeOn S)).1
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) S).inv).1
  simp only [Preadditive.comp_add, measureCoefficientNumerator_prequotient]
  exact measureCoefficientNumerator_add S c d F G H hF hG hH

end LightCondensed.Solid
