/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIIFixedCycleBlockValues
import Mathlib.Data.Finset.Sort
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Lean Elab Term in
elab "supportKernel%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIISLnDisplacedClassWords"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnDisplacedClassWords"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique frozen support kernel {id} not found"

namespace NikolovSegal.PartIISupportedClassTransport
open Matrix Equiv PartIISLnDisplacedClassWords PartIISLnUnipotentCommutators
open PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {N d : ℕ}

/-- Extract the genuine ordered principal submatrix; determinant1 follows
from the actual ambient unitriangular entries, including d=0. -/
noncomputable def principalUpper (e : Fin d ↪o Fin N)
    (a : SpecialLinearGroup (Fin N) F) (ha : LayerDepth 1 (a.val-1)) :
    SpecialLinearGroup (Fin d) F :=
  ⟨a.val.submatrix e e,by
    have hd : ∀ i : Fin d, a (e i) (e i)=1 := by
      intro i
      have h := ha (e i) (e i) (by omega)
      simpa only [Matrix.sub_apply,Matrix.one_apply_eq,sub_eq_zero] using h
    have ht : (a.val.submatrix e e).IsUpperTriangular := by
      intro i j hji
      have he : (e j).val<(e i).val := e.strictMono hji
      have h := ha (e i) (e j) (by omega)
      have hne : e i ≠ e j := ne_of_gt (show e j<e i from he)
      simpa [Matrix.submatrix_apply,Matrix.sub_apply,Matrix.one_apply,hne] using h
    rw [Matrix.det_of_isUpperTriangular ht]
    simp only [Matrix.submatrix_apply,hd,Finset.prod_const_one]⟩

theorem principalUpper_depth (e : Fin d ↪o Fin N)
    (a : SpecialLinearGroup (Fin N) F) (ha : LayerDepth 1 (a.val-1)) :
    LayerDepth 1 ((principalUpper e a ha).val-1) := by
  intro i j hij
  have hle : j ≤ i := by change j.val ≤ i.val; omega
  have he : e j ≤ e i := e.monotone hle
  have h := ha (e i) (e j) (by change (e j).val ≤ (e i).val at he; omega)
  simpa only [principalUpper,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.one_apply,e.injective.eq_iff] using h

theorem pad_double_on_first (e : (Fin d ⊕ Fin d) ↪ Fin N)
    (u : SpecialLinearGroup (Fin d) F) (i j : Fin d) :
    padAlong e (doubleEmbed u) (e (Sum.inl i)) (e (Sum.inl j))=u i j := by
  classical
  change (padAlong e (doubleEmbed u)).val
    ((supportKernel% padEquiv) e (Sum.inl (Sum.inl i)))
    ((supportKernel% padEquiv) e (Sum.inl (Sum.inl j)))= _
  simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,doubleEmbed]

/-- The auxiliary second block really is identity: the embedded double
matrix is supported ONLY on the first d selected coordinates. -/
theorem pad_double_support_first (e : (Fin d ⊕ Fin d) ↪ Fin N)
    (u : SpecialLinearGroup (Fin d) F) :
    Supported (Set.range (fun i : Fin d => e (Sum.inl i))) (padAlong e (doubleEmbed u)) := by
  classical
  intro i j hij
  obtain ⟨i,rfl⟩ := ((supportKernel% padEquiv) e).surjective i
  obtain ⟨j,rfl⟩ := ((supportKernel% padEquiv) e).surjective j
  have hl : ∀ x, (supportKernel% padEquiv) e (Sum.inl x)=e x := fun _ => rfl
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          exfalso
          rcases hij with hi|hj
          · exact hi ⟨i,hl _⟩
          · exact hj ⟨j,hl _⟩
        | inr j =>
          have hne : (supportKernel% padEquiv) e (Sum.inl (Sum.inl i)) ≠
              (supportKernel% padEquiv) e (Sum.inl (Sum.inr j)) := by
            intro h; have h:=((supportKernel% padEquiv) e).injective h; cases h
          simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,doubleEmbed,hne]
      | inr i =>
        cases j with
        | inl j =>
          have hne : (supportKernel% padEquiv) e (Sum.inl (Sum.inr i)) ≠
              (supportKernel% padEquiv) e (Sum.inl (Sum.inl j)) := by
            intro h; have h:=((supportKernel% padEquiv) e).injective h; cases h
          simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,doubleEmbed,hne]
        | inr j =>
          simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,doubleEmbed,
            Matrix.one_apply,((supportKernel% padEquiv) e).injective.eq_iff]
    | inr j =>
      have hne : (supportKernel% padEquiv) e (Sum.inl i) ≠ (supportKernel% padEquiv) e (Sum.inr j) := by
        intro h; have h:=((supportKernel% padEquiv) e).injective h; cases h
      simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,hne]
  | inr i =>
    cases j with
    | inl j =>
      have hne : (supportKernel% padEquiv) e (Sum.inr i) ≠ (supportKernel% padEquiv) e (Sum.inl j) := by
        intro h; have h:=((supportKernel% padEquiv) e).injective h; cases h
      simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,hne]
    | inr j =>
      simp [padAlong,SLnUnipotentWidth.reindexSL,Matrix.reindex_apply,
        Matrix.one_apply,((supportKernel% padEquiv) e).injective.eq_iff]

/-- Equality of supported matrices is determined by the ACTUAL principal
entries; this includes empty coordinate supports. -/
theorem supported_ext (e : Fin d ↪ Fin N) (a b : SpecialLinearGroup (Fin N) F)
    (ha : Supported (Set.range e) a) (hb : Supported (Set.range e) b)
    (h : ∀ i j, a (e i) (e j)=b (e i) (e j)) : a=b := by
  apply SpecialLinearGroup.ext
  intro i j
  by_cases hi : i ∈ Set.range e
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hi; obtain ⟨j,rfl⟩ := hj; exact h i j
    · rw [ha i j (Or.inr hj),hb i j (Or.inr hj)]
  · rw [ha i j (Or.inl hi),hb i j (Or.inl hi)]

end NikolovSegal.PartIISupportedClassTransport
