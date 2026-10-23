/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedFixedCycleClassWord
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedFixedCycleClassWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISupportedDetOneTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace NikolovSegal.PartIISupportedClassTransport
open Matrix Equiv PartIISLnDisplacedClassWords PartIISLnUnipotentCommutators
open PartIIUnitriangularLayers PartIIFixedCycleBlockValues PartIIFixedSLnPower
universe u
variable {F : Type u} [Field F]

/-- Extract and transport the literal upper supported block to the genuine
fixed-cycle block. The auxiliary double block is identity, not u^-1. -/
theorem actual_cycle_block_conjugate_supported (q r k d : ℕ) (hd : 4*d≤q*r+1)
    (e : Fin d ↪o Fin (k+4*(q*r+1)+2))
    (a : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)
    (ha : LayerDepth 1 (a.val-1)) (hs : Supported (Set.range e) a) :
    ∃ c : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      (MulAut.conj c) (padAlong (actualCycleEmbedding q r k d hd)
        (doubleEmbed (principalUpper e a ha)))=a := by
  let f : Fin d ↪ Fin (k+4*(q*r+1)+2) :=
    Function.Embedding.trans (Function.Embedding.inl) (actualCycleEmbedding q r k d hd)
  have hb : Supported (Set.range f) (padAlong (actualCycleEmbedding q r k d hd)
      (doubleEmbed (principalUpper e a ha))) := by
    change Supported (Set.range (fun i : Fin d => actualCycleEmbedding q r k d hd (Sum.inl i))) _
    exact pad_double_support_first _ _
  apply supported_coordinate_SL_transport (N := k+4*(q*r+1)+2) (d := d)
    e.toEmbedding f (by omega) a _ hs hb
  intro i j
  exact pad_double_on_first _ _ i j

/-- EVERY actual upper-unitriangular supported matrix on ANY d ordered
coordinates is a literal ordered12-word in the SAME fixedElement^q class.
No extraction, permutation, determinant-one transport or class-width oracle. -/
theorem actual_fixed_cycle_ordered_supported_upper_class_word (q r k d : ℕ)
    (hd : 4*d≤q*r+1) (e : Fin d ↪o Fin (k+4*(q*r+1)+2))
    (a : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)
    (ha : LayerDepth 1 (a.val-1)) (hs : Supported (Set.range e) a) :
    ∃ b : Fin 12 → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun i => (b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i)=a := by
  let u := principalUpper e a ha
  obtain ⟨b,hb⟩ := actual_fixed_cycle_upper_class_word q r k d hd u (principalUpper_depth e a ha)
  obtain ⟨c,hc⟩ := actual_cycle_block_conjugate_supported q r k d hd e a ha hs
  refine ⟨fun i => b i*c⁻¹,?_⟩
  have hmap := map_list_prod (MulAut.conj c).toMonoidHom
    (List.ofFn (fun i => (b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i))
  have hconj : orderedProduct (fun i =>
      (MulAut.conj c) ((b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i))=a := by
    have he : (MulAut.conj c)
        (orderedProduct (fun i => (b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i))=a := by
      rw [hb]
      exact hc
    simp only [List.map_ofFn,Function.comp_def] at hmap
    change (MulAut.conj c)
      (orderedProduct (fun i => (b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i))=
      orderedProduct (fun i => (MulAut.conj c) ((b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i)) at hmap
    exact hmap.symm.trans he
  rw [← hconj]
  congr 1
  funext i
  change (b i*c⁻¹)⁻¹*(fixedElement (F:=F) (q*r) k)^q*(b i*c⁻¹)=
    c*((b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i)*c⁻¹
  group

/-- Arbitrary finite support of cardinality AT MOST d. Native ordered
enumeration uses its actual cardinality; the fixed class and12 slots
remain exactly unchanged, including empty support. -/
theorem actual_fixed_cycle_finset_supported_upper_class_word (q r k d : ℕ)
    (hd : 4*d≤q*r+1) (T : Finset (Fin (k+4*(q*r+1)+2))) (hT : T.card≤d)
    (a : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)
    (ha : LayerDepth 1 (a.val-1)) (hs : Supported (T : Set _) a) :
    ∃ b : Fin 12 → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun i => (b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i)=a := by
  classical
  let e := T.orderEmbOfFin rfl
  have hde : 4*T.card≤q*r+1 := by omega
  apply actual_fixed_cycle_ordered_supported_upper_class_word q r k T.card hde e a ha
  simpa only [e,Finset.range_orderEmbOfFin] using hs

/-- Literal Set support version; finiteness is intrinsic to the ambient
finite coordinate type, and NO finite-field hypothesis is required. -/
theorem actual_fixed_cycle_set_supported_upper_class_word (q r k d : ℕ)
    (hd : 4*d≤q*r+1) (T : Set (Fin (k+4*(q*r+1)+2))) (hT : T.ncard≤d)
    (a : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)
    (ha : LayerDepth 1 (a.val-1)) (hs : Supported T a) :
    ∃ b : Fin 12 → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      orderedProduct (fun i => (b i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*b i)=a := by
  classical
  apply actual_fixed_cycle_finset_supported_upper_class_word q r k d hd T.toFinset
    (by rwa [← Set.ncard_eq_toFinset_card']) a ha
  simpa using hs

end NikolovSegal.PartIISupportedClassTransport
