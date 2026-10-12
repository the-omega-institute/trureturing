/- GID: D5/S1/Dynamics/Shadowing/ConstrainedProduct
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ConstrainedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-index common-source products of positively expansive shadowing extensions. -/

import D5.S1.Dynamics.Shadowing.UniformTracing
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.OfCompactT2
import Mathlib.Topology.Separation.Profinite
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Topology.Homeomorph.Lemmas

open TopologicalSpace Topology Set Function Filter UniformSpace

open scoped Uniformity

namespace D5.S1.Dynamics.Shadowing

universe u v w t

variable {I : Type u} {X : Type v} {B : I → Type w} {Y : I → Type t}

/-- This is a subspace of the product of extension spaces alone. -/
def commonSourceSet (π : ∀ i, X → B i) (p : ∀ i, Y i → B i) : Set (∀ i, Y i) :=
  {y | ∃ x : X, ∀ i, p i (y i) = π i x}

abbrev CommonSource (π : ∀ i, X → B i) (p : ∀ i, Y i → B i) :=
  ↥(commonSourceSet π p)

noncomputable def commonSourceMap (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (z : CommonSource π p) : X := z.property.choose

private theorem source_coordinates (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (z : CommonSource π p) (i : I) : p i (z.val i) = π i (commonSourceMap π p z) :=
  z.property.choose_spec i

/-- The product tuple has one actual source, unique under separation. -/
def SeparatesPoints (π : ∀ i, X → B i) : Prop :=
  ∀ x x', (∀ i, π i x = π i x') → x = x'

private theorem source_unique (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (hsep : SeparatesPoints π) (z : CommonSource π p) (x : X)
    (hx : ∀ i, p i (z.val i) = π i x) : commonSourceMap π p z = x :=
  hsep _ _ (fun i => (source_coordinates π p z i).symm.trans (hx i))

private theorem commonSource_isClosed [TopologicalSpace X] [CompactSpace X]
    [∀ i, TopologicalSpace (B i)] [∀ i, T2Space (B i)]
    [∀ i, TopologicalSpace (Y i)]
    (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (hπ : ∀ i, Continuous (π i)) (hp : ∀ i, Continuous (p i)) :
    IsClosed (commonSourceSet π p) := by
  have hR : IsClosed (range (fun x i => π i x)) :=
    (continuous_pi hπ).isClosedMap.isClosed_range
  have heq : commonSourceSet π p = (fun y i => p i (y i)) ⁻¹' range (fun x i => π i x) := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, funext fun i => (hx i).symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, fun i => (congrFun hx i).symm⟩
  rw [heq]
  exact hR.preimage (continuous_pi fun i => (hp i).comp (continuous_apply i))

private theorem commonSourceMap_continuous [TopologicalSpace X] [CompactSpace X]
    [∀ i, TopologicalSpace (B i)] [∀ i, T2Space (B i)]
    [∀ i, TopologicalSpace (Y i)]
    (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (hπ : ∀ i, Continuous (π i)) (hp : ∀ i, Continuous (p i))
    (hsep : SeparatesPoints π) : Continuous (commonSourceMap π p) := by
  have hi : Injective (fun x i => π i x) := fun x x' h => hsep x x' (congrFun h)
  apply ((continuous_pi hπ).isClosedEmbedding hi).isEmbedding.continuous_iff.mpr
  have h : (fun x i => π i x) ∘ commonSourceMap π p =
      fun z : CommonSource π p => fun i => p i (z.val i) := by
    funext z i
    exact (source_coordinates π p z i).symm
  rw [h]
  exact continuous_pi fun i => (hp i).comp ((continuous_apply i).comp continuous_subtype_val)

private theorem commonSourceMap_surjective (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (hsep : SeparatesPoints π) (hp : ∀ i, Surjective (p i)) :
    Surjective (commonSourceMap π p) := by
  intro x
  choose y hy using fun i => hp i (π i x)
  exact ⟨⟨y, x, hy⟩, source_unique π p hsep _ x hy⟩

/-- Restriction of the coordinatewise forward dynamics. -/
noncomputable def commonSourceDynamics (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (f : X → X) (d : ∀ i, B i → B i) (g : ∀ i, Y i → Y i)
    (hπ : ∀ i, Semiconj (π i) f (d i)) (hp : ∀ i, Semiconj (p i) (g i) (d i)) :
    CommonSource π p → CommonSource π p := fun z =>
  ⟨fun i => g i (z.val i), f (commonSourceMap π p z), fun i => by
    rw [hp i, source_coordinates π p z i, ← hπ i]⟩

private theorem dynamics_semiconj (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (hsep : SeparatesPoints π) (f : X → X) (d : ∀ i, B i → B i) (g : ∀ i, Y i → Y i)
    (hπ : ∀ i, Semiconj (π i) f (d i)) (hp : ∀ i, Semiconj (p i) (g i) (d i)) :
    Semiconj (commonSourceMap π p) (commonSourceDynamics π p f d g hπ hp) f := by
  intro z
  apply source_unique π p hsep
  intro i
  change p i (g i (z.val i)) = π i (f (commonSourceMap π p z))
  rw [hp i, source_coordinates π p z i, hπ i]

private theorem dynamics_continuous [∀ i, TopologicalSpace (Y i)]
    (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (f : X → X) (d : ∀ i, B i → B i) (g : ∀ i, Y i → Y i)
    (hπ : ∀ i, Semiconj (π i) f (d i)) (hp : ∀ i, Semiconj (p i) (g i) (d i))
    (hg : ∀ i, Continuous (g i)) : Continuous (commonSourceDynamics π p f d g hπ hp) :=
  (continuous_pi fun i => (hg i).comp
    ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _

private theorem coordinate_iterate (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (f : X → X) (d : ∀ i, B i → B i) (g : ∀ i, Y i → Y i)
    (hπ : ∀ i, Semiconj (π i) f (d i)) (hp : ∀ i, Semiconj (p i) (g i) (d i))
    (n : ℕ) (z : CommonSource π p) (i : I) :
    ((commonSourceDynamics π p f d g hπ hp)^[n] z).val i = (g i)^[n] (z.val i) :=
  (show Semiconj (fun z : CommonSource π p => z.val i)
    (commonSourceDynamics π p f d g hπ hp) (g i) from fun _ => rfl).iterate_right n z

/-- An entourage on any product subspace is implied by finitely many positive
metric coordinate tolerances. Empty index and empty support remain in scope. -/
theorem finite_support_entourage [∀ i, MetricSpace (Y i)]
    (S : Set (∀ i, Y i)) (E : Set (S × S)) (hE : E ∈ 𝓤 S) :
    ∃ (F : Finset I) (ε : I → ℝ), (∀ i ∈ F, 0 < ε i) ∧
      ∀ a b : S, (∀ i ∈ F, dist (a.val i) (b.val i) < ε i) → (a, b) ∈ E := by
  classical
  rw [uniformity_subtype, mem_comap] at hE
  obtain ⟨T, hT, hTE⟩ := hE
  rw [Pi.uniformity] at hT
  have hb := Filter.HasBasis.iInf' (fun i : I =>
    (Metric.uniformity_basis_dist (α := Y i)).comap (fun yy : (∀ i, Y i) × (∀ i, Y i) =>
      (yy.1 i, yy.2 i)))
  obtain ⟨⟨F, ε⟩, ⟨hF, hε⟩, hFT⟩ := hb.mem_iff.mp hT
  refine ⟨hF.toFinset, ε, ?_, fun a b hab => hTE (hFT ?_)⟩
  · simpa only [Set.Finite.mem_toFinset] using hε
  · exact mem_iInter₂.mpr fun i hi => hab i (hF.mem_toFinset.mpr hi)

/-- Genuine shadowing of the constrained subspace, obtained from one base tracer
and derived prescribed-source tracing at every controlled coordinate. -/
theorem constrained_product_hasShadowing [UniformSpace X] [CompactSpace X]
    [∀ i, MetricSpace (B i)] [∀ i, MetricSpace (Y i)] [∀ i, CompactSpace (Y i)]
    (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (hπc : ∀ i, Continuous (π i)) (hpc : ∀ i, Continuous (p i))
    (hsep : SeparatesPoints π) (hps : ∀ i, Surjective (p i))
    (f : X → X) (d : ∀ i, B i → B i) (g : ∀ i, Y i → Y i)
    (hπe : ∀ i, Semiconj (π i) f (d i)) (hpe : ∀ i, Semiconj (p i) (g i) (d i))
    (hs : HasShadowing f) (hgs : ∀ i, HasShadowing (g i))
    (hd : ∀ i, PositivelyExpansive (d i)) :
    HasShadowing (commonSourceDynamics π p f d g hπe hpe) := by
  classical
  let Z := CommonSource π p
  let q := commonSourceMap π p
  let G := commonSourceDynamics π p f d g hπe hpe
  letI : CompactSpace Z := (commonSource_isClosed π p hπc hpc).isClosedEmbedding_subtypeVal.compactSpace
  apply (cover_shadowing_iff_uniform G).mpr
  intro E hE
  obtain ⟨F, ε, hε, hFE⟩ := finite_support_entourage (commonSourceSet π p) E hE
  have hsr := fun i => positive_expansivity_source_relative (p i) (g i) (d i)
    (hpc i) (hpe i) (hgs i) (hd i)
  have hchoices : ∀ i : F, ∃ D ∈ 𝓤 (Y i.val), ∃ V ∈ 𝓤 (B i.val),
      ∀ a : ℕ → Y i.val, ∀ x : B i.val, UniformPseudoOrbit (g i.val) D a →
        (∀ n, (p i.val (a n), (d i.val)^[n] x) ∈ V) →
        ∃ b, p i.val b = x ∧ ∀ n, dist ((g i.val)^[n] b) (a n) < ε i.val := by
    intro i
    exact hsr i.val {yy | dist yy.1 yy.2 < ε i.val} (Metric.dist_mem_uniformity (hε i.val i.property))
  choose D hD V hV ht using hchoices
  let A : Set (X × X) := ⋂ i : F, (fun xx : X × X => (π i.val xx.2, π i.val xx.1)) ⁻¹' V i
  have hA : A ∈ 𝓤 X := iInter_mem.mpr fun i =>
    (CompactSpace.uniformContinuous_of_continuous (hπc i.val)) (symm_le_uniformity (hV i))
  obtain ⟨W, hW, hbase⟩ := ((cover_shadowing_iff_uniform f).mp hs) A hA
  let C : Set (Z × Z) := ⋂ i : F, (fun zz : Z × Z => (zz.1.val i.val, zz.2.val i.val)) ⁻¹' D i
  have hC : C ∈ 𝓤 Z := iInter_mem.mpr fun i =>
    ((Pi.uniformContinuous_proj Y i.val).comp uniformContinuous_subtype_val) (hD i)
  have hq : UniformContinuous q := CompactSpace.uniformContinuous_of_continuous
    (commonSourceMap_continuous π p hπc hpc hsep)
  let L : Set (Z × Z) := C ∩ (fun zz : Z × Z => (q zz.1, q zz.2)) ⁻¹' W
  refine ⟨L, inter_mem hC (hq hW), fun a ha => ?_⟩
  have he : Semiconj q G f := dynamics_semiconj π p hsep f d g hπe hpe
  have hqa : UniformPseudoOrbit f W (fun n => q (a n)) := by
    intro n
    have hh : (q (G (a n)), q (a (n + 1))) ∈ W := (ha n).2
    rw [he] at hh
    exact hh
  obtain ⟨x, hx⟩ := hbase _ hqa
  have hcoords : ∀ i : F, ∃ b : Y i.val, p i.val b = π i.val x ∧
      ∀ n, dist ((g i.val)^[n] b) ((a n).val i.val) < ε i.val := by
    intro i
    apply ht i (fun n => (a n).val i.val) (π i.val x)
    · intro n
      exact mem_iInter.mp (ha n).1 i
    · intro n
      have hh := mem_iInter.mp (hx n) i
      change (π i.val (q (a n)), π i.val (f^[n] x)) ∈ V i at hh
      rw [source_coordinates π p (a n) i.val, ← (hπe i.val).iterate_right n]
      exact hh
  choose b hb hbt using hcoords
  choose c hc using fun i => hps i (π i x)
  let y : ∀ i, Y i := fun i => if hi : i ∈ F then b ⟨i, hi⟩ else c i
  have hy : ∀ i, p i (y i) = π i x := by
    intro i
    dsimp only [y]
    split_ifs with hi
    · exact hb ⟨i, hi⟩
    · exact hc i
  refine ⟨⟨y, x, hy⟩, fun n => hFE _ _ (fun i hi => ?_)⟩
  rw [coordinate_iterate]
  simpa only [y, dif_pos hi] using hbt ⟨i, hi⟩ n

/-- Arbitrary-index compact Hausdorff zero-dimensional shadowing extension.
The metric extension spaces, maps, shadowing and expansivity are supplied
parameters. No countability or onto-dynamics hypothesis is present. -/
theorem constrained_product_extension [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [∀ i, MetricSpace (B i)] [∀ i, MetricSpace (Y i)]
    [∀ i, CompactSpace (Y i)] [∀ i, TotallyDisconnectedSpace (Y i)]
    (π : ∀ i, X → B i) (p : ∀ i, Y i → B i)
    (hπc : ∀ i, Continuous (π i)) (hpc : ∀ i, Continuous (p i))
    (hsep : SeparatesPoints π) (hps : ∀ i, Surjective (p i))
    (f : X → X) (d : ∀ i, B i → B i) (g : ∀ i, Y i → Y i)
    (hgc : ∀ i, Continuous (g i))
    (hπe : ∀ i, Semiconj (π i) f (d i)) (hpe : ∀ i, Semiconj (p i) (g i) (d i))
    (hs : HasShadowing f) (hgs : ∀ i, HasShadowing (g i))
    (hd : ∀ i, PositivelyExpansive (d i)) :
    let Z := CommonSource π p
    let q := commonSourceMap π p
    let G := commonSourceDynamics π p f d g hπe hpe
    IsClosed (commonSourceSet π p) ∧ CompactSpace Z ∧ T2Space Z ∧
      TotallyDisconnectedSpace Z ∧ Continuous q ∧ Surjective q ∧ Continuous G ∧
      Semiconj q G f ∧ HasShadowing G ∧
      (∀ x : X, ∃ z : Z, q z = x ∧
        ∀ (i : I) (n : ℕ), p i ((G^[n] z).val i) = π i (f^[n] x)) := by
  letI : UniformSpace X := uniformSpaceOfCompactR1
  let Z := CommonSource π p
  let q := commonSourceMap π p
  let G := commonSourceDynamics π p f d g hπe hpe
  have hclosed := commonSource_isClosed π p hπc hpc
  letI : CompactSpace Z := hclosed.isClosedEmbedding_subtypeVal.compactSpace
  have he : Semiconj q G f := dynamics_semiconj π p hsep f d g hπe hpe
  have hsur : Surjective q := commonSourceMap_surjective π p hsep hps
  refine ⟨hclosed, inferInstance, inferInstance, inferInstance,
    commonSourceMap_continuous π p hπc hpc hsep, hsur,
    dynamics_continuous π p f d g hπe hpe hgc, he,
    constrained_product_hasShadowing π p hπc hpc hsep hps f d g hπe hpe hs hgs hd, ?_⟩
  intro x
  obtain ⟨z, hz⟩ := hsur x
  refine ⟨z, hz, fun i n => ?_⟩
  rw [source_coordinates π p (G^[n] z) i]
  change π i (q (G^[n] z)) = π i (f^[n] x)
  rw [he.iterate_right n, hz]

#print axioms finite_support_entourage
#print axioms constrained_product_hasShadowing
#print axioms constrained_product_extension

end D5.S1.Dynamics.Shadowing
