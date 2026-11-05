import D5.S3.TotalVariation.LocalLeafInverse
import D5.S3.Combinatorics.CircularWords.PairedDeletionLaw
import D5.S3.Combinatorics.CircularWords.PairedDeletionSharpness
import D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope

/-! Task-private exact application on the complete fixed-support oriented-cycle carrier. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
open D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
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
  have hfg : OppositeLeaves starF starG := by
    unfold OppositeLeaves IsLeaf
    decide
  have hgf : OppositeLeaves starG starF := by
    unfold OppositeLeaves IsLeaf
    decide
  exact total_variation_le_sum starF starG hfg hgf p q


private lemma push_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (f : X → Y) (g : Y → Z) (p : X → ℝ) :
    pushMass g (pushMass f p) = pushMass (g ∘ f) p := by
  classical
  funext z
  change (∑ y, if g y = z then ∑ x, if f x = y then p x else 0 else 0) =
    ∑ x, if g (f x) = z then p x else 0
  calc
    _ = ∑ y, ∑ x, if f x = y then (if g y = z then p x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = z <;> simp [hy]
    _ = ∑ x, ∑ y, if f x = y then (if g y = z then p x else 0) else 0 := 
      Finset.sum_comm
    _ = _ := by simp

private lemma embed_l1 {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hi : Function.Injective f) (p : X → ℝ) :
    (∑ y, |pushMass f p y|) = ∑ x, |p x| := by
  classical
  let s := Finset.univ.image f
  have pin (x : X) : pushMass f p (f x) = p x := by
    change (∑ y, if f y = f x then p y else 0) = p x
    simp [hi.eq_iff]
  have pout (y : Y) (hy : y ∉ s) : pushMass f p y = 0 := by
    change (∑ x, if f x = y then p x else 0) = 0
    apply Finset.sum_eq_zero
    intro x _
    apply ite_eq_right
    intro he
    exact hy (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, he⟩)
  calc
    _ = ∑ y ∈ s, |pushMass f p y| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      rw [pout y hy, abs_zero]
    _ = ∑ x, |p x| := by
      rw [Finset.sum_image (fun _ _ _ _ h => hi h)]
      simp only [pin]

private lemma embed_tv {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hi : Function.Injective f) (p q : X → ℝ) :
    totalVariation (pushMass f p) (pushMass f q) = totalVariation p q := by
  have he := embed_l1 f hi (p-q)
  rw [map_sub] at he
  simpa only [totalVariation, Pi.sub_apply] using
    congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) he

-- Equality of native laws is unchanged by a measurable output embedding.
private lemma map_embed_eq_iff {X U V : Type*}
    [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace V]
    (i : U → V) (hi : MeasurableEmbedding i) (f : X → U) (hf : Measurable f)
    (μ ν : ProbabilityMeasure X) :
    μ.map (i ∘ f) = ν.map (i ∘ f) ↔ μ.map f = ν.map f := by
  have comp (ρ : ProbabilityMeasure X) :
      ((ρ.map f : ProbabilityMeasure U) : Measure U).map i =
        (ρ.map (i ∘ f) : Measure V) := by
    change ((ρ : Measure X).map f).map i = (ρ : Measure X).map (i ∘ f)
    exact Measure.map_map hi.measurable hf
  constructor
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    apply hi.map_injective
    rw [comp μ, comp ν]
    exact congrArg ProbabilityMeasure.toMeasure h
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    rw [← comp μ, ← comp ν, h]

section ActualCycles
variable {α : Type*} [DecidableEq α] {A : Finset α}
variable (hA : 4 ≤ A.card) {a b c : α}
variable (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
variable (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)

private def rawF (C : FixedCycles A) := paired a b C.val
private def rawG (C : FixedCycles A) := paired b c C.val

private noncomputable instance outF : Fintype (Set.range (rawF (A := A) (a := a) (b := b))) := 
  (Set.finite_range _).fintype
private noncomputable instance outG : Fintype (Set.range (rawG (A := A) (b := b) (c := c))) := 
  (Set.finite_range _).fintype

private def actualF (C : FixedCycles A) : Set.range (rawF (A := A) (a := a) (b := b)) := 
  ⟨rawF C, ⟨C,rfl⟩⟩
private def actualG (C : FixedCycles A) : Set.range (rawG (A := A) (b := b) (c := c)) := 
  ⟨rawG C, ⟨C,rfl⟩⟩

-- The full signed conclusion is an exact application, not a retained wrapper.
include hA ha hb hc hab hbc hac in
private theorem full_signed_identification (p q : FixedCycles A → ℝ)
    (hF : pushforward (rawF (a := a) (b := b)) p = pushforward (rawF (a := a) (b := b)) q)
    (hG : pushforward (rawG (b := b) (c := c)) p = pushforward (rawG (b := b) (c := c)) q) : p = q := by
  exact signed_injective hA ha hb hc hab hbc hac Subtype.val Subtype.val_injective
    (fun C => C.property.1) (fun C => C.property.2) p q hF hG

include hA ha hb hc hab hbc hac in
private lemma actual_fg : OppositeLeaves (actualF (A := A) (a := a) (b := b))
    (actualG (A := A) (b := b) (c := c)) := by
  classical
  intro x _ hgx y hxy hyx z hzy
  by_contra hne
  obtain ⟨k,hkx,hkn⟩ : ∃ k, actualG (b := b) (c := c) k = actualG (b := b) (c := c) x ∧ k ≠ x := by
    by_contra hn
    apply hgx
    intro k hk
    by_contra hkn
    exact hn ⟨k, hk, hkn⟩
  exact swap_has_leaf hA ha hb hc hab hbc hac
    x.property.1 y.property.1 k.property.1 z.property.1
    x.property.2 y.property.2 k.property.2 z.property.2
    (congrArg Subtype.val hxy).symm (fun h => hyx (Subtype.ext h))
    (congrArg Subtype.val hkx).symm (fun h => hkn (Subtype.ext h))
    (congrArg Subtype.val hzy).symm (fun h => hne (Subtype.ext h))

include hA ha hb hc hab hbc hac in
private lemma actual_gf : OppositeLeaves (actualG (A := A) (b := b) (c := c))
    (actualF (A := A) (a := a) (b := b)) := by
  classical
  intro x _ hfx y hxy hyx z hzy
  by_contra hne
  obtain ⟨k,hkx,hkn⟩ : ∃ k, actualF (a := a) (b := b) k = actualF (a := a) (b := b) x ∧ k ≠ x := by
    by_contra hn
    apply hfx
    intro k hk
    by_contra hkn
    exact hn ⟨k, hk, hkn⟩
  have flip {u v : α} {C D : Cycle α} (h : paired u v C = paired u v D) :
      paired v u C = paired v u D := 
    Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  exact swap_has_leaf hA hc hb ha hbc.symm hab.symm hac.symm
    x.property.1 y.property.1 k.property.1 z.property.1
    x.property.2 y.property.2 k.property.2 z.property.2
    (flip (congrArg Subtype.val hxy).symm) (fun h => hyx (Subtype.ext h))
    (flip (congrArg Subtype.val hkx).symm) (fun h => hkn (Subtype.ext h))
    (flip (congrArg Subtype.val hzy).symm) (fun h => hne (Subtype.ext h))

-- All legal cycles, no chosen finite subfamily and no desired estimate assumed.
include hA ha hb hc hab hbc hac in
example (p q : FixedCycles A → ℝ) :
    totalVariation p q ≤ (3 / 2 : ℝ) *
      (totalVariation (pushMass (actualF (a := a) (b := b)) p) (pushMass (actualF (a := a) (b := b)) q) +
       totalVariation (pushMass (actualG (b := b) (c := c)) p) (pushMass (actualG (b := b) (c := c)) q)) := 
  total_variation_le_sum _ _ (actual_fg hA ha hb hc hab hbc hac)
    (actual_gf hA ha hb hc hab hbc hac) p q

include hA ha hb hc hab hbc hac in
example (p q : FixedCycles A → ℝ) :
    totalVariation p q ≤ 3 *
      max (totalVariation (pushMass (actualF (a := a) (b := b)) p) (pushMass (actualF (a := a) (b := b)) q))
       (totalVariation (pushMass (actualG (b := b) (c := c)) p) (pushMass (actualG (b := b) (c := c)) q)) := 
  total_variation_le_max _ _ (actual_fg hA ha hb hc hab hbc hac)
    (actual_gf hA ha hb hc hab hbc hac) p q


private instance sourceSpace : MeasurableSpace (FixedCycles A) := ⊤
private instance sourceSingletons : MeasurableSingletonClass (FixedCycles A) := 
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance rangeSpaceF : MeasurableSpace (Set.range (rawF (A := A) (a := a) (b := b))) := ⊤
private instance rangeSingletonsF : MeasurableSingletonClass (Set.range (rawF (A := A) (a := a) (b := b))) := 
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance rangeSpaceG : MeasurableSpace (Set.range (rawG (A := A) (b := b) (c := c))) := ⊤
private instance rangeSingletonsG : MeasurableSingletonClass (Set.range (rawG (A := A) (b := b) (c := c))) := 
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

-- Ambient labels and output pairs need not form finite types. Their discrete
-- measurable structure includes every output, including unrealized ones.
private instance pairSpace : MeasurableSpace (Cycle α × Cycle α) := ⊤

private theorem native_range_correspondence (μ ν : ProbabilityMeasure (FixedCycles A)) :
    (μ.map (rawF (a := a) (b := b)) = ν.map (rawF (a := a) (b := b)) ↔
      μ.map (actualF (a := a) (b := b)) = ν.map (actualF (a := a) (b := b))) ∧
    (μ.map (rawG (b := b) (c := c)) = ν.map (rawG (b := b) (c := c)) ↔
      μ.map (actualG (b := b) (c := c)) = ν.map (actualG (b := b) (c := c))) := by
  have embF : MeasurableEmbedding
      (Subtype.val : Set.range (rawF (A := A) (a := a) (b := b)) → Cycle α × Cycle α) := 
    ⟨Subtype.val_injective, measurable_of_countable _,
      fun _ _ => MeasurableSpace.measurableSet_top⟩
  have embG : MeasurableEmbedding
      (Subtype.val : Set.range (rawG (A := A) (b := b) (c := c)) → Cycle α × Cycle α) := 
    ⟨Subtype.val_injective, measurable_of_countable _,
      fun _ _ => MeasurableSpace.measurableSet_top⟩
  exact ⟨map_embed_eq_iff _ embF (actualF (a := a) (b := b))
      (measurable_of_countable _) μ ν,
    map_embed_eq_iff _ embG (actualG (b := b) (c := c))
      (measurable_of_countable _) μ ν⟩

-- Actual native probability laws on every legal fixed-support cycle.
include hA ha hb hc hab hbc hac in
private theorem actual_native_upper_sum (μ ν : ProbabilityMeasure (FixedCycles A)) :
    totalVariation (massVector μ) (massVector ν) ≤ (3 / 2 : ℝ) *
      (totalVariation (massVector (μ.map (actualF (a := a) (b := b))))
        (massVector (ν.map (actualF (a := a) (b := b)))) +
       totalVariation (massVector (μ.map (actualG (b := b) (c := c))))
        (massVector (ν.map (actualG (b := b) (c := c))))) := by
  simp only [massVector_map]
  exact total_variation_le_sum _ _ (actual_fg hA ha hb hc hab hbc hac)
    (actual_gf hA ha hb hc hab hbc hac) (massVector μ) (massVector ν)


include hA ha hb hc hab hbc hac in
private theorem actual_native_upper_max (μ ν : ProbabilityMeasure (FixedCycles A)) :
    totalVariation (massVector μ) (massVector ν) ≤ 3 *
      max (totalVariation (massVector (μ.map (actualF (a := a) (b := b))))
        (massVector (ν.map (actualF (a := a) (b := b)))))
       (totalVariation (massVector (μ.map (actualG (b := b) (c := c))))
        (massVector (ν.map (actualG (b := b) (c := c))))) := by
  simp only [massVector_map]
  exact total_variation_le_max _ _ (actual_fg hA ha hb hc hab hbc hac)
    (actual_gf hA ha hb hc hab hbc hac) (massVector μ) (massVector ν)

-- Stability and finite-TV separation identify native laws without coordinate conversion.
include hA ha hb hc hab hbc hac in
private theorem full_native_range_identification (μ ν : ProbabilityMeasure (FixedCycles A))
    (hF : μ.map (actualF (a := a) (b := b)) = ν.map (actualF (a := a) (b := b)))
    (hG : μ.map (actualG (b := b) (c := c)) = ν.map (actualG (b := b) (c := c))) : μ = ν := by
  have hupper := actual_native_upper_sum hA ha hb hc hab hbc hac μ ν
  have hf0 : totalVariation (massVector (μ.map (actualF (a := a) (b := b))))
      (massVector (ν.map (actualF (a := a) (b := b)))) = 0 :=
    (D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff _ _).mpr
      (congrArg massVector hF)
  have hg0 : totalVariation (massVector (μ.map (actualG (b := b) (c := c))))
      (massVector (ν.map (actualG (b := b) (c := c)))) = 0 :=
    (D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff _ _).mpr
      (congrArg massVector hG)
  rw [hf0, hg0, zero_add, mul_zero] at hupper
  exact massVector_injective
    ((D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff _ _).mp
      (le_antisymm hupper (D5.S3.TotalVariation.Metric.total_variation_nonneg _ _)))

-- The hypotheses are two separately supplied native laws on all actual output
-- pairs. Both observations in each pair are deletions of the same source cycle.
include hA ha hb hc hab hbc hac in
private theorem full_native_identification (μ ν : ProbabilityMeasure (FixedCycles A))
    (hF : μ.map (rawF (a := a) (b := b)) = ν.map (rawF (a := a) (b := b)))
    (hG : μ.map (rawG (b := b) (c := c)) = ν.map (rawG (b := b) (c := c))) : μ = ν := by
  have correspondence := native_range_correspondence (a := a) (b := b) (c := c) μ ν
  exact full_native_range_identification hA ha hb hc hab hbc hac μ ν
    (correspondence.1.mp hF) (correspondence.2.mp hG)

set_option pp.universes true in
#check @native_range_correspondence
#print axioms native_range_correspondence
set_option pp.universes true in
#check @full_native_identification
#print axioms full_native_identification

set_option pp.universes true in
#check @full_signed_identification
#print axioms full_signed_identification
set_option pp.universes true in
#check @full_native_range_identification
#print axioms full_native_range_identification

set_option pp.universes true in
#check @actual_native_upper_sum
#print axioms actual_native_upper_sum
set_option pp.universes true in
#check @actual_native_upper_max
#print axioms actual_native_upper_max

open D5.S3.Combinatorics.CircularWords.PairedDeletionSharpness

-- Lift the actual six-cycle witnesses to the complete legal carrier. The
-- source embedding and the two output embeddings are injective, and the
-- observation squares commute, so all three TVs survive zero extension.
include hA ha hb hc hab hbc hac in
private lemma full_sharpness : ∃ μ ν : ProbabilityMeasure (FixedCycles A),
    totalVariation (massVector μ) (massVector ν) = 1 ∧
    totalVariation (massVector (μ.map (actualF (a := a) (b := b))))
      (massVector (ν.map (actualF (a := a) (b := b)))) = 1 / 3 ∧
    totalVariation (massVector (μ.map (actualG (b := b) (c := c))))
      (massVector (ν.map (actualG (b := b) (c := c)))) = 1 / 3 := by
  classical
  obtain ⟨L, _, _, _, hlegal, _, ρ, σ, _, _, hsource, hobsF, hobsG, _, _⟩ := 
    real_probability_paired_deletion_sharpness A hA a b c ha hb hc hab hac hbc
  let J : Source a b c L → FixedCycles A := fun C => ⟨C.val, hlegal C⟩
  have hJ : Function.Injective J := by
    intro C D he
    exact Subtype.ext (congrArg (fun t : FixedCycles A => t.val) he)
  let iF : Output a b c L (F a b) → Set.range (rawF (A := A) (a := a) (b := b)) := 
    fun o => ⟨o.val, by
      obtain ⟨C,hC,hCo⟩ := Finset.mem_image.mp o.property
      exact ⟨J ⟨C,hC⟩,hCo⟩⟩
  let iG : Output a b c L (G b c) → Set.range (rawG (A := A) (b := b) (c := c)) := 
    fun o => ⟨o.val, by
      obtain ⟨C,hC,hCo⟩ := Finset.mem_image.mp o.property
      exact ⟨J ⟨C,hC⟩,hCo⟩⟩
  have hiF : Function.Injective iF := by
    intro x y he
    exact Subtype.ext (congrArg
      (fun t : Set.range (rawF (A := A) (a := a) (b := b)) => t.val) he)
  have hiG : Function.Injective iG := by
    intro x y he
    exact Subtype.ext (congrArg
      (fun t : Set.range (rawG (A := A) (b := b) (c := c)) => t.val) he)
  have commF : (actualF (a := a) (b := b)) ∘ J = iF ∘ fChannel a b c L := by
    funext C
    apply Subtype.ext
    rfl
  have commG : (actualG (b := b) (c := c)) ∘ J = iG ∘ gChannel a b c L := by
    funext C
    apply Subtype.ext
    rfl
  have pushF (p : Source a b c L → ℝ) :
      pushMass (actualF (a := a) (b := b)) (pushMass J p) =
        pushMass iF (pushMass (fChannel a b c L) p) := by
    rw [push_comp,push_comp,commF]
  have pushG (p : Source a b c L → ℝ) :
      pushMass (actualG (b := b) (c := c)) (pushMass J p) =
        pushMass iG (pushMass (gChannel a b c L) p) := by
    rw [push_comp,push_comp,commG]
  refine ⟨ρ.map J, σ.map J, ?_, ?_, ?_⟩
  · rw [massVector_map,massVector_map,embed_tv J hJ]
    exact hsource
  · simp only [massVector_map]
    rw [pushF,pushF,embed_tv iF hiF]
    simpa only [massVector_map] using hobsF
  · simp only [massVector_map]
    rw [pushG,pushG,embed_tv iG hiG]
    simpa only [massVector_map] using hobsG


include hA ha hb hc hab hbc hac in
private theorem actual_optimal_sum (K : ℝ) (hK : ∀ μ ν : ProbabilityMeasure (FixedCycles A),
    totalVariation (massVector μ) (massVector ν) ≤ K *
      (totalVariation (massVector (μ.map (actualF (a := a) (b := b))))
        (massVector (ν.map (actualF (a := a) (b := b)))) +
       totalVariation (massVector (μ.map (actualG (b := b) (c := c))))
        (massVector (ν.map (actualG (b := b) (c := c)))))) : (3 / 2 : ℝ) ≤ K := by
  obtain ⟨μ,ν,hs,hf,hg⟩ := full_sharpness hA ha hb hc hab hbc hac
  have hh := hK μ ν
  rw [hs,hf,hg] at hh
  norm_num at hh
  linarith

include hA ha hb hc hab hbc hac in
private theorem actual_optimal_max (K : ℝ) (hK : ∀ μ ν : ProbabilityMeasure (FixedCycles A),
    totalVariation (massVector μ) (massVector ν) ≤ K *
      max (totalVariation (massVector (μ.map (actualF (a := a) (b := b))))
        (massVector (ν.map (actualF (a := a) (b := b)))))
       (totalVariation (massVector (μ.map (actualG (b := b) (c := c))))
        (massVector (ν.map (actualG (b := b) (c := c)))))) : (3 : ℝ) ≤ K := by
  obtain ⟨μ,ν,hs,hf,hg⟩ := full_sharpness hA ha hb hc hab hbc hac
  have hh := hK μ ν
  rw [hs,hf,hg] at hh
  norm_num at hh
  linarith

set_option pp.universes true in
#check @full_sharpness
#print axioms full_sharpness
set_option pp.universes true in
#check @actual_optimal_sum
#print axioms actual_optimal_sum
set_option pp.universes true in
#check @actual_optimal_max
#print axioms actual_optimal_max

end ActualCycles
end LocalLeafInverseCheck

#print axioms D5.S3.TotalVariation.LocalLeafInverse.signed_l1_le
#print axioms D5.S3.TotalVariation.LocalLeafInverse.total_variation_le_sum
#print axioms D5.S3.TotalVariation.LocalLeafInverse.total_variation_le_max
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionSharpness.real_probability_paired_deletion_sharpness

set_option pp.universes true in
#check @D5.S3.Combinatorics.CircularWords.PairedDeletionLaw.signed_injective
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionLaw.signed_injective
#print axioms D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope.massVector_map
#print axioms D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope.massVector_injective

#print axioms D5.S3.TotalVariation.Metric.total_variation_nonneg
#print axioms D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff
