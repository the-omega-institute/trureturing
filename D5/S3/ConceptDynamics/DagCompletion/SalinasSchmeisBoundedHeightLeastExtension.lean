/- GID: D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension
   mirror-E: none(waiver:pure-mathematical-argument)
   anchors: []
   utility: none
   digest: Bounded-height least omega extensions. -/

/- Escape audits for ordinalSum_isLeastExtension, hasLeastOmegaExtension_of_top,
   and hasLeastOmegaExtension_iff are unfinished
   under the linked source-family issue
   https://github.com/the-omega-institute/trureturing/issues/28004.
   The proofs give the order-theoretic comparison law. A lawful enrolled observation
   and the required observational variation remain unresolved. -/

import D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisCountablePartitions
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Height
import Mathlib.Order.Minimal
import Mathlib.Order.Shrink

/-! Least omega-partitionable extensions and the effect of reversing the order. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisBoundedHeightLeastExtension

open SalinasSchmeisOmegaChainExtensionRefutation (IsExtension OmegaPartitionable)
open SalinasSchmeisCountablePartitions
  (MaximalPoints MaximalRayExtension maximalRayBase maximalRayPart maximalRayPartition
    ordinalSumBase ordinalSumPart ordinalSumPartition)

universe a u v w z

/-- The whole carrier is partitioned into parts having the prescribed inherited order type. -/
def PartitionableBy (A : Type a) (X : Type u) [PartialOrder A] [PartialOrder X] : Prop :=
  ∃ D : Set (Set X), Setoid.IsPartition D ∧ ∀ C ∈ D, Nonempty (A ≃o C)

/-- A partitionable extension admitting an order embedding into every competing extension. -/
def IsLeastExtension (A : Type a) (P : Type u) (Q : Type v)
    [PartialOrder A] [PartialOrder P] [PartialOrder Q] : Prop :=
  IsExtension P Q ∧ PartitionableBy A Q ∧
    ∀ (X : Type w) (_xOrder : PartialOrder X),
      IsExtension P X → PartitionableBy A X → Nonempty (Q ↪o X)

/-- Leastness in fixed candidate and comparison universes. -/
def HasLeastExtension (A : Type a) (P : Type u) [PartialOrder A] [PartialOrder P] : Prop :=
  ∃ (Q : Type v) (_qOrder : PartialOrder Q), IsLeastExtension.{a, u, v, w} A P Q

private theorem partitionAlongIso {A : Type a} {X : Type u} {Y : Type v}
    [PartialOrder A] [PartialOrder X] [PartialOrder Y] (e : X ≃o Y)
    (h : PartitionableBy A X) : PartitionableBy A Y := by
  obtain ⟨D, hD, hparts⟩ := h
  let E := e.toEquiv.setCongr
  refine ⟨E '' D, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨C, hC, hempty⟩
    obtain ⟨x, hx⟩ := Setoid.nonempty_of_mem_partition hD hC
    have hy : e x ∈ E C := ⟨x, hx, rfl⟩
    rw [hempty] at hy
    exact hy
  · intro y
    obtain ⟨C, ⟨hC, hx⟩, uniq⟩ := hD.2 (e.symm y)
    refine ⟨E C, ⟨⟨C, hC, rfl⟩, ⟨e.symm y, hx, e.apply_symm_apply y⟩⟩, ?_⟩
    rintro B ⟨⟨C', hC', rfl⟩, x, hx', heq⟩
    have hxy : x = e.symm y := (e.symm_apply_eq.mpr heq.symm).symm
    exact congrArg E (uniq C' ⟨hC', hxy ▸ hx'⟩)
  · rintro B ⟨C, hC, rfl⟩
    obtain ⟨i⟩ := hparts C hC
    let j : C ≃o E C :=
      { toEquiv := e.toEquiv.image C
        map_rel_iff' := fun {_ _} => e.le_iff_le }
    exact ⟨i.trans j⟩

private theorem countableOrderCopy (X : Type u) [PartialOrder X] [Countable X] :
    ∃ (Y : Type v) (_yOrder : PartialOrder Y), Nonempty (X ≃o Y) := by
  let : Small.{v} X := Countable.toSmall X
  exact ⟨Shrink.{v} X, inferInstance, ⟨orderIsoShrink.{v} X⟩⟩

private theorem exactTargetCopy {P : Type u} {X : Type z}
    [PartialOrder P] [PartialOrder X] [Countable X]
    (base : IsExtension P X) (partition : OmegaPartitionable X) :
    ∃ (Y : Type v) (_yOrder : PartialOrder Y),
      IsExtension P Y ∧ OmegaPartitionable Y ∧ Nonempty (X ≃o Y) := by
  obtain ⟨Y, yOrder, ⟨e⟩⟩ := countableOrderCopy X
  obtain ⟨p⟩ := base
  exact ⟨Y, yOrder, ⟨p.trans e.toOrderEmbedding⟩, partitionAlongIso e partition, ⟨e⟩⟩

private theorem omegaTail {X : Type w} [PartialOrder X]
    (h : OmegaPartitionable X) (x : X) : ∃ e : ℕ ↪o X, ∀ n, x < e n := by
  obtain ⟨D, hD, hparts⟩ := h
  obtain ⟨C, ⟨hC, hx⟩, _⟩ := hD.2 x
  obtain ⟨i⟩ := hparts C hC
  let k := i.symm ⟨x, hx⟩
  let shift : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono (fun n => k + n + 1) (by
    intro n m hnm
    dsimp
    omega)
  let includePart : ℕ ↪o X := i.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ C))
  refine ⟨shift.trans includePart, fun n => ?_⟩
  have hi : includePart k = x := congrArg Subtype.val (i.apply_symm_apply ⟨x, hx⟩)
  rw [← hi]
  apply includePart.strictMono
  change k < k + n + 1
  omega

private theorem ordinalSumEmbeds {P : Type u} {X : Type w} [PartialOrder P] [PartialOrder X]
    {t : P} (ht : IsTop t) (p : P ↪o X) (hX : OmegaPartitionable X) :
    Nonempty ((P ⊕ₗ ℕ) ↪o X) := by
  obtain ⟨tail, habove⟩ := omegaTail hX (p t)
  let f : P ⊕ₗ ℕ → X := Sum.elim p tail
  refine ⟨OrderEmbedding.ofMapLEIff f (fun x y => ?_)⟩
  rcases x with x | n <;> rcases y with y | m
  · exact p.le_iff_le.trans Sum.Lex.inl_le_inl_iff.symm
  · have h := (p.monotone (ht x)).trans_lt (habove m)
    exact iff_of_true h.le (Sum.Lex.inl_le_inr x m)
  · have h := (p.monotone (ht y)).trans_lt (habove n)
    exact iff_of_false h.not_ge Sum.Lex.not_inr_le_inl
  · exact tail.le_iff_le.trans Sum.Lex.inr_le_inr_iff.symm

private theorem noOmegaEmbedding {P : Type u} [PartialOrder P]
    (height : (Set.univ : Set P).chainHeight (· ≤ ·) ≠ ⊤) (e : ℕ ↪o P) : False := by
  apply height
  have h := Set.encard_le_chainHeight_of_isChain Set.univ (Set.range e)
    (Set.subset_univ _) e.monotone.isChain_range
  rwa [e.injective.encard_range, ENat.card_eq_top_of_infinite, top_le_iff] at h

private theorem maximalAbove {P : Type u} [PartialOrder P]
    (height : (Set.univ : Set P).chainHeight (· ≤ ·) ≠ ⊤) (p : P) :
    ∃ m : MaximalPoints P, p ≤ m.val := by
  have wf : WellFounded (fun x y : P => y < x) :=
    wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ =>
      noOmegaEmbedding height (OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ hf))⟩
  obtain ⟨m, hm, hmax⟩ := wf.has_min (Set.Ici p) ⟨p, le_rfl⟩
  exact ⟨⟨m, isMax_iff_forall_not_lt.mpr (fun x hmx => hmax x (hm.trans hmx.le) hmx)⟩, hm⟩

private noncomputable def restrictToBase {P : Type u} {X : Type v} {Y : Type w}
    [PartialOrder P] [PartialOrder X] [PartialOrder Y]
    (b : P ↪o X) (f : Y ↪o X) (h : ∀ y, f y ∈ Set.range b) : Y ↪o P :=
  (OrderEmbedding.ofMapLEIff (fun y : Y => (⟨f y, h y⟩ : Set.range b))
    (fun _ _ => f.le_iff_le)).trans b.orderIso.symm.toOrderEmbedding

private theorem omegaEscapesBase {P : Type u} {X : Type v} [PartialOrder P] [PartialOrder X]
    (height : (Set.univ : Set P).chainHeight (· ≤ ·) ≠ ⊤)
    (b : P ↪o X) (f : ℕ ↪o X) : ∃ n, f n ∉ Set.range b := by
  by_contra! h
  exact noOmegaEmbedding height (restrictToBase b f h)

private theorem ordinalSumDirected {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    (height : (Set.univ : Set P).chainHeight (· ≤ ·) ≠ ⊤) (hQ : OmegaPartitionable Q)
    (f : Q ↪o (P ⊕ₗ ℕ)) : Directed (· ≤ ·) (id : Q → Q) := by
  intro x y
  obtain ⟨tail, hx⟩ := omegaTail hQ x
  let e : ℕ ↪o (P ⊕ₗ ℕ) := tail.trans f
  obtain ⟨n, hn⟩ := omegaEscapesBase height ordinalSumBase e
  have tailPoint (k : ℕ) : ∃ m : ℕ, e (n + k) = Sum.inrₗ m := by
    have h := e.monotone (Nat.le_add_right n k)
    rcases he : e n with p | m
    · exact (hn ⟨p, he.symm⟩).elim
    · rw [he] at h
      rcases hh : e (n + k) with q | l
      · rw [hh] at h
        exact (Sum.Lex.not_inr_le_inl h).elim
      · exact ⟨l, rfl⟩
  classical
  let m := fun k => (tailPoint k).choose
  have hm : ∀ k, e (n + k) = Sum.inrₗ (m k) := fun k => (tailPoint k).choose_spec
  have hmono : StrictMono m := by
    intro i j hij
    have h := e.strictMono (Nat.add_lt_add_left hij n)
    rw [hm i, hm j] at h
    exact Sum.Lex.inr_lt_inr_iff.mp h
  have hcofinal : IsCofinal (Set.range m) :=
    not_bddAbove_iff_isCofinal.mp (Set.infinite_range_of_injective hmono.injective).not_bddAbove
  have hy : ∃ k, f y ≤ e (n + k) := by
    rcases f y with p | j
    · refine ⟨0, ?_⟩
      change Sum.inlₗ p ≤ e (n + 0)
      rw [hm]
      exact Sum.Lex.inl_le_inr _ _
    · obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hcofinal j
      refine ⟨k, ?_⟩
      change Sum.inrₗ j ≤ e (n + k)
      rw [hm]
      exact Sum.Lex.inr_le_inr_iff.mpr hk
  obtain ⟨k, hk⟩ := hy
  exact ⟨tail (n + k), (hx _).le, f.le_iff_le.mp hk⟩

private theorem belowRay {P : Type u} [PartialOrder P] {x : MaximalRayExtension P}
    {m : MaximalPoints P} {n : ℕ} (h : x ≤ MaximalRayExtension.ray m n) :
    (∃ p : P, p ≤ m.val ∧ x = MaximalRayExtension.base p) ∨
      ∃ k : ℕ, x = MaximalRayExtension.ray m k := by
  rcases x with p | ⟨i, k⟩
  · exact Or.inl ⟨p, h, rfl⟩
  · have hle : i.val ≤ m.val := (Prod.Lex.toLex_le_toLex'.mp h).1
    have heq : i = m := Subtype.ext (le_antisymm hle (i.property hle))
    subst i
    exact Or.inr ⟨k, rfl⟩

private theorem rayConcentration {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    [Nonempty Q] (height : (Set.univ : Set P).chainHeight (· ≤ ·) ≠ ⊤)
    (hQ : OmegaPartitionable Q) (directed : Directed (· ≤ ·) (id : Q → Q))
    (f : Q ↪o MaximalRayExtension P) :
    ∃ m : MaximalPoints P, ∀ q,
      (∃ p : P, p ≤ m.val ∧ f q = MaximalRayExtension.base p) ∨
        ∃ k : ℕ, f q = MaximalRayExtension.ray m k := by
  obtain ⟨x⟩ := (inferInstance : Nonempty Q)
  obtain ⟨tail, _⟩ := omegaTail hQ x
  obtain ⟨n, hn⟩ := omegaEscapesBase height maximalRayBase (tail.trans f)
  rcases hfn : f (tail n) with p | ⟨m, i⟩
  · exact (hn ⟨p, hfn.symm⟩).elim
  · refine ⟨m, fun q => ?_⟩
    obtain ⟨z, hqz, hnz⟩ := directed q (tail n)
    have hz : f (tail n) ≤ f z := f.monotone hnz
    rw [hfn] at hz
    rcases hfz : f z with p | ⟨j, k⟩
    · rw [hfz] at hz
      exact (False.elim hz)
    · rw [hfz] at hz
      have hle : m.val ≤ j.val := (Prod.Lex.toLex_le_toLex'.mp hz).1
      have hj : m = j := Subtype.ext (le_antisymm hle (m.property hle))
      have hq : f q ≤ f z := f.monotone hqz
      rw [hfz, ← hj] at hq
      exact belowRay hq

private theorem blockComparable {P : Type u} [PartialOrder P] {m : MaximalPoints P}
    {x y : MaximalRayExtension P}
    (hx : (∃ p : P, p ≤ m.val ∧ x = MaximalRayExtension.base p) ∨
      ∃ k : ℕ, x = MaximalRayExtension.ray m k)
    (hy : (∃ p : P, p ≤ m.val ∧ y = MaximalRayExtension.base p) ∨
      ∃ k : ℕ, y = MaximalRayExtension.ray m k)
    (h : ¬ x < MaximalRayExtension.base m.val) : x ≤ y ∨ y ≤ x := by
  rcases hx with ⟨p, hp, rfl⟩ | ⟨i, rfl⟩
  · have heq : p = m.val := by
      by_contra! hne
      exact h (maximalRayBase.strictMono (lt_of_le_of_ne hp hne))
    subst p
    rcases hy with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inr hq
    · exact Or.inl le_rfl
  · rcases hy with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inr hq
    · rcases le_total i j with hij | hji
      · exact Or.inl (Prod.Lex.toLex_le_toLex'.mpr ⟨le_rfl, fun _ => hij⟩)
      · exact Or.inr (Prod.Lex.toLex_le_toLex'.mpr ⟨le_rfl, fun _ => hji⟩)

private theorem heightContradiction {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
    [Nonempty P] (height : (Set.univ : Set P).chainHeight (· ≤ ·) ≠ ⊤)
    (noTop : ¬ ∃ t : P, IsTop t) (hQ : OmegaPartitionable Q) (p : P ↪o Q)
    (intoU : Q ↪o (P ⊕ₗ ℕ)) (intoV : Q ↪o MaximalRayExtension P) : False := by
  classical
  let a (x : P) := (maximalAbove height x).choose
  have ha (x : P) : x ≤ (a x).val := (maximalAbove height x).choose_spec
  have distinctMax (x : MaximalPoints P) : ∃ y : MaximalPoints P, x ≠ y := by
    by_contra! h
    apply noTop
    refine ⟨x.val, fun z => ?_⟩
    exact (h (a z)).symm ▸ ha z
  let : Nonempty Q := ⟨p (Classical.arbitrary P)⟩
  obtain ⟨m, hm⟩ := rayConcentration height hQ (ordinalSumDirected height hQ intoU) intoV
  let f : P ↪o MaximalRayExtension P := p.trans intoV
  have hmax (x : MaximalPoints P) : f x.val < MaximalRayExtension.base m.val := by
    by_contra h
    obtain ⟨y, hy⟩ := distinctMax x
    rcases blockComparable (hm (p x.val)) (hm (p y.val)) h with hxy | hyx
    · exact hy (Subtype.ext (le_antisymm (f.le_iff_le.mp hxy) (x.property (f.le_iff_le.mp hxy))))
    · exact hy (Subtype.ext (le_antisymm (y.property (f.le_iff_le.mp hyx)) (f.le_iff_le.mp hyx)))
  have hbelow (x : P) : f x < MaximalRayExtension.base m.val :=
    (f.monotone (ha x)).trans_lt (hmax (a x))
  have inBase (x : P) : f x ∈ Set.range maximalRayBase := by
    rcases hfx : f x with b | b
    · exact ⟨b, rfl⟩
    · have h := (hbelow x).le
      rw [hfx] at h
      exact (False.elim h)
  let g := restrictToBase maximalRayBase f inBase
  have hg (x : P) : g x < m.val := by
    have heq : maximalRayBase (g x) = f x :=
      congrArg Subtype.val (maximalRayBase.orderIso.apply_symm_apply ⟨f x, inBase x⟩)
    apply maximalRayBase.lt_iff_lt.mp
    rw [heq]
    exact hbelow x
  obtain ⟨C, _, hcard, hC⟩ :=
    Set.exists_eq_chainHeight_of_chainHeight_ne_top Set.univ (· ≤ ·) height
  have himage : IsChain (· ≤ ·) (g '' C) := IsChain.image_embedding_iff.mpr hC
  have hnot : m.val ∉ g '' C := by
    rintro ⟨x, _, hx⟩
    exact (hg x).ne hx
  have hC' : IsChain (· ≤ ·) (insert m.val (g '' C)) :=
    himage.insert (by rintro _ ⟨x, _, rfl⟩ _; exact Or.inr (hg x).le)
  have hbound := Set.encard_le_chainHeight_of_isChain Set.univ _ (Set.subset_univ _) hC'
  rw [Set.encard_insert_of_notMem hnot, g.injective.encard_image, hcard] at hbound
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp height
  rw [← hh] at hbound
  exact (not_le_of_gt (show (h : ℕ∞) < (h : ℕ∞) + 1 by exact_mod_cast Nat.lt_succ_self h)) hbound

/-- A greatest element makes the ordinal sum least, with comparison maps given by strict tails. -/
theorem ordinalSum_isLeastExtension {P : Type u} [PartialOrder P] [Countable P]
    {t : P} (ht : IsTop t) : IsLeastExtension.{0, u, u, w} ℕ P (P ⊕ₗ ℕ) := by
  let : Nonempty P := ⟨t⟩
  obtain ⟨base, S, _, part, parts⟩ := ordinalSumPartition (P := P)
  exact ⟨base, ⟨Set.range (ordinalSumPart S), part, by
    rintro _ ⟨p, rfl⟩
    exact parts p⟩,
    fun _ _ ⟨p⟩ hX => ordinalSumEmbeds ht p hX⟩

/-- A countable poset with a greatest element admits a least candidate in every universe. -/
theorem hasLeastOmegaExtension_of_top {P : Type u} [PartialOrder P] [Countable P]
    {t : P} (ht : IsTop t) : HasLeastExtension.{0, u, v, w} ℕ P := by
  obtain ⟨base, partition, least⟩ := ordinalSum_isLeastExtension.{u, w} ht
  let : Countable (P ⊕ₗ ℕ) := inferInstanceAs (Countable (P ⊕ ℕ))
  obtain ⟨Q, qOrder, p, hQ, ⟨e⟩⟩ := exactTargetCopy base partition
  refine ⟨Q, qOrder, p, hQ, fun X xOrder j hX => ?_⟩
  obtain ⟨f⟩ := least X xOrder j hX
  exact ⟨e.symm.toOrderEmbedding.trans f⟩

/-- The comparison quantifier ranges over all admissible extensions in its prescribed universe. -/
theorem hasLeastOmegaExtension_iff {P : Type u} [PartialOrder P] [Nonempty P] [Countable P]
    (height : (Set.univ : Set P).chainHeight (· ≤ ·) ≠ ⊤) :
    HasLeastExtension.{0, u, v, w} ℕ P ↔ ∃ t : P, IsTop t := by
  classical
  refine ⟨?_, fun ⟨t, ht⟩ => hasLeastOmegaExtension_of_top ht⟩
  rintro ⟨Q, qOrder, ⟨p⟩, hQ, least⟩
  by_contra noTop
  obtain ⟨baseU, S, _, partU, partsU⟩ := ordinalSumPartition (P := P)
  have admU : OmegaPartitionable (P ⊕ₗ ℕ) :=
    ⟨Set.range (ordinalSumPart S), partU, by
      rintro _ ⟨i, rfl⟩
      exact partsU i⟩
  let a (x : P) := (maximalAbove height x).choose
  obtain ⟨baseV, T, _, partV, partsV⟩ :=
    maximalRayPartition a (fun x => (maximalAbove height x).choose_spec)
  have admV : OmegaPartitionable (MaximalRayExtension P) :=
    ⟨Set.range (maximalRayPart a T), partV, by
      rintro _ ⟨i, rfl⟩
      exact partsV i⟩
  let : Countable (P ⊕ₗ ℕ) := inferInstanceAs (Countable (P ⊕ ℕ))
  let : Countable (MaximalRayExtension P) :=
    inferInstanceAs (Countable (P ⊕ (MaximalPoints P × ℕ)))
  obtain ⟨U, uOrder, bu, hu, ⟨eu⟩⟩ := exactTargetCopy baseU admU
  obtain ⟨V, vOrder, bv, hv, ⟨ev⟩⟩ := exactTargetCopy baseV admV
  obtain ⟨f⟩ := least U uOrder bu hu
  obtain ⟨g⟩ := least V vOrder bv hv
  exact heightContradiction height noTop hQ p
    (f.trans eu.symm.toOrderEmbedding) (g.trans ev.symm.toOrderEmbedding)

end D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisBoundedHeightLeastExtension
