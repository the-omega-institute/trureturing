/- GID: D5/S3/Topology/AlmostDisjoint/ThresholdPartitionerElimination
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/ThresholdPartitionerElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-limit pairing eliminates every actual threshold-separating partitioner. -/

import D5.S3.Topology.AlmostDisjoint.BranchColorFiber
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Basic

open Set Filter Topology
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily
open D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal
open D5.S3.Topology.AlmostDisjoint.ColorFiberDiagonal
open D5.S3.Topology.AlmostDisjoint.BranchColorFiber
open scoped Cardinal Ordinal

namespace D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination


universe u

-- A reusable recursion lemma; planned as a consumed private supplier of the
-- actual no-threshold-partitioner theorem, not as a separate thin delivery.
private theorem exists_fresh_color_selection {ι α : Type u}
    [LinearOrder ι] [WellFoundedLT ι]
    (c : Cardinal) (F : ι → Bool → Set α)
    (hsmall : ∀ i : ι, Cardinal.mk (Iio i × Bool) < c)
    (hlarge : ∀ i b, Cardinal.mk (F i b) = c)
    (hdisj : ∀ i, Disjoint (F i false) (F i true)) :
    ∃ f : ι × Bool → α, Function.Injective f ∧ ∀ i b, f (i, b) ∈ F i b := by
  classical
  let old (i : ι) (p : ∀ j : ι, j < i → Bool → α) : Set α :=
    range (fun q : Iio i × Bool => p q.1.val q.1.property q.2)
  have fresh (i : ι) (p : ∀ j : ι, j < i → Bool → α) (b : Bool) :
      (F i b \ old i p).Nonempty := by
    apply Cardinal.sdiff_nonempty_of_mk_lt_mk
    rw [hlarge]
    exact (Cardinal.mk_range_le).trans_lt (hsmall i)
  let step (i : ι) (p : ∀ j : ι, j < i → Bool → α) : Bool → α :=
    fun b => (fresh i p b).choose
  have hstep (i : ι) (p : ∀ j : ι, j < i → Bool → α) (b : Bool) :
      step i p b ∈ F i b ∧ step i p b ∉ old i p :=
    (fresh i p b).choose_spec
  let f₀ : ι → Bool → α := WellFoundedLT.fix step
  have hfix (i : ι) : f₀ i = step i (fun j _ => f₀ j) :=
    WellFoundedLT.fix_eq step i
  have hmem (i : ι) (b : Bool) : f₀ i b ∈ F i b := by
    rw [hfix]
    exact (hstep i (fun j _ => f₀ j) b).1
  have havoid (i j : ι) (hji : j < i) (b b' : Bool) : f₀ i b ≠ f₀ j b' := by
    intro heq
    have hn := (hstep i (fun j _ => f₀ j) b).2
    rw [← hfix] at hn
    apply hn
    exact ⟨(⟨j, hji⟩, b'), heq.symm⟩
  have hpair (i : ι) : Function.Injective (f₀ i) := by
    intro b b' heq
    cases b <;> cases b'
    · rfl
    · exact False.elim (Set.disjoint_left.mp (hdisj i)
        (heq ▸ hmem i false) (hmem i true))
    · exact False.elim (Set.disjoint_left.mp (hdisj i)
        (hmem i false) (heq ▸ hmem i true))
    · rfl
  refine ⟨fun q => f₀ q.1 q.2, ?_, hmem⟩
  rintro ⟨i, b⟩ ⟨j, b'⟩ heq
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (havoid j i hij b' b heq.symm)
  · subst j
    exact congrArg (Prod.mk i) (hpair i heq)
  · exact False.elim (havoid i j hij b b' heq)




private noncomputable def mate {ι α : Type*} (f : ι × Bool → α) (x : α) : α := by
  classical
  exact if hx : x ∈ range f then
    f ((Classical.choose hx).1, !(Classical.choose hx).2)
  else x

private theorem mate_apply {ι α : Type*} (f : ι × Bool → α) (hf : Function.Injective f)
    (i : ι) (b : Bool) : mate f (f (i, b)) = f (i, !b) := by
  classical
  unfold mate
  split_ifs with h
  · have hpre : Classical.choose h = (i, b) := hf (Classical.choose_spec h)
    rw [hpre]
  · exact False.elim (h (mem_range_self (i, b)))

private theorem mate_involutive {ι α : Type*} (f : ι × Bool → α) (hf : Function.Injective f) :
    Function.Involutive (mate f) := by
  classical
  intro x
  by_cases hx : x ∈ range f
  · obtain ⟨⟨i, b⟩, rfl⟩ := hx
    simp only [mate_apply f hf, Bool.not_not]
  · simp only [mate, hx, not_false_eq_true, dif_neg]

private theorem mate_limit {ι α Y : Type*} (f : ι × Bool → α) (hf : Function.Injective f)
    (l : α → Y) (hl : ∀ i, l (f (i, false)) = l (f (i, true))) (x : α) :
    l (mate f x) = l x := by
  classical
  by_cases hx : x ∈ range f
  · obtain ⟨⟨i, b⟩, rfl⟩ := hx
    rw [mate_apply f hf]
    cases b
    · exact (hl i).symm
    · exact hl i
  · simp only [mate, hx, not_false_eq_true, dif_neg]




-- Finite pairing changes the generators but not the generated ideal. This
-- supplier needs no involution hypothesis and is consumed by the same main
-- construction.
private theorem merge_finiteUnionIdeal {ι α : Type*} (M : ι → Set α)
    (p : ι → ι) (E : Set α) :
    InFiniteUnionIdeal (fun x => M x ∪ M (p x)) E ↔ InFiniteUnionIdeal M E := by
  classical
  constructor
  · rintro ⟨F, K, hK, h⟩
    refine ⟨F ∪ F.image p, K, hK, ?_⟩
    intro a ha
    rcases h ha with hF | hKa
    · left
      obtain ⟨i, hi⟩ := mem_iUnion.mp hF
      obtain ⟨hiF, hai⟩ := mem_iUnion.mp hi
      rcases hai with hai | hapi
      · exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
          ⟨Finset.mem_union_left _ hiF, hai⟩⟩
      · exact mem_iUnion.mpr ⟨p i, mem_iUnion.mpr
          ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hiF, rfl⟩), hapi⟩⟩
    · exact Or.inr hKa
  · rintro ⟨F, K, hK, h⟩
    refine ⟨F, K, hK, ?_⟩
    intro a ha
    rcases h ha with hF | hKa
    · left
      obtain ⟨i, hi⟩ := mem_iUnion.mp hF
      obtain ⟨hiF, hai⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiF, Or.inl hai⟩⟩
    · exact Or.inr hKa

-- The actual merged family is the image, since paired labels name the same member.
private theorem merge_involution_mad {ι α : Type*} (M : ι → Set α)
    (hmad : MADFamily (range M))
    (had : ∀ x y, x ≠ y → (M x ∩ M y).Finite)
    (mate : ι → ι) (hinv : Function.Involutive mate) :
    MADFamily (range (fun x => M x ∪ M (mate x))) := by
  let N : ι → Set α := fun x => M x ∪ M (mate x)
  have hsym (x : ι) : N (mate x) = N x := by
    simp only [N, hinv x, union_comm]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro A ⟨x, rfl⟩
    exact (hmad.1.1 (M x) (mem_range_self x)).mono subset_union_left
  · rintro A ⟨x, rfl⟩ B ⟨y, rfl⟩ hne
    have hxy : x ≠ y := fun h => hne (congrArg N h)
    have hxmy : x ≠ mate y := fun h => hne ((congrArg N h).trans (hsym y))
    have hmxy : mate x ≠ y := fun h => hne ((hsym x).symm.trans (congrArg N h))
    have hmxmy : mate x ≠ mate y := fun h => hxy (hinv.injective h)
    change ((M x ∪ M (mate x)) ∩ (M y ∪ M (mate y))).Finite
    rw [union_inter_distrib_right, inter_union_distrib_left, inter_union_distrib_left]
    exact ((had x y hxy).union (had x (mate y) hxmy)).union
      ((had (mate x) y hmxy).union (had (mate x) (mate y) hmxmy))
  · intro E hE
    obtain ⟨A, ⟨x, rfl⟩, hi⟩ := hmad.2 E hE
    exact ⟨N x, mem_range_self x, hi.mono (inter_subset_inter_right _ subset_union_left)⟩




-- Enumerate actual separators and choose globally disjoint opposite-color pairs.
private def ThresholdSeparator (M : Branch → Set ℕ) :=
  {D : Set ℕ // Partitions M D ∧
    {n | (natValue n : ℝ) ≤ (1 : ℝ)/3} ⊆ D ∧
    D ⊆ {n | (natValue n : ℝ) < (2 : ℝ)/3}}

private theorem exists_actual_disjoint_threshold_pairs (M : Branch → Set ℕ)
    (hbranch : ∀ x, natBranch x ⊆ M x) (hmad : MADFamily (range M))
    (hc : ∀ x, ConvergesOn natValue (M x) (limitValue x))
    (hlarge : ∀ r V, V ∈ 𝓝 r → ¬ InFiniteUnionIdeal M (natValue ⁻¹' V)) :
    ∃ (I : Type) (e : I ≃ ThresholdSeparator M) (f : I × Bool → Branch),
      Function.Injective f ∧ ∀ i,
        limitValue (f (i, false)) = limitValue (f (i, true)) ∧
        (M (f (i, false)) \ (e i).val).Finite ∧
        (M (f (i, true)) ∩ (e i).val).Finite := by
  classical
  let κ : Cardinal := Cardinal.mk (ThresholdSeparator M)
  let E : Type := κ.ord.ToType
  have hcard : Cardinal.mk E = Cardinal.mk (ThresholdSeparator M) :=
    Cardinal.mk_ord_toType κ
  let e : E ≃ ThresholdSeparator M := Classical.choice (Cardinal.eq.mp hcard)
  have hκ : κ ≤ Cardinal.continuum :=
    (Cardinal.mk_subtype_le _).trans_eq Cardinal.mk_set_nat
  let r : E → unitInterval := fun i =>
    (threshold_common_color_support M hlarge (e i).val
      (e i).property.2.1 (e i).property.2.2).choose
  have hr (i : E) : r i ∈ ColorSupport M natValue (e i).val ∩
      ColorSupport M natValue (e i).valᶜ :=
    (threshold_common_color_support M hlarge (e i).val
      (e i).property.2.1 (e i).property.2.2).choose_spec
  let F : E → Bool → Set Branch := fun i b =>
    if b then {x | limitValue x = r i ∧ (M x ∩ (e i).val).Finite}
    else {x | limitValue x = r i ∧ (M x \ (e i).val).Finite}
  have hsmall (i : E) : Cardinal.mk (Iio i × Bool) < Cardinal.continuum := by
    have hseg : Cardinal.mk (Iio i) < κ := by
      have hinit : Cardinal.ord (Cardinal.mk E) = typeLT E := by
        simp only [E, Cardinal.mk_ord_toType, Ordinal.type_toType]
      simpa only [E, Cardinal.mk_ord_toType] using Cardinal.mk_Iio_lt i hinit
    simpa only [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_bool, Nat.cast_ofNat] using
      Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum (hseg.trans_le hκ)
        (Cardinal.nat_lt_continuum 2)
  have hfiber (i : E) (b : Bool) : Cardinal.mk (F i b) = Cardinal.continuum := by
    cases b
    · exact partitioner_fiber_continuum M hbranch hmad hc (e i).val
        (e i).property.1 (r i) (hr i).1
    · have hp : Partitions M (e i).valᶜ := by
        intro x
        rcases (e i).property.1 x with h | h
        · exact Or.inr (by simpa only [Set.sdiff_eq] using h)
        · exact Or.inl (by simpa only [Set.sdiff_compl] using h)
      let ef : F i true ≃ {x : Branch //
          limitValue x = r i ∧ (M x \ (e i).valᶜ).Finite} :=
        Equiv.subtypeEquivRight (fun x => by simp [F])
      exact (Cardinal.mk_congr ef).trans
        (partitioner_fiber_continuum M hbranch hmad hc (e i).valᶜ hp (r i) (hr i).2)
  have hdisj (i : E) : Disjoint (F i false) (F i true) := by
    apply Set.disjoint_left.mpr
    intro x hx0 hx1
    have h0 : (M x \ (e i).val).Finite := hx0.2
    have h1 : (M x ∩ (e i).val).Finite := hx1.2
    apply hmad.1.1 (M x) (mem_range_self x)
    apply (h0.union h1).subset
    intro n hn
    by_cases hd : n ∈ (e i).val
    · exact Or.inr ⟨hn, hd⟩
    · exact Or.inl ⟨hn, hd⟩
  obtain ⟨f, hf, hm⟩ := exists_fresh_color_selection Cardinal.continuum F hsmall hfiber hdisj
  refine ⟨E, e, f, hf, ?_⟩
  intro i
  have h0 : limitValue (f (i, false)) = r i ∧
      (M (f (i, false)) \ (e i).val).Finite := hm i false
  have h1 : limitValue (f (i, true)) = r i ∧
      (M (f (i, true)) ∩ (e i).val).Finite := hm i true
  exact ⟨h0.1.trans h1.1.symm, h0.2, h1.2⟩




private theorem eliminate_threshold_partitioners (M : Branch → Set ℕ)
    (hbranch : ∀ x, natBranch x ⊆ M x) (hmad : MADFamily (range M))
    (had : ∀ x y, x ≠ y → (M x ∩ M y).Finite)
    (hc : ∀ x, ConvergesOn natValue (M x) (limitValue x))
    (hlarge : ∀ r V, V ∈ 𝓝 r → ¬ InFiniteUnionIdeal M (natValue ⁻¹' V)) :
    ∃ N : Branch → Set ℕ,
      (∀ x, M x ⊆ N x) ∧ MADFamily (range N) ∧
      (∀ x, ConvergesOn natValue (N x) (limitValue x)) ∧
      (∀ r V, V ∈ 𝓝 r → ¬ InFiniteUnionIdeal N (natValue ⁻¹' V)) ∧
      ¬ ∃ D : Set ℕ, Partitions N D ∧
        {n | (natValue n : ℝ) ≤ (1 : ℝ)/3} ⊆ D ∧
        D ⊆ {n | (natValue n : ℝ) < (2 : ℝ)/3} := by
  classical
  obtain ⟨I, e, f, hf, hpairs⟩ :=
    exists_actual_disjoint_threshold_pairs M hbranch hmad hc hlarge
  let p : Branch → Branch := mate f
  have hinv : Function.Involutive p := mate_involutive f hf
  have hlim (x : Branch) : limitValue (p x) = limitValue x :=
    mate_limit f hf limitValue (fun i => (hpairs i).1) x
  let N : Branch → Set ℕ := fun x => M x ∪ M (p x)
  have hsub (x : Branch) : M x ⊆ N x := subset_union_left
  have hconv (x : Branch) : ConvergesOn natValue (N x) (limitValue x) := by
    have hfinite : ({M x, M (p x)} : Set (Set ℕ)).Finite :=
      (finite_singleton _).insert _
    have h := finite_sUnion_converges natValue {M x, M (p x)} hfinite (limitValue x)
      (by
        intro A hA
        simp only [mem_insert_iff, mem_singleton_iff] at hA
        rcases hA with rfl | rfl
        · exact hc x
        · simpa only [hlim x] using hc (p x))
    simpa only [sUnion_insert, sUnion_singleton, N] using h
  have hlargeN : ∀ r V, V ∈ 𝓝 r → ¬ InFiniteUnionIdeal N (natValue ⁻¹' V) := by
    intro r V hV hsmall
    apply hlarge r V hV
    exact (merge_finiteUnionIdeal M p (natValue ⁻¹' V)).mp hsmall
  refine ⟨N, hsub, merge_involution_mad M hmad had p hinv, hconv, hlargeN, ?_⟩
  rintro ⟨D, hD, hlower, hupper⟩
  have hDold : Partitions M D := by
    intro x
    rcases hD x with h | h
    · exact Or.inl (h.subset (sdiff_subset_sdiff (hsub x) Subset.rfl))
    · exact Or.inr (h.subset (inter_subset_inter_left D (hsub x)))
  let d : ThresholdSeparator M := ⟨D, hDold, hlower, hupper⟩
  let i : I := e.symm d
  have hei : (e i).val = D := congrArg Subtype.val (e.apply_symm_apply d)
  let x := f (i, false)
  let y := f (i, true)
  have hxy : p x = y := mate_apply f hf i false
  have h0 : (M x \ D).Finite := by
    simpa only [x, hei] using (hpairs i).2.1
  have h1 : (M y ∩ D).Finite := by
    simpa only [y, hei] using (hpairs i).2.2
  have hinf0 : (M x ∩ D).Infinite :=
    (hmad.1.1 (M x) (mem_range_self x)).inter_of_finite_sdiff h0
  have hinf1 : (M y \ D).Infinite := by
    intro hfin
    apply hmad.1.1 (M y) (mem_range_self y)
    apply (hfin.union h1).subset
    intro n hn
    by_cases hd : n ∈ D
    · exact Or.inr ⟨hn, hd⟩
    · exact Or.inl ⟨hn, hd⟩
  have hysub : M y ⊆ N x := by
    rw [show N x = M x ∪ M y by simp only [N, hxy]]
    exact subset_union_right
  rcases hD x with h | h
  · exact hinf1 (h.subset (sdiff_subset_sdiff hysub Subset.rfl))
  · exact hinf0 (h.subset (inter_subset_inter_left D (hsub x)))

-- Actual existence, consuming the preceding construction. The final family
-- is range N: paired labels may name the same actual member, so no false
-- labelwise almost-disjointness assertion occurs here.
theorem exists_mad_no_threshold_partitioner :
    ∃ N : Branch → Set ℕ,
      (∀ x, natBranch x ⊆ N x) ∧ MADFamily (range N) ∧
      (∀ x, ConvergesOn natValue (N x) (limitValue x)) ∧
      (∀ r V, V ∈ 𝓝 r → ¬ InFiniteUnionIdeal N (natValue ⁻¹' V)) ∧
      ¬ ∃ D : Set ℕ, Partitions N D ∧
        {n | (natValue n : ℝ) ≤ (1 : ℝ)/3} ⊆ D ∧
        D ⊆ {n | (natValue n : ℝ) < (2 : ℝ)/3} := by
  obtain ⟨M, hbranch, had, hmad, hc, hlarge⟩ := exists_mad_with_no_small_neighborhood
  obtain ⟨N, hsub, hmadN, hcN, hlargeN, hno⟩ :=
    eliminate_threshold_partitioners M hbranch hmad had hc hlarge
  exact ⟨N, fun x => (hbranch x).trans (hsub x), hmadN, hcN, hlargeN, hno⟩


end D5.S3.Topology.AlmostDisjoint.ThresholdPartitionerElimination
