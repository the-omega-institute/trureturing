/- GID: D5/S3/Combinatorics/Dice/RankingProfileFiniteGrid
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/RankingProfileFiniteGrid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Caratheodory, mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Compression and closedness of the finite cubic ranking test. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Instances.Real.Lemmas

/-! The finite cubic profile, its compression on ordered disjoint supports, and the
closed fifteen-label test used to take limits of quantized ranking profiles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.RankingProfileRealization

section FiniteCompression

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- The finite support of the weight function. -/
noncomputable def weightSupport (p : α → ℝ) : Finset α := by
  classical
  exact univ.filter (fun i => p i ≠ 0)

@[simp] private theorem mem_weightSupport {p : α → ℝ} {i : α} :
    i ∈ weightSupport p ↔ p i ≠ 0 := by
  classical
  simp [weightSupport]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Compress a finite convex combination of real vectors using its original input indices. -/
private theorem compressConvexCombination {n : ℕ} (v : α → Fin n → ℝ)
    (p : α → ℝ) (hp : IsProbability p) :
    ∃ q : α → ℝ, IsProbability q ∧ weightSupport q ⊆ weightSupport p ∧
      (weightSupport q).card ≤ n + 1 ∧ ∑ i, q i • v i = ∑ i, p i • v i := by
  classical
  let s := weightSupport p
  have hsum (g : α → ℝ) (hg : ∀ i ∉ s, g i = 0) :
      ∑ i : s, g i = ∑ i, g i := by
    rw [Finset.univ_eq_attach, Finset.sum_attach]
    exact Finset.sum_subset (subset_univ s) (fun i _ hi => hg i hi)
  have hsumVec :
      ∑ i : s, p i • v i = ∑ i, p i • v i := by
    rw [Finset.univ_eq_attach, Finset.sum_attach (f := fun i => p i • v i)]
    apply Finset.sum_subset (subset_univ s)
    intro i _ hi
    have hz : p i = 0 := by simpa [s] using hi
    simp [hz]
  have hull : (∑ i, p i • v i) ∈ convexHull ℝ (Set.range fun i : s => v i) :=
    mem_convexHull_of_exists_fintype (fun i : s => p i) (fun i : s => v i)
      (fun i => hp.1 i) ((hsum p (by intro i hi; simpa [s] using hi)).trans hp.2)
      (fun i => ⟨i, rfl⟩) hsumVec
  obtain ⟨ι, inst, z, w, hz, hind, hwpos, hwone, hwvec⟩ :=
    eq_pos_convex_span_of_mem_convexHull hull
  let _ : Fintype ι := inst
  have preimage (j : ι) : ∃ i : s, v i = z j := hz ⟨j, rfl⟩
  choose pick hpick using preimage
  let f : ι → α := fun j => pick j
  let q : α → ℝ := fun i => ∑ j, if f j = i then w j else 0
  have hmass : (∑ i, q i) = 1 := by
    unfold q
    rw [Finset.sum_comm]
    simpa using hwone
  have hsupport : weightSupport q ⊆ univ.image f := by
    intro i hi
    by_contra h
    have hn (j : ι) : f j ≠ i := fun hji => h (mem_image.mpr ⟨j, mem_univ _, hji⟩)
    exact mem_weightSupport.mp hi (by simp [q, hn])
  refine ⟨q, ⟨fun i => Finset.sum_nonneg fun j _ => ?_, hmass⟩,
    hsupport.trans ?_, ?_, ?_⟩
  · split_ifs
    · exact (hwpos j).le
    · exact le_rfl
  · intro i hi
    obtain ⟨j, -, rfl⟩ := mem_image.mp hi
    exact (pick j).property
  · have hd : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ n := by
      simpa only [Module.finrank_pi, Fintype.card_fin] using
        (Submodule.finrank_le (vectorSpan ℝ (Set.range z)))
    exact (Finset.card_le_card hsupport).trans
      (Finset.card_image_le.trans (by
        rw [Finset.card_univ]
        exact hind.card_le_finrank_succ.trans (Nat.add_le_add_right hd 1)))
  · unfold q
    simp only [Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simpa [show ∀ j, v (f j) = z j from hpick] using hwvec

section Ranked

variable [LinearOrder α]

/-- The probability of a strictly decreasing draw from three independent weights. -/
def rankMass (a b c : α → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, if z < y ∧ y < x then a x * b y * c z else 0

/-- The six coordinates of Eq. (7), in the order XYZ, XZY, YXZ, YZX, ZXY, ZYX. -/
def profile (a b c : α → ℝ) : Fin 6 → ℝ :=
  ![rankMass a b c, rankMass a c b, rankMass b a c,
    rankMass b c a, rankMass c a b, rankMass c b a]

private def topMass (b c : α → ℝ) (x : α) : ℝ :=
  ∑ y, ∑ z, if z < y ∧ y < x then b y * c z else 0

private def middleMass (b c : α → ℝ) (x : α) : ℝ :=
  ∑ y, ∑ z, if z < x ∧ x < y then b y * c z else 0

private def bottomMass (b c : α → ℝ) (x : α) : ℝ :=
  ∑ y, ∑ z, if x < z ∧ z < y then b y * c z else 0

private def pairMass (b c : α → ℝ) : ℝ :=
  ∑ y, ∑ z, if z < y then b y * c z else 0

private theorem rank_first (a b c : α → ℝ) :
    rankMass a b c = ∑ x, a x * topMass b c x := by
  unfold rankMass topMass
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp [mul_assoc]

private theorem rank_middle (a b c : α → ℝ) :
    rankMass b a c = ∑ x, a x * middleMass b c x := by
  unfold rankMass middleMass
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp [mul_left_comm, mul_assoc]

private theorem rank_last (a b c : α → ℝ) :
    rankMass b c a = ∑ x, a x * bottomMass b c x := by
  unfold rankMass bottomMass
  simp_rw [Finset.sum_comm (f := fun z x => if x < z ∧ z < _ then _ else _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp [mul_comm]

private theorem kernel_block (b c : α → ℝ) (x : α) (hx : b x = 0) (hc : c x = 0) :
    topMass b c x + middleMass b c x + bottomMass b c x = pairMass b c := by
  unfold topMass middleMass bottomMass pairMass
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  by_cases hyz : z < y
  · rcases lt_trichotomy x z with h | rfl | h
    · have hxy := h.trans hyz
      simp [hyz, h, not_lt_of_gt h, not_lt_of_gt hxy]
    · simp [hc]
    · rcases lt_trichotomy x y with hxy | rfl | hyx
      · simp [hyz, h, hxy, not_lt_of_gt h, not_lt_of_gt hxy]
      · simp [hx]
      · simp [hyz, hyx, not_lt_of_gt h, not_lt_of_gt hyx]
  · have hmid : ¬ (z < x ∧ x < y) := fun h => hyz (h.1.trans h.2)
    simp [hyz, hmid]

private theorem rank_block (a b c : α → ℝ) (ha : IsProbability a)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c)) :
    rankMass a b c + rankMass b a c + rankMass b c a = pairMass b c := by
  rw [rank_first a b c, rank_middle a b c, rank_last a b c]
  simp only [← Finset.sum_add_distrib, ← mul_add]
  calc
    _ = ∑ x, a x * pairMass b c := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : a x = 0
      · simp [hx]
      · have hxs := mem_weightSupport.mpr hx
        have hb : b x = 0 := by simpa using (Finset.disjoint_left.mp hab hxs)
        have hc : c x = 0 := by simpa using (Finset.disjoint_left.mp hac hxs)
        rw [kernel_block b c x hb hc]
    _ = _ := by rw [← Finset.sum_mul, ha.2, one_mul]

private def features (b c : α → ℝ) (x : α) : Fin 4 → ℝ :=
  ![topMass b c x, middleMass b c x, topMass c b x, middleMass c b x]

/-- Compress the first weight to five faces while preserving the six rankings. -/
private theorem compressFirst (a b c : α → ℝ) (ha : IsProbability a)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c)) :
    ∃ a' : α → ℝ, IsProbability a' ∧ weightSupport a' ⊆ weightSupport a ∧
      (weightSupport a').card ≤ 5 ∧ profile a' b c = profile a b c := by
  obtain ⟨a', ha', hsub, hcard, hvec⟩ := compressConvexCombination (features b c) a ha
  have hcoord (i : Fin 4) : ∑ x, a' x * features b c x i =
      ∑ x, a x * features b c x i := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hvec i
  have h0 : rankMass a' b c = rankMass a b c := by
    rw [rank_first a' b c, rank_first a b c]
    simpa [features] using hcoord 0
  have h1 : rankMass b a' c = rankMass b a c := by
    rw [rank_middle a' b c, rank_middle a b c]
    simpa [features] using hcoord 1
  have h2 : rankMass a' c b = rankMass a c b := by
    rw [rank_first a' c b, rank_first a c b]
    simpa [features] using hcoord 2
  have h3 : rankMass c a' b = rankMass c a b := by
    rw [rank_middle a' c b, rank_middle a c b]
    simpa [features] using hcoord 3
  have hab' := hab.mono_left hsub
  have hac' := hac.mono_left hsub
  have h4 : rankMass b c a' = rankMass b c a := by
    have h := rank_block a' b c ha' hab' hac'
    rw [h0, h1] at h
    exact add_left_cancel (h.trans (rank_block a b c ha hab hac).symm)
  have h5 : rankMass c b a' = rankMass c b a := by
    have h := rank_block a' c b ha' hac' hab'
    rw [h2, h3] at h
    exact add_left_cancel (h.trans (rank_block a c b ha hac hab).symm)
  exact ⟨a', ha', hsub, hcard, by simp only [profile, h0, h1, h2, h3, h4, h5]⟩

private theorem rotate_profile {a b c a' b' c' : α → ℝ}
    (h : profile a b c = profile a' b' c') :
    profile c a b = profile c' a' b' := by
  funext i
  fin_cases i
  · exact congrFun h 4
  · exact congrFun h 5
  · exact congrFun h 1
  · exact congrFun h 0
  · exact congrFun h 3
  · exact congrFun h 2

/-- Compress all three probability weights on their original ordered type. -/
private theorem compressFinite (a b c : α → ℝ)
    (ha : IsProbability a) (hb : IsProbability b) (hc : IsProbability c)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c))
    (hbc : Disjoint (weightSupport b) (weightSupport c)) :
    ∃ a' b' c' : α → ℝ,
      IsProbability a' ∧ IsProbability b' ∧ IsProbability c' ∧
      weightSupport a' ⊆ weightSupport a ∧ weightSupport b' ⊆ weightSupport b ∧
      weightSupport c' ⊆ weightSupport c ∧
      (weightSupport a').card ≤ 5 ∧ (weightSupport b').card ≤ 5 ∧
      (weightSupport c').card ≤ 5 ∧ profile a' b' c' = profile a b c := by
  obtain ⟨a', ha', hsa, hca, hpa⟩ := compressFirst a b c ha hab hac
  obtain ⟨b', hb', hsb, hcb, hpb⟩ :=
    compressFirst b c a' hb hbc (hab.mono_left hsa).symm
  obtain ⟨c', hc', hsc, hcc, hpc⟩ :=
    compressFirst c a' b' hc (hac.mono_left hsa).symm (hbc.mono_left hsb).symm
  exact ⟨a', b', c', ha', hb', hc', hsa, hsb, hsc, hca, hcb, hcc,
    (rotate_profile (rotate_profile hpc)).trans ((rotate_profile hpb).trans hpa)⟩

end Ranked

end FiniteCompression

section FiniteGrid

open scoped BigOperators

/-- The attainable profiles on `n` labels with at most `cap` positive weights per die. -/
private def finiteTest (n cap : ℕ) : Set (Fin 6 → ℝ) :=
  {v | ∃ a b c : Fin n → ℝ,
    IsProbability a ∧ IsProbability b ∧ IsProbability c ∧
    ((Finset.univ.filter fun i => 0 < a i).card ≤ cap) ∧
    ((Finset.univ.filter fun i => 0 < b i).card ≤ cap) ∧
    ((Finset.univ.filter fun i => 0 < c i).card ≤ cap) ∧
    profile a b c = v}

/-- The finite test with fifteen common ordered labels and five faces per die. -/
def finiteTest15 : Set (Fin 6 → ℝ) := finiteTest 15 5

private theorem positiveSupport_eq {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbability p) : (Finset.univ.filter fun i => 0 < p i) = weightSupport p := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_weightSupport]
  exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (hp.1 i) (Ne.symm h)⟩

private def simplexFace {n : ℕ} (s : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {p | IsProbability p ∧ ∀ i ∉ s, p i = 0}

private theorem isCompact_simplexFace {n : ℕ} (s : Finset (Fin n)) :
    IsCompact (simplexFace s) := by
  classical
  have hFace : simplexFace s =
      ((⋂ i : Fin n, {p : Fin n → ℝ | 0 ≤ p i}) ∩
        {p : Fin n → ℝ | ∑ i, p i = 1}) ∩
      (⋂ i : {i : Fin n // i ∉ s}, {p : Fin n → ℝ | p i = 0}) := by
    ext p
    simp [simplexFace, IsProbability]
  have hClosed : IsClosed (simplexFace s) := by
    rw [hFace]
    refine (IsClosed.inter (isClosed_iInter fun i => ?_) ?_).inter
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i)
        continuous_const
    · exact isClosed_eq (continuous_apply i.val) continuous_const
  have hBox : IsCompact (Set.Icc (0 : Fin n → ℝ) 1) := isCompact_Icc
  refine hBox.of_isClosed_subset hClosed ?_
  intro p hp
  change IsProbability p ∧ (∀ i ∉ s, p i = 0) at hp
  refine ⟨hp.1.1, fun i => ?_⟩
  change p i ≤ (1 : ℝ)
  rw [← hp.1.2]
  exact Finset.single_le_sum (f := p) (fun j _ => hp.1.1 j) (Finset.mem_univ i)

private def cappedSimplex (n cap : ℕ) : Set (Fin n → ℝ) :=
  ⋃ s : {s : Finset (Fin n) // s.card ≤ cap}, simplexFace s.val

private theorem mem_cappedSimplex {n cap : ℕ} {p : Fin n → ℝ} :
    p ∈ cappedSimplex n cap ↔
      IsProbability p ∧ (Finset.univ.filter fun i => 0 < p i).card ≤ cap := by
  simp only [cappedSimplex, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨s, hs⟩, hp, hz⟩
    refine ⟨hp, ?_⟩
    rw [positiveSupport_eq hp]
    refine (Finset.card_le_card (show weightSupport p ⊆ s from ?_)).trans hs
    intro i hi
    exact Classical.byContradiction fun h => mem_weightSupport.mp hi (hz i h)
  · rintro ⟨hp, hCard⟩
    rw [positiveSupport_eq hp] at hCard
    exact ⟨⟨weightSupport p, hCard⟩, hp, fun i hi => by simpa using hi⟩

private theorem continuous_profile {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      profile p.1 p.2.1 p.2.2) := by
  have rank {X : Type} [TopologicalSpace X] {a b c : X → Fin n → ℝ}
      (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
      Continuous (fun p => rankMass (a p) (b p) (c p)) := by
    unfold rankMass
    refine continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    by_cases h : k < j ∧ j < i
    · simp only [ite_eq_left h]
      have hai : Continuous (fun p => a p i) := (continuous_apply i).comp ha
      have hbj : Continuous (fun p => b p j) := (continuous_apply j).comp hb
      have hck : Continuous (fun p => c p k) := (continuous_apply k).comp hc
      exact (hai.mul hbj).mul hck
    · simp only [ite_eq_right h]
      exact continuous_const
  have ha : Continuous (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → _) :=
    continuous_fst
  have hb : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.2) :=
    continuous_snd.comp continuous_snd
  apply continuous_pi
  intro i
  fin_cases i
  · exact rank ha hb hc
  · exact rank ha hc hb
  · exact rank hb ha hc
  · exact rank hb hc ha
  · exact rank hc ha hb
  · exact rank hc hb ha

/-- The profile image of the finite union of products of simplex faces is compact. -/
private theorem isCompact_finiteTest (n cap : ℕ) : IsCompact (finiteTest n cap) := by
  have h : IsCompact (cappedSimplex n cap) :=
    isCompact_iUnion fun s => isCompact_simplexFace s.val
  have hImage : (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      profile p.1 p.2.1 p.2.2) '' ((cappedSimplex n cap).prod
        ((cappedSimplex n cap).prod (cappedSimplex n cap))) = finiteTest n cap := by
    ext v
    constructor
    · rintro ⟨⟨a, b, c⟩, ⟨ha, hb, hc⟩, hv⟩
      obtain ⟨ha, hca⟩ := mem_cappedSimplex.mp ha
      obtain ⟨hb, hcb⟩ := mem_cappedSimplex.mp hb
      obtain ⟨hc, hcc⟩ := mem_cappedSimplex.mp hc
      exact ⟨a, b, c, ha, hb, hc, hca, hcb, hcc, hv⟩
    · rintro ⟨a, b, c, ha, hb, hc, hca, hcb, hcc, hv⟩
      exact ⟨(a, b, c), ⟨mem_cappedSimplex.mpr ⟨ha, hca⟩,
        mem_cappedSimplex.mpr ⟨hb, hcb⟩, mem_cappedSimplex.mpr ⟨hc, hcc⟩⟩, hv⟩
  rw [← hImage]
  exact (h.prod (h.prod h)).image continuous_profile

private theorem isClosed_finiteTest (n cap : ℕ) : IsClosed (finiteTest n cap) :=
  (isCompact_finiteTest n cap).isClosed

theorem isClosed_finiteTest15 : IsClosed finiteTest15 :=
  isClosed_finiteTest 15 5

section Relabel

variable {ι α : Type*} [Fintype ι] [Fintype α]

private theorem sum_reindex (e : ι ↪ α) (f : α → ℝ)
    (hz : ∀ x ∉ Set.range e, f x = 0) :
    (∑ i, f (e i)) = ∑ x, f x := by
  rw [← Finset.sum_map]
  refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hz x ?_
  rintro ⟨i, rfl⟩
  exact hx (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem probability_comp (e : ι ↪ α) {p : α → ℝ} (hp : IsProbability p)
    (hz : ∀ x ∉ Set.range e, p x = 0) : IsProbability (fun i => p (e i)) :=
  ⟨fun i => hp.1 (e i), (sum_reindex e p hz).trans hp.2⟩

private theorem card_weightSupport_comp (e : ι ↪ α) (p : α → ℝ)
    (hz : ∀ x ∉ Set.range e, p x = 0) :
    (weightSupport (fun i => p (e i))).card = (weightSupport p).card := by
  have hMap : (weightSupport (fun i => p (e i))).map e = weightSupport p := by
    ext x
    simp only [Finset.mem_map, mem_weightSupport]
    constructor
    · rintro ⟨_, hi, rfl⟩
      exact hi
    · intro hx
      have hr : x ∈ Set.range e := Classical.byContradiction fun h => hx (hz x h)
      obtain ⟨i, rfl⟩ := hr
      exact ⟨i, hx, rfl⟩
  rw [← hMap, Finset.card_map]

variable [LinearOrder ι] [LinearOrder α]

private theorem rankMass_comp (e : ι ↪o α) (a b c : α → ℝ)
    (ha : ∀ x ∉ Set.range e, a x = 0) (hb : ∀ x ∉ Set.range e, b x = 0)
    (hc : ∀ x ∉ Set.range e, c x = 0) :
    rankMass (fun i => a (e i)) (fun i => b (e i)) (fun i => c (e i)) =
      rankMass a b c := by
  let term (x y z : α) := if z < y ∧ y < x then a x * b y * c z else 0
  calc
    _ = ∑ i, ∑ j, ∑ k, term (e i) (e j) (e k) := by
      simp only [rankMass, term, e.lt_iff_lt]
    _ = ∑ x, ∑ y, ∑ z, term x y z := by
      calc
        _ = ∑ i, ∑ j, ∑ z, term (e i) (e j) z := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            sum_reindex e.toEmbedding (term (e i) (e j)) ?_
          intro z hz
          simp [term, hc z hz]
        _ = ∑ i, ∑ y, ∑ z, term (e i) y z := by
          refine Finset.sum_congr rfl fun i _ =>
            sum_reindex e.toEmbedding (fun y => ∑ z, term (e i) y z) ?_
          intro y hy
          simp [term, hb y hy]
        _ = _ := by
          refine sum_reindex e.toEmbedding (fun x => ∑ y, ∑ z, term x y z) ?_
          intro x hx
          simp [term, ha x hx]
    _ = _ := rfl

/-- Restricting to an increasing enumeration that contains all three supports preserves the
existing six coordinates in their original order. -/
private theorem profile_comp_orderEmbedding (e : ι ↪o α) (a b c : α → ℝ)
    (ha : ∀ x ∉ Set.range e, a x = 0) (hb : ∀ x ∉ Set.range e, b x = 0)
    (hc : ∀ x ∉ Set.range e, c x = 0) :
    profile (fun i => a (e i)) (fun i => b (e i)) (fun i => c (e i)) =
      profile a b c := by
  simp only [profile, rankMass_comp e a b c ha hb hc, rankMass_comp e a c b ha hc hb,
    rankMass_comp e b a c hb ha hc, rankMass_comp e b c a hb hc ha,
    rankMass_comp e c a b hc ha hb, rankMass_comp e c b a hc hb ha]

end Relabel

/-- Sort a finite set containing the three supports and pad the remaining labels with zeros. -/
private theorem profile_mem_finiteTest_of_support_subset {α : Type*} [Fintype α] [LinearOrder α]
    {n cap : ℕ} (a b c : α → ℝ) (ha : IsProbability a) (hb : IsProbability b)
    (hc : IsProbability c) (s : Finset α) (hs : s.card ≤ n)
    (hsa : weightSupport a ⊆ s) (hsb : weightSupport b ⊆ s) (hsc : weightSupport c ⊆ s)
    (hca : (weightSupport a).card ≤ cap) (hcb : (weightSupport b).card ≤ cap)
    (hcc : (weightSupport c).card ≤ cap) :
    profile a b c ∈ finiteTest n cap := by
  let e := s.orderEmbOfFin rfl
  let d := Fin.castLEOrderEmb hs
  let pad (p : α → ℝ) : Fin n → ℝ := Function.extend d (fun i => p (e i)) (fun _ => 0)
  have hzero {p : α → ℝ} (hp : weightSupport p ⊆ s) :
      ∀ x ∉ Set.range e, p x = 0 := by
    intro x hx
    by_contra h
    exact hx ((s.range_orderEmbOfFin rfl).symm ▸ show x ∈ (s : Set α) from
      hp (mem_weightSupport.mpr h))
  have hPad (p : α → ℝ) (i : Fin s.card) : pad p (d i) = p (e i) :=
    d.injective.extend_apply _ _ i
  have hPadZero (p : α → ℝ) : ∀ x ∉ Set.range d, pad p x = 0 := by
    intro x hx
    exact Function.extend_apply' _ _ _ hx
  have hPadProb (p : α → ℝ) (hp : IsProbability p) (hsp : weightSupport p ⊆ s) :
      IsProbability (pad p) := by
    refine ⟨fun x => ?_, ?_⟩
    · by_cases hx : x ∈ Set.range d
      · obtain ⟨i, rfl⟩ := hx
        rw [hPad]
        exact hp.1 _
      · rw [hPadZero p x hx]
    · rw [← sum_reindex d.toEmbedding (pad p) (hPadZero p)]
      change (∑ i, pad p (d i)) = 1
      simp only [hPad]
      exact (probability_comp e.toEmbedding hp (hzero hsp)).2
  have hCard (p : α → ℝ) (hp : IsProbability (pad p)) (hsp : weightSupport p ⊆ s) :
      (Finset.univ.filter fun i => 0 < pad p i).card = (weightSupport p).card := by
    rw [positiveSupport_eq hp, ← card_weightSupport_comp d.toEmbedding (pad p) (hPadZero p)]
    change (weightSupport (fun i => pad p (d i))).card = (weightSupport p).card
    simp only [hPad]
    exact card_weightSupport_comp e.toEmbedding p (hzero hsp)
  have hpa := hPadProb a ha hsa
  have hpb := hPadProb b hb hsb
  have hpc := hPadProb c hc hsc
  refine ⟨pad a, pad b, pad c, hpa, hpb, hpc, ?_, ?_, ?_, ?_⟩
  · rw [hCard a hpa hsa]
    exact hca
  · rw [hCard b hpb hsb]
    exact hcb
  · rw [hCard c hpc hsc]
    exact hcc
  · rw [← profile_comp_orderEmbedding d (pad a) (pad b) (pad c)
      (hPadZero a) (hPadZero b) (hPadZero c)]
    simp only [hPad]
    exact profile_comp_orderEmbedding e a b c (hzero hsa) (hzero hsb) (hzero hsc)

/-- Three finite probability weights on a common linear order with pairwise disjoint supports
give a profile in the fifteen-label finite test. -/
theorem profile_mem_finiteTest15 {α : Type*} [Fintype α] [LinearOrder α]
    (a b c : α → ℝ) (ha : IsProbability a) (hb : IsProbability b) (hc : IsProbability c)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c))
    (hbc : Disjoint (weightSupport b) (weightSupport c)) :
    profile a b c ∈ finiteTest15 := by
  obtain ⟨a', b', c', ha', hb', hc', -, -, -, hca, hcb, hcc, hp⟩ :=
    compressFinite a b c ha hb hc hab hac hbc
  let s := weightSupport a' ∪ weightSupport b' ∪ weightSupport c'
  have hs : s.card ≤ 15 := by
    have hab' := Finset.card_union_le (weightSupport a') (weightSupport b')
    have habc' := Finset.card_union_le (weightSupport a' ∪ weightSupport b') (weightSupport c')
    change (weightSupport a' ∪ weightSupport b' ∪ weightSupport c').card ≤ 15
    omega
  rw [← hp]
  apply profile_mem_finiteTest_of_support_subset a' b' c' ha' hb' hc' s hs
      _ _ _ hca hcb hcc
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · exact Finset.subset_union_right.trans Finset.subset_union_left
  · exact Finset.subset_union_right

end FiniteGrid

end D5.S3.Combinatorics.Dice.RankingProfileRealization
