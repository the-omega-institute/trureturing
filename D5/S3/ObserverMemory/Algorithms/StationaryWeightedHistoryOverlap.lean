/- GID: D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unary histories retain multiplicity in background-sensitive overlap charging. -/

import D5.S3.ObserverMemory.Algorithms.StationaryHistorySlotGraph
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.PNat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.StationaryWeightedHistoryOverlap

open StationaryUnitControl StationaryReadHistory StationaryHistorySlotGraph
open scoped BigOperators NNReal
open private literal_le_tail history_target core_subset from
  D5.S3.ObserverMemory.Algorithms.StationaryHistoryCore
attribute [local instance] Classical.propDecidable

universe u
variable {P ell h : Nat} {Q : Type u} (C : Controller P Q) (hP : 1 < P)
  (I : Initialized C hP ell h) [NeZero (3 * P)] [DecidableEq Q]

def OrdinaryParent (n : Node C hP I) : Prop :=
  (children C hP I n).card = 1 ∧ ¬BackgroundParent C hP I n
abbrev Ordinary := {n : Node C hP I // OrdinaryParent C hP I n}

noncomputable def ordinaryChild (d : Ordinary C hP I) : Node C hP I :=
  Classical.choose (Finset.card_pos.mp (show 0 < (children C hP I d.val).card by
    rw [d.property.1]; omega))

private theorem ordinary_child_parent (d : Ordinary C hP I) :
    parent C hP I (ordinaryChild C hP I d) = some d.val := by
  exact (Finset.mem_filter.mp (Classical.choose_spec (Finset.card_pos.mp
    (show 0 < (children C hP I d.val).card by rw [d.property.1]; omega)))).2

private theorem ordinary_child_injective : Function.Injective (ordinaryChild C hP I) := by
  intro a b he
  have ha := ordinary_child_parent C hP I a
  rw [he,ordinary_child_parent C hP I b] at ha
  exact Subtype.ext (Option.some.inj ha.symm)

noncomputable def ordinaryChildren (q : Q) : Finset (Node C hP I) :=
  (Finset.univ.filter (fun d : Ordinary C hP I =>
    readControl C hP I (ordinaryChild C hP I d) = q)).image (ordinaryChild C hP I)

private theorem ordinary_child_unique {n p : Node C hP I}
    (hp : OrdinaryParent C hP I p) (hn : parent C hP I n = some p) :
    n = ordinaryChild C hP I ⟨p,hp⟩ := by
  exact FixedForestTargetInventory.unary_child_unique (physicalForest C hP I)
    hp.1 hn (ordinary_child_parent C hP I ⟨p,hp⟩)

/-- Unique forest parents partition every nonroot full history. Equal rows and
literal delays do not identify ordinary parents or their children. -/
theorem actual_child_partition (q : Q) :
    (nonroots C hP I).filter (fun n => readControl C hP I n = q) =
      backgroundChildren C hP I q ∪ ordinaryChildren C hP I q ∧
    Disjoint (backgroundChildren C hP I q) (ordinaryChildren C hP I q) ∧
    Function.Injective (ordinaryChild C hP I) := by
  refine ⟨?_,?_,ordinary_child_injective C hP I⟩
  · ext n
    constructor
    · intro hn
      have hh := Finset.mem_filter.mp hn
      have hnp : parent C hP I n ≠ none := (Finset.mem_filter.mp hh.1).2
      cases hp : parent C hP I n with
      | none => exact False.elim (hnp hp)
      | some p =>
        by_cases hb : BackgroundParent C hP I p
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.2,p,hp,hb⟩)
        · have hi : (children C hP I p).Nonempty :=
            ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
          have hu : (children C hP I p).card = 1 := by
            have hc := branching C hP I p
            have hpos := Finset.card_pos.mpr hi
            have hnb : (children C hP I p).card ≠ 2 := by
              intro he; exact hb (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩))
            omega
          let d : Ordinary C hP I := ⟨p,hu,hb⟩
          have he : n = ordinaryChild C hP I d := ordinary_child_unique C hP I ⟨hu,hb⟩ hp
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hh.2⟩,he.symm⟩
    · intro hn
      rcases Finset.mem_union.mp hn with hn | hn
      · have hh := (Finset.mem_filter.mp hn).2
        obtain ⟨p,hp,_⟩ := hh.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
          change parent C hP I n ≠ none
          rw [hp]; simp⟩,hh.1⟩
      · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
          change parent C hP I (ordinaryChild C hP I d) ≠ none
          rw [ordinary_child_parent]; simp⟩,(Finset.mem_filter.mp hd).2⟩
  · apply Finset.disjoint_left.mpr
    intro n hn ho
    obtain ⟨p,hp,hb⟩ := (Finset.mem_filter.mp hn).2.2
    obtain ⟨d,_,he⟩ := Finset.mem_image.mp ho
    rw [← he,ordinary_child_parent] at hp
    exact d.property.2 (Option.some.inj hp ▸ hb)

/-- Indexed occurrences are partitioned by actual history, retaining read
indices even when the same original label occurs in several histories. -/
theorem actual_indexed_partition :
    (∀ e : Event C hP I, ∃! n : Node C hP I, e ∈ indexedSupport C hP I n) ∧
    (∀ n m : Node C hP I, n ≠ m →
      Disjoint (indexedSupport C hP I n) (indexedSupport C hP I m)) ∧
    (∀ d d' : Ordinary C hP I, d ≠ d' →
      Disjoint (indexedSupport C hP I (ordinaryChild C hP I d))
        (indexedSupport C hP I (ordinaryChild C hP I d'))) := by
  refine ⟨?_,(actual_history_data C hP I).indexed_disjoint,?_⟩
  · intro e
    refine ⟨event C hP I e,by simp [indexedSupport],?_⟩
    intro n hn
    exact (Finset.mem_filter.mp hn).2.symm
  · intro d d' hne
    exact (actual_history_data C hP I).indexed_disjoint _ _
      (fun he => hne (ordinary_child_injective C hP I he))

noncomputable def backgroundEvents (q : Q) : Finset (Event C hP I) :=
  Finset.univ.filter (fun e => event C hP I e ∈ backgroundChildren C hP I q)
noncomputable def ordinaryEvents (q : Q) : Finset (Event C hP I) :=
  Finset.univ.filter (fun e => event C hP I e ∈ ordinaryChildren C hP I q)

/-- The unique original read occurrence belongs to exactly its classified child
history. The index remains part of the event and is never quotiented away. -/
theorem actual_event_partition (q : Q) :
    (Finset.univ.filter (fun e : Event C hP I =>
      parent C hP I (event C hP I e) ≠ none ∧
      readControl C hP I (event C hP I e) = q)) =
      backgroundEvents C hP I q ∪ ordinaryEvents C hP I q ∧
    Disjoint (backgroundEvents C hP I q) (ordinaryEvents C hP I q) ∧
    (∀ e : Event C hP I, ∃! n : Node C hP I, e ∈ indexedSupport C hP I n) := by
  have hp := actual_child_partition C hP I q
  refine ⟨?_,?_,(actual_indexed_partition C hP I).1⟩
  · ext e
    have he := Finset.ext_iff.mp hp.1 (event C hP I e)
    have hn : ∀ n : Node C hP I, n ∈ nonroots C hP I ↔ parent C hP I n ≠ none := by
      intro n
      exact ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    simpa only [backgroundEvents,ordinaryEvents,Finset.mem_filter,Finset.mem_univ,
      true_and,Finset.mem_union,hn] using he
  · apply Finset.disjoint_left.mpr
    intro e hb ho
    exact Finset.disjoint_left.mp hp.2.1
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ho).2

private theorem ordinary_positive (d : Ordinary C hP I) : 0 < delay C hP I d.val :=
  (child_delay_target C hP I (ordinary_child_parent C hP I d)).1

noncomputable def score (f : ℕ+ → ℝ) (d : Nat) : ℝ≥0 :=
  if hd : 0 < d then (f ⟨d,hd⟩).toNNReal else 0
noncomputable def weight (f : ℕ+ → ℝ) (d : Ordinary C hP I) : ℝ≥0 :=
  score f (delay C hP I d.val)
noncomputable def demands (q : Q) (c : Fin 3) : Finset (Ordinary C hP I) :=
  Finset.univ.filter (fun d => row C hP I (ordinaryChild C hP I d) = (q,c))
noncomputable def Af (f : ℕ+ → ℝ) : ℝ≥0 := ∑ d : Ordinary C hP I, weight C hP I f d
noncomputable def a (f : ℕ+ → ℝ) (q : Q) (c : Fin 3) : ℝ≥0 :=
  ∑ d ∈ demands C hP I q c, weight C hP I f d
noncomputable def m (f : ℕ+ → ℝ) (q : Q) (c : Fin 3) : ℝ≥0 :=
  (demands C hP I q c).sup (weight C hP I f)
noncomputable def z (f : ℕ+ → ℝ) (q : Q) (c : Fin 3) : ℝ≥0 :=
  if c ∈ backgroundDigits C hP I q then a C hP I f q c else a C hP I f q c - m C hP I f q c
noncomputable def Zf (f : ℕ+ → ℝ) : ℝ≥0 := ∑ q ∈ targets C hP I, ∑ c, z C hP I f q c
noncomputable def retained (f : ℕ+ → ℝ) (q : Q) : ℝ≥0 :=
  ∑ c ∈ Finset.univ \ backgroundDigits C hP I q, m C hP I f q c

private theorem fiber_sum (f : ℕ+ → ℝ) :
    Af C hP I f = ∑ q ∈ targets C hP I, ∑ c, a C hP I f q c := by
  let slot := fun d : Ordinary C hP I => row C hP I (ordinaryChild C hP I d)
  have maps : ∀ d ∈ (Finset.univ : Finset (Ordinary C hP I)),
      slot d ∈ (targets C hP I) ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro d _
    obtain ⟨v, hv⟩ := event_surjective C hP I (ordinaryChild C hP I d)
    have ho : v ∈ ordinaryEvents C hP I (slot d).1 := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hv]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    have he : v ∈ Finset.univ.filter (fun e : Event C hP I =>
        parent C hP I (event C hP I e) ≠ none ∧
        readControl C hP I (event C hP I e) = (slot d).1) := by
      rw [(actual_event_partition C hP I (slot d).1).1]
      exact Finset.mem_union_right _ ho
    have hn := (Finset.mem_filter.mp he).2.1
    rw [hv] at hn
    exact Finset.mem_product.mpr ⟨by
      exact Finset.mem_image.mpr ⟨slot d, Finset.mem_image.mpr
        ⟨ordinaryChild C hP I d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩, rfl⟩,
      Finset.mem_univ _⟩
  have eq := Finset.sum_fiberwise_of_maps_to maps (weight C hP I f)
  rw [Finset.sum_product] at eq
  exact eq.symm

private theorem maximum_le_sum (f : ℕ+ → ℝ) (q : Q) (c : Fin 3) :
    m C hP I f q c ≤ a C hP I f q c := by
  apply Finset.sup_le
  intro d hd
  exact Finset.single_le_sum (fun _ _ => zero_le) hd

private theorem score_coe (f : ℕ+ → ℝ) (hf : ∀ x, 0 ≤ f x)
    {d : Nat} (hd : 0 < d) : (score f d : ℝ) = f ⟨d,hd⟩ := by
  simp [score,hd,Real.toNNReal_of_nonneg (hf ⟨d,hd⟩)]

/-- Every ordinary full-history weight occurs once. Background digits retain
zero; other digits retain exactly their largest weight, with empty maximum zero. -/
theorem retained_identity (f : ℕ+ → ℝ) :
    Af C hP I f = Zf C hP I f + ∑ q ∈ targets C hP I, retained C hP I f q ∧
    (0 : ℝ) ≤ Zf C hP I f ∧
    (∀ q c, (a C hP I f q c : ℝ) =
      (z C hP I f q c : ℝ) + if c ∈ backgroundDigits C hP I q then 0 else (m C hP I f q c : ℝ)) ∧
    (∀ q c, demands C hP I q c = ∅ → m C hP I f q c = 0) ∧
    (∀ _hf : ∀ x, 0 ≤ f x,
      (Af C hP I f : ℝ) = ∑ d : Ordinary C hP I,
        f ⟨delay C hP I d.val,ordinary_positive C hP I d⟩ ∧
      ∀ q c, (a C hP I f q c : ℝ) = ∑ d ∈ demands C hP I q c,
        f ⟨delay C hP I d.val,ordinary_positive C hP I d⟩) ∧
    (f 1 = 0 → ∀ d : Ordinary C hP I,
      delay C hP I d.val = 1 → weight C hP I f d = 0) ∧
    (∀ d d' : Ordinary C hP I, row C hP I d.val = row C hP I d'.val →
      delay C hP I d.val = delay C hP I d'.val) := by
  have slot (q : Q) (c : Fin 3) : a C hP I f q c = z C hP I f q c +
      if c ∈ backgroundDigits C hP I q then 0 else m C hP I f q c := by
    by_cases hc : c ∈ backgroundDigits C hP I q
    · simp [z,hc]
    · simp only [z,if_neg hc]
      exact (tsub_add_cancel_of_le (maximum_le_sum C hP I f q c)).symm
  refine ⟨?_,(Zf C hP I f).coe_nonneg,?_,?_,?_,?_,?_⟩
  · rw [fiber_sum]
    unfold Zf retained
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    have hr : (∑ c ∈ Finset.univ \ backgroundDigits C hP I q, m C hP I f q c) =
        ∑ c : Fin 3, if c ∈ backgroundDigits C hP I q then 0 else m C hP I f q c := by
      simp [Finset.sum_filter,Finset.sdiff_eq_filter,ite_not]
    rw [hr,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => slot q c)
  · intro q c
    have hh := congrArg (fun x : ℝ≥0 => (x : ℝ)) (slot q c)
    simpa only [NNReal.coe_add,apply_ite,NNReal.coe_zero] using hh
  · intro q c he
    simp [m,he]
  · intro hf
    constructor
    · simp only [Af,NNReal.coe_sum]
      exact Finset.sum_congr rfl (fun d _ => score_coe f hf (ordinary_positive C hP I d))
    · intro q c
      simp only [a,NNReal.coe_sum]
      exact Finset.sum_congr rfl (fun d _ => score_coe f hf (ordinary_positive C hP I d))
  · intro hunit d hd
    simp [weight,score,hd,hunit]
  · intro d d' he
    exact (row_delay_target C hP I
      (Finset.card_pos.mp (by rw [d.property.1]; omega))
      (congrArg Prod.fst he) (congrArg Prod.snd he)).1



private theorem score_mono (f : ℕ+ → ℝ) (hf : ∀ x, 0 ≤ f x) (hm : Monotone f)
    {d L : Nat} (hd : 0 < d) (hL : d ≤ L) : score f d ≤ score f L := by
  apply NNReal.coe_le_coe.mp
  rw [score_coe f hf hd,score_coe f hf (by omega : 0 < L)]
  exact hm (show (⟨d,hd⟩ : ℕ+) ≤ ⟨L,by omega⟩ from hL)

private theorem maximum_le_tail (f : ℕ+ → ℝ) (hf : ∀ x, 0 ≤ f x) (hm : Monotone f)
    (q : Q) (c : Fin 3) : m C hP I f q c ≤ score f (tail C hP I q) := by
  apply Finset.sup_le
  intro d hd
  have ht := literal_le_tail C hP I d.val
    (Finset.card_pos.mp (by rw [d.property.1]; omega))
  have hc := (child_delay_target C hP I (ordinary_child_parent C hP I d)).2.2.1
  have he := congrArg Prod.fst (Finset.mem_filter.mp hd).2
  change readControl C hP I (ordinaryChild C hP I d) = q at he
  rw [← hc,he] at ht
  exact score_mono f hf hm ht.1 ht.2

private theorem retained_slots (f : ℕ+ → ℝ) (hf : ∀ x, 0 ≤ f x) (hm : Monotone f)
    (q : Q) : retained C hP I f q ≤ (k C hP I q : ℝ≥0) * score f (tail C hP I q) := by
  calc
    _ ≤ ∑ c ∈ Finset.univ \ backgroundDigits C hP I q, score f (tail C hP I q) :=
      Finset.sum_le_sum (fun c _ => maximum_le_tail C hP I f hf hm q c)
    _ = _ := by simp [k,Finset.card_sdiff_of_subset (Finset.subset_univ _),nsmul_eq_mul]

private theorem score_lipschitz (f : ℕ+ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hl : LipschitzWith 1 f) {l L : Nat} (hp : 0 < l) (hL : l ≤ L) :
    (score f L : ℝ) ≤ (score f l : ℝ) + (L - l : Nat) := by
  rw [score_coe f hf (by omega : 0 < L),score_coe f hf hp]
  have hle := hl.le_add_mul (⟨L,by omega⟩ : ℕ+) ⟨l,hp⟩
  have hcast : (l : ℝ) ≤ L := by exact_mod_cast hL
  change f ⟨L,by omega⟩ ≤ f ⟨l,hp⟩ + (1 : ℝ) * |(L : ℝ) - (l : ℝ)| at hle
  rw [one_mul,abs_of_nonneg (sub_nonneg.mpr hcast),← Nat.cast_sub hL] at hle
  exact hle

/-- The maximum retained on the sole possible spare core digit uses the
actual longest literal tail, while the baseline remains score-independent. -/
theorem core_retained_bound (f : ℕ+ → ℝ) (hf : ∀ x, 0 ≤ f x) (hm : Monotone f)
    (hl : LipschitzWith 1 f) (q : Q) (hq : q ∈ core C hP I) :
    (retained C hP I f q : ℝ) ≤
      (k C hP I q : ℝ) * score f (baseline C hP I q) +
        (tail C hP I q - baseline C hP I q : Nat) := by
  have hb := baseline_bounds C hP I q (core_subset C hP I hq)
  have hk := (background_structure C hP I).1 q hq |>.2
  have hr := retained_slots C hP I f hf hm q
  have hr' : (retained C hP I f q : ℝ) ≤ (k C hP I q : ℝ) * score f (tail C hP I q) := by
    exact_mod_cast hr
  have hs := score_lipschitz f hf hl (by omega : 0 < baseline C hP I q) hb.2.1
  have casesk : k C hP I q = 0 ∨ k C hP I q = 1 := by omega
  rcases casesk with hk | hk <;> rw [hk] at hr' ⊢ <;>
    simp only [Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,zero_add] at hr' ⊢
  · exact hr'.trans (Nat.cast_nonneg _)
  · exact hr'.trans hs

/-- Extras have three available digits and pay their joint maximum tail once. -/
theorem extra_retained_bound (f : ℕ+ → ℝ) (hf : ∀ x, 0 ≤ f x) (hm : Monotone f)
    (hcap : ∀ L : ℕ+, 3 * f L ≤ (L : Nat) + 1) (q : Q) (hq : q ∈ extras C hP I) :
    (retained C hP I f q : ℝ) ≤ (tail C hP I q : ℝ) + 1 := by
  have ht := baseline_bounds C hP I q (Finset.mem_sdiff.mp hq).1
  have hk : k C hP I q = 3 := by
    simp [k,backgroundDigits,(background_structure C hP I).2.1 q hq]
  have hr := retained_slots C hP I f hf hm q
  have hr' : (retained C hP I f q : ℝ) ≤ 3 * score f (tail C hP I q) := by
    have hh := NNReal.coe_le_coe.mpr hr
    rw [hk] at hh
    norm_num only [NNReal.coe_mul,NNReal.coe_natCast,Nat.cast_ofNat] at hh
    exact hh
  rw [score_coe f hf (by omega : 0 < tail C hP I q)] at hr'
  exact hr'.trans (hcap ⟨tail C hP I q,by omega⟩)

noncomputable def E : Nat := ∑ q ∈ targets C hP I, (tail C hP I q - 1)
noncomputable def E0 : Nat := ∑ q ∈ core C hP I, (baseline C hP I q - 1)

/-- The actual target partition charges each longest tail and growth once. -/
theorem exact_tail_decomposition :
    E C hP I + 2 * e C hP I = E0 C hP I +
      (∑ q ∈ core C hP I, (tail C hP I q - baseline C hP I q)) +
      (∑ q ∈ extras C hP I, (tail C hP I q + 1)) := by
  have hp : targets C hP I = core C hP I ∪ extras C hP I := by
    rw [extras,Finset.union_sdiff_of_subset (core_subset C hP I)]
  have hd : Disjoint (core C hP I) (extras C hP I) := by
    apply Finset.disjoint_left.mpr
    intro q hq he
    exact (Finset.mem_sdiff.mp he).2 hq
  have hc : (∑ q ∈ core C hP I, (tail C hP I q - 1)) =
      E0 C hP I + ∑ q ∈ core C hP I, (tail C hP I q - baseline C hP I q) := by
    unfold E0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hb := baseline_bounds C hP I q (core_subset C hP I hq)
    omega
  have he : (∑ q ∈ extras C hP I, (tail C hP I q + 1)) =
      (∑ q ∈ extras C hP I, (tail C hP I q - 1)) + 2 * e C hP I := by
    have pos : ∀ q ∈ extras C hP I, 1 ≤ tail C hP I q := by
      intro q hq
      have hb := baseline_bounds C hP I q (Finset.mem_sdiff.mp hq).1
      omega
    calc
      _ = ∑ q ∈ extras C hP I, ((tail C hP I q - 1) + 2) :=
        Finset.sum_congr rfl (fun q hq => by have := pos q hq; omega)
      _ = _ := by rw [Finset.sum_add_distrib]; simp [(structural_core C hP I).2.2.1,mul_comm]
  unfold E
  rw [hp,Finset.sum_union hd,hc,he]
  omega



/-- The positive-integer score contract imposes no value at zero. -/
structure Admissible (f : ℕ+ → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ f x
  monotone : Monotone f
  lipschitz : LipschitzWith 1 f
  unit_zero : f 1 = 0
  cap : ∀ L : ℕ+, 3 * f L ≤ (L : Nat) + 1

variable [Fintype Q]
open private read_state_mem read_states_partition from
  D5.S3.ObserverMemory.Algorithms.StationaryHistoryCore
private noncomputable def targetNonrootEquiv :
    {q : Q // q ∈ targets C hP I} ≃ NonrootRead C hP I where
  toFun q := targetRead C hP I q.val q.property
  invFun q := ⟨q.val.val,by
    have hs := (read_state_mem C hP I q.val.val).2 q.val.property
    rw [read_states_partition] at hs
    rcases Finset.mem_insert.mp hs with hs | hs
    · exact False.elim (q.property hs)
    · exact hs⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full nominal carrier, including unused states, pays every original
terminal, actual read, common-prefix position and longest target-tail unit. -/
private theorem full_nominal_charge :
    3 * P + 2 * (3 * (P - 1)) + 1 + 2 * e C hP I + ell + E C hP I ≤ Fintype.card Q := by
  obtain ⟨emb⟩ := full_nominal_resource_embedding C hP I
  have hb := Fintype.card_le_of_embedding emb
  have hs := (targetNonrootEquiv C hP I).sum_comp (actualL C hP I)
  have ht : (∑ q : {q : Q // q ∈ targets C hP I},
      actualL C hP I (targetNonrootEquiv C hP I q)) = ∑ q ∈ targets C hP I, tail C hP I q := by
    calc
      _ = ∑ q : {q : Q // q ∈ targets C hP I}, tail C hP I q.val := by
        apply Finset.sum_congr rfl
        intro q _
        simp only [tail,dif_pos q.property,targetNonrootEquiv]
        rfl
      _ = _ := Finset.sum_coe_sort (targets C hP I) (tail C hP I)
  have hp : ∀ q ∈ targets C hP I, 1 ≤ tail C hP I q := by
    intro q hq
    have hh := baseline_bounds C hP I q hq
    omega
  have hl : (∑ q ∈ targets C hP I, tail C hP I q) = E C hP I + (targets C hP I).card := by
    unfold E
    have hone : (targets C hP I).card = ∑ q ∈ targets C hP I, (1 : Nat) := by simp
    rw [hone,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hh := hp q hq
    omega
  have hcard : (targets C hP I).card = 3 * (P - 1) + e C hP I := by
    have hn := Finset.card_le_card (core_subset C hP I)
    have hc := (structural_core C hP I).2.1
    unfold e
    omega
  simp only [Resource,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,ZMod.card] at hb
  rw [← hs,ht,hl,hcard,(actual_core_data C hP I).actual_reads] at hb
  omega

/-- This necessary inequality is derived for the actual initialized controller;
no inventory, core count, injection or graph-statistic restriction is supplied. -/
theorem necessary_inequality (f : ℕ+ → ℝ) (hf : Admissible f) :
    (E C hP I : ℝ) + 2 * e C hP I ≥ (E0 C hP I : ℝ) + Af C hP I f -
      (∑ q ∈ core C hP I, (k C hP I q : ℝ) * score f (baseline C hP I q)) - Zf C hP I f ∧
    3 * P + 2 * (3 * (P - 1)) + 1 + 2 * e C hP I + ell + E C hP I ≤ Fintype.card Q := by
  refine ⟨?_,full_nominal_charge C hP I⟩
  · have hd := exact_tail_decomposition C hP I
    have hd' : (E C hP I : ℝ) + 2 * e C hP I = (E0 C hP I : ℝ) +
        (∑ q ∈ core C hP I, (tail C hP I q - baseline C hP I q : Nat)) +
        (∑ q ∈ extras C hP I, ((tail C hP I q : ℝ) + 1)) := by
      exact_mod_cast hd
    simp only [Nat.cast_sum] at hd'
    have hi := congrArg (fun x : ℝ≥0 => (x : ℝ)) (retained_identity C hP I f).1
    simp only [NNReal.coe_add,NNReal.coe_sum] at hi
    have hp : targets C hP I = core C hP I ∪ extras C hP I := by
      rw [extras,Finset.union_sdiff_of_subset (core_subset C hP I)]
    have dis : Disjoint (core C hP I) (extras C hP I) := by
      apply Finset.disjoint_left.mpr
      intro q hq he
      exact (Finset.mem_sdiff.mp he).2 hq
    rw [hp,Finset.sum_union dis] at hi
    have hc := Finset.sum_le_sum (s := core C hP I) (fun q hq =>
      core_retained_bound C hP I f hf.nonnegative hf.monotone hf.lipschitz q hq)
    have he := Finset.sum_le_sum (s := extras C hP I) (fun q hq =>
      extra_retained_bound C hP I f hf.nonnegative hf.monotone hf.cap q hq)
    rw [Finset.sum_add_distrib] at hc
    linarith


end D5.S3.ObserverMemory.Algorithms.StationaryWeightedHistoryOverlap
