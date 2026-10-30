/- GID: D5/S3/Topology/FiniteOrbitChainMetric
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteOrbitChainMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.HausdorffDistance, mathlib/module/Mathlib.Topology.Constructions]
   utility: none
   digest: Finite actual orbits of closed partial isometries give the original quotient its chain extended metric. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Constructions
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Choose

set_option autoImplicit false

open Set
open scoped NNReal ENNReal Topology

namespace D5.S3.Topology.FiniteOrbitChainMetric

universe u v w

structure Datum (I : Type u) (J : Type v) (X : I → Type w)
    [∀ i, EMetricSpace (X i)] where
  src : J → I
  dst : J → I
  dom : ∀ j, Set (X (src j))
  ran : ∀ j, Set (X (dst j))
  iso : ∀ j, dom j ≃ᵢ ran j
  closed_dom : ∀ j, IsClosed (dom j)
  closed_ran : ∀ j, IsClosed (ran j)

namespace Datum

variable {I : Type u} {J : Type v} {X : I → Type w}
variable [∀ i, EMetricSpace (X i)] (G : Datum I J X)

def Step (a b : Sigma X) : Prop :=
  ∃ (j : J) (x : G.dom j),
    a = ⟨G.src j, x.val⟩ ∧ b = ⟨G.dst j, (G.iso j x).val⟩

abbrev Rel : Sigma X → Sigma X → Prop := Relation.EqvGen G.Step

/-- All finite actual jumps and generator/inverse transitions. ENNReal is
the cost codomain; paid steps and finite derivations may have infinite cost. -/
inductive Chain (a : Sigma X) : Sigma X → ℝ≥0∞ → Prop
  | nil : Chain a a 0
  | move {i : I} (x y : X i) {t : ℝ≥0∞} :
      Chain a ⟨i, x⟩ t → Chain a ⟨i, y⟩ (t + edist x y)
  | forward (j : J) (x : G.dom j) {t : ℝ≥0∞} :
      Chain a ⟨G.src j, x.val⟩ t →
      Chain a ⟨G.dst j, (G.iso j x).val⟩ t
  | backward (j : J) (x : G.ran j) {t : ℝ≥0∞} :
      Chain a ⟨G.dst j, x.val⟩ t →
      Chain a ⟨G.src j, ((G.iso j).symm x).val⟩ t

noncomputable def distance (a b : Sigma X) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0∞) (_ : G.Chain a b t), t

/- Chain reversal, concatenation and the infimum characterization. -/

private theorem chain_append {a b c : Sigma X} {t u : ℝ≥0∞}
    (h : G.Chain a b t) (k : G.Chain b c u) : G.Chain a c (t + u) := by
  induction k with
  | nil => simpa using h
  | @move i x y u k ih =>
      simpa only [add_assoc] using Chain.move x y ih
  | @forward j x u k ih => exact Chain.forward j x ih
  | @backward j x u k ih => exact Chain.backward j x ih

private theorem chain_reverse {a b : Sigma X} {t : ℝ≥0∞}
    (h : G.Chain a b t) : G.Chain b a t := by
  induction h with
  | nil => exact Chain.nil
  | @move i x y t h ih =>
      have one : G.Chain (⟨i, y⟩ : Sigma X) ⟨i, x⟩ (edist x y) := by
        simpa only [zero_add, edist_comm] using
          (Chain.move y x (Chain.nil (G := G)))
      simpa only [add_comm] using chain_append G one ih
  | @forward j x t h ih =>
      have one : G.Chain (⟨G.dst j, (G.iso j x).val⟩ : Sigma X)
          ⟨G.src j, x.val⟩ 0 := by
        simpa using (Chain.backward j (G.iso j x) (Chain.nil (G := G)))
      simpa using chain_append G one ih
  | @backward j x t h ih =>
      have one : G.Chain (⟨G.src j, ((G.iso j).symm x).val⟩ : Sigma X)
          ⟨G.dst j, x.val⟩ 0 := by
        simpa using (Chain.forward j ((G.iso j).symm x) (Chain.nil (G := G)))
      simpa using chain_append G one ih

private theorem zero_chain_of_rel {a b : Sigma X} (h : G.Rel a b) :
    G.Chain a b 0 := by
  induction h with
  | rel a b h =>
      rcases h with ⟨j, x, rfl, rfl⟩
      exact Chain.forward j x Chain.nil
  | refl a => exact Chain.nil
  | symm a b h ih => exact chain_reverse G ih
  | trans a b c hab hbc ihab ihbc =>
      simpa using chain_append G ihab ihbc

private theorem distance_le_chain {a b : Sigma X} {t : ℝ≥0∞}
    (h : G.Chain a b t) : G.distance a b ≤ t :=
  iInf₂_le t h

private theorem distance_lt_iff {a b : Sigma X} {s : ℝ≥0∞} :
    G.distance a b < s ↔ ∃ t, G.Chain a b t ∧ t < s := by
  simp only [distance, iInf_lt_iff, exists_prop]

private theorem finite_fiber (a : Sigma X)
    (hf : Set.Finite {b : Sigma X | G.Rel a b}) (i : I) :
    Set.Finite {x : X i | G.Rel a ⟨i, x⟩} := by
  exact Set.Finite.preimage sigma_mk_injective.injOn hf

/-- A finite actual equivalence class has a positive exclusion radius,
short-chain capture and an exact local-ball formula. -/
theorem finite_orbit_local_model [Fintype J] (a : Sigma X)
    (hf : Set.Finite {b : Sigma X | G.Rel a b}) :
    ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ⊤ ∧
      (∀ (b : Sigma X) (t : ℝ≥0∞), G.Chain a b t → t < ρ →
        ∃ c : X b.1, G.Rel a ⟨b.1, c⟩ ∧ edist c b.2 ≤ t) ∧
      (∀ (b : Sigma X) (s : ℝ≥0∞), 0 < s → s < ρ →
        (G.distance a b < s ↔
          ∃ c : X b.1, G.Rel a ⟨b.1, c⟩ ∧ edist c b.2 < s)) := by
  classical
  have forward_sep (j : J) : ∃ r : ℝ≥0, 0 < r ∧
      ∀ c : X (G.src j), G.Rel a ⟨G.src j, c⟩ → c ∉ G.dom j →
      ∀ x ∈ G.dom j, (r : ℝ≥0∞) < edist c x := by
    have hC : Set.Finite ({c : X (G.src j) | G.Rel a ⟨G.src j, c⟩} \ G.dom j) :=
      (finite_fiber G a hf (G.src j)).subset Set.sdiff_subset
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
      hC.isCompact (G.closed_dom j) Set.disjoint_sdiff_left
    exact ⟨r, hr, fun c hc hnot x hx => hsep c ⟨hc, hnot⟩ x hx⟩
  have backward_sep (j : J) : ∃ r : ℝ≥0, 0 < r ∧
      ∀ c : X (G.dst j), G.Rel a ⟨G.dst j, c⟩ → c ∉ G.ran j →
      ∀ x ∈ G.ran j, (r : ℝ≥0∞) < edist c x := by
    have hC : Set.Finite ({c : X (G.dst j) | G.Rel a ⟨G.dst j, c⟩} \ G.ran j) :=
      (finite_fiber G a hf (G.dst j)).subset Set.sdiff_subset
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
      hC.isCompact (G.closed_ran j) Set.disjoint_sdiff_left
    exact ⟨r, hr, fun c hc hnot x hx => hsep c ⟨hc, hnot⟩ x hx⟩
  choose rF hrF hF using forward_sep
  choose rB hrB hB using backward_sep
  let radii : J → ℝ≥0∞ := fun j => min (rF j : ℝ≥0∞) (rB j : ℝ≥0∞)
  let ρ : ℝ≥0∞ := min 1 (Finset.univ.inf radii)
  have hρ : 0 < ρ := by
    apply lt_min (by simp)
    apply (Finset.lt_inf_iff (by simp)).mpr
    intro j _
    exact lt_min (ENNReal.coe_pos.mpr (hrF j)) (ENNReal.coe_pos.mpr (hrB j))
  have hρtop : ρ < ⊤ := lt_of_le_of_lt (min_le_left _ _) (by simp)
  have boundF (j : J) : ρ ≤ (rF j : ℝ≥0∞) :=
    (min_le_right _ _).trans
      ((Finset.inf_le (Finset.mem_univ j)).trans (min_le_left _ _))
  have boundB (j : J) : ρ ≤ (rB j : ℝ≥0∞) :=
    (min_le_right _ _).trans
      ((Finset.inf_le (Finset.mem_univ j)).trans (min_le_right _ _))
  have guardF (j : J) (c : X (G.src j)) (hc : G.Rel a ⟨G.src j, c⟩)
      (x : G.dom j) (hclose : edist c x.val < ρ) : c ∈ G.dom j := by
    by_contra hnot
    exact (not_lt_of_ge (boundF j)) ((hF j c hc hnot x.val x.property).trans hclose)
  have guardB (j : J) (c : X (G.dst j)) (hc : G.Rel a ⟨G.dst j, c⟩)
      (x : G.ran j) (hclose : edist c x.val < ρ) : c ∈ G.ran j := by
    by_contra hnot
    exact (not_lt_of_ge (boundB j)) ((hB j c hc hnot x.val x.property).trans hclose)
  have capture (b : Sigma X) (t : ℝ≥0∞) (h : G.Chain a b t) :
      t < ρ → ∃ c : X b.1, G.Rel a ⟨b.1, c⟩ ∧ edist c b.2 ≤ t := by
    induction h with
    | nil =>
        intro _
        exact ⟨a.2, Relation.EqvGen.refl a, by simp⟩
    | @move i x y t h ih =>
        intro ht
        have ht' : t < ρ :=
          (le_add_of_nonneg_right (show 0 ≤ edist x y from bot_le)).trans_lt ht
        obtain ⟨c, hc, hcx⟩ := ih ht'
        exact ⟨c, hc, (edist_triangle c x y).trans (add_le_add hcx le_rfl)⟩
    | @forward j x t h ih =>
        intro ht
        obtain ⟨c, hc, hcx⟩ := ih ht
        have hmem : c ∈ G.dom j := guardF j c hc x (hcx.trans_lt ht)
        let c' : G.dom j := ⟨c, hmem⟩
        refine ⟨(G.iso j c').val, ?_, ?_⟩
        · exact Relation.EqvGen.trans _ _ _ hc
            (Relation.EqvGen.rel _ _ ⟨j, c', rfl, rfl⟩)
        · change edist (G.iso j c') (G.iso j x) ≤ t
          rw [(G.iso j).isometry.edist_eq]
          exact hcx
    | @backward j x t h ih =>
        intro ht
        obtain ⟨c, hc, hcx⟩ := ih ht
        have hmem : c ∈ G.ran j := guardB j c hc x (hcx.trans_lt ht)
        let c' : G.ran j := ⟨c, hmem⟩
        refine ⟨((G.iso j).symm c').val, ?_, ?_⟩
        · apply Relation.EqvGen.trans _ _ _ hc
          apply Relation.EqvGen.symm
          apply Relation.EqvGen.rel
          refine ⟨j, (G.iso j).symm c', rfl, ?_⟩
          simp [c']
        · change edist ((G.iso j).symm c') ((G.iso j).symm x) ≤ t
          rw [(G.iso j).symm.isometry.edist_eq]
          exact hcx
  refine ⟨ρ, hρ, hρtop, capture, ?_⟩
  intro b s hs hsρ
  constructor
  · intro hab
    obtain ⟨t, ht, hts⟩ := (distance_lt_iff G).mp hab
    obtain ⟨c, hc, hcb⟩ := capture b t ht (hts.trans hsρ)
    exact ⟨c, hc, hcb.trans_lt hts⟩
  · rintro ⟨c, hc, hcb⟩
    have jump : G.Chain a b (edist c b.2) := by
      simpa using Chain.move c b.2 (zero_chain_of_rel G hc)
    exact (distance_le_chain G jump).trans_lt hcb

/- Short-chain capture prevents additional zero-distance identifications. -/
private theorem distance_zero_iff [Fintype J] (a b : Sigma X)
    (hf : Set.Finite {c : Sigma X | G.Rel a c}) :
    G.distance a b = 0 ↔ G.Rel a b := by
  constructor
  · intro hz
    obtain ⟨ρ, hρ, _, capture, _⟩ := finite_orbit_local_model G a hf
    let C : Set (X b.1) := {c | G.Rel a ⟨b.1, c⟩}
    have hclosed : IsClosed C := (finite_fiber G a hf b.1).isClosed
    have hb : b.2 ∈ closure C := by
      apply EMetric.mem_closure_iff.mpr
      intro ε hε
      have hab : G.distance a b < min ρ ε := by rw [hz]; exact lt_min hρ hε
      obtain ⟨t, ht, hsmall⟩ := (distance_lt_iff G).mp hab
      obtain ⟨c, hc, hcb⟩ := capture b t ht (hsmall.trans_le (min_le_left _ _))
      refine ⟨c, hc, ?_⟩
      rw [edist_comm]
      exact hcb.trans_lt (hsmall.trans_le (min_le_right _ _))
    rw [hclosed.closure_eq] at hb
    exact hb
  · intro hab
    exact le_antisymm (distance_le_chain G (zero_chain_of_rel G hab)) bot_le

/-- Neighborhood capture on the original disjoint union.
The open set must be saturated under the actual full relation. The radius
is proved to exist; no quotient-topology compatibility is assumed. -/
private theorem original_open_neighborhood_capture [Fintype I] [Fintype J]
    (hfinite : ∀ a : Sigma X, Set.Finite {b : Sigma X | G.Rel a b})
    (V : Set (Sigma X)) (hV : IsOpen V)
    (hsat : ∀ a b, G.Rel a b → (a ∈ V ↔ b ∈ V)) :
    (∀ a b, G.distance a b = 0 ↔ G.Rel a b) ∧
    ∀ a ∈ V, ∃ ε : ℝ≥0∞, 0 < ε ∧ ε < ⊤ ∧
      ∀ b, G.distance a b < ε → b ∈ V := by
  classical
  refine ⟨fun a b => distance_zero_iff G a b (hfinite a), ?_⟩
  intro a ha
  obtain ⟨ρ, hρ, hρtop, capture, _⟩ := finite_orbit_local_model G a (hfinite a)
  have sep (i : I) : ∃ r : ℝ≥0, 0 < r ∧
      ∀ c : X i, G.Rel a ⟨i, c⟩ →
      ∀ y : X i, (⟨i, y⟩ : Sigma X) ∉ V → (r : ℝ≥0∞) < edist c y := by
    have hC := finite_fiber G a (hfinite a) i
    have hclosed : IsClosed ((Sigma.mk i ⁻¹' V)ᶜ) :=
      (isOpen_sigma_iff.mp hV i).isClosed_compl
    have hdisj : Disjoint {c : X i | G.Rel a ⟨i, c⟩} ((Sigma.mk i ⁻¹' V)ᶜ) := by
      apply Set.disjoint_left.mpr
      intro c hc hn
      exact hn ((hsat a ⟨i, c⟩ hc).mp ha)
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist hC.isCompact hclosed hdisj
    exact ⟨r, hr, fun c hc y hy => hsep c hc y hy⟩
  choose r hr hsep using sep
  let ε : ℝ≥0∞ := min ρ (Finset.univ.inf fun i => (r i : ℝ≥0∞))
  have hε : 0 < ε := by
    apply lt_min hρ
    apply (Finset.lt_inf_iff (by simp)).mpr
    intro i _
    exact ENNReal.coe_pos.mpr (hr i)
  refine ⟨ε, hε, (min_le_left _ _).trans_lt hρtop, ?_⟩
  intro b hab
  obtain ⟨t, ht, hsmall⟩ := (distance_lt_iff G).mp hab
  obtain ⟨c, hc, hcb⟩ := capture b t ht (hsmall.trans_le (min_le_left _ _))
  have hεr : ε ≤ (r b.1 : ℝ≥0∞) :=
    (min_le_right _ _).trans (Finset.inf_le (Finset.mem_univ b.1))
  by_contra hb
  exact (not_lt_of_ge hεr) ((hsep b.1 c hc b.2 hb).trans (hcb.trans_lt hsmall))

/-- The literal original quotient, its original topology, and the exact extended
chain distance, including infinite paid steps and empty cases. -/
theorem chain_metric_on_original_quotient [Fintype I] [Fintype J]
    (hfinite : ∀ a : Sigma X, Set.Finite {b : Sigma X | G.Rel a b}) :
    let S := Relation.EqvGen.setoid G.Step
    let Q := Quotient S
    let τ : TopologicalSpace Q := inferInstance
    ∃ m : EMetricSpace Q,
      m.toUniformSpace.toTopologicalSpace = τ ∧
      (∀ a b : Sigma X,
        @edist Q m.toEDist (Quotient.mk S a) (Quotient.mk S b) = G.distance a b) ∧
      (∀ a b, G.distance a b = 0 ↔ G.Rel a b) ∧
      (∀ a b, G.distance a b = ⊤ ↔ ¬ ∃ t, G.Chain a b t ∧ t < ⊤) ∧
      (letI : EMetricSpace Q := m
       ∀ i, LipschitzWith 1 (fun x : X i => (Quotient.mk S ⟨i, x⟩ : Q))) := by
  classical
  let S : Setoid (Sigma X) := Relation.EqvGen.setoid G.Step
  let Q := Quotient S
  let τ : TopologicalSpace Q := inferInstance
  let q : Sigma X → Q := Quotient.mk S
  -- Capture the ORIGINAL quotient topology before introducing any metric instance.
  have original_open (U : Set Q) : @IsOpen Q τ U ↔ IsOpen (q ⁻¹' U) := by
    exact (isQuotientMap_quotient_mk' (s := S)).isOpen_preimage.symm
  have hzero (a b : Sigma X) : G.distance a b = 0 ↔ G.Rel a b :=
    distance_zero_iff G a b (hfinite a)
  have hself (a : Sigma X) : G.distance a a = 0 :=
    le_antisymm (distance_le_chain G Chain.nil) bot_le
  have rev_le (a b : Sigma X) : G.distance a b ≤ G.distance b a := by
    apply le_iInf₂
    intro t ht
    exact distance_le_chain G (chain_reverse G ht)
  have hcomm (a b : Sigma X) : G.distance a b = G.distance b a :=
    le_antisymm (rev_le a b) (rev_le b a)
  have htri (a b c : Sigma X) :
      G.distance a c ≤ G.distance a b + G.distance b c := by
    apply ENNReal.le_iInf₂_add_iInf₂
    intro t ht u hu
    exact distance_le_chain G (chain_append G ht hu)
  have shift_le {a b a' b' : Sigma X} (ha : G.Rel a a') (hb : G.Rel b b') :
      G.distance a b ≤ G.distance a' b' := by
    calc
      G.distance a b ≤ G.distance a a' + G.distance a' b := htri a a' b
      _ ≤ G.distance a a' + (G.distance a' b' + G.distance b' b) :=
        add_le_add le_rfl (htri a' b' b)
      _ = G.distance a' b' := by
        rw [(hzero a a').mpr ha,
          (hzero b' b).mpr (Relation.EqvGen.symm _ _ hb)]
        simp
  have invariant {a b a' b' : Sigma X} (ha : G.Rel a a') (hb : G.Rel b b') :
      G.distance a b = G.distance a' b' :=
    le_antisymm (shift_le ha hb)
      (shift_le (Relation.EqvGen.symm _ _ ha) (Relation.EqvGen.symm _ _ hb))
  let d : Q → Q → ℝ≥0∞ := Quotient.lift₂ G.distance (by
    intro a b a' b' ha hb
    exact invariant ha hb)
  have dself (x : Q) : d x x = 0 := by
    refine Quotient.inductionOn x ?_
    intro a
    exact hself a
  have dcomm (x y : Q) : d x y = d y x := by
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact hcomm a b
  have dtri (x y z : Q) : d x z ≤ d x y + d y z := by
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.inductionOn z ?_
    intro c
    exact htri a b c
  have dzero {x y : Q} : d x y = 0 → x = y := by
    refine Quotient.inductionOn₂ x y ?_
    intro a b h
    exact Quotient.sound ((hzero a b).mp h)
  let m₀ : EMetricSpace Q :=
    { PseudoEMetricSpace.ofEDist d dself dcomm dtri with
      eq_of_edist_eq_zero := dzero }
  let : EMetricSpace Q := m₀
  have pieceLip (i : I) : LipschitzWith 1 (fun x : X i => q ⟨i, x⟩) := by
    intro x y
    change G.distance ⟨i, x⟩ ⟨i, y⟩ ≤ (1 : ℝ≥0∞) * edist x y
    rw [one_mul]
    apply distance_le_chain G
    simpa using (Chain.move x y (Chain.nil (G := G)))
  have htop : τ = m₀.toUniformSpace.toTopologicalSpace := by
    apply TopologicalSpace.ext
    funext U
    apply propext
    constructor
    · intro hU
      apply EMetric.isOpen_iff.mpr
      intro z hz
      revert hz
      refine Quotient.inductionOn z ?_
      intro a ha
      have hV : IsOpen (q ⁻¹' U) := (original_open U).mp hU
      have hsat : ∀ x y, G.Rel x y → (x ∈ q ⁻¹' U ↔ y ∈ q ⁻¹' U) := by
        intro x y hxy
        have heq : q x = q y := Quotient.sound hxy
        change q x ∈ U ↔ q y ∈ U
        rw [heq]
      obtain ⟨ε, hε, _, hball⟩ :=
        (original_open_neighborhood_capture G hfinite (q ⁻¹' U) hV hsat).2 a ha
      refine ⟨ε, hε, ?_⟩
      intro y hy
      revert hy
      refine Quotient.inductionOn y ?_
      intro b hb
      apply hball b
      change G.distance b a < ε at hb
      rwa [hcomm b a] at hb
    · intro hU
      apply (original_open U).mpr
      apply isOpen_sigma_iff.mpr
      intro i
      apply EMetric.isOpen_iff.mpr
      intro x hx
      obtain ⟨ε, hε, hball⟩ := EMetric.isOpen_iff.mp hU (q ⟨i, x⟩) hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      apply hball
      change G.distance ⟨i, y⟩ ⟨i, x⟩ < ε
      have hle : G.distance ⟨i, y⟩ ⟨i, x⟩ ≤ edist y x := by
        have hh := pieceLip i y x
        change G.distance ⟨i, y⟩ ⟨i, x⟩ ≤ (1 : ℝ≥0∞) * edist y x at hh
        simpa only [one_mul] using hh
      exact hle.trans_lt hy
  let m : EMetricSpace Q := @EMetricSpace.replaceTopology Q τ m₀ htop
  refine ⟨m, rfl, ?_, hzero, ?_, ?_⟩
  · intro a b
    rfl
  · intro a b
    constructor
    · intro htop hpath
      obtain ⟨t, ht, hfinitecost⟩ := hpath
      have hlt : G.distance a b < ⊤ :=
        (distance_le_chain G ht).trans_lt hfinitecost
      rw [htop] at hlt
      exact (lt_irrefl _) hlt
    · intro hn
      by_contra hne
      obtain ⟨t, ht, hlt⟩ := (distance_lt_iff G).mp (lt_top_iff_ne_top.mpr hne)
      exact hn ⟨t, ht, hlt⟩
  · exact pieceLip



end Datum
end D5.S3.Topology.FiniteOrbitChainMetric
