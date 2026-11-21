/- GID: D5/S3/Combinatorics/Graph/LeaflessDynamics/ThetaExactExpansivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LeaflessDynamics/ThetaExactExpansivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Topologically exact dynamics of order m on the graph with m + 1 parallel edges. -/

import Batteries.Tactic.OpenPrivate
import D5.S1.Dynamics.Shadowing.BouquetExactExpansivity
import D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivisionRealization

/-!
The tour on the bouquet descends after identifying the copies of the negative
semicircle pointwise. The shared circle base bounds the size of each forward
Bowen ball. Near the zero vertex, distinct lifts coalesce after one step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Function Set Topology
open D5.S1.Dynamics.Shadowing

namespace D5.S3.Combinatorics.Graph.LeaflessDynamics.ThetaExactExpansivity

open CircleFinitePositiveExpansiveness (Circle project continuous_project
  coordinate coordinate_mem project_coordinate project_dist_eq)
open InvarianceGluedSheets (lift)
open private circle_positivelyExpansive continuous_sheet exists_sheet sheet_label_eq from
  D5.S1.Dynamics.Shadowing.BouquetExactExpansivity

variable {m : ℕ}

/-- The closed negative semicircle, including both vertices. -/
def negativeArc : Set Circle := project '' Icc (1 / 2 : ℝ) 1

private theorem project_zero : project 0 = 0 := AddCircle.coe_zero 1
private theorem project_one : project 1 = 0 := AddCircle.coe_period 1

private theorem zero_mem_negativeArc : (0 : Circle) ∈ negativeArc :=
  ⟨1, by norm_num, project_one⟩

private theorem half_mem_negativeArc : project (1 / 2) ∈ negativeArc :=
  ⟨1 / 2, by norm_num, rfl⟩

private theorem isClosed_negativeArc : IsClosed negativeArc :=
  (isCompact_Icc.image continuous_project).isClosed

private theorem project_not_mem_negativeArc {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    project t ∉ negativeArc := by
  rintro ⟨s, hs, he⟩
  have ht' : t ∈ Ico (0 : ℝ) (0 + 1) := ⟨ht.1.le, by linarith [ht.2]⟩
  rcases hs.2.lt_or_eq with h | rfl
  · have hs' : s ∈ Ico (0 : ℝ) (0 + 1) := ⟨by linarith [hs.1], by simpa using h⟩
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hs' ht').mp he
    linarith [hs.1, ht.2]
  · rw [project_one, ← project_zero] at he
    have hz : (0 : ℝ) ∈ Ico 0 (0 + 1) := by norm_num
    exact ht.1.ne' ((AddCircle.coe_eq_coe_iff_of_mem_Ico hz ht').mp he).symm

/-- The height is zero precisely where all sheets are identified. -/
def height (x : Circle) : ℝ := Metric.infDist x negativeArc

private theorem continuous_height : Continuous height := Metric.continuous_infDist_pt negativeArc

private theorem height_zero_iff {x : Circle} : height x = 0 ↔ x ∈ negativeArc :=
  (isClosed_negativeArc.mem_iff_infDist_zero ⟨0, zero_mem_negativeArc⟩).symm

/-- The metric realization with labelled positive semicircles and one common negative semicircle. -/
abbrev Space (m : ℕ) := InvarianceGluedSheets.Space m height

/-- Forget the sheet label while retaining the circle point. -/
def projection (p : Space m) : Circle := p.val.1

private theorem continuous_projection : Continuous (projection (m := m)) :=
  continuous_fst.comp continuous_subtype_val

private theorem continuous_lift (i : Fin m) : Continuous (lift height i) :=
  (continuous_id.prodMk (continuous_const.mul continuous_height)).subtype_mk _

private theorem lift_eq_of_mem {x : Circle} (hx : x ∈ negativeArc) (i j : Fin m) :
    lift height i x = lift height j x := by
  apply Subtype.ext
  change (x, (i.val : ℝ) * height x) = (x, (j.val : ℝ) * height x)
  rw [height_zero_iff.mpr hx, mul_zero, mul_zero]

private theorem exists_lift (p : Space m) : ∃ i : Fin m, lift height i (projection p) = p := by
  obtain ⟨i, hi⟩ := p.property
  exact ⟨i, Subtype.ext (Prod.ext rfl hi.symm)⟩

/-- Identify the negative semicircles pointwise in the bouquet. -/
def collapse (p : BouquetExactExpansivity.Space m) : Space m :=
  lift height (exists_sheet p).choose (BouquetExactExpansivity.projection p)

private theorem collapse_sheet (i : Fin m) (x : Circle) :
    collapse (BouquetExactExpansivity.sheet i x) = lift height i x := by
  let p := BouquetExactExpansivity.sheet i x
  let j := (exists_sheet p).choose
  change lift height j x = lift height i x
  by_cases hx : x = 0
  · exact lift_eq_of_mem (hx ▸ zero_mem_negativeArc) j i
  · have h : BouquetExactExpansivity.sheet j x = BouquetExactExpansivity.sheet i x :=
      (exists_sheet p).choose_spec
    rw [sheet_label_eq hx h]

private theorem continuous_collapse : Continuous (collapse (m := m)) := by
  let q : Fin m × Circle → BouquetExactExpansivity.Space m :=
    fun a => BouquetExactExpansivity.sheet a.1 a.2
  have hc : Continuous q := continuous_prod_of_discrete_left.mpr continuous_sheet
  have hq : IsQuotientMap q := hc.isClosedMap.isQuotientMap hc (fun p => by
    obtain ⟨i, hi⟩ := exists_sheet p
    exact ⟨(i, BouquetExactExpansivity.projection p), hi⟩)
  exact hq.continuous_iff.mpr (continuous_prod_of_discrete_left.mpr fun i =>
    (continuous_lift i).congr fun x => (collapse_sheet i x).symm)

private theorem surjective_collapse : Surjective (collapse (m := m)) := by
  intro p
  obtain ⟨i, hi⟩ := exists_lift p
  exact ⟨BouquetExactExpansivity.sheet i (projection p), (collapse_sheet i _).trans hi⟩

/-- Traverse the bouquet and apply the pointwise identification on the negative arc. -/
def thetaMap (hm : 0 < m) : Space m → Space m :=
  collapse ∘ BouquetExactExpansivity.traverse hm ∘ projection

private theorem collapse_semiconj (hm : 0 < m) :
    Semiconj collapse (BouquetExactExpansivity.bouquetMap hm) (thetaMap hm) := fun _ => rfl

private theorem projection_semiconj (hm : 0 < m) :
    Semiconj projection (thetaMap hm) (fun x : Circle => m • x) :=
  fun p => BouquetExactExpansivity.projection_traverse hm (projection p)

private theorem topologicallyExact (hm : 2 ≤ m) :
    ∀ U : Set (Space m), IsOpen U → U.Nonempty →
      ∃ k : ℕ, 0 < k ∧ (thetaMap (by omega : 0 < m))^[k] '' U = univ := by
  let hpos : 0 < m := by omega
  obtain ⟨_, _, _, hex, _, _⟩ := BouquetExactExpansivity.exact_order hm
  intro U hU hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, rfl⟩ := surjective_collapse y
  obtain ⟨k, hk, himage⟩ := hex (collapse ⁻¹' U) (hU.preimage continuous_collapse) ⟨x, hy⟩
  refine ⟨k, hk, eq_univ_of_forall fun z => ?_⟩
  obtain ⟨p, rfl⟩ := surjective_collapse z
  have hp : p ∈ (BouquetExactExpansivity.bouquetMap hpos)^[k] '' (collapse ⁻¹' U) := by
    rw [himage]
    exact mem_univ _
  obtain ⟨w, hw, rfl⟩ := hp
  exact ⟨collapse w, hw, ((collapse_semiconj hpos).iterate_right k w).symm⟩

private theorem forwardBowenBound (hm : 2 ≤ m) :
    ∃ ε > 0, ForwardBowenBound (thetaMap (by omega : 0 < m)) univ ε m := by
  let hpos : 0 < m := by omega
  obtain ⟨c, hc, hex⟩ := circle_positivelyExpansive hm
  refine ⟨c, hc, fun p _ => (Set.encard_mono (b := range (fun i => lift height i (projection p)))
    ?_).trans ?_⟩
  · intro q hq
    have he : projection p = projection q := hex _ _ fun n => by
      rw [← (projection_semiconj hpos).iterate_right n p,
        ← (projection_semiconj hpos).iterate_right n q]
      exact (le_max_left _ _).trans_lt (hq.2 n)
    obtain ⟨i, hi⟩ := exists_lift q
    exact ⟨i, he.symm ▸ hi⟩
  · simpa only [← image_univ, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      using Set.encard_image_le (fun i : Fin m => lift height i (projection p)) univ

private theorem lift_label_eq {x : Circle} (hx : x ∉ negativeArc) {i j : Fin m}
    (h : lift height i x = lift height j x) : i = j := by
  have hh : (i.val : ℝ) * height x = (j.val : ℝ) * height x :=
    congrArg (fun p : Space m => p.val.2) h
  exact Fin.ext (by exact_mod_cast mul_right_cancel₀ (mt height_zero_iff.mp hx) hh)

/-- At arbitrarily small positive phases, the entire fibre is distinct, close to
the zero vertex, and has a single common image. -/
theorem coalescing_fibre (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Ioo (0 : ℝ) (1 / 2),
      t < ε ∧ Injective (fun i : Fin m => lift height i (project t)) ∧
      (∀ i : Fin m, dist (lift height i (project t)) (lift height ⟨0, hm⟩ 0) < ε / 2) ∧
      ∀ i j : Fin m, thetaMap hm (lift height i (project t)) =
        thetaMap hm (lift height j (project t)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let t : ℝ := min (1 / 4) (ε / (4 * (m + 1 : ℝ)))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have htmax : t ≤ 1 / 4 := min_le_left _ _
  have htd : dist (project t) 0 = t := by
    rw [← project_zero, project_dist_eq (by rw [sub_zero, abs_of_pos ht]; linarith),
      Real.dist_eq, sub_zero, abs_of_pos ht]
  have hbound : ((m : ℝ) + 1) * t ≤ ε / 4 := by
    calc
      _ ≤ ((m : ℝ) + 1) * (ε / (4 * (m + 1 : ℝ))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = ε / 4 := by field_simp
  have htε : t < ε / 2 := by nlinarith
  have hheight : height (project t) ≤ t :=
    (Metric.infDist_le_dist_of_mem zero_mem_negativeArc).trans_eq htd
  have hnonneg : 0 ≤ height (project t) := Metric.infDist_nonneg
  have htI : t ∈ Ioo (0 : ℝ) (1 / 2) := ⟨ht, by linarith⟩
  refine ⟨t, htI, by linarith, fun _ _ => lift_label_eq (project_not_mem_negativeArc htI),
    fun i => ?_, fun _ _ => rfl⟩
  change max (dist (project t) 0)
    (dist ((i.val : ℝ) * height (project t)) (((0 : ℕ) : ℝ) * height 0)) < ε / 2
  rw [htd, Nat.cast_zero, zero_mul, Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hnonneg)]
  apply max_lt htε
  have hi : (i.val : ℝ) ≤ m := Nat.cast_le.mpr i.isLt.le
  calc
    _ ≤ (m : ℝ) * t := mul_le_mul hi hheight hnonneg hm'.le
    _ < ε / 2 := by nlinarith

private theorem no_smaller_bound (hm : 2 ≤ m) :
    ∀ ε > 0, ¬ ForwardBowenBound (thetaMap (by omega : 0 < m)) univ ε (m - 1) := by
  let hpos : 0 < m := by omega
  intro ε hε hb
  obtain ⟨t, _, _, hi, hclose, hcoalesce⟩ := coalescing_fibre hpos hε
  let i : Fin m := ⟨0, hpos⟩
  let p := lift height i (project t)
  have hcard : (m : ℕ∞) ≤ (univ ∩ ForwardBowen (thetaMap hpos) ε p).encard := by
    refine (Set.le_encard_iff_exists_fin_injective _ m).mpr
      ⟨fun j => lift height j (project t), fun j => ⟨mem_univ _, ?_⟩, hi⟩
    intro n
    cases n with
    | zero =>
      have h := dist_triangle p (lift height i 0) (lift height j (project t))
      rw [dist_comm (lift height i 0)] at h
      change dist p (lift height j (project t)) < ε
      linarith [hclose i, hclose j]
    | succ n =>
      rw [iterate_succ_apply, iterate_succ_apply, hcoalesce i j, dist_self]
      exact hε
  have hbad : m ≤ m - 1 := by exact_mod_cast hcard.trans (hb p (mem_univ _))
  omega

/-- For every `m ≥ 2`, the displayed map on the metric carrier is continuous,
surjective, topologically exact, and has least positive Bowen order `m`. -/
theorem exact_order (hm : 2 ≤ m) :
    let f := thetaMap (by omega : 0 < m)
    CompactSpace (Space m) ∧ Continuous f ∧ Surjective f ∧
      (∀ U : Set (Space m), IsOpen U → U.Nonempty → ∃ k : ℕ, 0 < k ∧ f^[k] '' U = univ) ∧
      (∃ ε > 0, ForwardBowenBound f univ ε m) ∧
      (∀ ε > 0, ¬ ForwardBowenBound f univ ε (m - 1)) := by
  let hpos : 0 < m := by omega
  obtain ⟨_, _, hsurj, _, _, _⟩ := BouquetExactExpansivity.exact_order hm
  refine ⟨InvarianceGluedSheets.compactSpace_space continuous_height,
    continuous_collapse.comp ((BouquetExactExpansivity.continuous_traverse hpos).comp
      continuous_projection), ?_, topologicallyExact hm, forwardBowenBound hm,
    no_smaller_bound hm⟩
  intro y
  obtain ⟨q, rfl⟩ := surjective_collapse y
  obtain ⟨p, rfl⟩ := hsurj q
  exact ⟨collapse p, (collapse_semiconj hpos p).symm⟩

section GraphRealization

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (DirectedMultigraph)
open TripleEdgeSubdivisionRealization (realization)
open private normal zeroParam oneParam from
  D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivisionRealization

/-- Two distinct vertices joined by `m` labelled positive edges and one common negative edge. -/
def parallelGraph (m : ℕ) : DirectedMultigraph Bool (Fin m ⊕ PUnit) where
  source := fun _ => false
  target := fun _ => true

local notation "I" => Icc (0 : ℝ) 1
private abbrev Edges (m : ℕ) := Fin m ⊕ PUnit
private abbrev Raw (m : ℕ) := Bool ⊕ (Edges m × I)

private def vertexPhase (v : Bool) : ℝ := if v then 1 / 2 else 0

private def edgePhase (e : Edges m) (t : ℝ) : ℝ :=
  e.elim (fun _ => t / 2) (fun _ => 1 - t / 2)

private def edgeLabel (hm : 0 < m) (e : Edges m) : Fin m :=
  e.elim id (fun _ => ⟨0, hm⟩)

private def vertexPoint (hm : 0 < m) (v : Bool) : Space m :=
  lift height ⟨0, hm⟩ (project (vertexPhase v))

private def edgePoint (hm : 0 < m) (e : Edges m) (t : I) : Space m :=
  lift height (edgeLabel hm e) (project (edgePhase e t))

private def raw (hm : 0 < m) : Raw m → Space m :=
  Sum.elim (vertexPoint hm) (fun a => edgePoint hm a.1 a.2)

private theorem edgePoint_zero (hm : 0 < m) (e : Edges m) :
    edgePoint hm e zeroParam = vertexPoint hm false := by
  have h : project (edgePhase e zeroParam) = 0 := by
    cases e <;> simp [edgePhase, zeroParam, project_zero, project_one]
  unfold edgePoint vertexPoint
  rw [h, show vertexPhase false = 0 from rfl, project_zero]
  exact lift_eq_of_mem zero_mem_negativeArc _ _

private theorem edgePoint_one (hm : 0 < m) (e : Edges m) :
    edgePoint hm e oneParam = vertexPoint hm true := by
  have h : edgePhase e oneParam = 1 / 2 := by
    cases e <;> norm_num [edgePhase, oneParam]
  unfold edgePoint vertexPoint
  rw [h]
  exact lift_eq_of_mem half_mem_negativeArc _ _

private theorem raw_normal (hm : 0 < m) (a : Raw m) :
    raw hm (normal (parallelGraph m) a) = raw hm a := by
  classical
  cases a with
  | inl v => rfl
  | inr a =>
    obtain ⟨e, t⟩ := a
    by_cases h0 : t = zeroParam
    · subst t
      simpa [normal, parallelGraph, raw] using (edgePoint_zero hm e).symm
    by_cases h1 : t = oneParam
    · subst t
      simpa [normal, parallelGraph, raw, h0] using (edgePoint_one hm e).symm
    · simp [normal, h0, h1]

private def Interior : Raw m → Prop :=
  Sum.elim (fun _ => True) (fun a => (a.2 : ℝ) ∈ Ioo 0 1)

private theorem interior_normal (a : Raw m) : Interior (normal (parallelGraph m) a) := by
  classical
  cases a with
  | inl v => trivial
  | inr a =>
    obtain ⟨e, t⟩ := a
    by_cases h0 : t = zeroParam
    · simp [normal, h0, Interior]
    by_cases h1 : t = oneParam
    · subst t
      simp [normal, h0, Interior]
    · simp only [normal, h0, h1, ite_false, Interior, Sum.elim_inr]
      exact ⟨t.2.1.lt_of_ne (fun h => h0 (Subtype.ext h.symm)),
        t.2.2.lt_of_ne (fun h => h1 (Subtype.ext h))⟩

private theorem edgePhase_mem (e : Edges m) (t : I) (ht : (t : ℝ) ∈ Ioo 0 1) :
    edgePhase e t ∈ Ico (0 : ℝ) (0 + 1) := by
  have ⟨ht0, ht1⟩ := ht
  cases e <;> dsimp [edgePhase] <;> constructor <;> linarith

private theorem edgePhase_ne_vertex (e : Edges m) (t : I) (ht : (t : ℝ) ∈ Ioo 0 1)
    (v : Bool) : edgePhase e t ≠ vertexPhase v := by
  have ⟨ht0, ht1⟩ := ht
  cases e <;> cases v <;> dsimp [edgePhase, vertexPhase] <;> linarith

private theorem vertexPhase_mem (v : Bool) : vertexPhase v ∈ Ico (0 : ℝ) (0 + 1) := by
  cases v <;> norm_num [vertexPhase]

private theorem vertexPoint_ne_edgePoint (hm : 0 < m) (v : Bool) (e : Edges m) (t : I)
    (ht : (t : ℝ) ∈ Ioo 0 1) : vertexPoint hm v ≠ edgePoint hm e t := by
  intro h
  have hphase : project (vertexPhase v) = project (edgePhase e t) := congrArg projection h
  have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico (vertexPhase_mem v)
    (edgePhase_mem e t ht)).mp hphase
  exact edgePhase_ne_vertex e t ht v he.symm

private theorem edgePoint_injective (hm : 0 < m) {e f : Edges m} {t u : I}
    (ht : (t : ℝ) ∈ Ioo 0 1) (hu : (u : ℝ) ∈ Ioo 0 1)
    (h : edgePoint hm e t = edgePoint hm f u) : (e, t) = (f, u) := by
  have hphase : project (edgePhase e t) = project (edgePhase f u) := congrArg projection h
  have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico (edgePhase_mem e t ht)
    (edgePhase_mem f u hu)).mp hphase
  have ⟨ht0, ht1⟩ := ht
  have ⟨hu0, hu1⟩ := hu
  rcases e with i | ⟨⟩ <;> rcases f with j | ⟨⟩ <;> dsimp [edgePhase] at he
  · obtain rfl : t = u := Subtype.ext (by linarith)
    have ht' : (t : ℝ) / 2 ∈ Ioo 0 (1 / 2) := ⟨by linarith, by linarith⟩
    have hi : i = j := lift_label_eq (project_not_mem_negativeArc ht') h
    rw [hi]
  · linarith
  · linarith
  · exact Prod.ext rfl (Subtype.ext (by linarith))

private theorem raw_injOn (hm : 0 < m) {a b : Raw m} (ha : Interior a) (hb : Interior b)
    (h : raw hm a = raw hm b) : a = b := by
  rcases a with v | ⟨e, t⟩ <;> rcases b with w | ⟨f, u⟩
  · have hp : project (vertexPhase v) = project (vertexPhase w) := congrArg projection h
    have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico (vertexPhase_mem v) (vertexPhase_mem w)).mp hp
    cases v <;> cases w <;> simp_all [vertexPhase]
  · exact (vertexPoint_ne_edgePoint hm v f u hb h).elim
  · exact (vertexPoint_ne_edgePoint hm w e t ha h.symm).elim
  · exact congrArg Sum.inr (edgePoint_injective hm ha hb h)

private theorem continuous_raw (hm : 0 < m) : Continuous (raw hm) := by
  apply continuous_sum_dom.mpr
  refine ⟨continuous_of_discreteTopology, continuous_prod_of_discrete_left.mpr fun e => ?_⟩
  change Continuous (edgePoint hm e)
  apply (continuous_lift (edgeLabel hm e)).comp
  apply continuous_project.comp
  cases e with
  | inl i => exact continuous_subtype_val.div_const _
  | inr i => exact continuous_const.sub (continuous_subtype_val.div_const _)

private theorem surjective_raw (hm : 0 < m) : Surjective (raw hm) := by
  intro p
  obtain ⟨i, hi⟩ := exists_lift p
  let t := coordinate 0 (projection p)
  have ht := coordinate_mem 0 (projection p)
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t < 1 := by simpa [t] using ht.2
  by_cases h : t ≤ 1 / 2
  · let u : I := ⟨2 * t, by linarith, by linarith⟩
    refine ⟨Sum.inr (Sum.inl i, u), ?_⟩
    change lift height i (project (2 * t / 2)) = p
    rw [show 2 * t / 2 = t by ring, project_coordinate, hi]
  · let u : I := ⟨2 * (1 - t), by linarith, by linarith⟩
    refine ⟨Sum.inr (Sum.inr PUnit.unit, u), ?_⟩
    change lift height ⟨0, hm⟩ (project (1 - 2 * (1 - t) / 2)) = p
    rw [show 1 - 2 * (1 - t) / 2 = t by ring]
    exact (lift_eq_of_mem ⟨t, ⟨by linarith, ht1.le⟩, rfl⟩ _ i).trans
      (by rw [project_coordinate, hi])

/-- The metric carrier is the closed-edge quotient of the two-vertex multigraph. -/
def graphHomeomorph (hm : 0 < m) : realization (parallelGraph m) ≃ₜ Space m := by
  let q : C(Raw m, Space m) := ⟨raw hm, continuous_raw hm⟩
  have hq : IsQuotientMap q :=
    q.continuous.isClosedMap.isQuotientMap q.continuous (surjective_raw hm)
  have hker (a b : Raw m) :
      (Setoid.ker (normal (parallelGraph m))).r a b ↔ (Setoid.ker q).r a b := by
    change normal (parallelGraph m) a = normal (parallelGraph m) b ↔ raw hm a = raw hm b
    rw [← raw_normal hm a, ← raw_normal hm b]
    exact ⟨congrArg (raw hm), raw_injOn hm (interior_normal a) (interior_normal b)⟩
  exact (Homeomorph.Quotient.congrRight hker).trans hq.homeomorph

/-- The ordinary realization of the two-vertex, `m + 1`-edge graph has a compact
metric model with a continuous surjective exact map of least positive Bowen order `m`. -/
theorem exists_exact_order_on_graph (hm : 2 ≤ m) :
    ∃ (X : Type) (_ : MetricSpace X), Nonempty (realization (parallelGraph m) ≃ₜ X) ∧
      CompactSpace X ∧
      ∃ f : X → X, Continuous f ∧ Surjective f ∧
        (∀ U : Set X, IsOpen U → U.Nonempty → ∃ k : ℕ, 0 < k ∧ f^[k] '' U = univ) ∧
        (∃ ε > 0, ForwardBowenBound f univ ε m) ∧
        (∀ ε > 0, ¬ ForwardBowenBound f univ ε (m - 1)) := by
  let hpos : 0 < m := by omega
  obtain ⟨hcompact, hf, hs, he, hupper, hlower⟩ := exact_order hm
  exact ⟨Space m, inferInstance, ⟨graphHomeomorph hpos⟩, hcompact, thetaMap hpos,
    hf, hs, he, hupper, hlower⟩

end GraphRealization

/--
info: 'D5.S3.Combinatorics.Graph.LeaflessDynamics.ThetaExactExpansivity.coalescing_fibre'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coalescing_fibre

/--
info: 'D5.S3.Combinatorics.Graph.LeaflessDynamics.ThetaExactExpansivity.exact_order'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exact_order

/--
info: 'D5.S3.Combinatorics.Graph.LeaflessDynamics.ThetaExactExpansivity.graphHomeomorph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphHomeomorph

/--
info: 'D5.S3.Combinatorics.Graph.LeaflessDynamics.ThetaExactExpansivity.exists_exact_order_on_graph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_exact_order_on_graph

end D5.S3.Combinatorics.Graph.LeaflessDynamics.ThetaExactExpansivity
