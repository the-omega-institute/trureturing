/- GID: D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Variable neighborhood retraction and the old-coordinate intersection equivalence. -/
import D5.S3.Geometry.FiniteGraphSubgraphSuspensionConstruction

/-!
# Neighborhood retraction and intersection

The variable cutoff retracts the second open set onto the actual apex
star cluster, while the fixed cutoff identifies the open intersection
with the old graph independence realization.
-/

noncomputable section
open Set Topology CategoryTheory
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteGraphSubgraphSuspension

open FiniteConeCollapse FiniteGraphVertexSubstitution FiniteCoordinateTruncation

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V)

namespace Coordinates

/- Unlike the fixed cutoff used in the contraction, the following variable
cutoff vanishes on B. Thus it gives an actual neighborhood retraction. -/
def retractRaw (x : Vertex H → ℝ) := cut (delta H x) x
def retractCoords (x : Vertex H → ℝ) := FiniteCoordinateTruncation.normalize (retractRaw H x)

private theorem retract_sum_lower (x : O G H) :
    (3 / 4 : ℝ) < ∑ a, retractRaw H x.val.val a := by
  have hb := cut_sum_bound (probability _ x.val) (delta H x.val.val)
  have he := card_epsilon H
  have hle : (Fintype.card (Vertex H) : ℝ) * delta H x.val.val ≤
      (Fintype.card (Vertex H) : ℝ) * epsilon H :=
    mul_le_mul_of_nonneg_left x.property.le (by positivity)
  change (3 / 4 : ℝ) < ∑ a, cut (delta H x.val.val) x.val.val a
  linarith

theorem retract_sum_pos (x : O G H) : 0 < ∑ a, retractRaw H x.val.val a :=
  lt_trans (by norm_num : (0 : ℝ) < 3 / 4) (retract_sum_lower G H x)

theorem retract_probability (x : O G H) : Probability (retractCoords H x.val.val) :=
  probability_normalize (cut_nonneg _ _) (retract_sum_pos G H x)

theorem retract_support (x : O G H) (a : Vertex H) (ha : x.val.val a = 0) :
    retractCoords H x.val.val a = 0 :=
  FiniteCoordinateTruncation.normalize_zero (cut_zero (delta_nonneg H (probability _ x.val).1) ha)

theorem retract_bad_zero (x : O G H) (M : MaxIndependent H)
    (hM : delta H x.val.val = bad H M x.val.val) :
    bad H M (retractCoords H x.val.val) = 0 := by
  apply (bad_zero H (retract_probability G H x).1 M).mpr
  constructor
  · exact FiniteCoordinateTruncation.normalize_zero (cut_eq_zero (by rw [hM]; exact hub_le_bad H (probability _ x.val).1 M))
  · intro a ha
    exact FiniteCoordinateTruncation.normalize_zero (cut_eq_zero (by rw [hM]; exact old_le_bad H (probability _ x.val).1 M a ha))

def neighborhoodRetraction : C(↥(O G H), ↥(cluster G H)) :=
  regionMap G H (fun x => delta H x = 0) (fun x => retractCoords H x.val.val)
    (continuous_normalize
      (continuous_cut (continuous_subtype_val.comp continuous_subtype_val)
        ((continuous_delta H).comp (continuous_subtype_val.comp continuous_subtype_val)))
      (fun x => (retract_sum_pos G H x).ne'))
    (fun x => ⟨retract_probability G H x,
      avoid_of_support (avoid _ x.val) (retract_support G H x)⟩)
    (fun x => by
      obtain ⟨M, hM⟩ := delta_witness H x.val.val
      exact le_antisymm ((delta_le H M _).trans (retract_bad_zero G H x M hM).le)
        (delta_nonneg H (retract_probability G H x).1))

def neighborhoodFirst : (ContinuousMap.id ↥(O G H)).Homotopy
    ((clusterInO G H).comp (neighborhoodRetraction G H)) :=
  regionStraight G H (fun x => delta H x < epsilon H) _ _
    (fun t x => avoid_mix_of_support (avoid _ x.val) (retract_support G H x) t)
    (fun t x => by
      obtain ⟨M, hM⟩ := delta_witness H x.val.val
      exact delta_mix_lt H (probability _ x.val).1 x.property M hM
        (retract_bad_zero G H x M hM) t)

theorem retraction_fixes (x : cluster G H) :
    neighborhoodRetraction G H (clusterInO G H x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  ext a
  change FiniteCoordinateTruncation.normalize (cut (delta H x.val.val) x.val.val) a = x.val.val a
  rw [x.property]
  have hc : cut 0 x.val.val = x.val.val := by
    ext b
    simp [cut, max_eq_left ((probability _ x.val).1 b)]
  rw [hc]
  simp [FiniteCoordinateTruncation.normalize, (probability _ x.val).2]

/-- Explicit neighborhood equivalence, fixing the closed star cluster. -/
def neighborhoodEquiv : ↥(O G H) ≃ₕ ↥(cluster G H) where
  toFun := neighborhoodRetraction G H
  invFun := clusterInO G H
  left_inv := ⟨(neighborhoodFirst G H).symm⟩
  right_inv := by
    have he : (neighborhoodRetraction G H).comp (clusterInO G H) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact retraction_fixes G H x
    rw [he]

theorem contractible_O : ContractibleSpace ↥(O G H) := by
  letI := contractible_starB G H
  letI : ContractibleSpace ↥(cluster G H) := (clusterHomeomorph G H).symm.contractibleSpace
  exact (neighborhoodEquiv G H).contractibleSpace

def oldRaw (x : Vertex H → ℝ) (a : V) : ℝ := cut (epsilon H) x (old a)
def oldCoords (x : Vertex H → ℝ) : V → ℝ := FiniteCoordinateTruncation.normalize (oldRaw H x)

private theorem oldRaw_sum_lower (x : ↥(U G H ∩ O G H)) :
    (1 / 4 : ℝ) < ∑ a, oldRaw H x.val.val a := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  have hhub : x.val.val (hub H) < epsilon H :=
    (hub_le_bad H (probability _ x.val).1 M).trans_lt (hM ▸ x.property.2)
  have hcard : (Fintype.card V : ℝ) + 1 ≤ Fintype.card (Vertex H) := by
    exact_mod_cast (show Fintype.card V + 1 ≤ Fintype.card (Vertex H) by
      simp only [Vertex, Fintype.card_sum, Fintype.card_option]; omega)
  have hprod := mul_le_mul_of_nonneg_right hcard (epsilon_pos H).le
  have he := card_epsilon H
  have hsum : (∑ a : V, x.val.val (old a)) - (Fintype.card V : ℝ) * epsilon H ≤
      ∑ a, oldRaw H x.val.val a := by
    calc
      _ = ∑ a : V, (x.val.val (old a) - epsilon H) := by
        rw [Finset.sum_sub_distrib]; simp
      _ ≤ _ := Finset.sum_le_sum fun _ _ => le_max_left _ _
  have ht := total G H x.val
  have hu := x.property.1
  dsimp [U] at hu
  nlinarith

theorem oldRaw_sum_pos (x : ↥(U G H ∩ O G H)) : 0 < ∑ a, oldRaw H x.val.val a :=
  lt_trans (by norm_num : (0 : ℝ) < 1 / 4) (oldRaw_sum_lower G H x)

theorem old_probability (x : ↥(U G H ∩ O G H)) : Probability (oldCoords H x.val.val) :=
  probability_normalize (fun a => cut_nonneg _ _ _) (oldRaw_sum_pos G H x)

theorem old_support (x : X G H) (a : V) (ha : x.val (old a) = 0) :
    oldCoords H x.val a = 0 :=
  FiniteCoordinateTruncation.normalize_zero (cut_zero (epsilon_pos H).le ha)

theorem old_off_M (x : X G H) (M : MaxIndependent H)
    (hM : bad H M x.val < epsilon H) (a : V) (ha : a ∉ M.val) :
    oldCoords H x.val a = 0 :=
  FiniteCoordinateTruncation.normalize_zero (cut_eq_zero ((old_le_bad H (probability _ x).1 M a ha).trans hM.le))

theorem old_avoid (x : ↥(U G H ∩ O G H)) : Avoid G (oldCoords H x.val.val) := by
  obtain ⟨M, hM⟩ := delta_witness H x.val.val
  have hbad : bad H M x.val.val < epsilon H := hM ▸ x.property.2
  intro a b hab
  by_cases hH : H.Adj a b
  · by_cases ha : a ∈ M.val
    · right
      apply old_off_M G H x.val M hbad b
      intro hb
      exact M.property.1 ha hb (H.ne_of_adj hH) hH
    · exact Or.inl (old_off_M G H x.val M hbad a ha)
  · exact (avoid _ x.val (old a) (old b) ⟨hab, hH⟩).imp
      (old_support G H x.val a) (old_support G H x.val b)

theorem continuous_oldRaw : Continuous (oldRaw H) := by
  apply continuous_pi
  intro a
  exact ((continuous_apply (old a)).sub continuous_const).max continuous_const

def oldReturn : C(↥(U G H ∩ O G H), Ispace G) where
  toFun x := ⟨oldCoords H x.val.val,
    (realization_iff _ _).mpr ⟨old_probability G H x, old_avoid G H x⟩⟩
  continuous_toFun := (continuous_normalize ((continuous_oldRaw H).comp
    (continuous_subtype_val.comp continuous_subtype_val))
    (fun x => (oldRaw_sum_pos G H x).ne')).subtype_mk _

def oldInclusion (hHG : H ≤ G) : C(Ispace G, ↥(U G H ∩ O G H)) :=
  regionMap G H (fun x => mass H x < 1 / 2 ∧ delta H x < epsilon H)
    (fun z => liftOld H z.val)
    ((continuous_liftOld H).comp continuous_subtype_val)
    (fun z => ⟨probability_liftOld H (probability _ z), avoid_liftOld G H (avoid _ z)⟩)
    (fun z => ⟨by rw [mass_liftOld]; norm_num,
      by rw [delta_liftOld G H hHG (probability _ z) (avoid _ z)]; exact epsilon_pos H⟩)

theorem return_lift_support (x : ↥(U G H ∩ O G H)) (a : Vertex H)
    (ha : x.val.val a = 0) : liftOld H (oldCoords H x.val.val) a = 0 := by
  rcases a with a | a
  · exact old_support G H x.val a ha
  · rfl

theorem return_bad_zero (x : ↥(U G H ∩ O G H)) (M : MaxIndependent H)
    (hM : bad H M x.val.val < epsilon H) :
    bad H M (liftOld H (oldCoords H x.val.val)) = 0 :=
  (bad_zero H (probability_liftOld H (old_probability G H x)).1 M).mpr
    ⟨rfl, fun a ha => old_off_M G H x.val M hM a ha⟩

def intersectionFirst (hHG : H ≤ G) :
    (ContinuousMap.id ↥(U G H ∩ O G H)).Homotopy
      ((oldInclusion G H hHG).comp (oldReturn G H)) :=
  regionStraight G H (fun x => mass H x < 1 / 2 ∧ delta H x < epsilon H) _ _
    (fun t x => avoid_mix_of_support (avoid _ x.val) (return_lift_support G H x) t)
    (fun t x => by
      constructor
      · exact mass_mix_lt H x.property.1
          (Finset.sum_nonneg fun _ _ => (probability _ x.val).1 _) (mass_liftOld H _) t
      · obtain ⟨M, hM⟩ := delta_witness H x.val.val
        exact delta_mix_lt H (probability _ x.val).1 x.property.2 M hM
          (return_bad_zero G H x M (hM ▸ x.property.2)) t)

def intersectionSecond (hHG : H ≤ G) :
    (ContinuousMap.id (Ispace G)).Homotopy
      ((oldReturn G H).comp (oldInclusion G H hHG)) :=
  straight _ _ (fun t z => by
    apply (realization_iff G _).mpr
    refine ⟨probability_mix (probability _ z)
      (probability _ ((oldReturn G H) ((oldInclusion G H hHG) z))) t, ?_⟩
    apply avoid_mix_of_support (avoid _ z)
    intro a ha
    apply FiniteCoordinateTruncation.normalize_zero
    exact cut_zero (epsilon_pos H).le ha)

/-- The intersection of the constructed OPEN neighborhoods is homotopy
equivalent to the actual old independence realization, with both homotopies
given above. This is the finite-cover bridge required by Mayer--Vietoris. -/
def intersectionEquiv (hHG : H ≤ G) : ↥(U G H ∩ O G H) ≃ₕ Ispace G where
  toFun := oldReturn G H
  invFun := oldInclusion G H hHG
  left_inv := ⟨(intersectionFirst G H hHG).symm⟩
  right_inv := ⟨(intersectionSecond G H hHG).symm⟩

end Coordinates

end D5.S3.Geometry.FiniteGraphSubgraphSuspension
