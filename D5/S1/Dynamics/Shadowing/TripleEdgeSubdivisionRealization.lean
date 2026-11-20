/- GID: D5/S1/Dynamics/Shadowing/TripleEdgeSubdivisionRealization
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/TripleEdgeSubdivisionRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The closed-edge quotient of a finite graph is its affine three-segment subdivision. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
import D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.LocallyFinite

/-! The original edge interval traverses the three subdivided segments in equal time. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function Set SimpleGraph
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (DirectedMultigraph)
open D5.S3.Combinatorics.Graph.LeaflessDynamics.TripleEdgeSubdivision (graph Flag)

namespace D5.S1.Dynamics.Shadowing.TripleEdgeSubdivisionRealization

open FiniteGraphAffineRealization

noncomputable section

variable {V E : Type*} (M : DirectedMultigraph V E)

local notation "I" => Icc (0 : ℝ) 1
local notation "Z" => V ⊕ Flag E
local notation "R" => V ⊕ (E × I)

private def zeroParam : I := ⟨0, le_rfl, zero_le_one⟩
private def oneParam : I := ⟨1, zero_le_one, le_rfl⟩

private def src (e : E) (i : Fin 3) : Z :=
  ![Sum.inl (M.source e), Sum.inr (Sum.inl e), Sum.inr (Sum.inr e)] i

private def dst (e : E) (i : Fin 3) : Z :=
  ![Sum.inr (Sum.inl e), Sum.inr (Sum.inr e), Sum.inl (M.target e)] i

private theorem adj (e : E) (i : Fin 3) : (graph M).Adj (src M e i) (dst M e i) := by
  fin_cases i <;> rfl

private def time (i : Fin 3) (t : I) : I :=
  ⟨((i.val : ℝ) + (t : ℝ)) / 3,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) t.2.1) (by norm_num),
    (div_le_one (by norm_num : (0 : ℝ) < 3)).mpr (by
      have hi : (i.val : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
      linarith [t.2.2])⟩

private def cell (i : Fin 3) : Set I :=
  {t | (i.val : ℝ) ≤ 3 * (t : ℝ) ∧ 3 * (t : ℝ) ≤ (i.val : ℝ) + 1}

private def timeInCell {i : Fin 3} (t : cell i) : I :=
  ⟨3 * (t.val : ℝ) - i.val, sub_nonneg.mpr t.2.1, sub_le_iff_le_add'.mpr t.2.2⟩

private theorem cell_covers : ⋃ i : Fin 3, cell i = univ := by
  apply Set.eq_univ_of_forall
  intro t
  have ht := t.2
  by_cases ha : 3 * (t : ℝ) ≤ 1
  · refine mem_iUnion.mpr ⟨0, ?_⟩
    simpa [cell] using (show 0 ≤ 3 * (t : ℝ) ∧ 3 * (t : ℝ) ≤ 1 from
      ⟨by linarith [ht.1], ha⟩)
  by_cases hb : 3 * (t : ℝ) ≤ 2
  · refine mem_iUnion.mpr ⟨1, ?_⟩
    norm_num [cell]
    exact ⟨by linarith, hb⟩
  · refine mem_iUnion.mpr ⟨2, ?_⟩
    norm_num [cell]
    constructor <;> linarith [ht.2]

private theorem time_mem (i : Fin 3) (s : I) : time i s ∈ cell i := by
  change (i.val : ℝ) ≤ 3 * (((i.val : ℝ) + (s : ℝ)) / 3) ∧
    3 * (((i.val : ℝ) + (s : ℝ)) / 3) ≤ (i.val : ℝ) + 1
  constructor <;> linarith [s.2.1, s.2.2]

private theorem time_roundtrip {i : Fin 3} (t : cell i) : time i (timeInCell t) = t.val := by
  apply Subtype.ext
  change ((i.val : ℝ) + (3 * (t.val : ℝ) - i.val)) / 3 = (t.val : ℝ)
  ring

private theorem timeInCell_roundtrip (i : Fin 3) (s : I) :
    timeInCell ⟨time i s, time_mem i s⟩ = s := by
  apply Subtype.ext
  change 3 * (((i.val : ℝ) + (s : ℝ)) / 3) - i.val = (s : ℝ)
  ring

/-- The endpoint gluing relation collapses endpoints to their named original vertices. -/
private def normal (x : R) : R := by
  classical
  exact match x with
  | .inl v => .inl v
  | .inr (e, t) =>
    if t = zeroParam then .inl (M.source e)
    else if t = oneParam then .inl (M.target e) else .inr (e, t)

/-- The ordinary graph realization, with one closed interval for each named edge. -/
def realization : Type _ := Quotient (Setoid.ker (normal M))

instance [TopologicalSpace V] [TopologicalSpace E] : TopologicalSpace (realization M) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (normal M))))

variable [DecidableEq V] [DecidableEq E]

private def piece (e : E) (i : Fin 3) (t : cell i) : Space (graph M) :=
  edgeChart (graph M) (adj M e i) (timeInCell t)

private theorem pieces_agree (e : E) (i j : Fin 3) (t : I)
    (hi : t ∈ cell i) (hj : t ∈ cell j) :
    piece M e i ⟨t, hi⟩ = piece M e j ⟨t, hj⟩ := by
  have agree (i j : Fin 3) (hi : t ∈ cell i) (hj : t ∈ cell j) (hij : i.val < j.val) :
      piece M e i ⟨t, hi⟩ = piece M e j ⟨t, hj⟩ := by
    have h₁ : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
    have h₂ : (j.val : ℝ) ≤ (i.val : ℝ) + 1 := hj.1.trans hi.2
    have hn : i.val + 1 = j.val := by exact_mod_cast le_antisymm h₁ h₂
    have hs : timeInCell ⟨t, hi⟩ = oneParam := by
      apply Subtype.ext
      change 3 * (t : ℝ) - i.val = 1
      linarith [hi.2, hj.1]
    have ht : timeInCell ⟨t, hj⟩ = zeroParam := by
      apply Subtype.ext
      change 3 * (t : ℝ) - j.val = 0
      linarith [hi.2, hj.1]
    rw [piece, piece, hs, ht, oneParam, zeroParam, edgeChart_one, edgeChart_zero]
    congr 1
    fin_cases i <;> fin_cases j <;> simp at hn ⊢ <;> rfl
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact agree i j hi hj h
  · obtain rfl : i = j := Fin.ext h
    rfl
  · exact (agree j i hj hi h).symm

private def path (e : E) : I → Space (graph M) :=
  liftCover cell (piece M e) (pieces_agree M e) cell_covers

private theorem path_time (e : E) (i : Fin 3) (t : I) :
    path M e (time i t) = edgeChart (graph M) (adj M e i) t := by
  rw [path, liftCover_of_mem (time_mem i t), piece, timeInCell_roundtrip]

private theorem continuous_path (e : E) : Continuous (path M e) := by
  apply (locallyFinite_of_finite cell).continuous cell_covers
  · intro i
    exact (isClosed_le continuous_const (continuous_const.mul continuous_subtype_val)).inter
      (isClosed_le (continuous_const.mul continuous_subtype_val) continuous_const)
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Continuous (timeInCell : cell i → I) :=
      ((continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).sub
        continuous_const).subtype_mk _
    have heq : (fun t : cell i => path M e t) = piece M e i := by
      funext t
      exact liftCover_coe t
    change Continuous (fun t : cell i => path M e t)
    rw [heq]
    exact (continuous_edgeChart (graph M) (adj M e i)).comp h

private def raw : R → Space (graph M) :=
  Sum.elim (fun v => vertex (graph M) (.inl v)) (fun p => path M p.1 p.2)

private theorem path_zero (e : E) : path M e zeroParam = vertex (graph M) (.inl (M.source e)) := by
  convert path_time M e 0 zeroParam using 1
  · congr 1
    apply Subtype.ext
    norm_num [time, zeroParam]
  · exact (edgeChart_zero _ _).symm

private theorem path_one (e : E) : path M e oneParam = vertex (graph M) (.inl (M.target e)) := by
  convert path_time M e 2 oneParam using 1
  · congr 1
    apply Subtype.ext
    norm_num [time, oneParam]
  · exact (edgeChart_one _ _).symm

private theorem raw_normal (x : R) : raw M (normal M x) = raw M x := by
  classical
  rcases x with v | ⟨e, t⟩
  · rfl
  by_cases h₀ : t = zeroParam
  · subst t
    simp [normal, raw, path_zero]
  by_cases h₁ : t = oneParam
  · subst t
    simp only [normal, h₀, ite_false, ite_true, raw, Sum.elim_inl, Sum.elim_inr, path_one]
  · simp [normal, h₀, h₁]

/-- The map from the original closed-edge quotient to the subdivided affine realization. -/
def toSubdivision : realization M → Space (graph M) :=
  Quotient.lift (raw M) fun x y h => by
    change normal M x = normal M y at h
    rw [← raw_normal M x, ← raw_normal M y, h]


private theorem split_time (t : I) : ∃ (i : Fin 3) (s : I), time i s = t := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (cell_covers ▸ mem_univ t)
  exact ⟨i, timeInCell ⟨t, hi⟩, time_roundtrip ⟨t, hi⟩⟩

private def code (x : Z) : R :=
  match x with
  | .inl v => .inl v
  | .inr (.inl e) => .inr (e, time 0 oneParam)
  | .inr (.inr e) => .inr (e, time 1 oneParam)

private def endVertex (e : E) (i : Fin 3) (last : Bool) : Z :=
  if last then dst M e i else src M e i

private def endParam (last : Bool) : I := if last then oneParam else zeroParam

omit [DecidableEq V] [DecidableEq E] in
private theorem timeCode (e : E) (i : Fin 3) (last : Bool) :
    normal M (.inr (e, time i (endParam last))) = code (endVertex M e i last) := by
  classical
  have h00 : time 0 zeroParam = zeroParam := by
    apply Subtype.ext
    norm_num [time, zeroParam]
  have h21 : time 2 oneParam = oneParam := by
    apply Subtype.ext
    norm_num [time, oneParam]
  have h10 : time 1 zeroParam = time 0 oneParam := by
    apply Subtype.ext
    norm_num [time, zeroParam, oneParam]
  have h20 : time 2 zeroParam = time 1 oneParam := by
    apply Subtype.ext
    norm_num [time, zeroParam, oneParam]
  have h01₀ : time 0 oneParam ≠ zeroParam := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [time, zeroParam, oneParam] at h'
  have h01₁ : time 0 oneParam ≠ oneParam := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [time, oneParam] at h'
  have h11₀ : time 1 oneParam ≠ zeroParam := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [time, zeroParam, oneParam] at h'
  have h11₁ : time 1 oneParam ≠ oneParam := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [time, oneParam] at h'
  have h₁₀ : oneParam ≠ zeroParam := by
    intro h
    have h' := congrArg Subtype.val h
    norm_num [zeroParam, oneParam] at h'
  fin_cases i <;> cases last <;>
    simp [endParam, endVertex, src, dst, code, h00, h21, h10, h20, h01₀, h01₁,
      h11₀, h11₁, h₁₀, normal]

private theorem chart_end (e : E) (i : Fin 3) (last : Bool) :
    edgeChart (graph M) (adj M e i) (endParam last) =
      vertex (graph M) (endVertex M e i last) := by
  cases last <;> simp [endParam, endVertex, zeroParam, oneParam]

private theorem vertex_injective : Injective (vertex (graph M)) := by
  intro u v h
  by_contra hn
  have h' := congrArg (fun x => coord (graph M) x u) h
  change (if u = u then (1 : ℝ) else 0) = (if u = v then (1 : ℝ) else 0) at h'
  simp [hn] at h'

private theorem chart_ne_vertex {u v w : Z} (h : (graph M).Adj u v) {t : I}
    (h₀ : 0 < (t : ℝ)) (h₁ : (t : ℝ) < 1) :
    edgeChart (graph M) h t ≠ vertex (graph M) w := by
  intro he
  have h' : edgeVector u v (t : ℝ) = edgeVector w w 0 := by
    exact (congrArg Subtype.val he).trans (edgeVector_zero w w).symm
  rcases endpoints_of_interior_eq h.ne h₀ h₁ h' with ⟨hu, hv⟩ | ⟨hu, hv⟩
  all_goals exact h.ne (hu.trans hv.symm)

private theorem endParam_of_not_interior (t : I)
    (h : ¬ (0 < (t : ℝ) ∧ (t : ℝ) < 1)) : ∃ b, t = endParam b := by
  push Not at h
  by_cases h₀ : (t : ℝ) = 0
  · exact ⟨false, Subtype.ext h₀⟩
  · have hp : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm h₀)
    exact ⟨true, Subtype.ext (le_antisymm t.2.2 (h hp))⟩

omit [DecidableEq V] [DecidableEq E] in
private theorem segment_unique {e f : E} {i j : Fin 3}
    (h : s(src M e i, dst M e i) = s(src M f j, dst M f j)) : e = f ∧ i = j := by
  fin_cases i <;> fin_cases j <;> simp [src, dst] at h ⊢ <;> tauto

private theorem raw_fiber [Finite V] [Finite E] {x y : R}
    (h : raw M x = raw M y) : normal M x = normal M y := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  have mixed (e : E) (i : Fin 3) (s : I) (v : V)
      (h : edgeChart (graph M) (adj M e i) s = vertex (graph M) (.inl v)) :
      normal M (.inr (e, time i s)) = normal M (.inl v) := by
    obtain ⟨b, rfl⟩ := endParam_of_not_interior s (fun hi =>
      chart_ne_vertex M (adj M e i) hi.1 hi.2 h)
    rw [chart_end] at h
    exact (timeCode M e i b).trans (congrArg code (vertex_injective M h))
  rcases x with u | ⟨e, t⟩ <;> rcases y with v | ⟨f, w⟩
  · exact congrArg Sum.inl (Sum.inl_injective (vertex_injective M h))
  · obtain ⟨j, s, rfl⟩ := split_time w
    change vertex (graph M) (.inl u) = path M f (time j s) at h
    rw [path_time] at h
    exact (mixed f j s u h.symm).symm
  · obtain ⟨i, s, rfl⟩ := split_time t
    change path M e (time i s) = vertex (graph M) (.inl v) at h
    rw [path_time] at h
    exact mixed e i s v h
  · obtain ⟨i, s, rfl⟩ := split_time t
    obtain ⟨j, r, rfl⟩ := split_time w
    change path M e (time i s) = path M f (time j r) at h
    rw [path_time, path_time] at h
    by_cases he : s(src M e i, dst M e i) = s(src M f j, dst M f j)
    · obtain ⟨rfl, rfl⟩ := segment_unique M he
      have hs : s = r := (isometry_edgeChart (graph M) (adj M e i)).injective h
      subst r
      rfl
    have noInterior (a b : E) (i j : Fin 3) (s r : I)
        (h : edgeChart (graph M) (adj M a i) s = edgeChart (graph M) (adj M b j) r)
        (he : s(src M a i, dst M a i) ≠ s(src M b j, dst M b j)) :
        ¬ (0 < (s : ℝ) ∧ (s : ℝ) < 1) := by
      intro hi
      exact he (Sym2.eq_iff.mpr (endpoints_of_interior_eq (adj M a i).ne hi.1 hi.2
        (congrArg Subtype.val h)))
    obtain ⟨a, rfl⟩ := endParam_of_not_interior s (noInterior e f i j s r h he)
    obtain ⟨b, rfl⟩ := endParam_of_not_interior r (noInterior f e j i r _ h.symm (fun hr => he hr.symm))
    rw [chart_end, chart_end] at h
    rw [timeCode, timeCode, vertex_injective M h]

private theorem raw_surjective : Surjective (raw M) := by
  have hseg (e : E) (i : Fin 3) (s : I) :
      ∃ x, raw M x = edgeChart (graph M) (adj M e i) s :=
    ⟨.inr (e, time i s), path_time M e i s⟩
  have hvertex (x : Z) : ∃ y, raw M y = vertex (graph M) x := by
    rcases x with x | (e | e)
    · exact ⟨.inl x, rfl⟩
    · exact ⟨.inr (e, time 0 oneParam),
        (path_time M e 0 oneParam).trans (edgeChart_one _ _)⟩
    · exact ⟨.inr (e, time 1 oneParam),
        (path_time M e 1 oneParam).trans (edgeChart_one _ _)⟩
  intro x
  rcases x.property with ⟨v, hv⟩ | hx
  · rw [← show vertex (graph M) v = x from Subtype.ext hv]
    exact hvertex v
  obtain ⟨⟨⟨u, v⟩, h⟩, t, ht⟩ := mem_iUnion.mp hx
  rw [← show edgeChart (graph M) h t = x from Subtype.ext ht]
  let r : I := ⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩
  rcases u with u | (e | e) <;> rcases v with v | (f | f)
  · exact False.elim h
  · have hf : M.source f = u := h
    subst u
    exact hseg f 0 t
  · have hf : M.target f = u := h
    subst u
    obtain ⟨y, hy⟩ := hseg f 2 r
    exact ⟨y, hy.trans (edgeChart_reverse _ (adj M f 2).symm t)⟩
  · have he : M.source e = v := h
    subst v
    obtain ⟨y, hy⟩ := hseg e 0 r
    exact ⟨y, hy.trans (edgeChart_reverse _ (adj M e 0).symm t)⟩
  · exact False.elim h
  · have he : e = f := h
    subst f
    exact hseg e 1 t
  · have he : M.target e = v := h
    subst v
    exact hseg e 2 t
  · have he : e = f := h
    subst f
    obtain ⟨y, hy⟩ := hseg e 1 r
    exact ⟨y, hy.trans (edgeChart_reverse _ (adj M e 1).symm t)⟩
  · exact False.elim h

variable [TopologicalSpace V] [DiscreteTopology V] [TopologicalSpace E] [DiscreteTopology E]

private theorem continuous_toSubdivision : Continuous (toSubdivision M) := by
  apply continuous_quot_lift
  apply continuous_sum_dom.mpr
  exact ⟨continuous_of_discreteTopology,
    continuous_prod_of_discrete_left.mpr (continuous_path M)⟩

/-- Subdividing each original edge into three segments gives a homeomorphic affine graph. -/
def subdivisionHomeomorph [Fintype V] [Fintype E] :
    realization M ≃ₜ Space (graph M) := by
  have hinj : Injective (toSubdivision M) := by
    intro x y
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        intro h
        exact Quotient.sound (raw_fiber M h)
  have hsurj : Surjective (toSubdivision M) := fun x =>
    let ⟨y, hy⟩ := raw_surjective M x
    ⟨Quotient.mk'' y, hy⟩
  haveI : CompactSpace (realization M) :=
    inferInstanceAs (CompactSpace (Quotient (Setoid.ker (normal M))))
  exact (Equiv.ofBijective (toSubdivision M) ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
    (continuous_toSubdivision M) (continuous_toSubdivision M).isClosedMap

#print axioms subdivisionHomeomorph

end

end D5.S1.Dynamics.Shadowing.TripleEdgeSubdivisionRealization
