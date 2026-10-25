import D5.S3.Geometry.Hyperideal.CFMPCellIntersections435Transient
import D5.S3.Geometry.Hyperideal.LengthGramSideTrace
import D5.S3.Geometry.Hyperideal.CapTraceHull
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Convex.Topology


noncomputable section
open Set
open scoped BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private support_body from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private support_barycenter from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private endpoint_support from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private endpoint_support_zero_iff from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
set_option autoImplicit false

namespace CFMPFiniteSupportRay435Transient

/-- Transient maximum-ratio certificate. No retention/admission claim. -/
theorem finite_support_ray {I E : Type*} [Finite I] [AddCommGroup E] [Module ℝ E]
    (L : I → E →ₗ[ℝ] ℝ) (o x : E)
    (ho : ∀ i, L i o ≤ 0) (hx : ∀ i, L i x ≤ 0)
    (hdir : ∃ i, L i o < 0 ∧ 0 < L i (x-o)) :
    ∃ t : ℝ, ∃ z : E, ∃ i : I,
      0 < t ∧ t ≤ 1 ∧ L i o < 0 ∧ L i z = 0 ∧
      (∀ j, L j z ≤ 0) ∧ z = o + t⁻¹ • (x-o) ∧
      x = (1-t) • o + t • z := by
  classical
  let J := {i : I // L i o < 0}
  obtain ⟨i₀, hi₀, hd₀⟩ := hdir
  letI : Nonempty J := ⟨⟨i₀,hi₀⟩⟩
  let f : J → ℝ := fun i => L i.val (x-o) / (-L i.val o)
  obtain ⟨i, hmax⟩ := Finite.exists_max f
  let t := f i
  have hpos : 0 < t := lt_of_lt_of_le
    (div_pos hd₀ (neg_pos.mpr hi₀)) (hmax ⟨i₀,hi₀⟩)
  have hden : 0 < -L i.val o := neg_pos.mpr i.property
  have ht : t ≤ 1 := by
    change L i.val (x-o) / (-L i.val o) ≤ 1
    rw [div_le_one hden]
    rw [map_sub]
    linarith [hx i.val]
  let z := o + t⁻¹ • (x-o)
  have hz (j : I) : L j z = L j o + t⁻¹ * (L j x - L j o) := by
    simp [z, map_add, map_smul, map_sub, smul_eq_mul]
  have hzero : L i.val z = 0 := by
    rw [hz]
    have he : L i.val x - L i.val o = t * (-L i.val o) := by
      dsimp [t, f]
      rw [map_sub, div_mul_cancel₀ _ (ne_of_gt hden)]
    rw [he]
    field_simp [hpos.ne']
    <;> ring
  have hzle (j : I) : L j z ≤ 0 := by
    rw [hz]
    by_cases hj : L j o < 0
    · have hbound : (L j x - L j o) / (-L j o) ≤ t := by
        simpa only [f, t, map_sub] using hmax ⟨j,hj⟩
      have hb := (div_le_iff₀ (neg_pos.mpr hj)).mp hbound
      have hinv : 0 < t⁻¹ := inv_pos.mpr hpos
      have hc := mul_le_mul_of_nonneg_left hb hinv.le
      have hcancel : t⁻¹ * (t * (-L j o)) = -L j o := by
        field_simp [hpos.ne']
      rw [hcancel] at hc
      linarith
    · have hjo : L j o = 0 := le_antisymm (ho j) (not_lt.mp hj)
      rw [hjo, sub_zero, zero_add]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hpos.le) (hx j)
  refine ⟨t,z,i.val,hpos,ht,i.property,hzero,hzle,rfl,?_⟩
  dsimp [z]
  rw [smul_add, smul_smul, mul_inv_cancel₀ hpos.ne']
  simp only [one_smul, smul_sub, sub_smul, one_smul]
  abel

theorem body_ray (l : Fin 6 → ℝ) (o x : V)
    (ho : o ∈ cutBody l) (hx : x ∈ cutBody l) (hne : x ≠ o) :
    ∃ t : ℝ, ∃ z : V, ∃ f : Support,
      0 < t ∧ t ≤ 1 ∧ support l f o < 0 ∧ support l f z = 0 ∧
      z ∈ cutBody l ∧ z = o + t⁻¹ • (x-o) ∧ x ∈ segment ℝ o z := by
  classical
  have hdir : ∃ f : Support, support l f o < 0 ∧ 0 < support l f (x-o) := by
    have hdrop : ∃ q, x q < o q := by
      by_contra hn
      push Not at hn
      have hn' : ∀ q, 0 ≤ x q - o q := fun q => sub_nonneg.mpr (hn q)
      have hsum : ∑ q, (x q - o q) = 0 := by
        rw [Finset.sum_sub_distrib, hx.1.2, ho.1.2]
        ring
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hn' q)).mp hsum
      apply hne
      funext q
      have hz := hzero q (Finset.mem_univ q)
      linarith
    obtain ⟨q,hq⟩ := hdrop
    refine ⟨Sum.inl q, ?_, ?_⟩
    · change -o q < 0
      linarith [hx.1.1 q]
    · change -(x q - o q) > 0
      linarith
  obtain ⟨t,z,f,ht,h1,hfo,hfz,hz,hformula,hsegment⟩ :=
    finite_support_ray (support l) o x (support_body l o ho)
      (support_body l x hx) hdir
  have hbody : z ∈ cutBody l := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro q
      have := hz (Sum.inl q)
      change -z q ≤ 0 at this
      linarith
    · rw [hformula]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        hx.1.2, ho.1.2]
      ring
    · intro q
      simpa [support] using hz (Sum.inr q)
  refine ⟨t,z,f,ht,h1,hfo,hfz,hbody,hformula,?_⟩
  exact ⟨1-t,t,sub_nonneg.mpr h1,ht.le,by ring,hsegment.symm⟩

theorem cell_join (l : Fin 6 → ℝ) (n : Fin 20) :
    cell l n = convexJoin ℝ {barycenter} (boundaryTriangle l n) := by
  have hhead : vertices l n 0 = barycenter := by fin_cases n <;> rfl
  have hr : range (vertices l n) =
      insert barycenter (range (fun j : Fin 3 => vertices l n j.succ)) := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩
      fin_cases j
      · exact Or.inl hhead
      · exact Or.inr ⟨0,rfl⟩
      · exact Or.inr ⟨1,rfl⟩
      · exact Or.inr ⟨2,rfl⟩
    · rintro (rfl | ⟨j,rfl⟩)
      · exact ⟨0,hhead⟩
      · exact ⟨j.succ,rfl⟩
  unfold cell boundaryTriangle
  rw [hr, convexHull_insert (by exact ⟨vertices l n 1, ⟨0,rfl⟩⟩)]

theorem cap_trace (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (i : Fin 4) :
    {x ∈ cutBody l | support l (Sum.inr i) x = 0} =
      boundaryTriangle l (capIndex i) := by
  have h := D5.S3.Geometry.Hyperideal.CapTraceHull.cap_trace_hull l hl i
  change {x ∈ cutBody l | support l (Sum.inr i) x = 0} =
    convexHull ℝ (range (D5.S3.Geometry.Hyperideal.CapTraceHull.capEndpoint l i)) at h
  rw [h]
  unfold boundaryTriangle
  congr 1
  ext x
  constructor
  · rintro ⟨⟨j,hji⟩,rfl⟩
    fin_cases i <;> fin_cases j <;>
      simp_all [D5.S3.Geometry.Hyperideal.CapTraceHull.capEndpoint,
        capIndex,vertices,Fin.exists_fin_succ] <;> try exact (hji rfl).elim
  · rintro ⟨j,rfl⟩
    fin_cases i <;> fin_cases j
    all_goals exact ⟨⟨_,by decide⟩,rfl⟩

theorem no_diagonal_trace (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (k : Fin 4) (x : V) (hx : x ∈ cutBody l)
    (hk : support l (Sum.inl k) x = 0) : support l (Sum.inr k) x ≠ 0 := by
  let P : Set V := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  let L : Fin 2 → V →ₗ[ℝ] ℝ := ![support l (Sum.inl k),support l (Sum.inr k)]
  have hP : convexHull ℝ P = cutBody l := (cut_body_polytope l hl).2.1
  have hz := D5.S3.Geometry.Hyperideal.ZeroTraceHull.zero_trace_hull P L (by
    rintro z ⟨⟨⟨a,b⟩,hab⟩,rfl⟩ j
    fin_cases j
    · exact support_body l _ ((cut_body_polytope l hl).2.2.2 a b hab).1 (Sum.inl k)
    · exact support_body l _ ((cut_body_polytope l hl).2.2.2 a b hab).1 (Sum.inr k))
  have hempty : {z ∈ P | ∀ j, L j z = 0} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨⟨⟨⟨a,b⟩,hab⟩,rfl⟩,h⟩
    have h0 := (endpoint_support_zero_iff l hl (Sum.inl k) a b hab).mp (h 0)
    have h1 := (endpoint_support_zero_iff l hl (Sum.inr k) a b hab).mp (h 1)
    exact h0.1 h1
  rw [hempty,convexHull_empty,hP] at hz
  intro hrow
  have hh : x ∈ ({z ∈ cutBody l | ∀ j, L j z = 0} : Set V) := by
    refine ⟨hx,?_⟩
    intro j
    fin_cases j
    · exact hk
    · exact hrow
  rw [← hz] at hh
  exact hh

def fanEdge (r : Fin 4) : Fin 6 := ⟨r.val+1,by omega⟩

theorem side_triangle_join (l : Fin 6 → ℝ) (k r : Fin 4) :
    boundaryTriangle l (sideIndex k r) =
      convexJoin ℝ {sideCycle l k 0}
        (segment ℝ (sideCycle l k (fanEdge r)) (sideCycle l k (fanEdge r + 1))) := by
  have hr : range (fun j : Fin 3 => vertices l (sideIndex k r) j.succ) =
      {sideCycle l k 0,sideCycle l k (fanEdge r),sideCycle l k (fanEdge r+1)} := by
    ext x
    fin_cases k <;> fin_cases r <;>
      simp [vertices,sideIndex,sideCycle,sideOrder,fanEdge,Fin.exists_fin_succ,
        eq_comm,or_assoc,or_comm,or_left_comm]
  unfold boundaryTriangle
  rw [hr,convexHull_insert (by exact ⟨_,Or.inl rfl⟩),convexHull_pair]

theorem side_root (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (k : Fin 4) :
    sideCycle l k 0 ∈ cutBody l ∧ support l (Sum.inl k) (sideCycle l k 0) = 0 := by
  let σ := sideOrder k
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have h01 : k ≠ σ 1 := by fin_cases k <;> decide
  have h02 : k ≠ σ 2 := by fin_cases k <;> decide
  refine ⟨((cut_body_polytope l hl).2.2.2 (σ 1) (σ 2) h12).1, ?_⟩
  exact (endpoint_support l hl (Sum.inl k) (σ 1) (σ 2) h12).1 ⟨h01,h02⟩

theorem strict_side_exit (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (k : Fin 4)
    (f : Support) (hf : support l f (sideCycle l k 0) < 0) :
    f = Sum.inr k ∨ ∃ r : Fin 4, f = cycleSupport k (fanEdge r) := by
  have h12 : sideOrder k 1 ≠ sideOrder k 2 := (sideOrder k).injective.ne (by decide)
  have hn : ¬incident f (sideOrder k 1) (sideOrder k 2) := by
    intro hi
    have hz := (endpoint_support l hl f _ _ h12).1 hi
    have : support l f (sideCycle l k 0) = 0 := hz
    linarith
  cases f with
  | inl i =>
    fin_cases k <;> fin_cases i <;>
      simp_all [incident,sideOrder,cycleSupport,fanEdge,Fin.exists_fin_succ]
  | inr i =>
    fin_cases k <;> fin_cases i <;>
      simp_all [incident,sideOrder,cycleSupport,fanEdge,Fin.exists_fin_succ]

theorem side_cover (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (k : Fin 4)
    (x : V) (hx : x ∈ cutBody l) (hk : support l (Sum.inl k) x = 0) :
    ∃ r : Fin 4, x ∈ boundaryTriangle l (sideIndex k r) := by
  have hroot := side_root l hl k
  by_cases he : x = sideCycle l k 0
  · subst x
    refine ⟨0,?_⟩
    rw [side_triangle_join]
    apply subset_convexJoin_left (by exact ⟨_,left_mem_segment _ _ _⟩)
    exact rfl
  obtain ⟨t,z,f,ht,h1,hfo,hfz,hz,hformula,hsegment⟩ :=
    body_ray l (sideCycle l k 0) x hroot.1 hx he
  have hzk : support l (Sum.inl k) z = 0 := by
    rw [hformula]
    simp only [map_add,map_smul,map_sub,hk,hroot.2,sub_self,smul_zero,add_zero]
  rcases strict_side_exit l hl k f hfo with hbad | ⟨r,hr⟩
  · subst f
    exact ((no_diagonal_trace l hl k z hz hzk) hfz).elim
  · refine ⟨r,?_⟩
    have hzseg : z ∈ segment ℝ (sideCycle l k (fanEdge r))
        (sideCycle l k (fanEdge r+1)) := by
      rw [← cycle_edge_hull l hl k (fanEdge r)]
      exact ⟨hz,hzk,hr ▸ hfz⟩
    rw [side_triangle_join]
    exact mem_convexJoin.mpr ⟨sideCycle l k 0,rfl,z,hzseg,hsegment⟩

theorem twenty_cell_cover (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) :
    cutBody l = ⋃ n : Fin 20, cell l n := by
  have hb : barycenter ∈ cutBody l := (shared_radial_body l hl).2.1
  have hc : Convex ℝ (cutBody l) := by
    rw [← (cut_body_polytope l hl).2.1]
    exact convex_convexHull _ _
  apply Set.Subset.antisymm
  · intro x hx
    by_cases he : x = barycenter
    · subst x
      refine Set.mem_iUnion.mpr ⟨0,?_⟩
      exact subset_convexHull ℝ _ ⟨0,rfl⟩
    obtain ⟨t,z,f,ht,h1,hfo,hfz,hz,hformula,hsegment⟩ := body_ray l barycenter x hb hx he
    cases f with
    | inr i =>
      have hztri : z ∈ boundaryTriangle l (capIndex i) := by
        rw [← cap_trace l hl i]
        exact ⟨hz,hfz⟩
      refine Set.mem_iUnion.mpr ⟨capIndex i,?_⟩
      rw [cell_join]
      exact mem_convexJoin.mpr ⟨barycenter,rfl,z,hztri,hsegment⟩
    | inl k =>
      obtain ⟨r,hr⟩ := side_cover l hl k z hz hfz
      refine Set.mem_iUnion.mpr ⟨sideIndex k r,?_⟩
      rw [cell_join]
      exact mem_convexJoin.mpr ⟨barycenter,rfl,z,hr,hsegment⟩
  · intro x hx
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    change x ∈ convexHull ℝ (range (vertices l n)) at hn
    apply convexHull_min ?_ hc hn
    rintro y ⟨j,rfl⟩
    fin_cases n <;> fin_cases j
    all_goals first
      | exact hb
      | exact ((cut_body_polytope l hl).2.2.2 _ _ (by decide)).1

end CFMPFiniteSupportRay435Transient


noncomputable section
open Set
open scoped BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private support_barycenter from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private endpoint_support from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
set_option autoImplicit false
set_option maxRecDepth 10000



namespace CFMPTwentyCellIntegralAssembly435Transient

open scoped Function ENNReal
open MeasureTheory
open CFMPCellIntersections435Transient

abbrev C (l : Fin 6 → ℝ) (n : Fin 20) : Set (Fin 3 → ℝ) := drop '' cell l n
abbrev K (l : Fin 6 → ℝ) : Set (Fin 3 → ℝ) := drop '' cutBody l

-- Temporary exact applications of existing finite-union integration APIs.
theorem chart_cover (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    K l = ⋃ n : Fin 20, C l n := by
  simp only [K, C, CFMPFiniteSupportRay435Transient.twenty_cell_cover l hl,
    Set.image_iUnion]

theorem chart_cell_compact (l : Fin 6 → ℝ) (n : Fin 20) : IsCompact (C l n) := by
  exact ((Set.finite_range (vertices l n)).isCompact_convexHull ℝ).image
    drop.continuous_of_finiteDimensional

theorem chart_cell_ae_disjoint (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    Pairwise (AEDisjoint volume on C l) := by
  intro i j hij
  exact chart_overlap_null l hl i j hij

theorem actual_body_lintegral (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : (Fin 3 → ℝ) → ℝ≥0∞) :
    (∫⁻ z in K l, f z) = ∑ n : Fin 20, ∫⁻ z in C l n, f z := by
  rw [chart_cover l hl]
  have hd : Set.Pairwise (↑(Finset.univ : Finset (Fin 20)))
      (AEDisjoint volume on C l) := by
    intro i hi j hj hij
    exact chart_cell_ae_disjoint l hl hij
  simpa using lintegral_biUnion_finset₀ hd
    (fun n _ => (chart_cell_compact l n).measurableSet.nullMeasurableSet) f

theorem actual_body_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : (Fin 3 → ℝ) → E) (hf : IntegrableOn f (K l)) :
    (∫ z in K l, f z) = ∑ n : Fin 20, ∫ z in C l n, f z := by
  rw [chart_cover l hl] at hf ⊢
  simpa only [tsum_fintype] using integral_iUnion_ae
    (fun n => (chart_cell_compact l n).measurableSet.nullMeasurableSet)
    (chart_cell_ae_disjoint l hl) hf

end CFMPTwentyCellIntegralAssembly435Transient
