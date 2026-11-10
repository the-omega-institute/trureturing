/- GID: D5/S3/Geometry/EuclideanSphereJoin
   generality: G
   mirror-B: D5/B/S3/Geometry/EuclideanSphereJoin
   mirror-E: none(waiver:classical-sphere-join)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: The ordinary quotient sphere join has the Euclidean sphere homeomorphism. -/
import D5.S3.Geometry.FiniteSimplicialJoin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! The classical sphere join, with actual quotient and Euclidean subspace topologies.
The intermediate product sphere uses the maximum norm, followed by radial normalization.
The ordinary join of an empty factor is not treated as a join unit. -/

noncomputable section
open Set Topology
open scoped unitInterval

namespace D5.S3.Geometry.EuclideanSphereJoin

open FiniteSimplicialJoin

/-- The actual unit sphere of a real normed space. -/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1

/-- The standard sphere of dimension `n`, including the two-point sphere when `n = 0`. -/
abbrev StdSphere (n : ℕ) := UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))

private def height (t : I) : ℝ := max (1 - (t : ℝ)) (t : ℝ)

private theorem height_pos (t : I) : 0 < height t := by
  have h₁ := le_max_left (1 - (t : ℝ)) (t : ℝ)
  have h₂ := le_max_right (1 - (t : ℝ)) (t : ℝ)
  dsimp [height]
  linarith

private def leftWeight (t : I) : ℝ := (1 - (t : ℝ)) / height t
private def rightWeight (t : I) : ℝ := (t : ℝ) / height t

private theorem leftWeight_nonneg (t : I) : 0 ≤ leftWeight t :=
  div_nonneg (sub_nonneg.mpr t.property.2) (height_pos t).le

private theorem rightWeight_nonneg (t : I) : 0 ≤ rightWeight t :=
  div_nonneg t.property.1 (height_pos t).le

private theorem recover_parameter (t : I) :
    rightWeight t / (leftWeight t + rightWeight t) = (t : ℝ) := by
  dsimp [leftWeight, rightWeight]
  field_simp [(height_pos t).ne']
  ring

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem unit_norm {G : Type*} [NormedAddCommGroup G] (x : UnitSphere G) :
    ‖(x : G)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property

/-- The normalized maximum-norm formula on actual join representatives. -/
def representative (p : UnitSphere E × UnitSphere F × I) : E × F :=
  (leftWeight p.2.2 • p.1.val, rightWeight p.2.2 • p.2.1.val)

private theorem block_norms (p : UnitSphere E × UnitSphere F × I) :
    ‖(representative p).1‖ = leftWeight p.2.2 ∧
      ‖(representative p).2‖ = rightWeight p.2.2 := by
  simp [representative, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (leftWeight_nonneg _), abs_of_nonneg (rightWeight_nonneg _)]

private theorem representative_mem (p : UnitSphere E × UnitSphere F × I) :
    representative p ∈ UnitSphere (E × F) := by
  rw [mem_sphere_zero_iff_norm, Prod.norm_def,
    (block_norms p).1, (block_norms p).2]
  dsimp [leftWeight, rightWeight]
  rw [max_div_div_right (height_pos _).le]
  exact div_self (height_pos _).ne'

/-- Equality of normalized vectors is precisely the ordinary join's endpoint relation. -/
theorem representative_eq_iff (p q : UnitSphere E × UnitSphere F × I) :
    representative p = representative q ↔
      (ordinaryJoinSetoid (UnitSphere E) (UnitSphere F)).r p q := by
  constructor
  · intro h
    have hl : leftWeight p.2.2 = leftWeight q.2.2 := by
      rw [← (block_norms p).1, ← (block_norms q).1, h]
    have hr : rightWeight p.2.2 = rightWeight q.2.2 := by
      rw [← (block_norms p).2, ← (block_norms q).2, h]
    have ht : p.2.2 = q.2.2 := Subtype.ext (by
      rw [← recover_parameter p.2.2, ← recover_parameter q.2.2, hl, hr])
    refine ⟨ht, ?_, ?_⟩
    · by_cases he : p.2.2 = 1
      · exact Or.inl he
      · right
        apply Subtype.ext
        have hc := congrArg Prod.fst h
        change leftWeight p.2.2 • p.1.val = leftWeight q.2.2 • q.1.val at hc
        rw [← ht] at hc
        have hn : leftWeight p.2.2 ≠ 0 := div_ne_zero
          (sub_ne_zero.mpr (fun hh => he (Subtype.ext hh.symm))) (height_pos _).ne'
        exact (smul_right_injective E hn) hc
    · by_cases he : p.2.2 = 0
      · exact Or.inl he
      · right
        apply Subtype.ext
        have hc := congrArg Prod.snd h
        change rightWeight p.2.2 • p.2.1.val = rightWeight q.2.2 • q.2.1.val at hc
        rw [← ht] at hc
        have hn : rightWeight p.2.2 ≠ 0 := div_ne_zero
          (fun hh => he (Subtype.ext hh)) (height_pos _).ne'
        exact (smul_right_injective F hn) hc
  · rintro ⟨ht, hx, hy⟩
    apply Prod.ext
    · rcases hx with hx | hx
      · simp [representative, ← ht, hx, leftWeight]
      · simp [representative, ← ht, hx]
    · rcases hy with hy | hy
      · simp [representative, ← ht, hy, rightWeight]
      · simp [representative, ← ht, hy]

private theorem continuous_representative :
    Continuous (representative (E := E) (F := F)) := by
  have ht : Continuous (fun p : UnitSphere E × UnitSphere F × I => (p.2.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hd : Continuous (fun p : UnitSphere E × UnitSphere F × I => height p.2.2) :=
    (continuous_const.sub ht).max ht
  exact ((continuous_const.sub ht).div hd (fun p => (height_pos p.2.2).ne') |>.smul
    (continuous_subtype_val.comp continuous_fst)).prodMk
    ((ht.div hd (fun p => (height_pos p.2.2).ne')).smul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))

private theorem factor_of_norm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (x₀ : UnitSphere G) (z : G) : ∃ x : UnitSphere G, ‖z‖ • x.val = z := by
  by_cases hz : z = 0
  · exact ⟨x₀, by simp [hz]⟩
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨⟨‖z‖⁻¹ • z, ?_⟩, ?_⟩
    · simp [UnitSphere, norm_smul, hn]
    · simp [smul_smul, hn]

private theorem representative_surjective (x₀ : UnitSphere E) (y₀ : UnitSphere F)
    (z : UnitSphere (E × F)) :
    ∃ p : UnitSphere E × UnitSphere F × I, representative p = z.val := by
  let r := ‖z.val.1‖
  let s := ‖z.val.2‖
  have hr : 0 ≤ r := norm_nonneg _
  have hs : 0 ≤ s := norm_nonneg _
  have hm : max r s = 1 := by simpa only [Prod.norm_def] using unit_norm z
  have hp : 0 < r + s := by
    have := le_max_iff.mp (le_of_eq hm.symm)
    rcases this with h | h <;> linarith
  let t : I := ⟨s / (r+s), div_nonneg hs hp.le, (div_le_one hp).mpr (by linarith)⟩
  have hl : 1 - (t : ℝ) = r / (r+s) := by dsimp [t]; field_simp [hp.ne']; ring
  have hd : height t = 1 / (r+s) := by
    dsimp [height]
    rw [hl, max_div_div_right hp.le, hm]
  have hw₁ : leftWeight t = r := by rw [leftWeight, hl, hd]; field_simp [hp.ne']
  have hw₂ : rightWeight t = s := by rw [rightWeight, hd]; dsimp [t]; field_simp [hp.ne']
  obtain ⟨x, hx⟩ := factor_of_norm x₀ z.val.1
  obtain ⟨y, hy⟩ := factor_of_norm y₀ z.val.2
  exact ⟨(x, y, t), Prod.ext (by simpa [representative, hw₁] using hx)
    (by simpa [representative, hw₂] using hy)⟩

/-- The normalized formula descended through the admitted ordinary quotient. -/
def productSphereMap : OrdinaryJoin (UnitSphere E) (UnitSphere F) → UnitSphere (E × F) :=
  Quotient.lift (fun p => ⟨representative p, representative_mem p⟩)
    (fun p q h => Subtype.ext ((representative_eq_iff p q).2 h))

/-- The ordinary join of compact, nonempty unit spheres is the product unit sphere. -/
def productSphereHomeomorph [CompactSpace (UnitSphere E)] [CompactSpace (UnitSphere F)]
    (x₀ : UnitSphere E) (y₀ : UnitSphere F) :
    OrdinaryJoin (UnitSphere E) (UnitSphere F) ≃ₜ UnitSphere (E × F) := by
  have hb : Function.Bijective (productSphereMap (E := E) (F := F)) := by
    constructor
    · intro p q
      refine Quotient.inductionOn₂ p q ?_
      intro a b h
      exact Quotient.sound ((representative_eq_iff a b).1 (congrArg Subtype.val h))
    · intro z
      obtain ⟨p, hp⟩ := representative_surjective x₀ y₀ z
      exact ⟨Quotient.mk _ p, Subtype.ext hp⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective productSphereMap hb)
    ((continuous_representative (E := E) (F := F)).subtype_mk _ |>.quotient_lift _)

private def radialMap {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G ≃L[ℝ] H)
    (x : UnitSphere G) : UnitSphere H :=
  (homeomorphUnitSphereProd H ⟨L x.val, by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz
    have hx : x.val = 0 := L.injective (by simpa using hz)
    have := unit_norm x
    simp [hx] at this⟩).1

private theorem radialMap_inverse {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G ≃L[ℝ] H)
    (x : UnitSphere G) : radialMap L.symm (radialMap L x) = x := by
  have hx : x.val ≠ 0 := by
    intro h
    have := unit_norm x
    simp [h] at this
  have hl : ‖L x.val‖ ≠ 0 := norm_ne_zero_iff.mpr (by
    intro h
    exact hx (L.injective (by simpa using h)))
  apply Subtype.ext
  simp [radialMap, map_smul, norm_smul, smul_smul, hl]

private def radialHomeomorph {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G ≃L[ℝ] H) :
    UnitSphere G ≃ₜ UnitSphere H where
  toFun := radialMap L
  invFun := radialMap L.symm
  left_inv := radialMap_inverse L
  right_inv := radialMap_inverse L.symm
  continuous_toFun := continuous_fst.comp ((homeomorphUnitSphereProd H).continuous.comp
    ((L.continuous.comp continuous_subtype_val).subtype_mk _))
  continuous_invFun := continuous_fst.comp ((homeomorphUnitSphereProd G).continuous.comp
    ((L.symm.continuous.comp continuous_subtype_val).subtype_mk _))

/-- The first coordinate unit point of the actual standard sphere. -/
def coordinatePoint (n : ℕ) : StdSphere n :=
  ⟨EuclideanSpace.single 0 1, by
    simp [EuclideanSpace.single, PiLp.norm_single]⟩

private def blockEquiv (p q : ℕ) :
    (EuclideanSpace ℝ (Fin (p+1)) × EuclideanSpace ℝ (Fin (q+1))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (p+q+1+1)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p+1) (m := q+1)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (by omega))).toContinuousLinearEquiv

/-- The classical homeomorphism for every pair of natural sphere dimensions.
Its source uses the actual ordinary join quotient and its target the Euclidean norm. -/
def sphereJoinHomeomorph (p q : ℕ) :
    OrdinaryJoin (StdSphere p) (StdSphere q) ≃ₜ StdSphere (p+q+1) := by
  letI : CompactSpace (StdSphere p) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  letI : CompactSpace (StdSphere q) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact (productSphereHomeomorph (coordinatePoint p) (coordinatePoint q)).trans
    (radialHomeomorph (blockEquiv p q))

private theorem blockEquiv_coordinatePoint (p q : ℕ) :
    blockEquiv p q ((coordinatePoint p).val, 0) = (coordinatePoint (p+q+1)).val := by
  have hs : (EuclideanSpace.sumEquivProd (𝕜 := ℝ)
      (ι := Fin (p+1)) (κ := Fin (q+1))).symm ((coordinatePoint p).val, 0) =
      EuclideanSpace.single (Sum.inl 0) 1 := by
    apply (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    apply Prod.ext
    · ext i
      change (coordinatePoint p).val i =
        (EuclideanSpace.single (Sum.inl (0 : Fin (p+1))) 1 :
          EuclideanSpace ℝ (Fin (p+1) ⊕ Fin (q+1))) (Sum.inl i)
      simp [coordinatePoint, EuclideanSpace.single, PiLp.single_apply]
    · ext i
      change (0 : ℝ) =
        (EuclideanSpace.single (Sum.inl (0 : Fin (p+1))) 1 :
          EuclideanSpace ℝ (Fin (p+1) ⊕ Fin (q+1))) (Sum.inr i)
      simp [EuclideanSpace.single]
  simp only [blockEquiv, EuclideanSpace.finAddEquivProd,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_trans_apply,
    ← LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    LinearIsometryEquiv.piLpCongrLeft_symm, Equiv.symm_symm,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have hs' : (PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : Fin (p+1) ⊕ Fin (q+1) => ℝ)).symm
      ((WithLp.prodContinuousLinearEquiv 2 ℝ
        (EuclideanSpace ℝ (Fin (p+1))) (EuclideanSpace ℝ (Fin (q+1)))).symm
          ((coordinatePoint p).val, 0)) = EuclideanSpace.single (Sum.inl 0) 1 := hs
  rw [hs']
  simp [coordinatePoint, EuclideanSpace.single]
  congr 1

/-- The chosen left endpoint is sent exactly to the first target coordinate point. -/
theorem sphereJoinHomeomorph_coordinatePoint (p q : ℕ) (y : StdSphere q) :
    sphereJoinHomeomorph p q (Quotient.mk _ (coordinatePoint p, y, (0 : I))) =
      coordinatePoint (p+q+1) := by
  apply Subtype.ext
  change (radialMap (blockEquiv p q)
    ⟨representative (coordinatePoint p, y, (0 : I)), representative_mem _⟩).val = _
  simp only [radialMap, homeomorphUnitSphereProd_apply_fst_coe]
  change ‖blockEquiv p q (representative (coordinatePoint p, y, (0 : I)))‖⁻¹ •
    blockEquiv p q (representative (coordinatePoint p, y, (0 : I))) = _
  have hr : representative (coordinatePoint p, y, (0 : I)) =
      ((coordinatePoint p).val, (0 : EuclideanSpace ℝ (Fin (q+1)))) := by
    simp [representative, leftWeight, rightWeight, height]
  rw [hr, blockEquiv_coordinatePoint, unit_norm]
  simp

#print axioms representative_eq_iff
#print axioms sphereJoinHomeomorph
#print axioms sphereJoinHomeomorph_coordinatePoint

end D5.S3.Geometry.EuclideanSphereJoin
