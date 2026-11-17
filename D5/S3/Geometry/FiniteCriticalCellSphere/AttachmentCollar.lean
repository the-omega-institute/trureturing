/- GID: D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar
   mirror-E: none(waiver:finite-critical-cell-sphere)
   anchors: [mathlib/module/Mathlib.Topology.CompactOpen, mathlib/module/Mathlib.Topology.Piecewise]
   utility: none
   digest: The attachment collar and core quotient. -/


import D5.S3.Geometry.FiniteAlexanderDualCollapse
import D5.S3.Geometry.FiniteSimplexBoundarySphere
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Piecewise
import Mathlib.Data.Fintype.Card

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteCriticalCellSphere
open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteRelativeSimplicialCollapse
open FiniteSimplexBoundarySphere (Simplex E barycenter
  faceCoordinateHomeomorph minCoord sigma cardR minCoord_le minCoord_attained
  sigma_nonneg sigma_eq_zero_iff cardR_pos cardR_ne
  continuous_minCoord BoundaryQuotient)

/- Closed-cover gluing is used twice: first on the two radial regions, then on
   the core and the actual simplex. Neither function is extended by fiat. -/
private def pasteClosed {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    (S T : Set Z) (hS : IsClosed S) (hT : IsClosed T)
    (cover : ∀ z, z ∈ S ∨ z ∈ T) (f : C(S, Y)) (g : C(T, Y))
    (agree : ∀ z (hs : z ∈ S) (ht : z ∈ T), f ⟨z, hs⟩ = g ⟨z, ht⟩) : C(Z, Y) := by
  classical
  let k : Z → Y := fun z => if hs : z ∈ S then f ⟨z, hs⟩
    else g ⟨z, (cover z).resolve_left hs⟩
  have kS (z : S) : k z = f z := by simp only [k, dif_pos z.2]
  have kT (z : T) : k z = g z := by
    dsimp only [k]
    split_ifs with hs
    · exact agree z hs z.2
    · rfl
  have hcS : ContinuousOn k S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact f.continuous.congr (fun z => (kS z).symm)
  have hcT : ContinuousOn k T := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact g.continuous.congr (fun z => (kT z).symm)
  have hu : S ∪ T = univ := Set.eq_univ_of_forall cover
  exact ⟨k, by
    rw [← continuousOn_univ, ← hu]
    exact hcS.union_of_isClosed hcT hS hT⟩

private theorem pasteClosed_left {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    (S T : Set Z) (hS : IsClosed S) (hT : IsClosed T)
    (cover : ∀ z, z ∈ S ∨ z ∈ T) (f : C(S, Y)) (g : C(T, Y))
    (agree : ∀ z (hs : z ∈ S) (ht : z ∈ T), f ⟨z, hs⟩ = g ⟨z, ht⟩)
    (z : Z) (hz : z ∈ S) : pasteClosed S T hS hT cover f g agree z = f ⟨z, hz⟩ := by
  classical
  simp only [pasteClosed, ContinuousMap.coe_mk, dif_pos hz]

private theorem pasteClosed_right {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    (S T : Set Z) (hS : IsClosed S) (hT : IsClosed T)
    (cover : ∀ z, z ∈ S ∨ z ∈ T) (f : C(S, Y)) (g : C(T, Y))
    (agree : ∀ z (hs : z ∈ S) (ht : z ∈ T), f ⟨z, hs⟩ = g ⟨z, ht⟩)
    (z : Z) (hz : z ∈ T) : pasteClosed S T hS hT cover f g agree z = g ⟨z, hz⟩ := by
  classical
  dsimp only [pasteClosed, ContinuousMap.coe_mk]
  split_ifs with hs
  · exact agree z hs hz
  · rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All geometric inputs refer to the original ambient labels. The ONLY
homotopy input is a standalone based contraction of the core P. -/
structure Attachment (V : Type*) [Fintype V] [DecidableEq V] where
  X : PreAbstractSimplicialComplex V
  P : PreAbstractSimplicialComplex V
  face : Finset V
  face_nonempty : face.Nonempty
  union_eq : X = P ⊔ FiniteAlexanderDualCollapse.simplex face
  intersection_eq : P ⊓ FiniteAlexanderDualCollapse.simplex face =
    FiniteAlexanderDualCollapse.boundary face
  p : Space P
  contraction : (ContinuousMap.id (Space P)).HomotopyRel
    (ContinuousMap.const _ p) {p}

namespace Attachment
variable (A : Attachment V)

instance faceInhabited : Nonempty A.face :=
  ⟨⟨A.face_nonempty.choose, A.face_nonempty.choose_spec⟩⟩

abbrev Disk := Simplex A.face
abbrev BDisk := {x : A.Disk // FiniteSimplexBoundarySphere.boundary x}

def coreSet : Set (Space A.X) := {x | x.1 ∈ realization A.P}
def diskSet : Set (Space A.X) := {x | x.1 ∈ faceSimplex A.face}

private theorem core_le : A.P ≤ A.X := by rw [A.union_eq]; exact le_sup_left
private theorem simplex_le : FiniteAlexanderDualCollapse.simplex A.face ≤ A.X := by
  rw [A.union_eq]; exact le_sup_right

def coreIn : C(Space A.P, Space A.X) := realizationInclusion A.core_le

def basepoint : Space A.X := A.coreIn A.p

private theorem simplex_realization :
    realization (FiniteAlexanderDualCollapse.simplex A.face) = faceSimplex A.face := by
  ext x
  rw [realization_mem_iff]
  constructor
  · rintro ⟨s, ⟨_, hs⟩, hx⟩
    exact ⟨hx.1, hx.2.1, fun v hv => hx.2.2 v (fun h => hv (hs h))⟩
  · intro hx
    exact ⟨A.face, ⟨A.face_nonempty, subset_rfl⟩, hx⟩

private theorem disk_mem (x : A.Disk) :
    (faceCoordinateHomeomorph A.face x).1 ∈ realization A.X := by
  apply (realization_mem_iff _ _).mpr
  exact ⟨A.face, A.simplex_le ⟨A.face_nonempty, subset_rfl⟩,
    (faceCoordinateHomeomorph A.face x).2⟩

/-- The existing zero-extension homeomorphism followed by literal inclusion. -/
def diskIn : C(A.Disk, Space A.X) :=
  ⟨fun x => ⟨(faceCoordinateHomeomorph A.face x).1, A.disk_mem x⟩,
    (continuous_subtype_val.comp (faceCoordinateHomeomorph A.face).continuous).subtype_mk _⟩

private def coreRestrict : C(A.coreSet, Space A.P) :=
  ⟨fun x => ⟨x.1.1, x.2⟩, (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def diskRestrict : C(A.diskSet, A.Disk) :=
  (toContinuousMap (faceCoordinateHomeomorph A.face).symm).comp
    ⟨fun x => ⟨x.1.1, x.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem diskIn_restrict (x : A.diskSet) : A.diskIn (A.diskRestrict x) = x.1 := by
  apply Subtype.ext
  change (faceCoordinateHomeomorph A.face
    ((faceCoordinateHomeomorph A.face).symm ⟨x.1.1, x.2⟩)).1 = x.1.1
  exact congrArg (fun y : ↥(faceSimplex A.face) => y.1)
    ((faceCoordinateHomeomorph A.face).apply_symm_apply ⟨x.1.1, x.2⟩)

theorem restrict_diskIn (x : A.Disk) :
    A.diskRestrict ⟨A.diskIn x, (faceCoordinateHomeomorph A.face x).2⟩ = x :=
  (faceCoordinateHomeomorph A.face).symm_apply_apply x

theorem cover (x : Space A.X) : x ∈ A.coreSet ∨ x ∈ A.diskSet := by
  obtain ⟨s, hs, hx⟩ := (realization_mem_iff A.X x.1).mp x.2
  rw [A.union_eq] at hs
  rcases hs with hs | hs
  · exact Or.inl ((realization_mem_iff _ _).mpr ⟨s, hs, hx⟩)
  · exact Or.inr ⟨hx.1, hx.2.1, fun v hv => hx.2.2 v (fun h => hv (hs.2 h))⟩

theorem core_closed : IsClosed A.coreSet :=
  (realization_closed A.P).preimage continuous_subtype_val

theorem disk_closed : IsClosed A.diskSet := by
  have hc : IsClosed (faceSimplex A.face) := by
    rw [faceSimplex_eq_convexHull]
    exact (A.face.finite_toSet.image (fun v : V => Pi.single v (1 : ℝ))).isClosed_convexHull ℝ
  exact hc.preimage continuous_subtype_val

/- This bridge is about the entire native boundary, including its empty
   ordinary realization when the face has one label. -/
private theorem native_boundary_iff (x : ↥(faceSimplex A.face)) :
    x.1 ∈ realization (FiniteAlexanderDualCollapse.boundary A.face) ↔
      FiniteSimplexBoundarySphere.faceBoundary A.face x := by
  rw [realization_mem_iff]
  constructor
  · rintro ⟨s, ⟨_, hs⟩, hx⟩
    obtain ⟨i, hi, his⟩ := Finset.exists_of_ssubset hs
    exact ⟨i, hi, hx.2.2 i his⟩
  · rintro ⟨i, hi, hxi⟩
    have hn : (A.face.erase i).Nonempty := by
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
        (show (∑ j, x.1 j) ≠ 0 by rw [x.2.2.1]; norm_num)
      refine ⟨j, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · intro h; subst j; exact hj hxi
      · by_contra h; exact hj (x.2.2.2 j h)
    refine ⟨A.face.erase i, ⟨hn, Finset.erase_ssubset hi⟩, x.2.1, x.2.2.1, ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j; exact hxi
    · exact x.2.2.2 j (fun h => hj (Finset.mem_erase.mpr ⟨hji, h⟩))

theorem diskIn_mem_core_iff (x : A.Disk) :
    A.diskIn x ∈ A.coreSet ↔ FiniteSimplexBoundarySphere.boundary x := by
  have hx : (faceCoordinateHomeomorph A.face x).1 ∈
      realization (FiniteAlexanderDualCollapse.simplex A.face) := by
    rw [A.simplex_realization]; exact (faceCoordinateHomeomorph A.face x).2
  have hi := realization_intersection A.P (FiniteAlexanderDualCollapse.simplex A.face)
  constructor
  · intro hp
    have hb : (faceCoordinateHomeomorph A.face x).1 ∈
        realization (FiniteAlexanderDualCollapse.boundary A.face) := by
      rw [← A.intersection_eq, hi]; exact ⟨hp, hx⟩
    exact (FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary A.face x).mp
      ((A.native_boundary_iff _).mp hb)
  · intro hb
    have hn := (A.native_boundary_iff _).mpr
      ((FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_boundary A.face x).mpr hb)
    rw [← A.intersection_eq, hi] at hn
    exact hn.1

def boundaryToCore : C(A.BDisk, Space A.P) :=
  ⟨fun x => ⟨(A.diskIn x.1).1, (A.diskIn_mem_core_iff x.1).mpr x.2⟩,
    (continuous_subtype_val.comp (A.diskIn.continuous.comp continuous_subtype_val)).subtype_mk _⟩

private theorem boundaryToCore_in (x : A.BDisk) :
    A.coreIn (A.boundaryToCore x) = A.diskIn x.1 := Subtype.ext rfl

/-- The radial gauge uses only face labels; ambient ghosts never enter a min. -/
def rho (x : A.Disk) : ℝ := 1 - sigma x

private theorem continuous_rho : Continuous A.rho :=
  continuous_const.sub (continuous_const.mul continuous_minCoord)

private theorem rho_le_one (x : A.Disk) : A.rho x ≤ 1 := sub_le_self _ (sigma_nonneg x)

private theorem rho_boundary (x : A.Disk) (hx : FiniteSimplexBoundarySphere.boundary x) :
    A.rho x = 1 := by rw [rho, (sigma_eq_zero_iff x).mpr hx]; ring

/-- Radial expansion at a positive denominator u, bounded below by rho.
This stays in the literal simplex; no norm of a plain function is involved. -/
def expand (x : A.Disk) (u : ℝ) (hu : 0 < u) (hr : A.rho x ≤ u) : A.Disk :=
  ⟨barycenter A.face + u⁻¹ • (x.1 - barycenter A.face), by
    constructor
    · intro i
      change 0 ≤ (cardR A.face)⁻¹ + u⁻¹ * (x.1 i - (cardR A.face)⁻¹)
      have hm := cardR_pos (Λ := A.face)
      have hi := minCoord_le x i
      have h : 0 ≤ u + cardR A.face * x.1 i - 1 := by
        have him := mul_le_mul_of_nonneg_left hi hm.le
        dsimp [rho, sigma] at hr
        linarith
      have he : (cardR A.face)⁻¹ + u⁻¹ * (x.1 i - (cardR A.face)⁻¹) =
          (u + cardR A.face * x.1 i - 1) / (cardR A.face * u) := by
        field_simp [hu.ne', cardR_ne (Λ := A.face)] <;> ring
      rw [he]
      exact div_nonneg h (mul_nonneg hm.le hu.le)
    · have hb : (∑ i, barycenter A.face i) = 1 := by
        change (∑ _ : A.face, (cardR A.face)⁻¹) = 1
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (cardR_ne (Λ := A.face))
      change (∑ i, (barycenter A.face i + u⁻¹ * (x.1 i - barycenter A.face i))) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, x.2.2, hb]
      ring⟩

private theorem expand_coordinate (x : A.Disk) (u : ℝ) (hu : 0 < u)
    (hr : A.rho x ≤ u) (i : A.face) :
    (A.expand x u hu hr).1 i = (cardR A.face)⁻¹ + (x.1 i - (cardR A.face)⁻¹) / u := by
  change (cardR A.face)⁻¹ + u⁻¹ * (x.1 i - (cardR A.face)⁻¹) = _
  rw [div_eq_mul_inv, mul_comm _ u⁻¹]

private theorem expand_one (x : A.Disk) :
    A.expand x 1 zero_lt_one (A.rho_le_one x) = x := by
  apply Subtype.ext
  change barycenter A.face + (1 : ℝ)⁻¹ • (x.1 - barycenter A.face) = x.1
  simp only [inv_one, one_smul]
  abel

private theorem expand_congr (x : A.Disk) {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hru : A.rho x ≤ u) (hrv : A.rho x ≤ v) (he : u = v) :
    A.expand x u hu hru = A.expand x v hv hrv := by subst v; rfl

private theorem expand_boundary (x : A.Disk) (hr : 0 < A.rho x) :
    FiniteSimplexBoundarySphere.boundary (A.expand x (A.rho x) hr le_rfl) := by
  obtain ⟨i, hi⟩ := minCoord_attained x
  refine ⟨i, ?_⟩
  rw [A.expand_coordinate, hi]
  have hm := cardR_ne (Λ := A.face)
  change 0 < 1 - cardR A.face * minCoord x at hr
  dsimp [rho, sigma]
  field_simp [hm, hr.ne'] <;> ring

private theorem continuous_expand {Z : Type*} [TopologicalSpace Z]
    (f : Z → A.Disk) (u : Z → ℝ) (hu : ∀ z, 0 < u z)
    (hr : ∀ z, A.rho (f z) ≤ u z) (hf : Continuous f) (hc : Continuous u) :
    Continuous (fun z => A.expand (f z) (u z) (hu z) (hr z)) := by
  apply Continuous.subtype_mk
  exact continuous_const.add ((hc.inv₀ (fun z => (hu z).ne')).smul
    ((continuous_subtype_val.comp hf).sub continuous_const))

/-- The seam denominator, always at least one half. -/
def cut (_A : Attachment V) (s : I) : ℝ := 1 - (s : ℝ) / 2

private theorem cut_lower (s : I) : (1 / 2 : ℝ) ≤ A.cut s := by
  dsimp [cut]; linarith [s.2.2]
theorem cut_pos (s : I) : 0 < A.cut s := lt_of_lt_of_le (by norm_num) (A.cut_lower s)
private theorem cut_le_one (s : I) : A.cut s ≤ 1 := by dsimp [cut]; linarith [s.2.1]
private theorem continuous_cut : Continuous A.cut :=
  continuous_const.sub (continuous_subtype_val.div_const 2)

private def innerRegion : Set (I × A.Disk) := {z | A.rho z.2 ≤ A.cut z.1}
def outerRegion : Set (I × A.Disk) := {z | A.cut z.1 ≤ A.rho z.2}
private theorem inner_closed : IsClosed A.innerRegion :=
  isClosed_le (A.continuous_rho.comp continuous_snd) (A.continuous_cut.comp continuous_fst)
private theorem outer_closed : IsClosed A.outerRegion :=
  isClosed_le (A.continuous_cut.comp continuous_fst) (A.continuous_rho.comp continuous_snd)
private theorem radial_cover (z : I × A.Disk) : z ∈ A.innerRegion ∨ z ∈ A.outerRegion :=
  le_total (A.rho z.2) (A.cut z.1)

private def innerMap : C(A.innerRegion, Space A.X) :=
  A.diskIn.comp ⟨fun z => A.expand z.1.2 (A.cut z.1.1) (A.cut_pos _) z.2,
    A.continuous_expand (fun z : A.innerRegion => z.1.2) (fun z => A.cut z.1.1)
      (fun z => A.cut_pos _) (fun z => z.2)
      (continuous_snd.comp continuous_subtype_val)
      (A.continuous_cut.comp (continuous_fst.comp continuous_subtype_val))⟩

private theorem outer_denominator_lower (z : A.outerRegion) : (1 / 2 : ℝ) ≤ A.rho z.1.2 :=
  (A.cut_lower z.1.1).trans z.2

private theorem outer_rho_pos (z : A.outerRegion) : 0 < A.rho z.1.2 :=
  lt_of_lt_of_le (by norm_num) (A.outer_denominator_lower z)

def projection : C(A.outerRegion, A.BDisk) :=
  ⟨fun z => ⟨A.expand z.1.2 (A.rho z.1.2) (A.outer_rho_pos z) le_rfl,
      A.expand_boundary z.1.2 (A.outer_rho_pos z)⟩,
    (A.continuous_expand (fun z : A.outerRegion => z.1.2) (fun z => A.rho z.1.2)
      (fun z => A.outer_rho_pos z) (fun _ => le_rfl)
      (continuous_snd.comp continuous_subtype_val)
      (A.continuous_rho.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

def outerTime : C(A.outerRegion, I) := by
  refine ⟨fun z => ⟨2 * A.rho z.1.2 - 2 + (z.1.1 : ℝ), ?_⟩, ?_⟩
  · have h := z.2
    dsimp [outerRegion, cut] at h
    constructor
    · linarith
    · linarith [A.rho_le_one z.1.2, z.1.1.2.2]
  · exact (((continuous_const.mul (A.continuous_rho.comp
      (continuous_snd.comp continuous_subtype_val))).sub continuous_const).add
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))).subtype_mk _

private def outerMap : C(A.outerRegion, Space A.X) :=
  A.coreIn.comp ⟨fun z => A.contraction (A.outerTime z, A.boundaryToCore (A.projection z)),
    A.contraction.continuous.comp
      (A.outerTime.continuous.prodMk (A.boundaryToCore.continuous.comp A.projection.continuous))⟩

private theorem radial_seam (z : I × A.Disk) (hi : z ∈ A.innerRegion)
    (ho : z ∈ A.outerRegion) : A.innerMap ⟨z, hi⟩ = A.outerMap ⟨z, ho⟩ := by
  have he : A.rho z.2 = A.cut z.1 := le_antisymm hi ho
  have ht : A.outerTime ⟨z, ho⟩ = 0 := by
    apply Subtype.ext
    change 2 * A.rho z.2 - 2 + (z.1 : ℝ) = 0
    rw [he]
    dsimp [cut]; ring
  change A.diskIn (A.expand z.2 (A.cut z.1) (A.cut_pos _) hi) =
    A.coreIn (A.contraction (A.outerTime ⟨z, ho⟩, A.boundaryToCore (A.projection ⟨z, ho⟩)))
  rw [ht, A.contraction.apply_zero]
  change A.diskIn (A.expand z.2 (A.cut z.1) (A.cut_pos _) hi) =
    A.coreIn (A.boundaryToCore (A.projection ⟨z, ho⟩))
  rw [A.boundaryToCore_in]
  apply congrArg A.diskIn
  exact A.expand_congr z.2 (A.cut_pos z.1)
    (A.outer_rho_pos ⟨z, ho⟩) hi le_rfl he.symm

/-- The actual disk collar, built by closed-cover pasting, including its seam. -/
def diskCollar : C(I × A.Disk, Space A.X) :=
  pasteClosed A.innerRegion A.outerRegion A.inner_closed A.outer_closed
    A.radial_cover A.innerMap A.outerMap A.radial_seam

private theorem diskCollar_inner (s : I) (x : A.Disk) (hx : A.rho x ≤ A.cut s) :
    A.diskCollar (s, x) = A.diskIn (A.expand x (A.cut s) (A.cut_pos s) hx) :=
  pasteClosed_left A.innerRegion A.outerRegion A.inner_closed A.outer_closed
    A.radial_cover A.innerMap A.outerMap A.radial_seam (s, x) hx

private theorem diskCollar_outer (s : I) (x : A.Disk) (hx : A.cut s ≤ A.rho x) :
    A.diskCollar (s, x) = A.outerMap ⟨(s, x), hx⟩ :=
  pasteClosed_right A.innerRegion A.outerRegion A.inner_closed A.outer_closed
    A.radial_cover A.innerMap A.outerMap A.radial_seam (s, x) hx

private theorem diskCollar_zero (x : A.Disk) : A.diskCollar (0, x) = A.diskIn x := by
  have hc : A.cut 0 = 1 := by norm_num [cut]
  have hr : A.rho x ≤ A.cut 0 := by simpa only [hc] using A.rho_le_one x
  rw [A.diskCollar_inner 0 x hr]
  apply congrArg A.diskIn
  exact (A.expand_congr _ _ _ _ _ hc).trans (A.expand_one x)

private theorem diskCollar_boundary (s : I) (x : A.BDisk) :
    A.diskCollar (s, x.1) = A.coreIn (A.contraction (s, A.boundaryToCore x)) := by
  have hr := A.rho_boundary x.1 x.2
  have ho : A.cut s ≤ A.rho x.1 := by simpa only [hr] using A.cut_le_one s
  rw [A.diskCollar_outer s x.1 ho]
  have ht : A.outerTime ⟨(s, x.1), ho⟩ = s := by
    apply Subtype.ext
    change 2 * A.rho x.1 - 2 + (s : ℝ) = (s : ℝ)
    rw [hr]; ring
  have hp : A.projection ⟨(s, x.1), ho⟩ = x := by
    apply Subtype.ext
    change A.expand x.1 (A.rho x.1) (A.outer_rho_pos ⟨(s, x.1), ho⟩) le_rfl = x.1
    exact (A.expand_congr x.1 (A.outer_rho_pos ⟨(s, x.1), ho⟩)
      zero_lt_one le_rfl (A.rho_le_one x.1) hr).trans (A.expand_one x.1)
  change A.coreIn (A.contraction (A.outerTime ⟨(s, x.1), ho⟩,
    A.boundaryToCore (A.projection ⟨(s, x.1), ho⟩))) = _
  rw [ht, hp]

private def coreCylinder : Set (I × Space A.X) := {z | z.2 ∈ A.coreSet}
private def diskCylinder : Set (I × Space A.X) := {z | z.2 ∈ A.diskSet}
private theorem coreCylinder_closed : IsClosed A.coreCylinder := A.core_closed.preimage continuous_snd
private theorem diskCylinder_closed : IsClosed A.diskCylinder := A.disk_closed.preimage continuous_snd
private theorem cylinder_cover (z : I × Space A.X) : z ∈ A.coreCylinder ∨ z ∈ A.diskCylinder :=
  A.cover z.2

private def coreCylinderMap : C(A.coreCylinder, Space A.X) :=
  A.coreIn.comp ⟨fun z => A.contraction (z.1.1, A.coreRestrict ⟨z.1.2, z.2⟩),
    A.contraction.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (A.coreRestrict.continuous.comp
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)))⟩

private def diskCylinderMap : C(A.diskCylinder, Space A.X) :=
  A.diskCollar.comp ⟨fun z => (z.1.1, A.diskRestrict ⟨z.1.2, z.2⟩),
    (continuous_fst.comp continuous_subtype_val).prodMk
      (A.diskRestrict.continuous.comp
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩

private theorem attachment_seam (z : I × Space A.X)
    (hp : z ∈ A.coreCylinder) (hd : z ∈ A.diskCylinder) :
    A.coreCylinderMap ⟨z, hp⟩ = A.diskCylinderMap ⟨z, hd⟩ := by
  let x := A.diskRestrict ⟨z.2, hd⟩
  have hix : A.diskIn x = z.2 := A.diskIn_restrict ⟨z.2, hd⟩
  have hb : FiniteSimplexBoundarySphere.boundary x :=
    (A.diskIn_mem_core_iff x).mp (hix.symm ▸ hp)
  have hc : A.boundaryToCore ⟨x, hb⟩ = A.coreRestrict ⟨z.2, hp⟩ := by
    apply Subtype.ext
    change (A.diskIn x).1 = z.2.1
    exact congrArg (fun y : Space A.X => y.1) hix
  change A.coreIn (A.contraction (z.1, A.coreRestrict ⟨z.2, hp⟩)) = A.diskCollar (z.1, x)
  rw [A.diskCollar_boundary z.1 ⟨x, hb⟩, hc]

/-- The contraction is extended over the disk by the explicit collar, not by
assuming that a free pair in P stays free in X. Time is the first coordinate. -/
def collar : C(I × Space A.X, Space A.X) :=
  pasteClosed A.coreCylinder A.diskCylinder A.coreCylinder_closed A.diskCylinder_closed
    A.cylinder_cover A.coreCylinderMap A.diskCylinderMap A.attachment_seam

private theorem collar_core_apply (s : I) (x : A.coreSet) :
    A.collar (s, x.1) = A.coreIn (A.contraction (s, A.coreRestrict x)) :=
  pasteClosed_left _ _ _ _ _ _ _ _ (s, x.1) x.2

private theorem collar_disk_apply (s : I) (x : A.Disk) :
    A.collar (s, A.diskIn x) = A.diskCollar (s, x) := by
  have hd := pasteClosed_right A.coreCylinder A.diskCylinder
    A.coreCylinder_closed A.diskCylinder_closed A.cylinder_cover
    A.coreCylinderMap A.diskCylinderMap A.attachment_seam
    (s, A.diskIn x) (faceCoordinateHomeomorph A.face x).2
  change A.collar (s, A.diskIn x) = A.diskCollar
    (s, A.diskRestrict ⟨A.diskIn x, (faceCoordinateHomeomorph A.face x).2⟩) at hd
  rw [A.restrict_diskIn x] at hd
  exact hd

private theorem collar_zero_apply (x : Space A.X) : A.collar (0, x) = x := by
  rcases A.cover x with hp | hd
  · rw [A.collar_core_apply 0 ⟨x, hp⟩, A.contraction.apply_zero]
    exact Subtype.ext rfl
  · have hx := A.diskIn_restrict ⟨x, hd⟩
    change A.diskIn (A.diskRestrict ⟨x, hd⟩) = x at hx
    exact (congrArg (fun y => A.collar (0, y)) hx.symm).trans
      ((A.collar_disk_apply 0 _).trans ((A.diskCollar_zero _).trans hx))

private theorem collar_core_one (x : A.coreSet) : A.collar (1, x.1) = A.basepoint := by
  rw [A.collar_core_apply, A.contraction.apply_one]
  rfl

private theorem collar_preserves_core (s : I) (x : A.coreSet) :
    A.collar (s, x.1) ∈ A.coreSet := by
  rw [A.collar_core_apply]
  exact (A.contraction (s, A.coreRestrict x)).2

private theorem collar_fixed (s : I) : A.collar (s, A.basepoint) = A.basepoint := by
  have hb : A.basepoint ∈ A.coreSet := A.p.2
  rw [A.collar_core_apply s ⟨A.basepoint, hb⟩]
  change A.coreIn (A.contraction (s, A.p)) = A.coreIn A.p
  rw [A.contraction.eq_fst s (by simp)]
  rfl

/-- The literal subset quotient and its original canonical map. -/
abbrev Q := Collapse A.coreSet

def q : C(Space A.X, A.Q) := collapseMap A.coreSet

/-- Its inverse is the descent of the actual collar endpoint. -/
def quotientInverse : C(A.Q, Space A.X) :=
  { toFun := Quotient.lift (fun x => A.collar (1, x)) (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact (A.collar_core_one ⟨x, hx⟩).trans (A.collar_core_one ⟨y, hy⟩).symm)
    continuous_toFun := (A.collar.continuous.comp
      (continuous_const.prodMk continuous_id)).quotient_lift _ }

private def collarHomotopy : (ContinuousMap.id (Space A.X)).HomotopyRel
    (A.quotientInverse.comp A.q) {A.basepoint} where
  toFun := A.collar
  continuous_toFun := A.collar.continuous
  map_zero_left := A.collar_zero_apply
  map_one_left _ := rfl
  prop' := by
    intro s x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact A.collar_fixed s

private theorem quotient_collar_respects (s : I) (x y : Space A.X)
    (h : (subsetSetoid A.coreSet).r x y) :
    A.q (A.collar (s, x)) = A.q (A.collar (s, y)) := by
  apply Quotient.sound
  rcases h with rfl | ⟨hx, hy⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨A.collar_preserves_core s ⟨x, hx⟩, A.collar_preserves_core s ⟨y, hy⟩⟩

private def quotientCollar (s : I) : A.Q → A.Q :=
  Quotient.lift (fun x => A.q (A.collar (s, x))) (A.quotient_collar_respects s)

private def quotientHomotopy : (ContinuousMap.id A.Q).HomotopyRel
    (A.q.comp A.quotientInverse) {A.q A.basepoint} where
  toFun z := A.quotientCollar z.1 z.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact A.q.continuous.comp A.collar.continuous
  map_zero_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h x => exact congrArg A.q (A.collar_zero_apply x)
  map_one_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h x => rfl
  prop' := by
    intro s z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact congrArg A.q (A.collar_fixed s)

/-- Both based inverse homotopies for the unchanged map q. -/
def quotientEquivalence : SingletonRetractionBasedInverse.BasedEquivalence
    A.basepoint (A.q A.basepoint) where
  forward := A.q
  backward := A.quotientInverse
  forward_point := rfl
  backward_point := A.collar_fixed 1
  left := A.collarHomotopy.symm
  right := A.quotientHomotopy.symm

end Attachment

end D5.S3.Geometry.FiniteCriticalCellSphere
