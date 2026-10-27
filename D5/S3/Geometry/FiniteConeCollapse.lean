/- GID: D5/S3/Geometry/FiniteConeCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteConeCollapse
   mirror-E: none(waiver:finite-cone-collapse)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic, mathlib/module/Mathlib.Topology.Homotopy.Equiv]
   utility: none
   digest: Coordinate truncation and cone contraction give a based equivalence for the actual cone quotient. -/
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fintype.Powerset
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Tactic

/-!
# Collapsing a finite cone subcomplex

The realization is a subspace of the finite real coordinate space. A face is the
closed affine simplex spanned by its coordinate vertices. Empty faces contribute
no points. A cone is specified by its actual faces and closure under adjoining
its apex; it need not be a full subcomplex.

The constructive coordinate truncation is followed by a linear cone contraction.
No homotopy extension property or cofibration hypothesis is used.
-/

noncomputable section

open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteConeCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The usual closed simplex on a finite set of coordinate vertices. -/
def faceSimplex (s : Finset V) : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1 ∧ ∀ v ∉ s, x v = 0}

/-- The standard geometric realization, with the ambient real subspace topology. -/
def realization (M : PreAbstractSimplicialComplex V) : Set (V → ℝ) :=
  {x | ∃ s ∈ M,
    x ∈ convexHull ℝ ((fun v : V => Pi.single v (1 : ℝ)) '' (s : Set V))}

/-- A nonempty cone subcomplex, including the cone consisting of its apex alone. -/
structure ConePair (V : Type*) [Fintype V] [DecidableEq V] where
  ambient : PreAbstractSimplicialComplex V
  cone : PreAbstractSimplicialComplex V
  inclusion : cone ≤ ambient
  apex : V
  apex_face : ({apex} : Finset V) ∈ cone
  cone_face : ∀ s ∈ cone, insert apex s ∈ cone

private theorem faceSimplex_mono {s t : Finset V} (hst : s ⊆ t) :
    faceSimplex s ⊆ faceSimplex t := by
  rintro x ⟨hx, hsum, hs⟩
  exact ⟨hx, hsum, fun v hv => hs v (fun h => hv (hst h))⟩

private theorem convex_faceSimplex (s : Finset V) : Convex ℝ (faceSimplex s) := by
  rintro x ⟨hx, hsx, hzx⟩ y ⟨hy, hsy, hzy⟩ a b ha hb hab
  refine ⟨fun v => add_nonneg (mul_nonneg ha (hx v)) (mul_nonneg hb (hy v)), ?_, ?_⟩
  · change (∑ v, (a * x v + b * y v)) = 1
    simp only [sum_add_distrib, ← mul_sum, hsx, hsy, mul_one, hab]
  · intro v hv
    change a * x v + b * y v = 0
    rw [hzx v hv, hzy v hv]
    ring

/-- The coordinate model uses the actual convex hull of each face's vertices. -/
theorem faceSimplex_eq_convexHull (s : Finset V) :
    faceSimplex s = convexHull ℝ ((fun v : V => Pi.single v (1 : ℝ)) '' (s : Set V)) := by
  apply le_antisymm
  · rintro x ⟨hx, hsum, hz⟩
    have hsum' : ∑ v ∈ s, x v = 1 := by
      rw [← hsum]
      exact sum_subset (subset_univ s) (fun v _ hv => hz v hv)
    have heq : s.centerMass x (fun v => Pi.single v (1 : ℝ)) = x := by
      rw [s.centerMass_eq_of_sum_1 _ hsum']
      ext v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hv : v ∈ s
      · simp [Pi.single_apply, hv]
      · simp [Pi.single_apply, hv, hz v hv]
    rw [← heq]
    exact s.centerMass_mem_convexHull (fun v _ => hx v) (by rw [hsum']; norm_num)
      (fun v hv => ⟨v, hv, rfl⟩)
  · apply convexHull_min _ (convex_faceSimplex s)
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, by simp, ?_⟩
    · intro w
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · intro w hw
      have hwv : w ≠ v := fun h => hw (h.symm ▸ hv)
      simp [Pi.single_apply, hwv, Ne.symm hwv]

private theorem realization_mem_iff (M : PreAbstractSimplicialComplex V) (x : V → ℝ) :
    x ∈ realization M ↔ ∃ s ∈ M, x ∈ faceSimplex s := by
  simp only [realization, mem_setOf_eq, faceSimplex_eq_convexHull]

private theorem realization_mono {M N : PreAbstractSimplicialComplex V} (h : M ≤ N) :
    realization M ⊆ realization N := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, h hs, hx⟩

namespace ConePair

variable (P : ConePair V)

abbrev Space := ↥(realization P.ambient)

/-- The actual realized cone inside the ambient realization. -/
def coneSet : Set P.Space := {x | x.val ∈ realization P.cone}

private theorem simplex_data (x : P.Space) :
    (∀ v, 0 ≤ x.val v) ∧ (∑ v, x.val v) = 1 := by
  obtain ⟨s, _, hx⟩ := (realization_mem_iff P.ambient x.val).1 x.property
  exact ⟨hx.1, hx.2.1⟩

private theorem coord_continuous (v : V) : Continuous (fun x : P.Space => x.val v) :=
  (continuous_apply v).comp continuous_subtype_val

private theorem apex_faceSimplex : Pi.single P.apex (1 : ℝ) ∈ faceSimplex {P.apex} := by
  refine ⟨?_, by simp, ?_⟩
  · intro v
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · intro v hv
    simp only [Finset.mem_singleton] at hv
    simp [Pi.single_apply, hv, Ne.symm hv]

/-- The coordinate vertex at the cone apex. -/
def apexPoint : P.Space :=
  ⟨Pi.single P.apex 1, (realization_mem_iff _ _).2
    ⟨{P.apex}, P.inclusion P.apex_face, P.apex_faceSimplex⟩⟩

private theorem apexPoint_mem : P.apexPoint ∈ P.coneSet := by
  exact (realization_mem_iff _ _).2 ⟨{P.apex}, P.apex_face, P.apex_faceSimplex⟩

private def faces : Finset (Finset V) := by
  classical
  exact univ.filter (fun s => s ∈ P.cone)

private theorem mem_faces (s : Finset V) : s ∈ P.faces ↔ s ∈ P.cone := by
  simp [faces]

private theorem faces_nonempty : P.faces.Nonempty :=
  ⟨{P.apex}, (P.mem_faces _).2 P.apex_face⟩

private def outsideMass (s : Finset V) (x : P.Space) : ℝ := ∑ v ∈ univ \ s, x.val v

private theorem outsideMass_nonneg (s : Finset V) (x : P.Space) : 0 ≤ P.outsideMass s x :=
  sum_nonneg (fun v _ => (P.simplex_data x).1 v)

private theorem continuous_outsideMass (s : Finset V) : Continuous (P.outsideMass s) := by
  exact continuous_finset_sum _ (fun v _ => P.coord_continuous v)

private def delta (x : P.Space) : ℝ :=
  P.faces.inf' P.faces_nonempty (fun s => P.outsideMass s x)

private theorem delta_nonneg (x : P.Space) : 0 ≤ P.delta x :=
  le_inf' _ _ (fun s _ => P.outsideMass_nonneg s x)

private theorem continuous_delta : Continuous P.delta :=
  Continuous.finset_inf'_apply _ (fun s _ => P.continuous_outsideMass s)

private theorem delta_witness (x : P.Space) :
    ∃ s ∈ P.cone, P.delta x = P.outsideMass s x := by
  obtain ⟨s, hs, heq⟩ := exists_mem_eq_inf' P.faces_nonempty (fun s => P.outsideMass s x)
  exact ⟨s, (P.mem_faces s).1 hs, heq⟩

private theorem outside_coord_le {s : Finset V} (x : P.Space) {v : V} (hv : v ∉ s) :
    x.val v ≤ P.outsideMass s x :=
  single_le_sum (fun w _ => (P.simplex_data x).1 w) (by simp [hv])

private theorem delta_eq_zero_iff (x : P.Space) : P.delta x = 0 ↔ x ∈ P.coneSet := by
  constructor
  · intro hd
    obtain ⟨s, hs, heq⟩ := P.delta_witness x
    apply (realization_mem_iff P.cone x.val).2
    refine ⟨s, hs, (P.simplex_data x).1, (P.simplex_data x).2, ?_⟩
    intro v hv
    exact le_antisymm (by simpa [← heq, hd] using P.outside_coord_le x hv)
      ((P.simplex_data x).1 v)
  · intro hx
    obtain ⟨s, hs, hx⟩ := (realization_mem_iff P.cone x.val).1 hx
    apply le_antisymm _ (P.delta_nonneg x)
    have hmass : P.outsideMass s x = 0 := by
      apply sum_eq_zero
      intro v hv
      exact hx.2.2 v (mem_sdiff.mp hv).2
    exact (inf'_le _ ((P.mem_faces s).2 hs)).trans hmass.le

private def epsilon (_P : ConePair V) : ℝ := 1 / (2 * ((Fintype.card V : ℝ) + 1))

private theorem epsilon_pos : 0 < P.epsilon := by unfold epsilon; positivity

private theorem card_mul_epsilon : (Fintype.card V : ℝ) * P.epsilon ≤ 1 / 2 := by
  unfold epsilon
  rw [← mul_div_assoc, mul_one]
  apply (div_le_iff₀ (by positivity : 0 < 2 * ((Fintype.card V : ℝ) + 1))).2
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V)]

private def theta (x : P.Space) : ℝ := min (P.delta x) P.epsilon

private theorem theta_nonneg (x : P.Space) : 0 ≤ P.theta x :=
  le_min (P.delta_nonneg x) P.epsilon_pos.le

private def truncated (s : I) (x : P.Space) (v : V) : ℝ :=
  max (x.val v - (s : ℝ) * P.theta x) 0

private def denominator (s : I) (x : P.Space) : ℝ := ∑ v, P.truncated s x v

private theorem denominator_bound (s : I) (x : P.Space) : 1 / 2 ≤ P.denominator s x := by
  have ht : (s : ℝ) * P.theta x ≤ P.epsilon :=
    (mul_le_mul_of_nonneg_right s.property.2 (P.theta_nonneg x)).trans
      (by simpa [theta] using (min_le_right (P.delta x) P.epsilon))
  calc
    (1 / 2 : ℝ) ≤ 1 - (Fintype.card V : ℝ) * P.epsilon := by
      linarith [P.card_mul_epsilon]
    _ = ∑ v, (x.val v - P.epsilon) := by
      rw [sum_sub_distrib, (P.simplex_data x).2]
      simp
    _ ≤ P.denominator s x := by
      apply sum_le_sum
      intro v _
      exact (sub_le_sub_left ht _).trans (le_max_left _ _)

private theorem denominator_pos (s : I) (x : P.Space) : 0 < P.denominator s x :=
  lt_of_lt_of_le (by norm_num) (P.denominator_bound s x)

private def deformCoords (s : I) (x : P.Space) (v : V) : ℝ :=
  P.truncated s x v / P.denominator s x

private theorem deform_mem_face (s : I) (x : P.Space) {f : Finset V}
    (hx : x.val ∈ faceSimplex f) : P.deformCoords s x ∈ faceSimplex f := by
  refine ⟨fun v => div_nonneg (le_max_right _ _) (P.denominator_pos s x).le, ?_, ?_⟩
  · simp only [deformCoords, ← sum_div]
    change P.denominator s x / P.denominator s x = 1
    exact div_self (P.denominator_pos s x).ne'
  · intro v hv
    simp only [deformCoords, truncated, hx.2.2 v hv, zero_sub]
    rw [max_eq_right (neg_nonpos.mpr (mul_nonneg s.property.1 (P.theta_nonneg x)))]
    exact zero_div _

private def deform (s : I) (x : P.Space) : P.Space :=
  ⟨P.deformCoords s x, by
    obtain ⟨f, hf, hx⟩ := (realization_mem_iff P.ambient x.val).1 x.property
    apply (realization_mem_iff _ _).2
    exact ⟨f, hf, P.deform_mem_face s x hx⟩⟩

private theorem continuous_deform : Continuous (fun z : I × P.Space => P.deform z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  have ht : Continuous (fun x : P.Space => P.theta x) := P.continuous_delta.min continuous_const
  have hn (v : V) : Continuous (fun z : I × P.Space => P.truncated z.1 z.2 v) :=
    ((P.coord_continuous v |>.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst |>.mul (ht.comp continuous_snd))).max
      continuous_const
  exact (hn v).div (continuous_finset_sum _ (fun w _ => hn w))
    (fun z => (P.denominator_pos z.1 z.2).ne')

private theorem deform_zero (x : P.Space) : P.deform 0 x = x := by
  have ht (v) : P.truncated 0 x v = x.val v := by
    simp [truncated, max_eq_left ((P.simplex_data x).1 v)]
  apply Subtype.ext
  funext v
  change P.truncated 0 x v / (∑ w, P.truncated 0 x w) = x.val v
  simp only [ht, (P.simplex_data x).2, div_one]

private theorem deform_fixed (s : I) (x : P.Space) (hx : x ∈ P.coneSet) :
    P.deform s x = x := by
  have htheta : P.theta x = 0 := by
    simp [theta, (P.delta_eq_zero_iff x).2 hx, P.epsilon_pos.le]
  have ht (v) : P.truncated s x v = x.val v := by
    simp [truncated, htheta, max_eq_left ((P.simplex_data x).1 v)]
  apply Subtype.ext
  funext v
  change P.truncated s x v / (∑ w, P.truncated s x w) = x.val v
  simp only [ht, (P.simplex_data x).2, div_one]

private theorem deform_one_mem_cone (x : P.Space) (hx : P.delta x ≤ P.epsilon) :
    P.deform 1 x ∈ P.coneSet := by
  obtain ⟨f, hf, heq⟩ := P.delta_witness x
  apply (realization_mem_iff P.cone _).2
  refine ⟨f, hf, (P.simplex_data (P.deform 1 x)).1,
    (P.simplex_data (P.deform 1 x)).2, ?_⟩
  intro v hv
  have hcoord : x.val v ≤ P.delta x := by
    rw [heq]
    exact P.outside_coord_le x hv
  change max (x.val v - (1 : I).val * P.theta x) 0 / _ = 0
  rw [show (1 : I).val = (1 : ℝ) from rfl, one_mul, theta, min_eq_left hx,
    max_eq_right (sub_nonpos.mpr hcoord), zero_div]

private def earlyTime (t : I) : I :=
  ⟨min (2 * (t : ℝ)) 1,
    le_min (mul_nonneg (by norm_num) t.property.1) zero_le_one, min_le_right _ _⟩

private def lateTime (t : I) : ℝ := max (2 * (t : ℝ) - 1) 0

private def collar (x : P.Space) : ℝ := 1 - min (P.delta x / P.epsilon) 1

private theorem collar_bounds (x : P.Space) : 0 ≤ P.collar x ∧ P.collar x ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (min_le_right _ _)
  · have h := le_min (div_nonneg (P.delta_nonneg x) P.epsilon_pos.le) zero_le_one
    dsimp [collar]
    linarith

private theorem lateTime_bounds (t : I) : 0 ≤ lateTime t ∧ lateTime t ≤ 1 := by
  refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
  linarith [t.property.2]

private def coefficient (t : I) (x : P.Space) : ℝ := lateTime t * P.collar x

private theorem coefficient_bounds (t : I) (x : P.Space) :
    0 ≤ P.coefficient t x ∧ P.coefficient t x ≤ 1 := by
  exact ⟨mul_nonneg (lateTime_bounds t).1 (P.collar_bounds x).1,
    (mul_le_mul_of_nonneg_right (lateTime_bounds t).2 (P.collar_bounds x).1).trans
      (by simpa using (P.collar_bounds x).2)⟩

private theorem cone_segment (x : P.Space) (hx : x ∈ P.coneSet) (a : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (fun v => (1 - a) * x.val v + a * P.apexPoint.val v) ∈ realization P.cone := by
  obtain ⟨f, hf, hx⟩ := (realization_mem_iff P.cone x.val).1 hx
  apply (realization_mem_iff _ _).2
  refine ⟨insert P.apex f, P.cone_face f hf, ?_⟩
  apply convex_faceSimplex (insert P.apex f)
    (faceSimplex_mono (subset_insert _ _) hx)
    (faceSimplex_mono (singleton_subset_iff.mpr (mem_insert_self _ _))
      (show P.apexPoint.val ∈ faceSimplex {P.apex} from P.apex_faceSimplex))
    (sub_nonneg.mpr ha') ha
  ring

private theorem active_deform_mem (t : I) (x : P.Space) (h : P.coefficient t x ≠ 0) :
    P.deform (earlyTime t) x ∈ P.coneSet := by
  have hg : lateTime t ≠ 0 := fun hg => h (by simp [coefficient, hg])
  have hb : P.collar x ≠ 0 := fun hb => h (by simp [coefficient, hb])
  have ht : 1 ≤ 2 * (t : ℝ) := by
    by_contra hle
    exact hg (max_eq_right (by linarith : 2 * (t : ℝ) - 1 ≤ 0))
  have hearly : earlyTime t = 1 := Subtype.ext (min_eq_right ht)
  have hd : P.delta x ≤ P.epsilon := by
    by_contra hle
    have hr : 1 ≤ P.delta x / P.epsilon :=
      (le_div_iff₀ P.epsilon_pos).2 (by linarith)
    exact hb (by simp [collar, min_eq_right hr])
  rw [hearly]
  exact P.deform_one_mem_cone x hd

private def homotopyCoords (t : I) (x : P.Space) (v : V) : ℝ :=
  (1 - P.coefficient t x) * (P.deform (earlyTime t) x).val v +
    P.coefficient t x * P.apexPoint.val v

private theorem homotopy_mem (t : I) (x : P.Space) :
    P.homotopyCoords t x ∈ realization P.ambient := by
  by_cases h : P.coefficient t x = 0
  · have heq : P.homotopyCoords t x = (P.deform (earlyTime t) x).val := by
      funext v
      simp only [homotopyCoords, h, sub_zero, one_mul, zero_mul, add_zero]
    rw [heq]
    exact (P.deform (earlyTime t) x).property
  · exact realization_mono P.inclusion (P.cone_segment (P.deform (earlyTime t) x)
      (P.active_deform_mem t x h) (P.coefficient t x)
      (P.coefficient_bounds t x).1 (P.coefficient_bounds t x).2)

/-- The explicit ambient deformation: truncate coordinates, then contract within the cone. -/
def controlledHomotopy (t : I) (x : P.Space) : P.Space :=
  ⟨P.homotopyCoords t x, P.homotopy_mem t x⟩

private theorem continuous_controlledHomotopy :
    Continuous (fun z : I × P.Space => P.controlledHomotopy z.1 z.2) := by
  have he : Continuous (earlyTime : I → I) :=
    ((continuous_const.mul continuous_subtype_val).min continuous_const).subtype_mk _
  have hl : Continuous (lateTime : I → ℝ) :=
    ((continuous_const.mul continuous_subtype_val).sub continuous_const).max continuous_const
  have hb : Continuous P.collar :=
    continuous_const.sub ((P.continuous_delta.div_const P.epsilon).min continuous_const)
  have hc : Continuous (fun z : I × P.Space => P.coefficient z.1 z.2) :=
    (hl.comp continuous_fst).mul (hb.comp continuous_snd)
  have hd := P.continuous_deform.comp ((he.comp continuous_fst).prodMk continuous_snd)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact ((continuous_const.sub hc).mul ((P.coord_continuous v).comp hd)).add
    (hc.mul continuous_const)

private theorem controlled_zero (x : P.Space) : P.controlledHomotopy 0 x = x := by
  have he : earlyTime 0 = 0 := by ext; norm_num [earlyTime]
  have hc : P.coefficient 0 x = 0 := by norm_num [coefficient, lateTime]
  apply Subtype.ext
  funext v
  change P.homotopyCoords 0 x v = x.val v
  simp [homotopyCoords, hc, he, P.deform_zero]

private theorem controlled_preserves_cone (t : I) (x : P.Space) (hx : x ∈ P.coneSet) :
    P.controlledHomotopy t x ∈ P.coneSet := by
  change P.homotopyCoords t x ∈ realization P.cone
  have heq : P.homotopyCoords t x =
      (fun v => (1 - P.coefficient t x) * x.val v +
        P.coefficient t x * P.apexPoint.val v) := by
    funext v
    rw [homotopyCoords, P.deform_fixed (earlyTime t) x hx]
  rw [heq]
  exact P.cone_segment x hx (P.coefficient t x)
    (P.coefficient_bounds t x).1 (P.coefficient_bounds t x).2

private theorem controlled_one_cone (x : P.Space) (hx : x ∈ P.coneSet) :
    P.controlledHomotopy 1 x = P.apexPoint := by
  have hc : P.coefficient 1 x = 1 := by
    norm_num [coefficient, lateTime, collar, (P.delta_eq_zero_iff x).2 hx]
  apply Subtype.ext
  funext v
  simp [controlledHomotopy, homotopyCoords, hc]

private theorem controlled_apexPoint (t : I) : P.controlledHomotopy t P.apexPoint = P.apexPoint := by
  apply Subtype.ext
  funext v
  change P.homotopyCoords t P.apexPoint v = P.apexPoint.val v
  rw [homotopyCoords, P.deform_fixed (earlyTime t) P.apexPoint P.apexPoint_mem]
  ring

/-- Exactly equality, with every pair of points of the realized cone also identified. -/
def collapseSetoid : Setoid P.Space where
  r x y := x = y ∨ (x ∈ P.coneSet ∧ y ∈ P.coneSet)
  iseqv := ⟨fun _ => Or.inl rfl,
    by
      rintro x y (h | ⟨hx, hy⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩,
    by
      rintro x y z (rfl | ⟨hx, hy⟩) hz
      · exact hz
      · rcases hz with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩⟩

/-- The actual quotient with its quotient topology. -/
abbrev Collapse := Quotient P.collapseSetoid

/-- The canonical quotient map. -/
def quotientMap : C(P.Space, P.Collapse) := ⟨Quotient.mk P.collapseSetoid, continuous_quotient_mk'⟩

private theorem endpoint_respects {x y : P.Space} (h : P.collapseSetoid.r x y) :
    P.controlledHomotopy 1 x = P.controlledHomotopy 1 y := by
  rcases h with rfl | ⟨hx, hy⟩
  · rfl
  · rw [P.controlled_one_cone x hx, P.controlled_one_cone y hy]

/-- The continuous inverse induced by the final explicit deformation. -/
def collapseInverse : C(P.Collapse, P.Space) where
  toFun := Quotient.lift (P.controlledHomotopy 1) (fun _ _ h => P.endpoint_respects h)
  continuous_toFun := (P.continuous_controlledHomotopy.comp
    (continuous_const.prodMk continuous_id)).quotient_lift _

private theorem quotient_homotopy_respects (t : I) {x y : P.Space}
    (h : P.collapseSetoid.r x y) :
    P.quotientMap (P.controlledHomotopy t x) = P.quotientMap (P.controlledHomotopy t y) := by
  apply Quotient.sound
  rcases h with rfl | ⟨hx, hy⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨P.controlled_preserves_cone t x hx, P.controlled_preserves_cone t y hy⟩

private def quotientHomotopy (t : I) : P.Collapse → P.Collapse :=
  Quotient.lift (fun x => P.quotientMap (P.controlledHomotopy t x))
    (fun _ _ h => P.quotient_homotopy_respects t h)

private theorem continuous_quotientHomotopy :
    Continuous (fun z : I × P.Collapse => P.quotientHomotopy z.1 z.2) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  exact P.quotientMap.continuous.comp P.continuous_controlledHomotopy

/-- The two explicit inverse homotopies, relative to the apex and its quotient class. -/
def basedCollapse :
    (ContinuousMap.id P.Space).HomotopyRel (P.collapseInverse.comp P.quotientMap) {P.apexPoint} ×
    (ContinuousMap.id P.Collapse).HomotopyRel (P.quotientMap.comp P.collapseInverse)
      {P.quotientMap P.apexPoint} := by
  constructor
  · exact
      { toFun := fun z => P.controlledHomotopy z.1 z.2
        continuous_toFun := P.continuous_controlledHomotopy
        map_zero_left := P.controlled_zero
        map_one_left := fun _ => rfl
        prop' := by
          intro t x hx
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact P.controlled_apexPoint t }
  · exact
      { toFun := fun z => P.quotientHomotopy z.1 z.2
        continuous_toFun := P.continuous_quotientHomotopy
        map_zero_left := by
          intro z
          induction z using Quotient.inductionOn with
          | h x => exact congrArg P.quotientMap (P.controlled_zero x)
        map_one_left := by
          intro z
          induction z using Quotient.inductionOn with
          | h x => rfl
        prop' := by
          intro t z hz
          obtain rfl := Set.mem_singleton_iff.mp hz
          exact congrArg P.quotientMap (P.controlled_apexPoint t) }

/-- Collapsing a nonempty finite cone subcomplex is a based homotopy equivalence. -/
def collapseEquiv : P.Space ≃ₕ P.Collapse where
  toFun := P.quotientMap
  invFun := P.collapseInverse
  left_inv := ⟨P.basedCollapse.1.toHomotopy.symm⟩
  right_inv := ⟨P.basedCollapse.2.toHomotopy.symm⟩

end ConePair
end D5.S3.Geometry.FiniteConeCollapse
