/- GID: D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.subcritical_claim; result=D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.not_subcritical_claim; claim=D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds.subcritical_claim
   digest: Round unit-quaternion gains on four vertices admit a uniform fit with a quarter-turn obstruction. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic

/-! The four-vertex upper bound uses the round geometry of the unit three-sphere.
A cyclic choice of quarter-turn gains has a sharp lower bound by a skew form on the rim. -/

open scoped InnerProductSpace Quaternion
open Quaternion
open EuclideanGeometry

noncomputable section

namespace RoundQuaternionK4Bounds

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open scoped Real

local notation "U" => unitary ℍ[ℝ]

/-- The round geodesic distance on the unit quaternions. -/
def roundDist (p q : U) : ℝ := Real.arccos ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ

private theorem unit_norm (p : U) : ‖(p : ℍ[ℝ])‖ = 1 :=
  CStarRing.norm_coe_unitary p

private def ofUnit (p : ℍ[ℝ]) (hp : ‖p‖ = 1) : U :=
  ⟨p, by
    rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm]
    exact hp⟩

private theorem round_eq_angle (p q : U) :
    roundDist p q = angle (p : ℍ[ℝ]) (q : ℍ[ℝ]) := by
  simp [roundDist, angle, unit_norm]

private theorem round_self (p : U) : roundDist p p = 0 := by
  simp [roundDist, real_inner_self_eq_norm_sq, unit_norm]

private theorem round_comm (p q : U) : roundDist p q = roundDist q p := by
  rw [roundDist, roundDist, real_inner_comm]

private theorem round_mul_left (a p q : U) : roundDist (a * p) (a * q) = roundDist p q := by
  have h : ⟪(a : ℍ[ℝ]) * p, (a : ℍ[ℝ]) * q⟫_ℝ = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ :=
    LinearIsometry.inner_map_map
      { toLinearMap := LinearMap.mulLeft ℝ (a : ℍ[ℝ])
        norm_map' := fun x => by simp [LinearMap.mulLeft_apply, norm_mul, unit_norm] } _ _
  exact congrArg Real.arccos h

private theorem round_mul_right (a p q : U) : roundDist (p * a) (q * a) = roundDist p q := by
  have h : ⟪(p : ℍ[ℝ]) * a, (q : ℍ[ℝ]) * a⟫_ℝ = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ :=
    LinearIsometry.inner_map_map
      { toLinearMap := LinearMap.mulRight ℝ (a : ℍ[ℝ])
        norm_map' := fun x => by simp [LinearMap.mulRight_apply, norm_mul, unit_norm] } _ _
  exact congrArg Real.arccos h

private theorem round_inv (p q : U) : roundDist p⁻¹ q⁻¹ = roundDist p q := by
  calc
    _ = roundDist (p⁻¹ * p) (q⁻¹ * p) := (round_mul_right p _ _).symm
    _ = roundDist q p := by rw [inv_mul_cancel, ← round_mul_left q]; simp
    _ = _ := round_comm _ _

private theorem round_edge (a g b : U) :
    roundDist g (a⁻¹ * b) = roundDist (a * g) b := by
  rw [← round_mul_left a g (a⁻¹ * b), mul_inv_cancel_left]

/-- The bound on every directed edge of the complete graph on four vertices. -/
def Fits (g : Fin 4 → Fin 4 → U) (φ : Fin 4 → U) (r : ℝ) : Prop :=
  ∀ i j, i ≠ j → roundDist (g i j) ((φ i)⁻¹ * φ j) ≤ r

/-- Inverse reversal, the identity diagonal, and the distinct-vertex triangle bound. -/
def DefectLE (g : Fin 4 → Fin 4 → U) (ε : ℝ) : Prop :=
  (∀ i j, g j i = (g i j)⁻¹) ∧ (∀ i, g i i = 1) ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → roundDist (g i j * g j k) (g i k) ≤ ε

private theorem edge_rev {g : Fin 4 → Fin 4 → U} {φ : Fin 4 → U}
    (h : ∀ i j, g j i = (g i j)⁻¹) (i j : Fin 4) :
    roundDist (g j i) ((φ j)⁻¹ * φ i) = roundDist (g i j) ((φ i)⁻¹ * φ j) := by
  rw [h i j, ← round_inv (g i j)]
  simp

private theorem fits_of_six {g : Fin 4 → Fin 4 → U} {φ : Fin 4 → U} {r : ℝ}
    (h : ∀ i j, g j i = (g i j)⁻¹)
    (h01 : roundDist (φ 0 * g 0 1) (φ 1) ≤ r)
    (h02 : roundDist (φ 0 * g 0 2) (φ 2) ≤ r)
    (h03 : roundDist (φ 0 * g 0 3) (φ 3) ≤ r)
    (h12 : roundDist (φ 1 * g 1 2) (φ 2) ≤ r)
    (h23 : roundDist (φ 2 * g 2 3) (φ 3) ≤ r)
    (h31 : roundDist (φ 3 * g 3 1) (φ 1) ≤ r) :
    Fits g φ r := by
  simp only [← round_edge] at h01 h02 h03 h12 h23 h31
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h01 | exact h02 | exact h03 | exact h12 | exact h23 | exact h31
    | rw [edge_rev h]; first | exact h01 | exact h02 | exact h03 | exact h12 | exact h23 | exact h31

private theorem inner_bounds (x y : ℍ[ℝ]) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ ⟪x, y⟫_ℝ ∧ ⟪x, y⟫_ℝ ≤ 1 :=
  ⟨neg_one_le_real_inner_of_norm_eq_one hx hy, real_inner_le_one_of_norm_eq_one hx hy⟩

private theorem round_le_iff (x y : U) {r : ℝ} (hr : 0 ≤ r) (hrπ : r ≤ π) :
    roundDist x y ≤ r ↔ Real.cos r ≤ ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ := by
  have h := inner_bounds x y (unit_norm x) (unit_norm y)
  rw [roundDist, ← Real.arccos_cos hr hrπ]
  rw [Real.arccos_le_arccos_iff h.1 (Real.cos_le_one _),
    Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)]

private theorem orthogonal_unit {n : ℕ} (hn : n < 4) (a : Fin n → ℍ[ℝ]) :
    ∃ v : ℍ[ℝ], ‖v‖ = 1 ∧ ∀ i, ⟪a i, v⟫_ℝ = 0 := by
  let K := Submodule.span ℝ (Set.range a)
  have hdim : Module.finrank ℝ K ≤ n := by
    simpa [K] using (finrank_range_le_card (R := ℝ) a)
  have hs := K.finrank_add_finrank_orthogonal
  rw [Quaternion.finrank_eq_four] at hs
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  have hne : Kᗮ ≠ ⊥ := Submodule.finrank_pos.mp hpos
  obtain ⟨w, hw, hnw⟩ := Submodule.ne_bot_iff.mp hne
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hnw
  refine ⟨‖w‖⁻¹ • w, by simp [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hnorm], ?_⟩
  intro i
  rw [real_inner_smul_right, Submodule.mem_orthogonal _ _ |>.mp hw (a i)
    (Submodule.subset_span (Set.mem_range_self i)), mul_zero]

private theorem orthogonal_fit (g : Fin 4 → Fin 4 → U)
    (hrev : ∀ i j, g j i = (g i j)⁻¹) :
    ∃ φ, Fits g φ (π / 2) := by
  obtain ⟨v, hv, hv₁⟩ := orthogonal_unit (n := 1) (by decide) ![(g 0 1 : ℍ[ℝ])]
  let b := ofUnit v hv
  obtain ⟨w, hw, hw₂⟩ := orthogonal_unit (n := 2) (by decide)
    ![(g 0 2 : ℍ[ℝ]), (↑(b * g 1 2) : ℍ[ℝ])]
  let c := ofUnit w hw
  obtain ⟨z, hz, hz₃⟩ := orthogonal_unit (n := 3) (by decide)
    ![(g 0 3 : ℍ[ℝ]), (↑(b * g 1 3) : ℍ[ℝ]), (↑(c * g 2 3) : ℍ[ℝ])]
  let d := ofUnit z hz
  let φ : Fin 4 → U := ![1, b, c, d]
  have edge_zero {p q : U} (hpq : ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ = 0) :
      roundDist p q ≤ π / 2 := by simp [roundDist, hpq]
  refine ⟨φ, fits_of_six hrev ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [φ] using edge_zero (p := g 0 1) (q := b) (hv₁ 0)
  · simpa [φ] using edge_zero (p := g 0 2) (q := c) (hw₂ 0)
  · simpa [φ] using edge_zero (p := g 0 3) (q := d) (hz₃ 0)
  · exact edge_zero (p := b * g 1 2) (q := c) (hw₂ 1)
  · exact edge_zero (p := c * g 2 3) (q := d) (hz₃ 2)
  · rw [← round_edge, edge_rev hrev, round_edge]
    exact edge_zero (p := b * g 1 3) (q := d) (hz₃ 1)

