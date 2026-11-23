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
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Angles
import Mathlib.Tactic

/-! The four-vertex upper bound uses the round geometry of the unit three-sphere.
A cyclic choice of quarter-turn gains has a sharp lower bound by a skew form on the rim. -/

open scoped InnerProductSpace Quaternion
open Quaternion
open InnerProductGeometry

noncomputable section

namespace RoundQuaternionK4Bounds

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open scoped Real
open private degrees tan_half_sq cos_ratio boundRow midpoint_bound_table
  midpoint_trig_table covered_degrees small_gap from
  D5.S3.Combinatorics.Graph.Chordal.RoundQuaternionK4Angles

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
  have hc : Real.cos (roundDist x y) = ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ :=
    Real.cos_arccos h.1 h.2
  rw [← hc]
  exact (Real.strictAntiOn_cos.le_iff_ge ⟨hr, hrπ⟩
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩).symm

private theorem orthogonal_unit {n : ℕ} (hn : n < 4) (a : Fin n → ℍ[ℝ]) :
    ∃ v : ℍ[ℝ], ‖v‖ = 1 ∧ ∀ i, ⟪a i, v⟫_ℝ = 0 := by
  let K := Submodule.span ℝ (Set.range a)
  have hdim : Module.finrank ℝ K ≤ n := by
    exact (finrank_range_le_card (R := ℝ) a).trans_eq (Fintype.card_fin n)
  have hs := K.finrank_add_finrank_orthogonal
  rw [Quaternion.finrank_eq_four] at hs
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  obtain ⟨w₀, hnw₀⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mp hpos
  let w : ℍ[ℝ] := w₀
  have hw : w ∈ Kᗮ := w₀.property
  have hnw : w ≠ 0 := fun h => hnw₀ (Subtype.ext h)
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hnw
  refine ⟨‖w‖⁻¹ • w, by simp [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hnorm], ?_⟩
  intro i
  rw [real_inner_smul_right, (Submodule.mem_orthogonal K w).mp hw (a i)
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


private def omegaForm (x y : ℍ[ℝ]) : ℝ := ⟪x * (unitI : ℍ[ℝ]), y⟫_ℝ

private theorem omega_skew (x y : ℍ[ℝ]) : omegaForm y x = -omegaForm x y := by
  simp only [omegaForm, inner_eq_components, unitI, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

private theorem omega_cyclic (x y z : ℍ[ℝ]) :
    omegaForm x y + omegaForm y z + omegaForm z x =
      omegaForm (y - x) (2 • z - x - y) / 2 := by
  simp only [omegaForm, inner_eq_components, unitI, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_sub, Quaternion.imI_sub,
    Quaternion.imJ_sub, Quaternion.imK_sub, two_smul, Quaternion.re_add, Quaternion.imI_add,
    Quaternion.imJ_add, Quaternion.imK_add]
  ring

private theorem cyclic_obstruction (x y z : U) (u : ℝ) (hu : 0 ≤ u)
    (hx : u ≤ ⟪(1 : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ)
    (hy : u ≤ ⟪(1 : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ)
    (hz : u ≤ ⟪(1 : ℍ[ℝ]), (z : ℍ[ℝ])⟫_ℝ)
    (hxy : u ≤ omegaForm x y) (hyz : u ≤ omegaForm y z) (hzx : u ≤ omegaForm z x) :
    u ≤ Real.sqrt 3 / 2 * (1 - u ^ 2) := by
  let M : ℍ[ℝ] := (1 / 3 : ℝ) • ((x : ℍ[ℝ]) + y + z)
  let E : ℍ[ℝ] := (1 / Real.sqrt 2) • ((y : ℍ[ℝ]) - x)
  let J : ℍ[ℝ] := (1 / Real.sqrt 6) • (2 • (z : ℍ[ℝ]) - x - y)
  have hs₂ : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs₃ : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs₆ : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  have hm : u ≤ ‖M‖ := calc
    u ≤ ⟪(1 : ℍ[ℝ]), M⟫_ℝ := by
      simp only [M, real_inner_smul_right, inner_add_right]
      linarith
    _ ≤ ‖M‖ := by simpa using real_inner_le_norm (1 : ℍ[ℝ]) M
  have henergy : ‖E‖ ^ 2 + ‖J‖ ^ 2 = 3 * (1 - ‖M‖ ^ 2) := by
    simp only [E, J, M, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, one_pow,
      hs₂, hs₆, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, two_smul]
    simp only [real_inner_self_eq_norm_sq, unit_norm, one_pow]
    rw [real_inner_comm (y : ℍ[ℝ]) x, real_inner_comm (z : ℍ[ℝ]) x,
      real_inner_comm (z : ℍ[ℝ]) y]
    ring
  have hs : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, hs₂, hs₃, hs₆]
    norm_num
  have hsum : omegaForm x y + omegaForm y z + omegaForm z x =
      Real.sqrt 3 * omegaForm E J := by
    rw [omega_cyclic]
    simp only [E, J, omegaForm, smul_mul_assoc, real_inner_smul_left, real_inner_smul_right]
    have hcoeff : Real.sqrt 3 * (1 / Real.sqrt 6 * (1 / Real.sqrt 2)) = (1 / 2 : ℝ) := by
      rw [div_mul_div_comm, one_mul, mul_comm (Real.sqrt 6), hs]
      field_simp
    rw [← mul_assoc, ← mul_assoc, mul_assoc (Real.sqrt 3), hcoeff]
    ring
  have hb : omegaForm E J ≤ ‖E‖ * ‖J‖ := by
    unfold omegaForm
    simpa [norm_mul, unit_norm] using real_inner_le_norm (E * (unitI : ℍ[ℝ])) J
  have hprod : 2 * omegaForm E J ≤ ‖E‖ ^ 2 + ‖J‖ ^ 2 := by
    nlinarith [sq_nonneg (‖E‖ - ‖J‖)]
  have hmsq := (sq_le_sq₀ hu (norm_nonneg M)).2 hm
  have h₁ := mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg 3)
  have h₂ := mul_le_mul_of_nonneg_left hmsq (Real.sqrt_nonneg 3)
  rw [henergy] at h₁
  linarith

private theorem cyclic_quarter_turn_bound (u : ℝ)
    (h : u ≤ Real.sqrt 3 / 2 * (1-u^2)) : u ≤ 1 / Real.sqrt 3 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [le_div_iff₀ hp]
  by_contra! hbad
  have hl : 1 < u*Real.sqrt 3 := hbad
  have hsq : 1 < (u*Real.sqrt 3)^2 := by nlinarith [sq_nonneg (u*Real.sqrt 3 - 1)]
  have hmul := mul_le_mul_of_nonneg_right h hp.le
  have hmul' : (Real.sqrt 3 / 2 * (1-u^2)) * Real.sqrt 3 = 3/2*(1-u^2) := by
    calc
      _ = Real.sqrt 3 ^ 2 / 2 * (1-u^2) := by ring
      _ = _ := by rw [hs]
  rw [hmul'] at hmul
  rw [mul_pow, hs] at hsq
  linarith


/-- The unit quaternion quarter-turn gains on the rim of a star. -/
def quarterGains : Fin 4 → Fin 4 → U :=
  ![![1, 1, 1, 1], ![1, 1, unitI, unitI⁻¹], ![1, unitI⁻¹, 1, unitI],
    ![1, unitI, unitI⁻¹, 1]]

private theorem quarter_reverse (i j : Fin 4) :
    quarterGains j i = (quarterGains i j)⁻¹ := by
  fin_cases i <;> fin_cases j <;> simp [quarterGains]


private theorem unitI_inv_val : (↑(unitI⁻¹) : ℍ[ℝ]) = ⟨0, -1, 0, 0⟩ := by
  change star (unitI : ℍ[ℝ]) = _
  ext <;> simp [unitI]

private theorem quarter_defect : DefectLE quarterGains (π / 2) := by
  refine ⟨quarter_reverse, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i j k hij hjk hik
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first
      | exact (hij rfl).elim
      | exact (hjk rfl).elim
      | exact (hik rfl).elim
      | (simp [quarterGains, unitI_inv_val, roundDist, inner_eq_components]
         all_goals norm_num [unitI, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
           Quaternion.imK_mul])

/-- The least possible maximal edge error for the cyclic quarter-turn assignment. -/
def quarterError : ℝ := Real.arccos (1 / Real.sqrt 3)

private theorem threshold_bounds : 0 < 1 / Real.sqrt 3 ∧ 1 / Real.sqrt 3 ≤ (1 : ℝ) := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h₀ : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have h₁ : 1 ≤ Real.sqrt 3 := by nlinarith
  exact ⟨by positivity, (div_le_one (by positivity)).2 h₁⟩

private theorem quarter_lower (φ : Fin 4 → U) :
    ∃ i j : Fin 4, i ≠ j ∧ quarterError ≤ roundDist (quarterGains i j) ((φ i)⁻¹ * φ j) := by
  by_contra! h
  let x := (φ 0)⁻¹ * φ 1
  let y := (φ 0)⁻¹ * φ 2
  let z := (φ 0)⁻¹ * φ 3
  let t := 1 / Real.sqrt 3
  have edge {i j : Fin 4} (hij : i ≠ j) :
      t < ⟪(↑(((φ 0)⁻¹ * φ i) * quarterGains i j) : ℍ[ℝ]),
        (↑((φ 0)⁻¹ * φ j) : ℍ[ℝ])⟫_ℝ := by
    have hh := h i j hij
    rw [round_edge, ← round_mul_left (φ 0)⁻¹, ← mul_assoc] at hh
    unfold roundDist quarterError at hh
    apply (Real.strictAntiOn_arccos.lt_iff_gt
      (inner_bounds _ _ (unit_norm _) (unit_norm _))
      ⟨by linarith [threshold_bounds.1], threshold_bounds.2⟩).mp hh
  have hx : t < ⟪(1 : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ := by
    simpa [x, quarterGains] using edge (i := 0) (j := 1) (by decide)
  have hy : t < ⟪(1 : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ := by
    simpa [y, quarterGains] using edge (i := 0) (j := 2) (by decide)
  have hz : t < ⟪(1 : ℍ[ℝ]), (z : ℍ[ℝ])⟫_ℝ := by
    simpa [z, quarterGains] using edge (i := 0) (j := 3) (by decide)
  have hxy : t < omegaForm x y := by simpa [x, y, omegaForm, quarterGains] using
      (edge (i := 1) (j := 2) (by decide))
  have hyz : t < omegaForm y z := by simpa [y, z, omegaForm, quarterGains] using
      (edge (i := 2) (j := 3) (by decide))
  have hzx : t < omegaForm z x := by simpa [z, x, omegaForm, quarterGains] using
      (edge (i := 3) (j := 1) (by decide))
  let u := min (min ⟪(1 : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ
    (min ⟪(1 : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ⟪(1 : ℍ[ℝ]), (z : ℍ[ℝ])⟫_ℝ))
    (min (omegaForm x y) (min (omegaForm y z) (omegaForm z x)))
  have hu : t < u := by simp [u, lt_min_iff, hx, hy, hz, hxy, hyz, hzx]
  have hun : 0 ≤ u := threshold_bounds.1.le.trans hu.le
  exact (not_le_of_gt hu) (cyclic_quarter_turn_bound u (cyclic_obstruction x y z u hun
    (by dsimp [u]; exact (min_le_left _ _).trans (min_le_left _ _))
    (by dsimp [u]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    (by dsimp [u]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    (by dsimp [u]; exact (min_le_right _ _).trans (min_le_left _ _))
    (by dsimp [u]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    (by dsimp [u]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))

private theorem norm_one_of_coordinates (q : ℍ[ℝ])
    (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) : ‖q‖ = 1 := by
  have hs : ‖q‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_components]
    simpa only [pow_two] using h
  nlinarith [norm_nonneg q]

private def quarterPotential : Fin 4 → U := by
  let t := 1 / Real.sqrt 3
  let b := Real.sqrt 2 / 2
  let a := 2 * b * t
  have ht : t ^ 2 = 1 / 3 := by
    dsimp [t]
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hb : b ^ 2 = 1 / 2 := by
    dsimp [b]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have ha : a ^ 2 = 2 / 3 := by
    dsimp [a]
    rw [mul_pow, mul_pow, hb, ht]
    norm_num
  refine ![1, ofUnit ⟨t, 0, a, 0⟩ ?_, ofUnit ⟨t, 0, -a / 2, -b⟩ ?_,
    ofUnit ⟨t, 0, -a / 2, b⟩ ?_]
  all_goals
    apply norm_one_of_coordinates
    change _ ^ 2 + (0 : ℝ) ^ 2 + _ ^ 2 + _ ^ 2 = 1
    simp only [div_pow, neg_sq, ht, ha, hb]
    norm_num

private theorem quarter_attains (i j : Fin 4) (hij : i ≠ j) :
    roundDist (quarterGains i j) ((quarterPotential i)⁻¹ * quarterPotential j) = quarterError := by
  rw [round_edge]
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals
    first
    | rfl
    | (unfold roundDist quarterError
       congr 1
       simp [quarterPotential, quarterGains, ofUnit, unitI_inv_val]
       simp [inner_eq_components, unitI, Quaternion.re_mul, Quaternion.imI_mul,
         Quaternion.imJ_mul, Quaternion.imK_mul]
       all_goals ring_nf
       all_goals norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;> ring)

private theorem quarterError_gt : 3 * π / 10 < quarterError := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 5 < 7 / 3 := by nlinarith [Real.sqrt_nonneg 5]
  have hc := Real.cos_pi_div_five
  have hp : Real.cos (3 * π / 10) = Real.sin (π / 5) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    ring
  have hsum := Real.cos_sq_add_sin_sq (π / 5)
  have hb : (1 / Real.sqrt 3) ^ 2 = (1 / 3 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have ht : 1 / Real.sqrt 3 < Real.sin (π / 5) := by
    apply (sq_lt_sq₀ threshold_bounds.1.le
      (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]))).mp
    rw [hb]
    rw [hc] at hsum
    nlinarith
  apply (Real.strictAntiOn_cos.lt_iff_gt
    (show quarterError ∈ Set.Icc 0 π from ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
    (show 3 * π / 10 ∈ Set.Icc 0 π by constructor <;> linarith [Real.pi_pos])).mp
  rw [hp, quarterError, Real.cos_arccos (by linarith [threshold_bounds.1]) threshold_bounds.2]
  exact ht

private theorem distance_triangle (a b c : U) :
    roundDist a c ≤ roundDist a b + roundDist b c := by
  simp only [round_eq_angle]
  exact angle_le_angle_add_angle _ _ _

private theorem chord_sq (p q : U) :
    ‖(p : ℍ[ℝ]) - q‖ ^ 2 = 4 * Real.sin (roundDist p q / 2) ^ 2 := by
  have hcos : Real.cos (roundDist p q) = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ := by
    rw [round_eq_angle, cos_angle, unit_norm, unit_norm, one_mul, div_one]
  rw [norm_sub_sq_real, unit_norm, unit_norm, ← hcos, Real.sin_sq_eq_half_sub]
  rw [show 2 * (roundDist p q / 2) = roundDist p q by ring]
  ring

private theorem chord_le (p q : U) {ε : ℝ} (hε : ε ≤ π)
    (h : roundDist p q ≤ ε) : ‖(p : ℍ[ℝ]) - q‖ ≤ 2 * Real.sin (ε / 2) := by
  have hd : 0 ≤ roundDist p q := Real.arccos_nonneg _
  have he : 0 ≤ ε := hd.trans h
  have hm := Real.strictMonoOn_sin.monotoneOn
    (show roundDist p q / 2 ∈ Set.Icc (-(π / 2)) (π / 2) by
      constructor <;> linarith [Real.pi_pos])
    (show ε / 2 ∈ Set.Icc (-(π / 2)) (π / 2) by
      constructor <;> linarith [Real.pi_pos])
    (show roundDist p q / 2 ≤ ε / 2 by linarith)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := roundDist p q / 2)
    (by linarith) (by linarith [Real.pi_pos])
  have heq : ‖(p : ℍ[ℝ]) - q‖ = 2 * Real.sin (roundDist p q / 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [chord_sq]
    ring
  linarith

private theorem midpoint (p q : U) {ε : ℝ} (hε : ε < π) (hpq : roundDist p q ≤ ε) :
    ∃ (m : U) (L : ℝ), 0 < L ∧ (p : ℍ[ℝ]) + q = L • (m : ℍ[ℝ]) ∧
      2 * Real.cos (ε / 2) ≤ L ∧ roundDist p m ≤ ε / 2 ∧ roundDist q m ≤ ε / 2 := by
  let d := roundDist p q
  let L := 2 * Real.cos (d / 2)
  have hd : 0 ≤ d := Real.arccos_nonneg _
  have hL : 0 < L := by
    apply mul_pos (by norm_num)
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc : Real.cos d = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ := by
    rw [show d = roundDist p q from rfl, round_eq_angle, cos_angle, unit_norm, unit_norm,
      one_mul, div_one]
  have hdouble := Real.cos_two_mul (d / 2)
  rw [show 2 * (d / 2) = d by ring, hc] at hdouble
  have ln : ‖(p : ℍ[ℝ]) + q‖ = L := by
    apply (sq_eq_sq₀ (norm_nonneg _) hL.le).mp
    rw [norm_add_sq_real, unit_norm, unit_norm, hdouble]
    dsimp [L]
    ring
  let m := ofUnit (L⁻¹ • ((p : ℍ[ℝ]) + q)) (by
    rw [norm_smul, ln, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), inv_mul_cancel₀ hL.ne'])
  have hLm : (p : ℍ[ℝ]) + q = L • (m : ℍ[ℝ]) := by
    change _ = L • L⁻¹ • _
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (x := d / 2) (y := ε / 2)
    (by linarith) (by linarith [Real.pi_pos]) (by linarith)
  have hm₁ : ⟪(p : ℍ[ℝ]), (m : ℍ[ℝ])⟫_ℝ = Real.cos (d / 2) := by
    change ⟪(p : ℍ[ℝ]), L⁻¹ • ((p : ℍ[ℝ]) + q)⟫_ℝ = _
    rw [real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, unit_norm, hdouble]
    have hcd : Real.cos (d / 2) ≠ 0 := by dsimp [L] at hL; linarith
    dsimp only [L]
    field_simp [hcd]
    ring
  have hm₂ : ⟪(q : ℍ[ℝ]), (m : ℍ[ℝ])⟫_ℝ = Real.cos (d / 2) := by
    change ⟪(q : ℍ[ℝ]), L⁻¹ • ((p : ℍ[ℝ]) + q)⟫_ℝ = _
    rw [real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, unit_norm,
      show ⟪(q : ℍ[ℝ]), (p : ℍ[ℝ])⟫_ℝ = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ from real_inner_comm .., hdouble]
    have hcd : Real.cos (d / 2) ≠ 0 := by dsimp [L] at hL; linarith
    dsimp only [L]
    field_simp [hcd]
    ring
  refine ⟨m, L, hL, hLm, by dsimp [L]; linarith, ?_, ?_⟩
  · rw [roundDist, hm₁, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
    linarith
  · rw [roundDist, hm₂, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
    linarith


private theorem normalized_midpoints
    (a b c d m n : U) (ε L M : ℝ) (hε : 0 ≤ ε) (hπ : ε < π)
    (hac : roundDist a c ≤ ε) (hbd : roundDist b d ≤ ε)
    (hm : (a : ℍ[ℝ]) + b = L • (m : ℍ[ℝ]))
    (hn : (c : ℍ[ℝ]) + d = M • (n : ℍ[ℝ]))
    (hL : 2 * Real.cos (ε / 2) ≤ L) (hM : 2 * Real.cos (ε / 2) ≤ M) :
    Real.sin (roundDist m n / 2) ≤ Real.tan (ε / 2) := by
  have hcos := Real.cos_pos_of_mem_Ioo (x := ε / 2) ⟨by linarith [Real.pi_pos], by linarith⟩
  have hLp : 0 ≤ L := by linarith
  have hMp : 0 ≤ M := by linarith
  have hnorm : ‖L • (m : ℍ[ℝ]) - M • (n : ℍ[ℝ])‖ ≤ 4 * Real.sin (ε / 2) := by
    rw [← hm, ← hn, show (a : ℍ[ℝ]) + b - (c + d) = (a - c) + (b - d) by abel]
    exact (norm_add_le _ _).trans (by
      linarith [chord_le a c hπ.le hac, chord_le b d hπ.le hbd])
  have hid : ‖L • (m : ℍ[ℝ]) - M • (n : ℍ[ℝ])‖ ^ 2 =
      (L - M) ^ 2 + L * M * ‖(m : ℍ[ℝ]) - n‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hLp, abs_of_nonneg hMp, unit_norm, unit_norm,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hd₀ : 0 ≤ roundDist m n := Real.arccos_nonneg _
  have hd₁ : roundDist m n ≤ π := Real.arccos_le_pi _
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := roundDist m n / 2)
    (by linarith) (by linarith [Real.pi_pos])
  have hεs := Real.sin_nonneg_of_nonneg_of_le_pi (x := ε / 2)
    (by linarith) (by linarith [Real.pi_pos])
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  rw [hid, chord_sq] at hsq
  have hprod := mul_le_mul hL hM (by positivity) hLp
  have hprod' := mul_le_mul_of_nonneg_right hprod (sq_nonneg (Real.sin (roundDist m n / 2)))
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos]
  apply (sq_le_sq₀ (by positivity) hεs).mp
  rw [mul_pow]
  nlinarith [sq_nonneg (L - M)]


private theorem shift_midpoints (m n : U) {r δ : ℝ}
    (hr : 0 ≤ r) (hd : roundDist m n < π)
    (hδ : 0 ≤ δ) (hs : roundDist m n ≤ r + 2 * δ) :
    ∃ y z : U, roundDist m y ≤ δ ∧ roundDist n z ≤ δ ∧ roundDist y z ≤ r := by
  let D := roundDist m n
  by_cases h : D ≤ r
  · exact ⟨m, n, by simpa [round_self], by simpa [round_self], h⟩
  have hD : 0 < D := hr.trans_lt (lt_of_not_ge h)
  have hsp : 0 < Real.sin D := Real.sin_pos_of_pos_of_lt_pi hD hd
  have hmn : ⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ = Real.cos D := by
    dsimp [D]
    rw [round_eq_angle, cos_angle, unit_norm, unit_norm, one_mul, div_one]
  let e : ℍ[ℝ] := (Real.sin D)⁻¹ • ((n : ℍ[ℝ]) - Real.cos D • (m : ℍ[ℝ]))
  have hme : ⟪(m : ℍ[ℝ]), e⟫_ℝ = 0 := by
    simp [e, real_inner_smul_right, inner_sub_right, hmn, real_inner_self_eq_norm_sq, unit_norm]
  have hne : ‖e‖ = 1 := by
    have hinner : ‖(n : ℍ[ℝ]) - Real.cos D • (m : ℍ[ℝ])‖ = Real.sin D := by
      apply (sq_eq_sq₀ (norm_nonneg _) hsp.le).mp
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, unit_norm, unit_norm,
        real_inner_smul_right, show ⟪(n : ℍ[ℝ]), (m : ℍ[ℝ])⟫_ℝ = Real.cos D from (real_inner_comm ..).trans hmn]
      nlinarith [Real.cos_sq_add_sin_sq D]
    dsimp only [e]
    rw [norm_smul, hinner, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsp),
      inv_mul_cancel₀ hsp.ne']
  let circle : ℝ → U := fun t =>
    ofUnit (Real.cos t • (m : ℍ[ℝ]) + Real.sin t • e) (by
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        real_inner_smul_left, real_inner_smul_right, hme, hne, unit_norm, mul_one, mul_one,
        sq_abs, sq_abs]
      nlinarith [Real.cos_sq_add_sin_sq t])
  have hcircle (p q : ℝ) (hpq : 0 ≤ p - q) (hπ : p - q ≤ π) :
      roundDist (circle p) (circle q) = p - q := by
    unfold roundDist
    change Real.arccos ⟪Real.cos p • (m : ℍ[ℝ]) + Real.sin p • e,
      Real.cos q • (m : ℍ[ℝ]) + Real.sin q • e⟫_ℝ = _
    rw [← Real.arccos_cos hpq hπ, Real.cos_sub]
    congr 1
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hme, show ⟪e, (m : ℍ[ℝ])⟫_ℝ = 0 from (real_inner_comm ..).trans hme,
      real_inner_self_eq_norm_sq, unit_norm, hne]
    ring
  have hc₀ : circle 0 = m := by
    apply Subtype.ext
    change Real.cos 0 • (m : ℍ[ℝ]) + Real.sin 0 • e = _
    simp
  have hcD : circle D = n := by
    apply Subtype.ext
    change Real.cos D • (m : ℍ[ℝ]) + Real.sin D • e = _
    dsimp only [e]
    rw [smul_smul, mul_inv_cancel₀ hsp.ne', one_smul, add_sub_cancel]
  let a := (D - r) / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have haδ : a ≤ δ := by dsimp [a]; linarith
  have haπ : a ≤ π := by dsimp [a]; linarith [Real.pi_pos]
  refine ⟨circle a, circle (D - a), ?_, ?_, ?_⟩
  · rw [← hc₀, round_comm, hcircle _ _ (by linarith) (by linarith)]
    linarith
  · rw [← hcD, hcircle _ _ (by linarith) (by linarith)]
    linarith
  · rw [round_comm, hcircle _ _ (by dsimp [a]; linarith) (by linarith)]
    dsimp [a]
    linarith


private theorem midpoint_mixed_term (s t h z c C : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hz : 0 ≤ z) (hh0 : 0 < h) (hh : h ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ h) (hc : C ≤ c) (hun : h^2 + z^2 = 1)
    (hcoef : (1-C)*t^2 ≤ s^2*(1+C)^3) :
    t^2*(1-h) ≤ s*t*z*(1+c/h) := by
  have hrange : (1-h)*(1+C) ≤ (1-C)*(1+h) := by nlinarith
  have hnorm : (1-h)^2*(1+C) ≤ (1-C)*z^2 := calc
    _ = (1-h)*((1-h)*(1+C)) := by ring
    _ ≤ (1-h)*((1-C)*(1+h)) :=
      mul_le_mul_of_nonneg_left hrange (sub_nonneg.mpr hh)
    _ = (1-C)*(1-h^2) := by ring
    _ = _ := by rw [show 1-h^2 = z^2 by linarith]
  have hsq : (t*(1-h))^2*(1+C) ≤ (s*z*(1+C))^2*(1+C) := calc
    _ = t^2*((1-h)^2*(1+C)) := by ring
    _ ≤ t^2*((1-C)*z^2) := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
    _ = z^2*((1-C)*t^2) := by ring
    _ ≤ z^2*(s^2*(1+C)^3) := mul_le_mul_of_nonneg_left hcoef (sq_nonneg _)
    _ = _ := by ring
  have hsq' : (t*(1-h))^2 ≤ (s*z*(1+C))^2 := by
    by_contra! hn
    exact (not_lt_of_ge hsq) (mul_lt_mul_of_pos_right hn (by linarith))
  have hlin := (sq_le_sq₀ (mul_nonneg ht (sub_nonneg.mpr hh))
    (show 0 ≤ s*z*(1+C) by positivity)).mp hsq'
  have hdiv : C ≤ c/h := (le_div_iff₀ hh0).2 (calc
    C*h ≤ C*1 := mul_le_mul_of_nonneg_left hh hC0
    _ ≤ c := by simpa using hc)
  calc
    _ = t*(t*(1-h)) := by ring
    _ ≤ t*(s*z*(1+C)) := mul_le_mul_of_nonneg_left hlin ht
    _ = s*t*z*(1+C) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

set_option maxHeartbeats 700000 in
private theorem projected_centers
    (a b c d m n : U) (L M S C₀ C₁ U₀ ε : ℝ)
    (hm : (a : ℍ[ℝ]) + b = L • (m : ℍ[ℝ]))
    (hn : (c : ℍ[ℝ]) + d = M • (n : ℍ[ℝ]))
    (hL : 0 < L) (hM : 0 < M)
    (hab : roundDist a m ≤ ε / 2) (hbb : roundDist b m ≤ ε / 2)
    (hcd : roundDist c n ≤ ε / 2) (hdd : roundDist d n ≤ ε / 2)
    (he : 0 ≤ ε) (hε : ε ≤ 5 * π / 8)
    (hS : 0 ≤ S) (hS₁ : S ≤ 1)
    (hC₀ : 0 < C₀) (hC : C₀ ≤ -⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ)
    (hC₁ : -⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ ≤ C₁)
    (hcoef : (1 - C₀) * (1 - S) ≤ S * (1 + C₀)^3)
    (hu : Real.cos (4 * ε / 5) ≤ U₀) (hu₁ : U₀ ≤ 1 - (1 + C₁) * S)
    (hratio : Real.cos (4 * ε / 5) ≤ Real.sqrt S * Real.cos (ε / 2)) :
    ∃ y z : U, roundDist a y ≤ 4 * ε / 5 ∧ roundDist b y ≤ 4 * ε / 5 ∧
      roundDist c z ≤ 4 * ε / 5 ∧ roundDist d z ≤ 4 * ε / 5 ∧
        roundDist y z ≤ 4 * ε / 5 := by
  obtain ⟨v₀, hv₀, horth₀⟩ := orthogonal_unit (n := 3) (by decide)
    ![(a : ℍ[ℝ]), (b : ℍ[ℝ]), (d : ℍ[ℝ]) - c]
  obtain ⟨v, hv, horth, hζ⟩ : ∃ v : ℍ[ℝ], ‖v‖ = 1 ∧
      (∀ i : Fin 3, ⟪(![(a : ℍ[ℝ]), (b : ℍ[ℝ]), (d : ℍ[ℝ]) - c] : Fin 3 → ℍ[ℝ]) i,
        v⟫_ℝ = 0) ∧ 0 ≤ ⟪(n : ℍ[ℝ]), v⟫_ℝ := by
    by_cases h : 0 ≤ ⟪(n : ℍ[ℝ]), v₀⟫_ℝ
    · exact ⟨v₀, hv₀, horth₀, h⟩
    · exact ⟨-v₀, by simpa, fun i => by simp [horth₀ i], by simp; linarith⟩
  have hva : ⟪(a : ℍ[ℝ]), v⟫_ℝ = 0 := horth 0
  have hvb : ⟪(b : ℍ[ℝ]), v⟫_ℝ = 0 := horth 1
  have hvcd : ⟪(d : ℍ[ℝ]) - c, v⟫_ℝ = 0 := horth 2
  have hmv : ⟪(m : ℍ[ℝ]), v⟫_ℝ = 0 := by
    have hh := congrArg (fun q : ℍ[ℝ] => ⟪q, v⟫_ℝ) hm
    simp only [inner_add_left, real_inner_smul_left, hva, hvb, add_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hL.ne'
  let ζ := ⟪(n : ℍ[ℝ]), v⟫_ℝ
  let C := -⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ
  have hvn : ⟪v, (n : ℍ[ℝ])⟫_ℝ = ζ := real_inner_comm ..
  have hnm : ⟪(n : ℍ[ℝ]), (m : ℍ[ℝ])⟫_ℝ = -C := by simp only [C, neg_neg, real_inner_comm]
  have hvm : ⟪v, (m : ℍ[ℝ])⟫_ℝ = 0 := (real_inner_comm ..).trans hmv
  have hproj : ζ^2 ≤ 1 - C^2 := by
    have hh := sq_nonneg ‖(n : ℍ[ℝ]) - (ζ • v - C • (m : ℍ[ℝ]))‖
    simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      inner_sub_right, real_inner_smul_left, real_inner_smul_right, hmv, hvm, hnm,
      unit_norm, hv, one_pow] at hh
    change 1 - 2 * (ζ * ζ - C * -C) + _ ≥ 0 at hh
    nlinarith
  let h := Real.sqrt (1 - ζ^2)
  have hh₀ : 0 ≤ h := Real.sqrt_nonneg _
  have hsquare : h^2 = 1 - ζ^2 := Real.sq_sqrt (by nlinarith)
  have hCh : C ≤ h := (sq_le_sq₀ (hC₀.le.trans hC) hh₀).mp (by linarith)
  have hhp : 0 < h := hC₀.trans_le (hC.trans hCh)
  have hh₁ : h ≤ 1 := by nlinarith [sq_nonneg (h - 1), sq_nonneg ζ]
  let w₀ := (v - ζ • (n : ℍ[ℝ]))
  let w : ℍ[ℝ] := h⁻¹ • w₀
  have hwn : ⟪(n : ℍ[ℝ]), w⟫_ℝ = 0 := by
    simp [w, w₀, inner_sub_right, real_inner_smul_right, ζ]
  have hdiffn : ⟪(d : ℍ[ℝ]) - c, (n : ℍ[ℝ])⟫_ℝ = 0 := by
    apply (mul_eq_zero.mp (_ : M * ⟪(d : ℍ[ℝ]) - c, (n : ℍ[ℝ])⟫_ℝ = 0)).resolve_left hM.ne'
    rw [← real_inner_smul_right, ← hn, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, unit_norm, unit_norm,
      show ⟪(d : ℍ[ℝ]), (c : ℍ[ℝ])⟫_ℝ = ⟪(c : ℍ[ℝ]), (d : ℍ[ℝ])⟫_ℝ from real_inner_comm ..]
    ring
  have hwc : ⟪(c : ℍ[ℝ]), w⟫_ℝ = 0 := by
    have h₁ : ⟪(d : ℍ[ℝ]) - c, w⟫_ℝ = 0 := by
      simp [w, w₀, real_inner_smul_right, inner_sub_right, hvcd, hdiffn]
    have h₂ : ⟪(c : ℍ[ℝ]) + d, w⟫_ℝ = 0 := by
      simp [hn, real_inner_smul_left, hwn]
    rw [inner_sub_left] at h₁
    rw [inner_add_left] at h₂
    linarith
  have hwd : ⟪(d : ℍ[ℝ]), w⟫_ℝ = 0 := by
    have h₂ : ⟪(c : ℍ[ℝ]) + d, w⟫_ℝ = 0 := by simp [hn, real_inner_smul_left, hwn]
    rw [inner_add_left, hwc, zero_add] at h₂
    exact h₂

  have hw : ‖w‖ = 1 := by
    have hw₀ : ‖w₀‖ = h := by
      apply (sq_eq_sq₀ (norm_nonneg _) hh₀).mp
      simp only [w₀, norm_sub_sq_real, real_inner_smul_right, hvn, hv, unit_norm, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs, one_pow, mul_one]
      rw [hsquare]
      ring
    simp [w, norm_smul, hw₀, hhp.ne', abs_of_pos hhp]
  have hmw : ⟪(m : ℍ[ℝ]), w⟫_ℝ = C * ζ / h := by
    simp only [w, w₀, inner_sub_right, real_inner_smul_right, hmv, zero_sub, div_eq_mul_inv]
    rw [show ⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ = -C by simp [C]]
    ring
  have hvw : ⟪v, w⟫_ℝ = h := by
    simp only [w, w₀, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hvn, hv, one_pow]
    rw [← sq, ← hsquare]
    field_simp
  let s := Real.sqrt S
  let t := Real.sqrt (1 - S)
  have hs : s ^ 2 = S := Real.sq_sqrt hS
  have ht : t ^ 2 = 1 - S := Real.sq_sqrt (by linarith)
  have hunit (p : U) (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (hpq : ⟪(p : ℍ[ℝ]), q⟫_ℝ = 0) :
      ‖s • (p : ℍ[ℝ]) + t • q‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hpq,
      norm_smul, hq, Real.norm_eq_abs, sq_abs, hs, ht]
  let y := ofUnit _ (hunit m v hv hmv)
  let z := ofUnit _ (hunit n w hw hwn)
  have hside (p q : U) (v : ℍ[ℝ]) (hclose : roundDist p q ≤ ε / 2)
      (horth : ⟪(p : ℍ[ℝ]), v⟫_ℝ = 0) (u : U)
      (hu : (u : ℍ[ℝ]) = s • (q : ℍ[ℝ]) + t • v) :
      roundDist p u ≤ 4 * ε / 5 := by
    apply (round_le_iff _ _ (by positivity) (by linarith [Real.pi_pos])).mpr
    rw [hu, inner_add_right, real_inner_smul_right, real_inner_smul_right, horth,
      mul_zero, add_zero]
    exact hratio.trans (mul_le_mul_of_nonneg_left
      ((round_le_iff _ _ (by positivity) (by linarith [Real.pi_pos])).mp hclose)
      (Real.sqrt_nonneg _))
  refine ⟨y, z, hside a m v hab hva y rfl, hside b m v hbb hvb y rfl,
    hside c n w hcd hwc z rfl, hside d n w hdd hwd z rfl, ?_⟩
  apply (round_le_iff _ _ (by positivity) (by linarith [Real.pi_pos])).mpr
  have hmix := midpoint_mixed_term s t h ζ C C₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hζ hhp hh₁ hC₀.le (hC.trans hCh) hC (by linarith) (by simpa only [hs, ht] using hcoef)
  change Real.cos (4 * ε / 5) ≤
    ⟪s • (m : ℍ[ℝ]) + t • v, s • (n : ℍ[ℝ]) + t • w⟫_ℝ
  have heq : ⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ = -C := by simp [C]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hmw, hvw, hvn, heq]
  calc
    _ ≤ 1 - (1 + C₁) * S := hu.trans hu₁
    _ ≤ 1 - (1 + C) * S := by gcongr
    _ ≤ _ := by
      have heq : s * t * ζ * (1 + C / h) = s * (t * (C * ζ / h)) + t * (s * ζ) := by ring
      rw [heq] at hmix
      nlinarith [congrArg (fun q : ℝ => q * C) hs, congrArg (fun q : ℝ => q * h) ht]


private theorem intermediate_fit (a b c d m n : U) (ε L M : ℝ)
    (he : degrees 77 ≤ ε) (hε : ε ≤ 5*π/8) (hD : 7*ε/5 < roundDist m n)
    (hgap : Real.sin (roundDist m n / 2) ≤ Real.tan (ε/2))
    (hm : (a : ℍ[ℝ]) + b = L • (m : ℍ[ℝ]))
    (hn : (c : ℍ[ℝ]) + d = M • (n : ℍ[ℝ]))
    (hL : 0 < L) (hM : 0 < M)
    (ham : roundDist a m ≤ ε/2) (hbm : roundDist b m ≤ ε/2)
    (hcn : roundDist c n ≤ ε/2) (hdn : roundDist d n ≤ ε/2) :
    ∃ y z : U, roundDist a y ≤ 4*ε/5 ∧ roundDist b y ≤ 4*ε/5 ∧
      roundDist c z ≤ 4*ε/5 ∧ roundDist d z ≤ 4*ε/5 ∧ roundDist y z ≤ 4*ε/5 := by
  have hε₀ : 0 ≤ ε := (show 0 ≤ degrees 77 by unfold degrees; positivity).trans he
  let x := 180 * ε / π
  have hx : degrees x = ε := by dsimp [x, degrees]; field_simp [Real.pi_ne_zero]
  have hmono : StrictMono degrees := by
    intro a b hab
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hab Real.pi_pos) (by norm_num)
  have hx₀ : 77 ≤ x := hmono.le_iff_le.mp (by rw [hx]; exact he)
  have hx₁ : x ≤ 225/2 := hmono.le_iff_le.mp (by
    rw [hx, show degrees (225/2) = 5*π/8 by unfold degrees; ring]
    exact hε)
  obtain ⟨i, hai, hbi⟩ := covered_degrees x hx₀ hx₁
  have hr := midpoint_bound_table i
  have htrig := midpoint_trig_table i
  generalize hi : boundRow i = row at hai hbi hr htrig
  rcases row with ⟨a₀,b₀,u₀,m₀,c₀,c₁,S⟩
  dsimp at hai hbi hr htrig
  obtain ⟨ha₀, ha90, hab, hb₀, hu₀, hc₀, hS₀, hS₁, harith, hcoef, hlast⟩ := hr
  obtain ⟨hut, hmt, hct, hbt⟩ := htrig
  have ha : 0 ≤ degrees a₀ := by unfold degrees; positivity
  have hae : degrees a₀ ≤ ε := by rw [← hx]; exact hmono.monotone hai
  have heb : ε ≤ degrees b₀ := by rw [← hx]; exact hmono.monotone hbi
  have hfour : (4*degrees a₀/5) = degrees (4*a₀/5) := by unfold degrees; ring
  have hseven : (7*degrees a₀/5) = degrees (7*a₀/5) := by unfold degrees; ring
  have hu : Real.cos (4*ε/5) ≤ u₀/1000 := by
    apply le_trans (Real.cos_le_cos_of_nonneg_of_le_pi (x := 4*degrees a₀/5)
      (by positivity) (by linarith [Real.pi_pos]) (by linarith))
    simpa only [hfour] using hut
  have hc : c₀/1000 ≤ -⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (x := 7*degrees a₀/5)
      (by positivity) (Real.arccos_le_pi _) (by linarith : 7*degrees a₀/5 ≤ roundDist m n)
    rw [hseven, Real.cos_arccos (inner_bounds m n (unit_norm m) (unit_norm n)).1
      (inner_bounds m n (unit_norm m) (unit_norm n)).2] at hh
    linarith
  have hd : -⟪(m : ℍ[ℝ]), (n : ℍ[ℝ])⟫_ℝ ≤ c₁/1000 := by
    rcases hbt with rfl | ⟨hb, hbt⟩
    · have := (inner_bounds m n (unit_norm m) (unit_norm n)).1
      norm_num
      linarith
    · have hbπ : degrees b₀ ≤ π/2 := by unfold degrees; linarith [mul_le_mul_of_nonneg_right hb.le Real.pi_pos.le]
      have hbcos : 0 < Real.cos (degrees b₀/2) := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ha.trans (hmono.monotone hab), Real.pi_pos],
          by linarith [Real.pi_pos]⟩
      have hent : 0 ≤ Real.sin (roundDist m n/2) := Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [show 0 ≤ roundDist m n from Real.arccos_nonneg _])
        (by linarith [show roundDist m n ≤ π from Real.arccos_le_pi _, Real.pi_pos])
      have htan := Real.strictMonoOn_tan.monotoneOn
        (show ε/2 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
        (show degrees b₀/2 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
        (by linarith : ε/2 ≤ degrees b₀/2)
      have ht := hgap.trans htan
      have hsq := (sq_le_sq₀ hent (hent.trans ht)).2 ht
      rw [Real.sin_sq_eq_half_sub, show 2*(roundDist m n/2) = roundDist m n by ring,
        round_eq_angle, cos_angle, unit_norm, unit_norm, one_mul, div_one,
        tan_half_sq _ hbcos.ne'] at hsq
      have hden : 0 < 1 + Real.cos (degrees b₀) := by
        have := Real.cos_le_cos_of_nonneg_of_le_pi (x := degrees b₀) (y := π/2)
          (hε₀.trans heb) (by linarith [Real.pi_pos]) hbπ
        rw [Real.cos_pi_div_two] at this
        linarith
      have hbound := (le_div_iff₀ hden).mp hsq
      nlinarith [mul_pos (show 0 < 1 + Real.cos (degrees b₀) by linarith) (show 0 < (1:ℝ) by norm_num)]
  have hratio : Real.cos (4*ε/5) ≤ Real.sqrt (S/1000) * Real.cos (ε/2) := by
    have hcos (y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 5*π/8) : 0 < Real.cos (y/2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hCa := hcos _ ha (hae.trans hε)
    have hCe := hcos _ hε₀ hε
    have hsq : m₀/1000 ≤ Real.cos (degrees a₀/2)^2 := by
      have hh := Real.cos_two_mul (degrees a₀/2)
      rw [show 2*(degrees a₀/2) = degrees a₀ by ring] at hh
      linarith
    have hSq : 0 ≤ S/1000 := by positivity
    have hv : u₀/1000 ≤ Real.sqrt (S/1000) * Real.cos (degrees a₀/2) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hSq]
      nlinarith [mul_le_mul_of_nonneg_right hsq hSq]
    apply (div_le_iff₀ hCe).mp
    apply (cos_ratio ha hae hε).trans
    apply (div_le_iff₀ hCa).mpr
    exact (by simpa only [hfour] using hut : Real.cos (4*degrees a₀/5) ≤ u₀/1000).trans hv
  exact projected_centers a b c d m n L M (S/1000) (c₀/1000) (c₁/1000) (u₀/1000) ε
    hm hn hL hM ham hbm hcn hdn hε₀ hε (by positivity) (by linarith) (by positivity)
    hc hd hcoef hu hlast hratio


private theorem center_fit (a b c d : U) (ε : ℝ) (he : 0 ≤ ε) (hε : ε < 5 * π / 8)
    (hab : roundDist a b ≤ ε) (hcd : roundDist c d ≤ ε)
    (hac : roundDist a c ≤ ε) (hbd : roundDist b d ≤ ε) :
    ∃ y z : U, roundDist a y ≤ 4*ε/5 ∧ roundDist b y ≤ 4*ε/5 ∧
      roundDist c z ≤ 4*ε/5 ∧ roundDist d z ≤ 4*ε/5 ∧ roundDist y z ≤ 4*ε/5 := by
  have hπ : ε < π := by linarith [Real.pi_pos]
  obtain ⟨m, L, hL, hm, hLm, ham, hbm⟩ := midpoint a b hπ hab
  obtain ⟨n, M, hM, hn, hMn, hcn, hdn⟩ := midpoint c d hπ hcd
  have hgap := normalized_midpoints a b c d m n ε L M he hπ hac hbd hm hn hLm hMn
  by_cases hD : roundDist m n ≤ 7*ε/5
  · obtain ⟨y, z, hy, hz, hfin⟩ := shift_midpoints m n (r := 4*ε/5) (δ := 3*ε/10)
      (by positivity) (by linarith [Real.pi_pos]) (by positivity) (by linarith)
    refine ⟨y, z, ?_, ?_, ?_, ?_, hfin⟩
    · linarith [distance_triangle a m y]
    · linarith [distance_triangle b m y]
    · linarith [distance_triangle c n z]
    · linarith [distance_triangle d n z]
  · have hsmall : degrees 77 ≤ ε := by
      by_contra! hbad
      exact hD (small_gap he hbad.le (Real.arccos_nonneg _) (Real.arccos_le_pi _) hgap)
    exact intermediate_fit a b c d m n ε L M hsmall hε.le (lt_of_not_ge hD)
      hgap hm hn hL hM ham hbm hcn hdn

/-- Every admissible defect bound on four vertices gives a simultaneous fit of radius
four fifths of that bound in the round unit-quaternion distance. -/
theorem reconstruction_bound (g : Fin 4 → Fin 4 → U) (ε : ℝ)
    (he : 0 ≤ ε) (hπ : ε ≤ π) (hg : DefectLE g ε) :
    ∃ φ : Fin 4 → U, Fits g φ (4 * ε / 5) := by
  obtain ⟨hrev, hdiag, htri⟩ := hg
  by_cases hlarge : 5*π/8 ≤ ε
  · obtain ⟨φ, hφ⟩ := orthogonal_fit g hrev
    exact ⟨φ, fun i j hij => (hφ i j hij).trans (by linarith)⟩
  let a : Fin 4 → U := fun i => g 0 i
  let g' : Fin 4 → Fin 4 → U := fun i j => a i * g i j * (a j)⁻¹
  have ha : a 0 = 1 := hdiag 0
  have hsp (i : Fin 4) : g' 0 i = 1 := by simp [g', ha, a]
  have hr' (i j : Fin 4) : g' j i = (g' i j)⁻¹ := by simp [g', hrev i j, mul_assoc]
  have htri' (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      roundDist (g' i j * g' j k) (g' i k) ≤ ε := by
    have hgauge : g' i j * g' j k = a i * (g i j * g j k) * (a k)⁻¹ := by
      simp [g', mul_assoc]
    rw [hgauge]
    change roundDist (a i * (g i j * g j k) * (a k)⁻¹)
      (a i * g i k * (a k)⁻¹) ≤ ε
    rw [round_mul_right, round_mul_left]
    exact htri _ _ _ hij hjk hik
  let A := g' 1 2
  let B := g' 2 3
  let C := g' 3 1
  have hA : roundDist A 1 ≤ ε := by
    simpa [hsp, A] using htri' 0 1 2 (by decide) (by decide) (by decide)
  have hB : roundDist B 1 ≤ ε := by
    simpa [hsp, B] using htri' 0 2 3 (by decide) (by decide) (by decide)
  have hC : roundDist (1 : U) C⁻¹ ≤ ε := by
    have h := htri' 0 3 1 (by decide) (by decide) (by decide)
    rw [hsp, hsp, one_mul] at h
    have hh : roundDist C⁻¹ (1 : U)⁻¹ = roundDist C 1 := round_inv C 1
    rw [inv_one] at hh
    rw [round_comm, hh]
    exact h
  have hABC : roundDist (A * B) C⁻¹ ≤ ε := by
    have h := htri' 1 2 3 (by decide) (by decide) (by decide)
    have hr : g' 1 3 = C⁻¹ := hr' 3 1
    simpa [A, B, ← hr] using h
  have hAB : roundDist B (A * B) ≤ ε := by
    calc
      _ = roundDist ((1 : U) * B) (A * B) := by rw [one_mul]
      _ = roundDist 1 A := round_mul_right B 1 A
      _ ≤ ε := (round_comm 1 A).trans_le hA
  obtain ⟨y, z, hyB, hyAB, hz₁, hzC, hyz⟩ :=
    center_fit B (A*B) 1 C⁻¹ ε he (lt_of_not_ge hlarge) hAB hC hB hABC
  let ψ : Fin 4 → U := ![1, 1, y * B⁻¹, z]
  have hψ : Fits g' ψ (4*ε/5) := by
    apply fits_of_six hr'
    · simpa [ψ, hsp, round_self] using (show 0 ≤ 4*ε/5 by positivity)
    · simpa [ψ, hsp, ← round_mul_right B (1 : U) (y * B⁻¹), B, mul_assoc] using hyB
    · simpa [ψ, hsp] using hz₁
    · change roundDist (1 * A) (y * B⁻¹) ≤ _
      rw [one_mul, ← round_mul_right B, inv_mul_cancel_right]
      exact hyAB
    · change roundDist ((y * B⁻¹) * B) z ≤ _
      simpa using hyz
    · change roundDist (z * C) 1 ≤ _
      rw [← round_mul_right C⁻¹, mul_inv_cancel_right, one_mul, round_comm]
      exact hzC
  refine ⟨fun i => ψ i * a i, fun i j hij => ?_⟩
  calc
    _ = roundDist (a i * g i j * (a j)⁻¹)
        ((a i * (ψ i * a i)⁻¹ * (ψ j * a j)) * (a j)⁻¹) := by
        rw [round_mul_right, mul_assoc (a i), round_mul_left]
    _ = roundDist (g' i j) ((ψ i)⁻¹ * ψ j) := by simp [g', mul_assoc]
    _ ≤ _ := hψ i j hij

/-- The quarter-turn assignment attains its exact defect and minimax reconstruction radius.
The same potential attains the optimal error on every directed edge. -/
theorem quarter_turn_sharp :
    DefectLE quarterGains (π/2) ∧
    (∃ i j k : Fin 4, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      roundDist (quarterGains i j * quarterGains j k) (quarterGains i k) = π/2) ∧
    (∀ φ : Fin 4 → U, ∃ i j : Fin 4, i ≠ j ∧
      quarterError ≤ roundDist (quarterGains i j) ((φ i)⁻¹ * φ j)) ∧
    (∃ φ : Fin 4 → U, ∀ i j : Fin 4, i ≠ j →
      roundDist (quarterGains i j) ((φ i)⁻¹ * φ j) = quarterError) ∧
    3/5 < 2*quarterError/π := by
  refine ⟨quarter_defect, ⟨0,1,2,by decide, by decide, by decide, ?_⟩,
    quarter_lower, ⟨quarterPotential, quarter_attains⟩, ?_⟩
  · simp [quarterGains, roundDist, inner_eq_components, unitI]
  · apply (lt_div_iff₀ Real.pi_pos).mpr
    linarith [quarterError_gt]

/-- The claim that some coefficient below the quarter-turn ratio works for all admissible
unit-quaternion gain assignments on four vertices. -/
def subcritical_claim : Prop :=
  ∃ k : ℝ, k < 2*quarterError/π ∧
    ∀ (g : Fin 4 → Fin 4 → U) (ε : ℝ), 0 ≤ ε → ε ≤ π → DefectLE g ε →
      ∃ φ : Fin 4 → U, Fits g φ (k*ε)

/-- No universal coefficient can lie strictly below the quarter-turn ratio. -/
theorem not_subcritical_claim : ¬ subcritical_claim := by
  intro h
  obtain ⟨k, hk, hfit⟩ := h
  obtain ⟨hdefect, _, hrad, _, _⟩ := quarter_turn_sharp
  obtain ⟨φ, hφ⟩ := hfit quarterGains (π/2) (by positivity) (by linarith [Real.pi_pos]) hdefect
  obtain ⟨i,j,hij,hl⟩ := hrad φ
  have hu := hφ i j hij
  rw [lt_div_iff₀ Real.pi_pos] at hk
  linarith

end RoundQuaternionK4Bounds

