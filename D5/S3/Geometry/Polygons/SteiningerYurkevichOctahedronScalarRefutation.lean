/- GID: D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation
   generality: I
   mirror-B: D5/B/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.claim; result=D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.result; claim=D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation.claim
   digest: Two orthogonal octahedral shadows refute the diameter-plus-square scalar bound. -/
/-
result:
  proof_shape: content
  escape_witness: none
  admission_basis: open-problem-resolution (#27498; Refuted)
  Direct frozen dependencies:
    D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.Ambient
      statement_id: sha256:3d3ac3730482c6fb291c79e02d908aac38414aced691ae03897f7264f2b0aef1
    D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.crossHull
      statement_id: sha256:5cac71d308903ebcb88e2f7dc13402d044098dba5a3f99b1e911f2cd7fefd5cf
    D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.crossPolytope
      statement_id: sha256:303eacae3fa182be2f2b623ee9cf95ef47702296198528a208434c0d71cc57b9
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The source definitions use EuclideanSpace directly and the existing crossPolytope;
no new type alias, octahedron alias, column alias or linear-map alias is introduced.
The claim retains the supremum/infimum assertion and all rotation/translation
quantifiers of issue #27498. Weak enclosing lengths have the same infimum as
strict enclosing lengths. No attainment of a smallest strict enclosure is assumed.
The sharp H square bound eliminates translation using the antipodal vertices,
then uses the unit-circle strip inequalities uniformly over SO(2).
Private proof declarations below are consumed helpers. The nonlinear strip bound
and statements using it are content; the remaining helpers are bind-only.
-/
import D5.S3.Combinatorics.Geometry.CrossPolytopeFaceCounts
import D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope

namespace D5.S3.Geometry.Polygons.SteiningerYurkevichOctahedronScalarRefutation


/-- The source's orthogonal projection matrices satisfy M Mᵀ = I₂. -/
def IsProjection (M : Matrix (Fin 2) (Fin 3) ℝ) : Prop :=
  M * M.transpose = 1

/-- A planar shadow, with the Euclidean rather than the coordinate sup norm. -/
def shadow (M : Matrix (Fin 2) (Fin 3) ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun x : (EuclideanSpace ℝ (Fin 3)) => WithLp.toLp 2 (Matrix.mulVec M (WithLp.ofLp x))) '' (D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.crossPolytope 3)

/-- Diameter of the convex hull, as defined in the source. -/
noncomputable def diameter (P : Set (EuclideanSpace ℝ (Fin 2))) : ℝ := Metric.diam (convexHull ℝ P)

/-- Nonnegative side lengths of enclosing squares, with every rotation and translation allowed. -/
def enclosingSquareLengths (P : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  {l : ℝ | 0 ≤ l ∧
    ∃ R : Matrix.specialOrthogonalGroup (Fin 2) ℝ, ∃ t : (EuclideanSpace ℝ (Fin 2)),
      ∀ p : (EuclideanSpace ℝ (Fin 2)), p ∈ P → ∀ i : Fin 2,
        |(Matrix.mulVec (R : Matrix (Fin 2) (Fin 2) ℝ) (WithLp.ofLp (p - t))) i| ≤ l / 2}

/-- The source's smallest enclosing-square side length, expressed as an infimum. -/
noncomputable def squareSide (P : Set (EuclideanSpace ℝ (Fin 2))) : ℝ := sInf (enclosingSquareLengths P)

/-- The coefficient is fixed to 23/10 in the source's conjecture. -/
noncomputable def octahedralScalar (P : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  diameter P + (23 : ℝ) / 10 * squareSide P

/-- All scalar values of orthogonal shadows; the projection quantifier is explicit. -/
def projectionValues : Set ℝ :=
  {r : ℝ | ∃ M : Matrix (Fin 2) (Fin 3) ℝ,
    IsProjection M ∧ r = octahedralScalar (shadow M)}

/-- The unnumbered displayed conjecture in section 3 of arXiv:2609.10788v1. -/
def claim : Prop :=
  sSup projectionValues ≤ (3 * Real.sqrt 2 / 4) * sInf projectionValues

end D5.S3.Geometry.Polygons.SteiningerYurkevichOctahedronScalarRefutation


noncomputable section
open Set Matrix
open scoped BigOperators
namespace D5.S3.Geometry.Polygons.SteiningerYurkevichOctahedronScalarRefutation
set_option maxHeartbeats 500000
set_option maxRecDepth 4000


private def vertices (M : Matrix (Fin 2) (Fin 3) ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∃ j : Fin 3, p = (WithLp.toLp 2 (Matrix.col M j)) ∨ p = -(WithLp.toLp 2 (Matrix.col M j))}

private theorem shadow_hull (M : Matrix (Fin 2) (Fin 3) ℝ) :
    shadow M = convexHull ℝ (vertices M) := by
  unfold shadow
    D5.S3.Quantum.Entanglement.SymmetricBellPolytopeNotCrossPolytope.crossPolytope
    D5.S3.Combinatorics.Geometry.CrossPolytopeFaceCounts.crossHull
  rw [Set.image_image]
  change ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap.comp M.mulVecLin) '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq, vertices, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, ⟨j, rfl | rfl⟩, rfl⟩
    · exact ⟨j, Or.inl (by ext i; simp [Matrix.col])⟩
    · exact ⟨j, Or.inr (by ext i; simp [Matrix.col, Matrix.mulVec_neg])⟩
  · rintro ⟨j, rfl | rfl⟩
    · refine ⟨Pi.single j 1, ⟨j, Or.inl rfl⟩, ?_⟩
      ext i; simp [Matrix.col]
    · refine ⟨-Pi.single j 1, ⟨j, Or.inr rfl⟩, ?_⟩
      ext i; simp [Matrix.col, Matrix.mulVec_neg]

private theorem column_mem (M : Matrix (Fin 2) (Fin 3) ℝ) (j : Fin 3) :
    (WithLp.toLp 2 (Matrix.col M j)) ∈ shadow M := by
  rw [shadow_hull]
  exact subset_convexHull ℝ _ ⟨j, Or.inl rfl⟩
private theorem neg_column_mem (M : Matrix (Fin 2) (Fin 3) ℝ) (j : Fin 3) :
    -(WithLp.toLp 2 (Matrix.col M j)) ∈ shadow M := by
  rw [shadow_hull]
  exact subset_convexHull ℝ _ ⟨j, Or.inr rfl⟩

private theorem shadow_ball (M : Matrix (Fin 2) (Fin 3) ℝ) (r : ℝ)
    (h : ∀ j, ‖(WithLp.toLp 2 (Matrix.col M j))‖ ≤ r) : shadow M ⊆ Metric.closedBall 0 r := by
  rw [shadow_hull]
  apply convexHull_min _ (convex_closedBall 0 r)
  rintro x ⟨j, rfl | rfl⟩ <;> simpa [Metric.mem_closedBall, dist_zero_right] using h j

private theorem diameter_upper (M : Matrix (Fin 2) (Fin 3) ℝ) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ j, ‖(WithLp.toLp 2 (Matrix.col M j))‖ ≤ r) : diameter (shadow M) ≤ 2*r := by
  unfold diameter
  rw [convexHull_diam]
  exact Metric.diam_le_of_subset_closedBall hr (shadow_ball M r h)

private theorem shadow_bounded (M : Matrix (Fin 2) (Fin 3) ℝ) : Bornology.IsBounded (shadow M) := by
  let r : ℝ := ∑ j : Fin 3, ‖(WithLp.toLp 2 (Matrix.col M j))‖
  apply (Metric.isBounded_closedBall (x := (0 : (EuclideanSpace ℝ (Fin 2)))) (r := r)).subset
  apply shadow_ball
  intro j
  exact Finset.single_le_sum (fun k _ => norm_nonneg ((WithLp.toLp 2 (Matrix.col M k)))) (Finset.mem_univ j)

private theorem diam_column_lower (M : Matrix (Fin 2) (Fin 3) ℝ) (j : Fin 3) :
    2 * ‖(WithLp.toLp 2 (Matrix.col M j))‖ ≤ diameter (shadow M) := by
  have h := Metric.dist_le_diam_of_mem (shadow_bounded M) (column_mem M j) (neg_column_mem M j)
  simpa [diameter, convexHull_diam, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ, norm_smul] using h

private theorem square_nonneg (P : Set (EuclideanSpace ℝ (Fin 2))) : 0 ≤ squareSide P := by
  apply Real.sInf_nonneg
  intro l hl
  exact hl.1


private theorem coord_hull_bound (M : Matrix (Fin 2) (Fin 3) ℝ) (l : ℝ)
    (h : ∀ i j, |M i j| ≤ l/2) : ∀ p ∈ shadow M, ∀ i, |p i| ≤ l/2 := by
  intro p hp
  rw [shadow_hull] at hp
  have hc : Convex ℝ {p : (EuclideanSpace ℝ (Fin 2)) | ∀ i, |p i| ≤ l/2} := by
    have hb : Convex ℝ {v : Fin 2 → ℝ | ∀ i, |v i| ≤ l/2} := by
      simpa only [Set.pi, Set.mem_univ, Set.mem_Icc, forall_true_left, ← abs_le] using
        (convex_pi (𝕜 := ℝ) (s := Set.univ)
          (t := fun _ : Fin 2 => Set.Icc (-(l/2)) (l/2))
          (fun _ _ => convex_Icc _ _))
    exact hb.linear_preimage (EuclideanSpace.equiv (Fin 2) ℝ).toLinearMap
  apply convexHull_min _ hc hp
  rintro x ⟨j, rfl | rfl⟩ i <;> simpa [Matrix.col] using h i j

private theorem square_upper (M : Matrix (Fin 2) (Fin 3) ℝ) (l : ℝ)
    (hl : 0 ≤ l) (h : ∀ i j, |M i j| ≤ l/2) : squareSide (shadow M) ≤ l := by
  apply csInf_le ⟨0, fun _ hx => hx.1⟩
  refine ⟨hl, 1, 0, ?_⟩
  intro p hp i
  simpa using coord_hull_bound M l h p hp i

private theorem projection_entry (M : Matrix (Fin 2) (Fin 3) ℝ) (hM : IsProjection M)
    (i : Fin 2) (j : Fin 3) : |M i j| ≤ 1 := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i i) hM
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have hrow : (∑ k : Fin 3, (M i k)^2) = 1 := by simpa [pow_two] using h
  apply (sq_le_one_iff_abs_le_one _).mp
  rw [← hrow]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (M i k)) (Finset.mem_univ j)

private theorem projection_scalar_bounds (M : Matrix (Fin 2) (Fin 3) ℝ) (hM : IsProjection M) :
    0 ≤ octahedralScalar (shadow M) ∧ octahedralScalar (shadow M) ≤ 9 := by
  have hs := square_upper M 2 (by norm_num) (by intro i j; simpa using projection_entry M hM i j)
  have hnorm : ∀ j, ‖(WithLp.toLp 2 (Matrix.col M j))‖ ≤ 2 := by
    intro j
    have hn : ‖(WithLp.toLp 2 (Matrix.col M j))‖^2 ≤ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [Fin.sum_univ_two, Matrix.col, Matrix.transpose_apply, PiLp.toLp_apply]
      have h0 := (sq_le_one_iff_abs_le_one _).mpr (projection_entry M hM 0 j)
      have h1 := (sq_le_one_iff_abs_le_one _).mpr (projection_entry M hM 1 j)
      linarith
    nlinarith [norm_nonneg ((WithLp.toLp 2 (Matrix.col M j)))]
  have hd : diameter (shadow M) ≤ 4 := by
    convert diameter_upper M 2 (by norm_num) hnorm using 1 <;> norm_num
  have hd0 : 0 ≤ diameter (shadow M) := Metric.diam_nonneg
  have hs0 := square_nonneg (shadow M)
  unfold octahedralScalar
  constructor <;> nlinarith

private def H : Matrix (Fin 2) (Fin 3) ℝ :=
  !![Real.sqrt 2 / 2, -Real.sqrt 2 / 2, 0;
     Real.sqrt 6 / 6, Real.sqrt 6 / 6, -Real.sqrt 6 / 3]
private def I : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-1/3, 2/3, 2/3; 2/3, -1/3, 2/3]

private theorem H_projection : IsProjection H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, IsProjection, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
      Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)]

private theorem I_projection : IsProjection I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, IsProjection, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem I_diameter_upper : diameter (shadow I) ≤ 4 * Real.sqrt 2 / 3 := by
  have hnorm : ∀ j, ‖(WithLp.toLp 2 (Matrix.col I j))‖ ≤ 2 * Real.sqrt 2 / 3 := by
    intro j
    have hn : ‖(WithLp.toLp 2 (Matrix.col I j))‖^2 ≤ (8:ℝ)/9 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      fin_cases j <;> norm_num [Matrix.col, I, Fin.sum_univ_succ]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
      norm_nonneg ((WithLp.toLp 2 (Matrix.col I j)))]
  have h := diameter_upper I (2 * Real.sqrt 2 / 3) (by positivity) hnorm
  convert h using 1 <;> ring

private theorem I_square_upper : squareSide (shadow I) ≤ (4:ℝ)/3 := by
  apply square_upper I (4/3) (by norm_num)
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [I]
private theorem centered_vertex_enclosure (M : Matrix (Fin 2) (Fin 3) ℝ) {l : ℝ}
    (hl : l ∈ enclosingSquareLengths (shadow M)) :
    ∃ R : Matrix.specialOrthogonalGroup (Fin 2) ℝ,
      ∀ j : Fin 3, ∀ i : Fin 2,
        |Matrix.mulVec (R : Matrix (Fin 2) (Fin 2) ℝ) (WithLp.ofLp ((WithLp.toLp 2 (Matrix.col M j)))) i| ≤ l/2 := by
  obtain ⟨hl, R, t, ht⟩ := hl
  refine ⟨R, ?_⟩
  intro j i
  have hp := ht _ (column_mem M j) i
  have hn := ht _ (neg_column_mem M j) i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, PiLp.sub_apply, PiLp.neg_apply] at hp hn ⊢
  rcases abs_le.mp hp with ⟨hp0, hp1⟩
  rcases abs_le.mp hn with ⟨hn0, hn1⟩
  apply abs_le.mpr
  constructor <;> linarith

private theorem abs_sum_from_pair {x y L : ℝ} (hp : |x+y| ≤ L) (hm : |-x+y| ≤ L) :
    |x|+|y| ≤ L := by
  rcases abs_le.mp hp with ⟨hp0,hp1⟩
  rcases abs_le.mp hm with ⟨hm0,hm1⟩
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; linarith
  · rw [abs_of_nonneg hx, abs_of_nonpos hy]; linarith
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]; linarith
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]; linarith



private theorem sorted_sharp_strip_lower (p q l : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q ≤ p)
    (hu : p^2+q^2=1)
    (h1 : Real.sqrt 2 / 2*p + Real.sqrt 6 / 6*q ≤ l/2)
    (h3 : Real.sqrt 6 / 3*p ≤ l/2) : 1 + Real.sqrt 3 / 3 ≤ l := by
  by_contra hl
  have hlt : l < 1 + Real.sqrt 3 / 3 := lt_of_not_ge hl
  let A := Real.sqrt 2 / 2
  let B := Real.sqrt 6 / 6
  let K := (Real.sqrt 6 + Real.sqrt 2) / 4
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have h23 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have h36 : Real.sqrt 6 * Real.sqrt 3 = 3 * Real.sqrt 2 := by
    rw [← h23]; nlinarith [congrArg (fun t : ℝ => Real.sqrt 2 * t) hs3]
  have h26 : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
    rw [← h23]; nlinarith [congrArg (fun t : ℝ => t * Real.sqrt 3) hs2]
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAsq : A^2 = (1:ℝ)/2 := by dsimp [A]; nlinarith only [hs2]
  have hBK : 2*B*K = (1 + Real.sqrt 3 / 3)/2 := by dsimp [B,K]; nlinarith only [hs6,h26]
  have hBW : B * Real.sqrt 3 = A := by dsimp [A,B]; linarith
  have hlin : K * Real.sqrt 3 = K + A := by dsimp [K,A]; nlinarith only [h23,h36]
  have hconst : K^2 - A*K = (1:ℝ)/4 := by dsimp [K,A]; nlinarith only [hs2,hs6]
  have hlo : A ≤ p := by
    have hqpsq := pow_le_pow_left₀ hq hpq 2
    nlinarith
  have hhi : p < K := by
    apply (mul_lt_mul_iff_right₀ (show 0 < 2*B by positivity)).mp
    have h3' : 2*B*p ≤ l/2 := by dsimp [B]; nlinarith only [h3]
    nlinarith only [h3',hlt,hBK]
  have hBWP := congrArg (fun t : ℝ => t*p) hBW
  have hqbound : q < 2*K - Real.sqrt 3*p := by
    apply (mul_lt_mul_iff_right₀ hB).mp
    change A*p+B*q ≤ l/2 at h1
    nlinarith
  have hqsq := mul_self_lt_mul_self hq hqbound
  have hprod := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi.le)
  have hsp := congrArg (fun t : ℝ => t*p^2) hs3
  have hlinp := congrArg (fun t : ℝ => t*p) hlin
  have heq : p^2+(2*K-Real.sqrt 3*p)^2-1 = -4*((p-A)*(K-p)) := by
    nlinarith only [hsp,hlinp,hconst]
  nlinarith

private theorem sharp_unit_strip_lower (p q l : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hu : p^2+q^2=1)
    (h1 : Real.sqrt 2 / 2*p + Real.sqrt 6 / 6*q ≤ l/2)
    (h2 : Real.sqrt 6 / 6*p + Real.sqrt 2 / 2*q ≤ l/2)
    (h3 : Real.sqrt 6 / 3*p ≤ l/2)
    (h4 : Real.sqrt 6 / 3*q ≤ l/2) : 1 + Real.sqrt 3 / 3 ≤ l := by
  rcases le_total q p with h | h
  · exact sorted_sharp_strip_lower p q l hp hq h hu h1 h3
  · apply sorted_sharp_strip_lower q p l hq hp h
    · linarith
    · linarith
    · exact h4

private theorem H_enclosure_sharp (l : ℝ) (hl : l ∈ enclosingSquareLengths (shadow H)) :
    1 + Real.sqrt 3 / 3 ≤ l := by
  obtain ⟨R,hR⟩ := centered_vertex_enclosure H hl
  have hr := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.property
  let a : ℝ := (R : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  let b : ℝ := (R : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  have hd : (R : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = a := hr.1.symm
  have hc : (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -b := by dsimp [b]; linarith [hr.2.1]
  have h00 := hR 0 0
  have h10 := hR 1 0
  have h01 := hR 0 1
  have h11 := hR 1 1
  have h20 := hR 2 0
  have h21 := hR 2 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.col, H] at h00 h10 h01 h11 h20 h21
  simp only [hd,hc] at h01 h11 h21
  change |a * (Real.sqrt 2 / 2) + b * (Real.sqrt 6 / 6)| ≤ l/2 at h00
  change |a * (-Real.sqrt 2 / 2) + b * (Real.sqrt 6 / 6)| ≤ l/2 at h10
  have hab : Real.sqrt 2 / 2 * |a| + Real.sqrt 6 / 6 * |b| ≤ l/2 := by
    have h := abs_sum_from_pair h00 (by convert h10 using 2 <;> ring)
    simpa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (Real.sqrt_nonneg 6), abs_div, mul_comm] using h
  have hba : Real.sqrt 2 / 2 * |b| + Real.sqrt 6 / 6 * |a| ≤ l/2 := by
    have h := abs_sum_from_pair h11 (by convert h01 using 2 <;> ring)
    simpa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (Real.sqrt_nonneg 6), abs_div, mul_comm] using h
  have ha : Real.sqrt 6 / 3 * |a| ≤ l/2 := by
    simpa [a,b,hd,hc,abs_mul,abs_div,abs_neg,abs_of_nonneg (Real.sqrt_nonneg 6), mul_comm] using h21
  have hb : Real.sqrt 6 / 3 * |b| ≤ l/2 := by
    simpa [a,b,abs_mul,abs_div,abs_neg,abs_of_nonneg (Real.sqrt_nonneg 6), mul_comm] using h20
  apply sharp_unit_strip_lower |a| |b| l (abs_nonneg a) (abs_nonneg b)
  · simpa [sq_abs,a,b] using hr.2.2
  · exact hab
  · linarith
  · exact ha
  · exact hb

private theorem H_square_sharp_lower : 1 + Real.sqrt 3 / 3 ≤ squareSide (shadow H) := by
  apply le_csInf ?_ H_enclosure_sharp
  refine ⟨2, ?_⟩
  refine ⟨by norm_num, 1, 0, ?_⟩
  intro p hp i
  simpa using coord_hull_bound H 2 (by intro i j; simpa using projection_entry H H_projection i j) p hp i

private theorem enclosure_of_vertex_bounds (M : Matrix (Fin 2) (Fin 3) ℝ) (l : ℝ)
    (hl : 0 ≤ l) (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (h : ∀ j : Fin 3, ∀ i : Fin 2,
      |Matrix.mulVec (R : Matrix (Fin 2) (Fin 2) ℝ) (WithLp.ofLp ((WithLp.toLp 2 (Matrix.col M j)))) i| ≤ l/2) :
    l ∈ enclosingSquareLengths (shadow M) := by
  let f : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] (Fin 2 → ℝ) :=
    (R : Matrix (Fin 2) (Fin 2) ℝ).mulVecLin.comp (EuclideanSpace.equiv (Fin 2) ℝ).toLinearMap
  have hc : Convex ℝ {p : (EuclideanSpace ℝ (Fin 2)) | ∀ i, |f p i| ≤ l/2} := by
    have hb : Convex ℝ {v : Fin 2 → ℝ | ∀ i, |v i| ≤ l/2} := by
      simpa only [Set.pi, Set.mem_univ, Set.mem_Icc, forall_true_left, ← abs_le] using
        (convex_pi (𝕜 := ℝ) (s := Set.univ)
          (t := fun _ : Fin 2 => Set.Icc (-(l/2)) (l/2))
          (fun _ _ => convex_Icc _ _))
    exact hb.linear_preimage f
  refine ⟨hl,R,0,?_⟩
  intro p hp i
  simp only [sub_zero]
  change |f p i| ≤ l/2
  rw [shadow_hull] at hp
  apply convexHull_min _ hc hp i
  rintro x ⟨j, rfl | rfl⟩ k
  · exact h j k
  · rw [map_neg, Pi.neg_apply, abs_neg]
    exact h j k

private theorem H_square_exact : squareSide (shadow H) = 1 + Real.sqrt 3 / 3 := by
  apply le_antisymm _ H_square_sharp_lower
  let U := Real.sqrt 2
  let T : Matrix (Fin 2) (Fin 2) ℝ := !![U/2,U/2;-U/2,U/2]
  have hU : U^2=2 := Real.sq_sqrt (by norm_num)
  have hT : T ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff]
    dsimp [T]
    constructor
    · rfl
    constructor
    · ring
    · nlinarith
  have h26 : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
    calc
      _ = Real.sqrt 12 := by rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
      _ = _ := by rw [show (12:ℝ)=4*3 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
  apply csInf_le ⟨0,fun _ hx => hx.1⟩
  apply enclosure_of_vertex_bounds H (1+Real.sqrt 3/3) (by positivity) ⟨T,hT⟩
  intro j i
  fin_cases j <;> fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.col, Matrix.transpose_apply, PiLp.toLp_apply] <;>
    norm_num [H,T,U] <;> (try simp [abs_div, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (Real.sqrt_nonneg 6)]) <;> (try simp only [abs_le]) <;> (try constructor) <;>
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
      Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

private theorem H_column_norm (j : Fin 3) : ‖(WithLp.toLp 2 (Matrix.col H j))‖ = Real.sqrt 6 / 3 := by
  have hn : ‖(WithLp.toLp 2 (Matrix.col H j))‖^2 = (2:ℝ)/3 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases j <;> norm_num [Matrix.col,H,Fin.sum_univ_succ] <;>
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
        Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6,
    norm_nonneg ((WithLp.toLp 2 (Matrix.col H j)))]

private theorem H_diameter_exact : diameter (shadow H) = 2 * Real.sqrt 6 / 3 := by
  apply le_antisymm
  · convert diameter_upper H (Real.sqrt 6/3) (by positivity) (fun j => (H_column_norm j).le) using 1 <;> ring
  · have h := diam_column_lower H 0
    rw [H_column_norm] at h
    convert h using 1 <;> ring

private theorem I_diameter_exact : diameter (shadow I) = 4 * Real.sqrt 2 / 3 := by
  apply le_antisymm I_diameter_upper
  have hn : ‖(WithLp.toLp 2 (Matrix.col I 2))‖^2 = (8:ℝ)/9 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Matrix.col,I,Fin.sum_univ_succ]
  have he : ‖(WithLp.toLp 2 (Matrix.col I 2))‖ = 2 * Real.sqrt 2/3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
      norm_nonneg ((WithLp.toLp 2 (Matrix.col I 2)))]
  have h := diam_column_lower I 2
  rw [he] at h
  convert h using 1 <;> ring

private theorem I_enclosure_lower (l : ℝ) (hl : l ∈ enclosingSquareLengths (shadow I)) :
    (4:ℝ)/3 ≤ l := by
  have hl0 : 0 ≤ l := hl.1
  obtain ⟨R,hR⟩ := centered_vertex_enclosure I hl
  have hr := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.property
  let a : ℝ := (R : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  let b : ℝ := (R : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  have hd : (R : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = a := hr.1.symm
  have hc : (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -b := by dsimp [b]; linarith [hr.2.1]
  have h0 := hR 2 0
  have h1 := hR 2 1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.col,I] at h0 h1
  simp only [hd,hc] at h1
  change |a*(2/3)+b*(2/3)| ≤ l/2 at h0
  have h0sq := mul_self_le_mul_self (abs_nonneg _) h0
  have h1sq := mul_self_le_mul_self (abs_nonneg _) h1
  simp only [← sq, sq_abs] at h0sq h1sq
  have hu : a^2+b^2=1 := hr.2.2
  nlinarith

private theorem I_square_exact : squareSide (shadow I) = (4:ℝ)/3 := by
  apply le_antisymm I_square_upper
  apply le_csInf ?_ I_enclosure_lower
  refine ⟨2, ?_⟩
  refine ⟨by norm_num, 1, 0, ?_⟩
  intro p hp i
  simpa using coord_hull_bound I 2 (by intro i j; simpa using projection_entry I I_projection i j) p hp i



private theorem scalar_gap : (9:ℝ)/1250 < octahedralScalar (shadow H) -
    (3 * Real.sqrt 2 / 4) * octahedralScalar (shadow I) := by
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs6 := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hr2 : Real.sqrt 2 < (707107:ℝ)/500000 := by nlinarith [Real.sqrt_nonneg 2]
  have hr3 : (173205:ℝ)/100000 < Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3]
  have hr6 : (2449489:ℝ)/1000000 < Real.sqrt 6 := by nlinarith [Real.sqrt_nonneg 6]
  unfold octahedralScalar
  rw [H_diameter_exact,H_square_exact,I_diameter_exact,I_square_exact]
  nlinarith

private theorem projection_values_bounds : BddBelow projectionValues ∧ BddAbove projectionValues := by
  constructor
  · refine ⟨0, ?_⟩
    rintro r ⟨M,hM,rfl⟩
    exact (projection_scalar_bounds M hM).1
  · refine ⟨9, ?_⟩
    rintro r ⟨M,hM,rfl⟩
    exact (projection_scalar_bounds M hM).2

theorem result : ¬ claim := by
  intro hclaim
  have hH : octahedralScalar (shadow H) ∈ projectionValues := ⟨H,H_projection,rfl⟩
  have hI : octahedralScalar (shadow I) ∈ projectionValues := ⟨I,I_projection,rfl⟩
  have hu := le_csSup projection_values_bounds.2 hH
  have hl := csInf_le projection_values_bounds.1 hI
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 3 * Real.sqrt 2 / 4 by positivity)
  have hpair := le_trans hu (le_trans hclaim hm)
  linarith [scalar_gap]


end D5.S3.Geometry.Polygons.SteiningerYurkevichOctahedronScalarRefutation
