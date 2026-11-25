/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/PositiveGramQuartic
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quartic coefficient signs imply the four-copy spectral support bound. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.PositiveGramSupport
import D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The six polynomial signs imply the signed support bound for the three
embedded binary Gram forms.  Coefficients use the normalization of
`ThreeBlockGram.Kernel`. -/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

/-- The entries of the three symmetric edge blocks and of their row target. -/
structure QuarticData (R : Type*) where
  a : R
  b : R
  c : R
  d : R
  e : R
  f : R
  g : R
  l : R
  k : R
  U : R
  V : R
  W : R

namespace QuarticData

section

variable {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ] [OfNat R 2] [OfNat R 4]
  (s : QuarticData R)

def delta1 : R := s.a * s.b - s.c^2
def delta2 : R := s.d * s.e - s.f^2
def delta3 : R := s.g * s.l - s.k^2

def alpha : R := s.a + s.d - s.U^2
def beta : R := s.b + s.g - s.V^2
def gamma : R := s.e + s.l - s.W^2

def J : R := s.a*s.g*s.e + s.d*s.b*s.l + 2*s.c*s.f*s.k

def KX : R :=
  s.U^2*s.g*s.e + s.V^2*s.d*s.l + s.W^2*s.d*s.g +
  2*s.U*s.V*s.f*s.k - 2*s.U*s.W*s.g*s.f - 2*s.V*s.W*s.d*s.k

def KY : R :=
  s.U^2*s.b*s.l + s.V^2*s.a*s.l + s.W^2*s.a*s.g -
  2*s.U*s.V*s.c*s.l + 2*s.U*s.W*s.c*s.k - 2*s.V*s.W*s.a*s.k

def KZ : R :=
  s.U^2*s.b*s.e + s.V^2*s.a*s.e + s.W^2*s.b*s.d -
  2*s.U*s.V*s.c*s.e - 2*s.U*s.W*s.b*s.f + 2*s.V*s.W*s.c*s.f

def RX : R := s.J + s.d*s.delta3 + s.g*s.delta2 - s.KX
def RY : R := s.J + s.a*s.delta3 + s.l*s.delta1 - s.KY
def RZ : R := s.J + s.b*s.delta2 + s.e*s.delta1 - s.KZ

/-- The three axis discriminants, in the normalization of the sign replay. -/
def axis1 : R := 4*s.a*s.d - s.alpha^2
def axis2 : R := 4*s.b*s.g - s.beta^2
def axis3 : R := 4*s.e*s.l - s.gamma^2

/-- The tested middle coefficients, with the positive factors of
the first and third middle coefficients removed. -/
def mixed1 : R := 2*s.d*s.RY + 2*s.a*s.g*s.delta2 - s.alpha*s.RX
def mixed2 : R :=
  4*(s.d*s.delta3*s.RZ + s.g*s.delta2*s.RY) -
  s.RX^2 - 2*s.alpha*s.beta*s.delta2*s.delta3
def mixed3 : R := 2*s.b*s.d*s.delta3 + 2*s.g*s.RZ - s.beta*s.RX

/-- The doubled kernel gives polynomial expressions for all six signs. -/
def ofGapEntries (q : Fin 12 → R) : QuarticData R where
  a := 4 * q 8 * q 0
  b := 4 * q 8 * q 2
  c := 2 * q 8 * q 9
  d := 4 * q 7 * q 1
  e := 4 * q 7 * q 4
  f := 2 * q 7 * q 10
  g := 4 * q 6 * q 3
  l := 4 * q 6 * q 5
  k := 2 * q 6 * q 11
  U := 2 * q 6
  V := 2 * q 7
  W := 2 * q 8

end

variable (s : QuarticData ℝ)

structure PositiveEdges : Prop where
  a_pos : 0 < s.a
  b_pos : 0 < s.b
  d_pos : 0 < s.d
  e_pos : 0 < s.e
  g_pos : 0 < s.g
  l_pos : 0 < s.l
  delta1_pos : 0 < s.delta1
  delta2_pos : 0 < s.delta2
  delta3_pos : 0 < s.delta3

structure SixSigns : Prop where
  axis1_nonneg : 0 ≤ s.axis1
  axis2_nonneg : 0 ≤ s.axis2
  axis3_nonneg : 0 ≤ s.axis3
  mixed1_nonneg : 0 ≤ s.mixed1
  mixed2_nonneg : 0 ≤ s.mixed2
  mixed3_nonneg : 0 ≤ s.mixed3

theorem sixSigns_of_posScale (q : Fin 12 → ℝ) {c : ℝ} (hc : 0 < c)
    (hs : (ofGapEntries (fun i ↦ c * q i)).SixSigns) : (ofGapEntries q).SixSigns := by
  let S := ofGapEntries (fun i ↦ c * q i)
  let T := ofGapEntries q
  have h1 : S.axis1 = c^4*T.axis1 := by
    simp only [S, T, ofGapEntries, axis1, alpha]
    ring
  have h2 : S.axis2 = c^4*T.axis2 := by
    simp only [S, T, ofGapEntries, axis2, beta]
    ring
  have h3 : S.axis3 = c^4*T.axis3 := by
    simp only [S, T, ofGapEntries, axis3, gamma]
    ring
  have h4 : S.mixed1 = c^8*T.mixed1 := by
    simp only [S, T, ofGapEntries, mixed1, alpha, RX, RY, J, KX, KY, delta1, delta2, delta3]
    ring
  have h5 : S.mixed2 = c^12*T.mixed2 := by
    simp only [S, T, ofGapEntries, mixed2, alpha, beta, RX, RY, RZ,
      J, KX, KY, KZ, delta1, delta2, delta3]
    ring
  have h6 : S.mixed3 = c^8*T.mixed3 := by
    simp only [S, T, ofGapEntries, mixed3, beta, RX, RZ, J, KX, KZ, delta1, delta2, delta3]
    ring
  rcases hs with ⟨ha, hb, hd, he, hf, hg⟩
  change 0 ≤ S.axis1 at ha
  change 0 ≤ S.axis2 at hb
  change 0 ≤ S.axis3 at hd
  change 0 ≤ S.mixed1 at he
  change 0 ≤ S.mixed2 at hf
  change 0 ≤ S.mixed3 at hg
  rw [h1] at ha
  rw [h2] at hb
  rw [h3] at hd
  rw [h4] at he
  rw [h5] at hf
  rw [h6] at hg
  exact ⟨nonneg_of_mul_nonneg_right ha (pow_pos hc _),
    nonneg_of_mul_nonneg_right hb (pow_pos hc _), nonneg_of_mul_nonneg_right hd (pow_pos hc _),
    nonneg_of_mul_nonneg_right he (pow_pos hc _), nonneg_of_mul_nonneg_right hf (pow_pos hc _),
    nonneg_of_mul_nonneg_right hg (pow_pos hc _)⟩

def quartic (X Y Z : ℝ) : ℝ :=
  s.delta3*X*Y*(s.d*X^2 + s.alpha*X*Y + s.a*Y^2) +
  s.delta2*X*Z*(s.g*X^2 + s.beta*X*Z + s.b*Z^2) +
  s.delta1*Y*Z*(s.l*Y^2 + s.gamma*Y*Z + s.e*Z^2) +
  X*Y*Z*(s.RX*X + s.RY*Y + s.RZ*Z)

def Ar (r : ℝ) : ℝ := s.d*s.delta3 + s.g*s.delta2*r
def Br (r : ℝ) : ℝ := s.alpha*s.delta3 + s.RX*r + s.beta*s.delta2*r^2
def Cr (r : ℝ) : ℝ := s.a*s.delta3 + s.RY*r + s.RZ*r^2 + s.b*s.delta2*r^3
def Dr (r : ℝ) : ℝ := s.delta1*r*(s.l + s.gamma*r + s.e*r^2)

def Q (r : ℝ) : ℝ := 4*s.Ar r*s.Cr r - (s.Br r)^2

theorem quartic_at_one (z r : ℝ) :
    s.quartic z 1 r = s.Ar r*z^3 + s.Br r*z^2 + s.Cr r*z + s.Dr r := by
  unfold quartic Ar Br Cr Dr
  ring

/-- The complete degree-four discriminant polynomial, including both
axis terms and all three tested middle coefficients. -/
theorem Q_expansion (r : ℝ) :
    s.Q r = s.delta3^2*s.axis1 +
      2*s.delta3*s.mixed1*r + s.mixed2*r^2 +
      2*s.delta2*s.mixed3*r^3 + s.delta2^2*s.axis2*r^4 := by
  unfold Q Ar Br Cr axis1 axis2 mixed1 mixed2 mixed3
  ring

private theorem axis_capacity_sq (a b u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 ≤ 4*a*b - (a+b-u^2)^2) :
    u^2 ≤ (Real.sqrt a + Real.sqrt b)^2 := by
  have hsq : (a+b-u^2)^2 ≤ (2*Real.sqrt a*Real.sqrt b)^2 := by
    calc
      _ ≤ 4*a*b := by linarith only [hs]
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
        ring
  have habs : |a+b-u^2| ≤ 2*Real.sqrt a*Real.sqrt b :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)
  have hl := (abs_le.mp habs).1
  nlinarith only [hl, Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- The exact square completion, including the third axis capacity term. -/
theorem quartic_square_completion (z r : ℝ)
    (hA : s.Ar r ≠ 0) (he : 0 ≤ s.e) (hl : 0 ≤ s.l) :
    s.quartic z 1 r =
      s.Ar r*z*(z + s.Br r/(2*s.Ar r))^2 + z*s.Q r/(4*s.Ar r) +
      s.delta1*r*(Real.sqrt s.l - Real.sqrt s.e*r)^2 +
      s.delta1*((Real.sqrt s.e + Real.sqrt s.l)^2 - s.W^2)*r^2 := by
  have hcubic :
      s.Ar r*z^3 + s.Br r*z^2 + s.Cr r*z =
        s.Ar r*z*(z + s.Br r/(2*s.Ar r))^2 + z*s.Q r/(4*s.Ar r) := by
    unfold Q
    field_simp [hA] <;> ring
  have hconstant :
      s.Dr r = s.delta1*r*(Real.sqrt s.l - Real.sqrt s.e*r)^2 +
        s.delta1*((Real.sqrt s.e + Real.sqrt s.l)^2 - s.W^2)*r^2 := by
    unfold Dr gamma
    conv_lhs =>
      rw [← Real.sq_sqrt he, ← Real.sq_sqrt hl]
    ring
  rw [quartic_at_one, hcubic, hconstant]
  ring

theorem quartic_nonneg_at_one (hp : s.PositiveEdges) (hs : s.SixSigns)
    {z r : ℝ} (hz : 0 < z) (hr : 0 < r) : 0 ≤ s.quartic z 1 r := by
  have hA : 0 < s.Ar r := by
    unfold Ar
    exact add_pos (mul_pos hp.d_pos hp.delta3_pos)
      (mul_pos (mul_pos hp.g_pos hp.delta2_pos) hr)
  have hQ : 0 ≤ s.Q r := by
    rw [Q_expansion]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (sq_nonneg _) hs.axis1_nonneg)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.delta3_pos.le)
              hs.mixed1_nonneg) hr.le))
          (mul_nonneg hs.mixed2_nonneg (sq_nonneg _)))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.delta2_pos.le)
          hs.mixed3_nonneg) (pow_nonneg hr.le 3)))
      (mul_nonneg (mul_nonneg (sq_nonneg _) hs.axis2_nonneg) (pow_nonneg hr.le 4))
  have hw : 0 ≤ (Real.sqrt s.e + Real.sqrt s.l)^2 - s.W^2 :=
    sub_nonneg.mpr (axis_capacity_sq s.e s.l s.W hp.e_pos.le hp.l_pos.le hs.axis3_nonneg)
  rw [quartic_square_completion s z r hA.ne' hp.e_pos.le hp.l_pos.le]
  exact add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg hA.le hz.le) (sq_nonneg _))
        (div_nonneg (mul_nonneg hz.le hQ) (mul_nonneg (by norm_num) hA.le)))
      (mul_nonneg (mul_nonneg hp.delta1_pos.le hr.le) (sq_nonneg _)))
    (mul_nonneg (mul_nonneg hp.delta1_pos.le hw) (sq_nonneg _))

theorem quartic_homogeneous (X Y Z : ℝ) (hY : Y ≠ 0) :
    s.quartic X Y Z = Y^4 * s.quartic (X/Y) 1 (Z/Y) := by
  unfold quartic
  field_simp [hY] <;> ring

theorem quartic_nonneg (hp : s.PositiveEdges) (hs : s.SixSigns)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    0 ≤ s.quartic X Y Z := by
  rw [quartic_homogeneous s X Y Z hY.ne']
  exact mul_nonneg (pow_nonneg hY.le 4)
    (s.quartic_nonneg_at_one hp hs (div_pos hX hY) (div_pos hZ hY))

/-- The weighted sum of the three embedded edge matrices. -/
def weightedMatrix (X Y Z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![s.a/X + s.d/Y, s.c/X, s.f/Y;
     s.c/X, s.b/X + s.g/Z, s.k/Z;
     s.f/Y, s.k/Z, s.e/Y + s.l/Z]

def target : Fin 3 → ℝ := ![s.U, s.V, s.W]

def q12 (y : Fin 3 → ℝ) : ℝ := s.a*(y 0)^2 + 2*s.c*y 0*y 1 + s.b*(y 1)^2
def q13 (y : Fin 3 → ℝ) : ℝ := s.d*(y 0)^2 + 2*s.f*y 0*y 2 + s.e*(y 2)^2
def q23 (y : Fin 3 → ℝ) : ℝ := s.g*(y 1)^2 + 2*s.k*y 1*y 2 + s.l*(y 2)^2

theorem weighted_quadratic (X Y Z : ℝ) (y : Fin 3 → ℝ) :
    y ⬝ᵥ (s.weightedMatrix X Y Z *ᵥ y) =
      s.q12 y/X + s.q13 y/Y + s.q23 y/Z := by
  simp [weightedMatrix, q12, q13, q23, dotProduct, mulVec, Fin.sum_univ_three,
    div_eq_mul_inv, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> ring

theorem target_dot (y : Fin 3 → ℝ) :
    s.target ⬝ᵥ y = s.U*y 0 + s.V*y 1 + s.W*y 2 := by
  simp [target, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- Clear denominators in the determinant before combining with the
adjugate expression. -/
theorem weighted_det (X Y Z : ℝ) (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) :
    (X*Y*Z)^2 * (s.weightedMatrix X Y Z).det =
      s.delta3*X*Y*(s.d*X + s.a*Y) +
      s.delta2*X*Z*(s.g*X + s.b*Z) +
      s.delta1*Y*Z*(s.l*Y + s.e*Z) + s.J*X*Y*Z := by
  rw [Matrix.det_fin_three]
  simp [weightedMatrix, delta1, delta2, delta3, J,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> field_simp [hX, hY, hZ] <;> ring

theorem weighted_adjugate (X Y Z : ℝ) (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) :
    (X*Y*Z)^2 * (s.target ⬝ᵥ ((s.weightedMatrix X Y Z).adjugate *ᵥ s.target)) =
      s.U^2*s.delta3*X^2*Y^2 + s.V^2*s.delta2*X^2*Z^2 +
      s.W^2*s.delta1*Y^2*Z^2 +
      X*Y*Z*(s.KX*X + s.KY*Y + s.KZ*Z) := by
  rw [Matrix.adjugate_fin_three]
  simp [weightedMatrix, target, dotProduct, mulVec, Fin.sum_univ_three,
    delta1, delta2, delta3, KX, KY, KZ,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  <;> field_simp [hX, hY, hZ] <;> ring

/-- The exact determinant-to-quartic identity. -/
theorem quartic_eq_det (X Y Z : ℝ) (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0) :
    s.quartic X Y Z =
      (X*Y*Z)^2 *
        ((X+Y+Z)*(s.weightedMatrix X Y Z).det -
          s.target ⬝ᵥ ((s.weightedMatrix X Y Z).adjugate *ᵥ s.target)) := by
  symm
  calc
    _ = (X+Y+Z)*((X*Y*Z)^2*(s.weightedMatrix X Y Z).det) -
          (X*Y*Z)^2*(s.target ⬝ᵥ ((s.weightedMatrix X Y Z).adjugate *ᵥ s.target)) := by ring
    _ = _ := by
      rw [s.weighted_det X Y Z hX hY hZ, s.weighted_adjugate X Y Z hX hY hZ]
      unfold quartic alpha beta gamma RX RY RZ
      ring

private theorem binary_pos (a b c x y : ℝ) (ha : 0 < a)
    (hD : 0 < a*b-c^2) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < a*x^2 + 2*c*x*y + b*y^2 := by
  have hid : a*(a*x^2 + 2*c*x*y + b*y^2) =
      (a*x+c*y)^2 + (a*b-c^2)*y^2 := by ring
  apply (mul_pos_iff_of_pos_left ha).mp
  rw [hid]
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := hxy.resolve_right (by simp)
    simpa using sq_pos_of_ne_zero (mul_ne_zero ha.ne' hx)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hD (sq_pos_of_ne_zero hy))

private theorem binary_nonneg (a b c x y : ℝ) (ha : 0 < a)
    (hD : 0 < a*b-c^2) :
    0 ≤ a*x^2 + 2*c*x*y + b*y^2 := by
  by_cases hxy : x ≠ 0 ∨ y ≠ 0
  · exact (binary_pos a b c x y ha hD hxy).le
  · push_neg at hxy
    rcases hxy with ⟨rfl, rfl⟩
    simp

theorem q12_nonneg (hp : s.PositiveEdges) (y : Fin 3 → ℝ) : 0 ≤ s.q12 y :=
  binary_nonneg _ _ _ _ _ hp.a_pos hp.delta1_pos

theorem q13_nonneg (hp : s.PositiveEdges) (y : Fin 3 → ℝ) : 0 ≤ s.q13 y :=
  binary_nonneg _ _ _ _ _ hp.d_pos hp.delta2_pos

theorem q23_nonneg (hp : s.PositiveEdges) (y : Fin 3 → ℝ) : 0 ≤ s.q23 y :=
  binary_nonneg _ _ _ _ _ hp.g_pos hp.delta3_pos

theorem weighted_posDef (hp : s.PositiveEdges) {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    (s.weightedMatrix X Y Z).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro y hy
    rw [star_trivial, s.weighted_quadratic]
    have h12 := div_nonneg (s.q12_nonneg hp y) hX.le
    have h13 := div_nonneg (s.q13_nonneg hp y) hY.le
    have h23 := div_nonneg (s.q23_nonneg hp y) hZ.le
    by_cases hxy : y 0 ≠ 0 ∨ y 1 ≠ 0
    · have hq : 0 < s.q12 y := binary_pos _ _ _ _ _ hp.a_pos hp.delta1_pos hxy
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (div_pos hq hX) h13) h23
    · push_neg at hxy
      have hy2 : y 2 ≠ 0 := by
        intro hz
        apply hy
        funext i
        fin_cases i
        · exact hxy.1
        · exact hxy.2
        · exact hz
      have hq : 0 < s.q13 y := binary_pos _ _ _ _ _ hp.d_pos hp.delta2_pos (Or.inr hy2)
      exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos h12 (div_pos hq hY)) h23

/-- The rank-one bound follows from matrix Cauchy–Schwarz using the adjugate
vector. The determinant condition is the exact cleared-denominator test. -/
private theorem dot_sq_le_of_adjugate {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M.PosDef) (H y : Fin 3 → ℝ) (S : ℝ)
    (hdet : H ⬝ᵥ (M.adjugate *ᵥ H) ≤ S*M.det) :
    (H ⬝ᵥ y)^2 ≤ S*(y ⬝ᵥ (M *ᵥ y)) := by
  have hd : 0 < M.det := hM.det_pos
  let v : Fin 3 → ℝ := M.adjugate *ᵥ H
  have hv : M *ᵥ v = M.det • H := by
    unfold v
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hq : 0 ≤ y ⬝ᵥ (M *ᵥ y) := by
    simpa only [star_trivial] using hM.posSemidef.dotProduct_mulVec_nonneg y
  have hcs := hM.star_dotProduct_mulVec_mul_le y v
  simp only [star_trivial, hv, dotProduct_smul, smul_eq_mul] at hcs
  have hvH : v ⬝ᵥ H ≤ S*M.det := by
    rw [dotProduct_comm]
    exact hdet
  have hbound : M.det*(v ⬝ᵥ H) ≤ M.det*(S*M.det) :=
    mul_le_mul_of_nonneg_left hvH hd.le
  have hcs' : (M.det)^2*(H ⬝ᵥ y)^2 ≤
      (M.det)^2*(S*(y ⬝ᵥ (M *ᵥ y))) := by
    calc
      _ = (M.det*(y ⬝ᵥ H))*(M.det*(y ⬝ᵥ H)) := by rw [dotProduct_comm H y]; ring
      _ ≤ (y ⬝ᵥ (M *ᵥ y))*(M.det*(v ⬝ᵥ H)) := hcs
      _ ≤ (y ⬝ᵥ (M *ᵥ y))*(M.det*(S*M.det)) :=
        mul_le_mul_of_nonneg_left hbound hq
      _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_left (pow_pos hd 2)).mp hcs'

theorem weighted_support_sq (hp : s.PositiveEdges) (hs : s.SixSigns)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (y : Fin 3 → ℝ) :
    (s.target ⬝ᵥ y)^2 ≤ (X+Y+Z)*(s.q12 y/X + s.q13 y/Y + s.q23 y/Z) := by
  let M := s.weightedMatrix X Y Z
  have hP := s.quartic_nonneg hp hs hX hY hZ
  rw [s.quartic_eq_det X Y Z hX.ne' hY.ne' hZ.ne'] at hP
  have hD : s.target ⬝ᵥ (M.adjugate *ᵥ s.target) ≤ (X+Y+Z)*M.det := by
    apply sub_nonneg.mp
    exact nonneg_of_mul_nonneg_right hP (pow_pos (mul_pos (mul_pos hX hY) hZ) 2)
  rw [← s.weighted_quadratic X Y Z y]
  exact dot_sq_le_of_adjugate (s.weighted_posDef hp hX hY hZ) s.target y _ hD

private theorem div_sqrt_add_le (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
    q/(Real.sqrt q+t) ≤ Real.sqrt q := by
  apply (div_le_iff₀ (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ht)).2
  calc
    q = Real.sqrt q * Real.sqrt q := (Real.mul_self_sqrt hq).symm
    _ ≤ Real.sqrt q * (Real.sqrt q+t) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht.le) (Real.sqrt_nonneg _)

/-- All signed directions, including every zero edge form, are covered by
strictly positive weights. Under a hypothetical strict support violation,
add one third of the gap to each square root. -/
theorem support_of_six_signs (hp : s.PositiveEdges) (hs : s.SixSigns)
    (y : Fin 3 → ℝ) :
    s.target ⬝ᵥ y ≤ Real.sqrt (s.q12 y) + Real.sqrt (s.q13 y) + Real.sqrt (s.q23 y) := by
  let L := s.target ⬝ᵥ y
  let x := Real.sqrt (s.q12 y)
  let z := Real.sqrt (s.q13 y)
  let w := Real.sqrt (s.q23 y)
  let R := x+z+w
  change L ≤ R
  by_contra! hlt
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hR : 0 ≤ R := add_nonneg (add_nonneg hx hz) hw
  have hL : 0 < L := hR.trans_lt hlt
  let t := (L-R)/3
  have ht : 0 < t := div_pos (sub_pos.mpr hlt) (by norm_num)
  have hX : 0 < x+t := add_pos_of_nonneg_of_pos hx ht
  have hY : 0 < z+t := add_pos_of_nonneg_of_pos hz ht
  have hZ : 0 < w+t := add_pos_of_nonneg_of_pos hw ht
  have hsum : (x+t)+(z+t)+(w+t) = L := by
    dsimp only [t, R]
    ring
  have hq : s.q12 y/(x+t) + s.q13 y/(z+t) + s.q23 y/(w+t) ≤ R :=
    add_le_add (add_le_add
      (div_sqrt_add_le _ t (s.q12_nonneg hp y) ht)
      (div_sqrt_add_le _ t (s.q13_nonneg hp y) ht))
      (div_sqrt_add_le _ t (s.q23_nonneg hp y) ht)
  have hsq := s.weighted_support_sq hp hs hX hY hZ y
  change L^2 ≤ ((x+t)+(z+t)+(w+t)) *
    (s.q12 y/(x+t) + s.q13 y/(z+t) + s.q23 y/(w+t)) at hsq
  rw [hsum] at hsq
  have hle := hsq.trans (mul_le_mul_of_nonneg_left hq hL.le)
  have hstrict := mul_lt_mul_of_pos_left hlt hL
  exact (not_lt_of_ge hle) (by simpa only [pow_two] using hstrict)

end QuarticData

/-- The nine edge entries and three target entries in the shared kernel
normalization. Scaling the kernel by two gives exactly the integer
coefficients (4hf on diagonals, 2hg off diagonal, 2h for the target). -/
def kernelQuarticData (D : Kernel) : QuarticData ℝ where
  a := h D 2 0 1 * f D 0 1
  b := h D 2 0 1 * f D 1 0
  c := h D 2 0 1 * g D 0 1 / 2
  d := h D 1 0 2 * f D 0 2
  e := h D 1 0 2 * f D 2 0
  f := h D 1 0 2 * g D 0 2 / 2
  g := h D 0 1 2 * f D 1 2
  l := h D 0 1 2 * f D 2 1
  k := h D 0 1 2 * g D 1 2 / 2
  U := h D 0 1 2
  V := h D 1 0 2
  W := h D 2 0 1

theorem quarticData_of_gapEntries (D : Kernel) :
    QuarticData.ofGapEntries ![f D 0 1, f D 0 2, f D 1 0, f D 1 2, f D 2 0, f D 2 1,
      h D 0 1 2, h D 1 0 2, h D 2 0 1, g D 0 1, g D 0 2, g D 1 2] =
        kernelQuarticData (fun i j k l ↦ 2 * D i j k l) := by
  unfold QuarticData.ofGapEntries kernelQuarticData
  simp [f, g, h] <;> congr 1 <;> ring <;> simp

private theorem edge_entries_pos (D : Kernel) (i j k : Fin 3)
    (hp : EdgePivots D i j k) (hc : 0 < h D k i j) :
    0 < h D k i j * f D i j ∧
      0 < h D k i j * f D j i ∧
      0 < (h D k i j * f D i j) * (h D k i j * f D j i) -
        (h D k i j * g D i j / 2)^2 := by
  have ha := hp.first_pos
  have hbnd := sub_pos.mp hp.second_pos
  have hb : 0 < f D j i :=
    lt_of_le_of_lt (div_nonneg (sq_nonneg _) ha.le) hbnd
  have hd : 0 < f D i j * f D j i - (g D i j / 2)^2 := by
    apply sub_pos.mpr
    have hlt := (div_lt_iff₀ ha).mp hbnd
    rw [mul_comm (f D i j) (f D j i)]
    exact hlt
  refine ⟨mul_pos hc ha, mul_pos hc hb, ?_⟩
  have heq :
      (h D k i j * f D i j) * (h D k i j * f D j i) -
        (h D k i j * g D i j / 2)^2 =
        (h D k i j)^2 * (f D i j * f D j i - (g D i j / 2)^2) := by ring
  rw [heq]
  exact mul_pos (pow_pos hc 2) hd

/-- The strict complementary coefficients and the existing edge pivots supply
all positivity hypotheses of the quartic argument. -/
theorem kernelQuarticData_positiveEdges_of_pivots (D : Kernel)
    (hp01 : EdgePivots D 0 1 2) (hp02 : EdgePivots D 0 2 1)
    (hp12 : EdgePivots D 1 2 0) (h0 : 0 < h D 0 1 2)
    (h1 : 0 < h D 1 0 2) (h2 : 0 < h D 2 0 1) :
    (kernelQuarticData D).PositiveEdges := by
  obtain ⟨ha, hb, hd1⟩ := edge_entries_pos D 0 1 2 hp01 h2
  obtain ⟨hd, he, hd2⟩ := edge_entries_pos D 0 2 1 hp02 h1
  obtain ⟨hg, hl, hd3⟩ := edge_entries_pos D 1 2 0 hp12 h0
  exact ⟨ha, hb, hd, he, hg, hl, hd1, hd2, hd3⟩

/-- The three axis discriminants and three mixed signs imply the exact
`SharpSupport` consumed by `allocation_of_sharpSupport`. -/
theorem sharpSupport_of_quartic_signs (D : Kernel)
    (hp : (kernelQuarticData D).PositiveEdges) (hs : (kernelQuarticData D).SixSigns) :
    SharpSupport D := by
  intro y
  let s := kernelQuarticData D
  have h12 : s.q12 y = edgeQuadratic D 0 1 2 y := by
    simp only [s, kernelQuarticData, QuarticData.q12, edgeQuadratic]
    ring
  have h13 : s.q13 y = edgeQuadratic D 0 2 1 y := by
    simp only [s, kernelQuarticData, QuarticData.q13, edgeQuadratic]
    ring
  have h23 : s.q23 y = edgeQuadratic D 1 2 0 y := by
    simp only [s, kernelQuarticData, QuarticData.q23, edgeQuadratic]
    ring
  have hsup := s.support_of_six_signs hp hs y
  rw [s.target_dot, h12, h13, h23] at hsup
  exact hsup

/-- The integer sign replay uses twice the original kernel's entries. -/
theorem sharpSupport_of_doubled_quartic_signs (D : Kernel)
    (hp : (kernelQuarticData (fun i j k l ↦ 2 * D i j k l)).PositiveEdges)
    (hs : (kernelQuarticData (fun i j k l ↦ 2 * D i j k l)).SixSigns) :
    SharpSupport D := by
  apply sharpSupport_of_pos_scale D (by norm_num : (0 : ℝ) < 2)
  exact sharpSupport_of_quartic_signs _ hp hs

/-- The integer replay leaves the three axis tests unscaled, and uses the
doubled kernel for the mixed tests. Their precise scaling is 16. -/
theorem sharpSupport_of_replayed_signs (D : Kernel)
    (hp : (kernelQuarticData (fun i j k l ↦ 2 * D i j k l)).PositiveEdges)
    (ha1 : 0 ≤ (kernelQuarticData D).axis1)
    (ha2 : 0 ≤ (kernelQuarticData D).axis2)
    (ha3 : 0 ≤ (kernelQuarticData D).axis3)
    (hm1 : 0 ≤ (kernelQuarticData (fun i j k l ↦ 2 * D i j k l)).mixed1)
    (hm2 : 0 ≤ (kernelQuarticData (fun i j k l ↦ 2 * D i j k l)).mixed2)
    (hm3 : 0 ≤ (kernelQuarticData (fun i j k l ↦ 2 * D i j k l)).mixed3) :
    SharpSupport D := by
  let s := kernelQuarticData D
  let t := kernelQuarticData (fun i j k l ↦ 2 * D i j k l)
  have heq1 : t.axis1 = 16*s.axis1 := by
    simp only [t, s, QuarticData.axis1, QuarticData.alpha, kernelQuarticData, f, h]
    ring
  have heq2 : t.axis2 = 16*s.axis2 := by
    simp only [t, s, QuarticData.axis2, QuarticData.beta, kernelQuarticData, f, h]
    ring
  have heq3 : t.axis3 = 16*s.axis3 := by
    simp only [t, s, QuarticData.axis3, QuarticData.gamma, kernelQuarticData, f, h]
    ring
  apply sharpSupport_of_doubled_quartic_signs D hp
  refine ⟨?_, ?_, ?_, hm1, hm2, hm3⟩
  · change 0 ≤ t.axis1
    rw [heq1]
    exact mul_nonneg (by norm_num) ha1
  · change 0 ≤ t.axis2
    rw [heq2]
    exact mul_nonneg (by norm_num) ha2
  · change 0 ≤ t.axis3
    rw [heq3]
    exact mul_nonneg (by norm_num) ha3

private theorem twice_edgePivots (D : Kernel) (i j k : Fin 3) (hp : EdgePivots D i j k) :
    EdgePivots (fun l m n o ↦ 2 * D l m n o) i j k := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 < 2 * f D i j
    exact mul_pos (by norm_num) hp.first_pos
  · change 0 < 2 * f D j i - (2 * g D i j / 2)^2 / (2 * f D i j)
    convert mul_pos (by norm_num : (0 : ℝ) < 2) hp.second_pos using 1
    field_simp [hp.first_pos.ne'] <;> ring
  · change 0 ≤ 2 * h D k i j
    exact mul_nonneg (by norm_num) hp.last_nonneg

/-- The six signs certify the Gram support bound on the ordered positive spectrum. -/
theorem sharpSupport_of_positive_spectrum_signs
    (p : ℕ) (hp : 0 < p) (s : Fin 3 → ℝ)
    (hs : ∀ i, 0 < s i) (horder : StrictMono s)
    (hsigns : (kernelQuarticData (fun i j k l ↦ 2 * spectralDefect p s i j k l)).SixSigns) :
    SharpSupport (spectralDefect p s) := by
  let D := spectralDefect p s
  let N : Kernel := fun i j k l ↦ 2 * D i j k l
  have hnonneg (i : Fin 3) : 0 ≤ s i := (hs i).le
  have hb (i j : Fin 3) (hij : i < j) : (g D i j)^2 < 2 * f D i j * f D j i :=
    spectralDefect_binary_conditioning p hp s i j (hs i) (hs j) (ne_of_lt (horder hij))
  have hedge (i j k : Fin 3) (hij : i < j) : EdgePivots N i j k :=
    twice_edgePivots D i j k (spectral_edgePivots p s hnonneg i j k (hb i j hij))
  have hcomp (i j k : Fin 3) (hij : i ≠ j) : 0 < h N i j k := by
    change 0 < 2 * FourCopyGap.gapDefect p (s i) (s i) (s j) (s k)
    exact mul_pos (by norm_num)
      (gapDefect_pos_of_first_ne_third p hp (hnonneg i) (hnonneg i) (hnonneg j)
        (hnonneg k) (horder.injective.ne hij))
  have hN := kernelQuarticData_positiveEdges_of_pivots N
    (hedge 0 1 2 (by decide)) (hedge 0 2 1 (by decide)) (hedge 1 2 0 (by decide))
    (hcomp 0 1 2 (by decide)) (hcomp 1 0 2 (by decide)) (hcomp 2 0 1 (by decide))
  exact sharpSupport_of_doubled_quartic_signs D hN hsigns

#print axioms QuarticData.quartic_eq_det
#print axioms QuarticData.quartic_square_completion
#print axioms sharpSupport_of_quartic_signs
#print axioms sharpSupport_of_doubled_quartic_signs
#print axioms sharpSupport_of_replayed_signs

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
