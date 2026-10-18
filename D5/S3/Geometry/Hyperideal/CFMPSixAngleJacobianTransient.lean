/-
UNCOMPILED, transient, zero canonical retention.
Source packet: 94af6e606b01320de8b9f36a9099de3268b57626.
Mathlib pin: db584cd6d46c92f209a44c0f1c829460d327499d.

The quoted import below is the supplied, unchanged transient source file.
Its GramDomainContraction import is provisionally supplied by the unchanged
GramDomainContraction-pending.lean owner. No module is installed by this file.
All auxiliary declarations are consumed locally; no standalone admission is
proposed for expansions, calculus applications, or normalization identities.
-/
import D5.S3.Geometry.Hyperideal.CFMP80NativeDomainExactTransient
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.GramDomainContraction (gram delta Delta)
open CFMP80NativeDomainExactTransient

namespace OriginalSixAngleJacobianTransient

set_option autoImplicit false

abbrev V := Fin 6 → ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev M6 := Matrix (Fin 6) (Fin 6) ℝ

def xOf (l : V) : V := fun q => Real.cosh (l q)
def sigma (l : V) (q : Fin 6) : ℝ := Real.sinh (l q)
def alpha (l : V) : V := fun q => Real.arccos (rawCos (xOf l) q)

/-- Rows are original output angles, columns independent input lengths. -/
def J (l : V) : M6 := fun q f => (fderiv ℝ alpha l (Pi.single f 1)) q

private def G (x : V) : M4 := gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
private def firstVertex : Fin 6 → Fin 4 := ![0, 0, 0, 2, 1, 1]
private def secondVertex : Fin 6 → Fin 4 := ![1, 2, 3, 3, 3, 2]
private def opposite : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

/-- The coefficient with BOTH symmetric off-diagonal variations included.
The second slot is an ORIGINAL ANGLE slot, hence its complementary vertices. -/
private def Q (x : V) (e q : Fin 6) : ℝ :=
  let i := firstVertex e
  let j := secondVertex e
  let k := firstVertex (opposite q)
  let h := secondVertex (opposite q)
  G x i k * G x j h + G x i h * G x j k -
    G x i j * (G x i k * G x i h + G x j k * G x j h)

private def p (x : V) : V :=
  ![x 1*x 4+x 2*x 5+x 0*(x 1*x 2+x 4*x 5),
    x 0*x 3+x 2*x 5+x 1*(x 0*x 2+x 5*x 3),
    x 0*x 3+x 1*x 4+x 2*(x 0*x 1+x 4*x 3),
    x 1*x 4+x 2*x 5+x 3*(x 1*x 5+x 2*x 4),
    x 0*x 3+x 2*x 5+x 4*(x 0*x 5+x 2*x 3),
    x 0*x 3+x 1*x 4+x 5*(x 0*x 4+x 1*x 3)]

def W (x : V) : M6 :=
  !![p x 0/((x 0)^2-1), x 2, x 1, -1, x 5, x 4;
     x 2, p x 1/((x 1)^2-1), x 0, x 5, -1, x 3;
     x 1, x 0, p x 2/((x 2)^2-1), x 4, x 3, -1;
     -1, x 5, x 4, p x 3/((x 3)^2-1), x 2, x 1;
     x 5, -1, x 3, x 2, p x 4/((x 4)^2-1), x 0;
     x 4, x 3, -1, x 1, x 0, p x 5/((x 5)^2-1)]

/-- The stipulated inverse candidate, entrywise S W S / sqrt Delta. -/
def K (l : V) : M6 := fun e q =>
  sigma l e * W (xOf l) e q * sigma l q / Real.sqrt (Delta (xOf l))

private theorem xOf_gt (l : V) (hl : ∀ q, 0 < l q) : ∀ q, 1 < xOf l q :=
  fun q => Real.one_lt_cosh.mpr (hl q).ne'

private theorem sigma_pos (l : V) (hl : ∀ q, 0 < l q) (q : Fin 6) :
    0 < sigma l q := Real.sinh_pos_iff.mpr (hl q)

private theorem sigma_sq (l : V) (q : Fin 6) :
    (sigma l q)^2 = (xOf l q)^2 - 1 := Real.sinh_sq (l q)

private theorem rawCos_eq (x : V) (q : Fin 6) :
    rawCos x q = rawNum x q /
      (Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q)) := by
  simp only [rawCos, rawNum, leftRad, rightRad, cosine, div_div]

/- The four principal cofactors, encoded by existing source radicands.
The order of vertices is zero-based here; it is NOT the order of edge slots. -/
private def A (x : V) : Fin 4 → ℝ :=
  ![leftRad x 4, leftRad x 1, rightRad x 0, leftRad x 0]

private theorem A_pos (x : V) (hx : ∀ q, 1 < x q) (i : Fin 4) : 0 < A x i := by
  fin_cases i
  · exact (source_denominator_facts x hx 4).1
  · exact (source_denominator_facts x hx 1).1
  · exact (source_denominator_facts x hx 0).2.1
  · exact (source_denominator_facts x hx 0).1

private theorem adjugate_diag (x : V) (i : Fin 4) :
    (G x).adjugate i i = -A x i := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;>
    simp [G, gram, A, leftRad, rightRad, frame, rad,
      Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove] <;> ring

private theorem adjugate_complement (x : V) (q : Fin 6) :
    (G x).adjugate (firstVertex (opposite q)) (secondVertex (opposite q)) =
      rawNum x q := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases q <;>
    simp [G, gram, firstVertex, secondVertex, opposite, rawNum, frame, numerator,
      Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove] <;> ring

private theorem frame_rad_product (x : V) (q : Fin 6) :
    A x (firstVertex (opposite q)) * A x (secondVertex (opposite q)) =
      leftRad x q * rightRad x q := by
  fin_cases q <;>
    simp [A, firstVertex, secondVertex, opposite, leftRad, rightRad, frame, rad] <;> ring
  all_goals exact Or.inl True.intro

private theorem inverse_diag (x : V) (i : Fin 4) :
    (G x)⁻¹ i i = A x i / Delta x := by
  have hdet : (G x).det = -Delta x := by simp [G, Delta, delta]
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, adjugate_diag]
  rw [hdet]
  simp [div_eq_mul_inv, mul_comm]

private theorem inverse_complement (x : V) (q : Fin 6) :
    (G x)⁻¹ (firstVertex (opposite q)) (secondVertex (opposite q)) =
      -rawNum x q / Delta x := by
  have hdet : (G x).det = -Delta x := by simp [G, Delta, delta]
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, adjugate_complement]
  rw [hdet]
  simp [div_eq_mul_inv, mul_comm]

private def inverseRoot (x : V) (i : Fin 4) : ℝ := Real.sqrt ((G x)⁻¹ i i)

private def normalizedInverse (B : M4) : M4 := fun i j =>
  B⁻¹ i j / (Real.sqrt (B⁻¹ i i) * Real.sqrt (B⁻¹ j j))

private theorem inverseRoot_product (x : V) (hx : ∀ q, 1 < x q)
    (hΔ : 0 < Delta x) (q : Fin 6) :
    inverseRoot x (firstVertex (opposite q)) *
      inverseRoot x (secondVertex (opposite q)) =
        (Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q)) / Delta x := by
  have hroots : Real.sqrt (A x (firstVertex (opposite q))) *
      Real.sqrt (A x (secondVertex (opposite q))) =
        Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q) := by
    rw [← Real.sqrt_mul (A_pos x hx _).le, frame_rad_product,
      Real.sqrt_mul (source_denominator_facts x hx q).1.le]
  simp only [inverseRoot, inverse_diag]
  rw [Real.sqrt_div (A_pos x hx _).le, Real.sqrt_div (A_pos x hx _).le]
  calc
    _ = (Real.sqrt (A x (firstVertex (opposite q))) *
          Real.sqrt (A x (secondVertex (opposite q)))) / (Real.sqrt (Delta x))^2 := by ring
    _ = _ := by rw [hroots, Real.sq_sqrt hΔ.le]

private theorem normalized_source (x : V) (hx : ∀ q, 1 < x q)
    (hΔ : 0 < Delta x) :
    (∀ i, normalizedInverse (G x) i i = 1) ∧
    (∀ q, normalizedInverse (G x) (firstVertex (opposite q))
      (secondVertex (opposite q)) = -rawCos x q) := by
  constructor
  · intro i
    have hd : 0 < (G x)⁻¹ i i := by rw [inverse_diag]; exact div_pos (A_pos x hx i) hΔ
    simp only [normalizedInverse, ← pow_two, Real.sq_sqrt hd.le, div_self hd.ne']
  · intro q
    have hden := (source_denominator_facts x hx q).2.2.1
    change (G x)⁻¹ (firstVertex (opposite q)) (secondVertex (opposite q)) /
      (inverseRoot x (firstVertex (opposite q)) *
        inverseRoot x (secondVertex (opposite q))) = _
    rw [inverse_complement, inverseRoot_product x hx hΔ q, rawCos_eq]
    field_simp [hΔ.ne', hden.ne']
    <;> ring

/- These are ordinary smooth functions near every exact interior point.
Only the supplied denominator facts and strict-cosine theorem are consumed. -/
private theorem alpha_contDiffAt (l : V) (hl : ∀ q, 0 < l q)
    (hΔ : 0 < Delta (xOf l)) : ContDiffAt ℝ ∞ alpha l := by
  apply contDiffAt_pi.mpr
  intro q
  have hx := xOf_gt l hl
  obtain ⟨hA, hB, hden, hden2⟩ := source_denominator_facts (xOf l) hx q
  have hN : ContDiffAt ℝ ∞ (fun z : V => rawNum (xOf z) q) l := by
    unfold rawNum numerator xOf
    fun_prop
  have hLA : ContDiffAt ℝ ∞ (fun z : V => leftRad (xOf z) q) l := by
    unfold leftRad rad xOf
    fun_prop
  have hRB : ContDiffAt ℝ ∞ (fun z : V => rightRad (xOf z) q) l := by
    unfold rightRad rad xOf
    fun_prop
  have hC : ContDiffAt ℝ ∞ (fun z : V => rawCos (xOf z) q) l := by
    simp_rw [rawCos_eq]
    exact hN.div ((hLA.sqrt hA.ne').mul (hRB.sqrt hB.ne')) hden.ne'
  have hb := (delta_pos_iff_rawCos_strict (xOf l) hx q).mp hΔ
  exact (Real.contDiffAt_arccos hb.1.ne' hb.2.ne).comp l hC

/- Exact product-rule polynomials. These carry an arbitrary six-vector v;
there is no equal-length or one-dimensional restriction. -/
private def dRad (a b c da db dc : ℝ) : ℝ :=
  2*(da*b*c+a*db*c+a*b*dc)+2*a*da+2*b*db+2*c*dc

private def dNum (x v : V) (q : Fin 6) : ℝ :=
  let a := x (frame q 0); let b := x (frame q 1); let c := x (frame q 2)
  let d := x (frame q 3); let e := x (frame q 4); let f := x (frame q 5)
  let da := v (frame q 0); let db := v (frame q 1); let dc := v (frame q 2)
  let dd := v (frame q 3); let de := v (frame q 4); let df := v (frame q 5)
  db*c+b*dc+de*f+e*df+da*b*e+a*db*e+a*b*de+
    da*c*f+a*dc*f+a*c*df-(2*a*da*d+(a^2-1)*dd)

private def dLeft (x v : V) (q : Fin 6) : ℝ :=
  dRad (x (frame q 0)) (x (frame q 1)) (x (frame q 5))
    (v (frame q 0)) (v (frame q 1)) (v (frame q 5))

private def dRight (x v : V) (q : Fin 6) : ℝ :=
  dRad (x (frame q 0)) (x (frame q 2)) (x (frame q 4))
    (v (frame q 0)) (v (frame q 2)) (v (frame q 4))

/-- Numerator after differentiating the TWO normalization square roots. -/
private def E (x v : V) (q : Fin 6) : ℝ :=
  dNum x v q - rawNum x q / 2 *
    (dLeft x v q / leftRad x q + dRight x v q / rightRad x q)

private theorem rad_hasDerivAt {a b c : ℝ → ℝ} {da db dc t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hc : HasDerivAt c dc t) :
    HasDerivAt (fun s => rad (a s) (b s) (c s))
      (dRad (a t) (b t) (c t) da db dc) t := by
  -- Pointwise rules avoid residual applications of products/powers of functions.
  -- `convert!` also reconciles the concrete real instances at default transparency.
  convert! ((((((ha.const_mul 2).fun_mul hb).fun_mul hc).fun_add
    (ha.fun_pow 2)).fun_add (hb.fun_pow 2)).fun_add (hc.fun_pow 2)).sub_const 1
    using 1 <;> dsimp [rad, dRad] <;> ring

private theorem num_hasDerivAt (c : ℝ → V) (v : V) (t : ℝ)
    (hc : ∀ i, HasDerivAt (fun s => c s i) (v i) t) (q : Fin 6) :
    HasDerivAt (fun s => rawNum (c s) q) (dNum (c t) v q) t := by
  have h0 := hc (frame q 0)
  have h1 := hc (frame q 1)
  have h2 := hc (frame q 2)
  have h3 := hc (frame q 3)
  have h4 := hc (frame q 4)
  have h5 := hc (frame q 5)
  convert! (((((h1.fun_mul h2).fun_add (h4.fun_mul h5)).fun_add
    ((h0.fun_mul h1).fun_mul h4)).fun_add ((h0.fun_mul h2).fun_mul h5)).fun_sub
    (((h0.fun_pow 2).sub_const 1).fun_mul h3)) using 1 <;>
    dsimp [rawNum, numerator, dNum] <;> ring

private theorem quotient_normalization (n dn a b da db sa sb : ℝ)
    (ha : sa^2 = a) (hb : sb^2 = b) (hsa : sa ≠ 0) (hsb : sb ≠ 0) :
    (dn*(sa*sb)-n*((da/(2*sa))*sb+sa*(db/(2*sb))))/(sa*sb)^2 =
      (dn-n/2*(da/a+db/b))/(sa*sb) := by
  rw [← ha, ← hb]
  field_simp [hsa, hsb]
  <;> ring

private theorem rawCos_hasDerivAt (c : ℝ → V) (v : V) (t : ℝ)
    (hc : ∀ i, HasDerivAt (fun s => c s i) (v i) t)
    (hx : ∀ i, 1 < c t i) (q : Fin 6) :
    HasDerivAt (fun s => rawCos (c s) q)
      (E (c t) v q / (Real.sqrt (leftRad (c t) q) *
        Real.sqrt (rightRad (c t) q))) t := by
  obtain ⟨hA, hB, hden, hden2⟩ := source_denominator_facts (c t) hx q
  have hLA : HasDerivAt (fun s => leftRad (c s) q) (dLeft (c t) v q) t :=
    rad_hasDerivAt (hc (frame q 0)) (hc (frame q 1)) (hc (frame q 5))
  have hRB : HasDerivAt (fun s => rightRad (c s) q) (dRight (c t) v q) t :=
    rad_hasDerivAt (hc (frame q 0)) (hc (frame q 2)) (hc (frame q 4))
  have hsA := Real.sqrt_pos.mpr hA
  have hsB := Real.sqrt_pos.mpr hB
  have hd := (num_hasDerivAt c v t hc q).fun_div
    ((hLA.sqrt hA.ne').fun_mul (hRB.sqrt hB.ne')) hden.ne'
  have hquot : HasDerivAt
      (fun s => rawNum (c s) q /
        (Real.sqrt (leftRad (c s) q) * Real.sqrt (rightRad (c s) q)))
      (E (c t) v q / (Real.sqrt (leftRad (c t) q) *
        Real.sqrt (rightRad (c t) q))) t := by
    convert! hd using 1
    exact (quotient_normalization _ _ _ _ _ _ _ _
      (Real.sq_sqrt hA.le) (Real.sq_sqrt hB.le) hsA.ne' hsB.ne').symm
  simpa only [rawCos_eq] using! hquot

private theorem sine_denominator (l : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) (q : Fin 6) :
    Real.sqrt (1-(rawCos (xOf l) q)^2) *
      (Real.sqrt (leftRad (xOf l) q) * Real.sqrt (rightRad (xOf l) q)) =
        sigma l q * Real.sqrt (Delta (xOf l)) := by
  have hx := xOf_gt l hl
  obtain ⟨hA, hB, hden, hden2⟩ := source_denominator_facts (xOf l) hx q
  have hb := (delta_pos_iff_rawCos_strict (xOf l) hx q).mp hΔ
  have hsin : 0 < 1-(rawCos (xOf l) q)^2 := by
    have hp := mul_pos (sub_pos.mpr hb.2) (show 0 < 1+rawCos (xOf l) q by linarith)
    nlinarith only [hp]
  have hsquare : (Real.sqrt (1-(rawCos (xOf l) q)^2) *
      (Real.sqrt (leftRad (xOf l) q) * Real.sqrt (rightRad (xOf l) q)))^2 =
        (sigma l q * Real.sqrt (Delta (xOf l)))^2 := by
    calc
      _ = (1-(rawCos (xOf l) q)^2) *
          (Real.sqrt (leftRad (xOf l) q) * Real.sqrt (rightRad (xOf l) q))^2 := by
        rw [mul_pow, Real.sq_sqrt hsin.le]
      _ = leftRad (xOf l) q * rightRad (xOf l) q - (rawNum (xOf l) q)^2 := by
        rw [rawCos_eq]
        calc
          _ = (Real.sqrt (leftRad (xOf l) q) *
              Real.sqrt (rightRad (xOf l) q))^2 - (rawNum (xOf l) q)^2 := by
            field_simp [hden.ne']
            <;> ring
          _ = _ := by rw [hden2]
      _ = ((xOf l q)^2-1) * Delta (xOf l) := frame_discriminant_identity (xOf l) q
      _ = _ := by rw [mul_pow, sigma_sq, Real.sq_sqrt hΔ.le]
  have hleft := mul_pos (Real.sqrt_pos.mpr hsin) hden
  have hright := mul_pos (sigma_pos l hl q) (Real.sqrt_pos.mpr hΔ)
  nlinarith only [hsquare, hleft, hright]

/- This exposes the sign and normalization in the original complementary
entry, rather than substituting a separately assumed cosine map. -/
private theorem source_sine_scale (l : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) (q : Fin 6) :
    normalizedInverse (G (xOf l)) (firstVertex (opposite q))
        (secondVertex (opposite q)) = -Real.cos (alpha l q) ∧
    inverseRoot (xOf l) (firstVertex (opposite q)) *
      inverseRoot (xOf l) (secondVertex (opposite q)) * Real.sin (alpha l q) =
        sigma l q / Real.sqrt (Delta (xOf l)) := by
  have hx := xOf_gt l hl
  have hb := (delta_pos_iff_rawCos_strict (xOf l) hx q).mp hΔ
  constructor
  · rw [(normalized_source (xOf l) hx hΔ).2 q]
    simp only [alpha, Real.cos_arccos hb.1.le hb.2.le]
  · rw [inverseRoot_product (xOf l) hx hΔ q]
    simp only [alpha, Real.sin_arccos]
    have h := sine_denominator l hl hΔ q
    calc
      _ = (Real.sqrt (1-(rawCos (xOf l) q)^2) *
          (Real.sqrt (leftRad (xOf l) q) * Real.sqrt (rightRad (xOf l) q))) /
            Delta (xOf l) := by ring
      _ = sigma l q * Real.sqrt (Delta (xOf l)) / Delta (xOf l) := by rw [h]
      _ = _ := by rw [mul_div_assoc, Real.sqrt_div_self']; ring

private theorem original_directional_derivative (l v : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) (q : Fin 6) :
    (fderiv ℝ alpha l v) q =
      -E (xOf l) (fun i => sigma l i * v i) q /
        (sigma l q * Real.sqrt (Delta (xOf l))) := by
  let line : ℝ → V := fun t i => l i + t*v i
  let c : ℝ → V := fun t => xOf (line t)
  let w : V := fun i => sigma l i * v i
  have hline : HasDerivAt line v 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa [line] using! ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (l i)
  have hc : ∀ i, HasDerivAt (fun t => c t i) (w i) 0 := by
    intro i
    simpa [c, line, xOf, w, sigma] using!
      (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (l i)).cosh
  have hc0 : c 0 = xOf l := by ext i; simp [c, line]
  have hx : ∀ i, 1 < c 0 i := by rw [hc0]; exact xOf_gt l hl
  have hraw := rawCos_hasDerivAt c w 0 hc hx q
  have hb := (delta_pos_iff_rawCos_strict (xOf l) (xOf_gt l hl) q).mp hΔ
  have hangle := (Real.hasDerivAt_arccos
    (show rawCos (c 0) q ≠ -1 by rw [hc0]; exact hb.1.ne')
    (show rawCos (c 0) q ≠ 1 by rw [hc0]; exact hb.2.ne)).comp 0 hraw
  have hf := (alpha_contDiffAt l hl hΔ).differentiableAt (by simp)
  have hfl : HasFDerivAt alpha (fderiv ℝ alpha l) (line 0) := by
    simpa [line] using! hf.hasFDerivAt
  have hactual : HasDerivAt (fun t => alpha (line t) q)
      ((fderiv ℝ alpha l v) q) 0 := by
    simpa only [Function.comp_def] using!
      (hasDerivAt_pi.mp (hfl.comp_hasDerivAt 0 hline)) q
  have hangle' : HasDerivAt (fun t => alpha (line t) q)
      (-(1 / Real.sqrt (1-(rawCos (xOf l) q)^2)) *
        (E (xOf l) w q / (Real.sqrt (leftRad (xOf l) q) *
          Real.sqrt (rightRad (xOf l) q)))) 0 := by
    simpa only [Function.comp_def, hc0] using! hangle
  have heq := hactual.unique hangle'
  change (fderiv ℝ alpha l v) q = _ at heq
  rw [heq]
  calc
    _ = -E (xOf l) w q / (Real.sqrt (1-(rawCos (xOf l) q)^2) *
        (Real.sqrt (leftRad (xOf l) q) * Real.sqrt (rightRad (xOf l) q))) := by ring
    _ = _ := by rw [sine_denominator l hl hΔ q]

/- Canonicalize the denominators to four shared principal radicands before
the six rational identities. In particular, each slot uses the SAME x. -/
private theorem leftRad_table (x : V) (q : Fin 6) :
    leftRad x q = ![A x 3, A x 1, A x 1, A x 1, A x 0, A x 0] q := by
  fin_cases q <;> simp [A, leftRad, rightRad, frame, rad] <;> ring

private theorem rightRad_table (x : V) (q : Fin 6) :
    rightRad x q = ![A x 2, A x 3, A x 2, A x 0, A x 2, A x 3] q := by
  fin_cases q <;> simp [A, leftRad, rightRad, frame, rad] <;> ring

/- BEGIN PRIVATE STRUCTURAL REPLACEMENT HELPERS.
These declarations are UNCOMPILED. All source polynomials remain opaque in
the new contraction argument; the existing cofactor and radicand identities
above supply their values. The only determinant identification below is the
definitional sign Delta x = -(G x).det, with no determinant expansion. -/

private def variationLine (x v : V) (t : ℝ) : V := fun q => x q + t * v q

private theorem variationLine_zero (x v : V) : variationLine x v 0 = x := by
  ext q
  simp [variationLine]

private theorem variationLine_deriv (x v : V) (q : Fin 6) :
    HasDerivAt (fun t => variationLine x v t q) (v q) 0 := by
  simpa [variationLine] using!
    ((hasDerivAt_id (0 : ℝ)).mul_const (v q)).const_add (x q)

private theorem gram_symm (x : V) : (G x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [G, gram]

private theorem gram_diag (x : V) (i : Fin 4) : G x i i = 1 := by
  fin_cases i <;> simp [G, gram]

private def cofactor (x : V) : M4 := -(G x).adjugate

private theorem cofactor_symm (x : V) : (cofactor x).IsSymm :=
  (gram_symm x).adjugate.neg

private theorem cofactor_diag (x : V) (i : Fin 4) : cofactor x i i = A x i := by
  change -((G x).adjugate i i) = A x i
  rw [adjugate_diag, neg_neg]

private theorem cofactor_complement (x : V) (q : Fin 6) :
    cofactor x (firstVertex (opposite q)) (secondVertex (opposite q)) =
      -rawNum x q := by
  change -((G x).adjugate _ _) = -rawNum x q
  rw [adjugate_complement]

private theorem cofactor_table (x : V) :
    cofactor x =
      !![A x 0, -rawNum x 3, -rawNum x 4, -rawNum x 5;
         -rawNum x 3, A x 1, -rawNum x 2, -rawNum x 1;
         -rawNum x 4, -rawNum x 2, A x 2, -rawNum x 0;
         -rawNum x 5, -rawNum x 1, -rawNum x 0, A x 3] := by
  have h01 := cofactor_complement x 3
  have h02 := cofactor_complement x 4
  have h03 := cofactor_complement x 5
  have h12 := cofactor_complement x 2
  have h13 := cofactor_complement x 1
  have h23 := cofactor_complement x 0
  simp [firstVertex, secondVertex, opposite] at h01 h02 h03 h12 h13 h23
  have hs := cofactor_symm x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor_diag, h01, h02, h03, h12, h13, h23,
      hs.apply 0 1, hs.apply 0 2, hs.apply 0 3,
      hs.apply 1 2, hs.apply 1 3, hs.apply 2 3]

private theorem cofactor_products (x : V) :
    G x * cofactor x = Delta x • (1 : M4) ∧
      cofactor x * G x = Delta x • (1 : M4) := by
  -- This is a sign identification, not a determinant calculation.
  have hd : Delta x = -(G x).det := rfl
  constructor
  · rw [cofactor, mul_neg, Matrix.mul_adjugate]
    ext i j
    change -((G x).det * (1 : M4) i j) = Delta x * (1 : M4) i j
    rw [hd]
    ring
  · rw [cofactor, neg_mul, Matrix.adjugate_mul]
    ext i j
    change -((G x).det * (1 : M4) i j) = Delta x * (1 : M4) i j
    rw [hd]
    ring

private def gramTangent (v : V) : M4 :=
  !![0, -v 0, -v 1, -v 2;
     -v 0, 0, -v 5, -v 4;
     -v 1, -v 5, 0, -v 3;
     -v 2, -v 4, -v 3, 0]

private theorem gramTangent_diag (v : V) (i : Fin 4) : gramTangent v i i = 0 := by
  fin_cases i <;> simp [gramTangent]

private theorem gramTangent_edge (v : V) (e : Fin 6) :
    gramTangent v (firstVertex e) (secondVertex e) = -v e := by
  fin_cases e <;> simp [gramTangent, firstVertex, secondVertex]

private theorem gram_directional (x v : V) (i j : Fin 4) :
    HasDerivAt (fun t => G (variationLine x v t) i j) (gramTangent v i j) 0 := by
  have hc := variationLine_deriv x v
  fin_cases i <;> fin_cases j <;> first
    | simpa [G, gram, gramTangent] using! (hasDerivAt_const (0 : ℝ) (1 : ℝ))
    | simpa [G, gram, gramTangent] using! (hc 0).fun_neg
    | simpa [G, gram, gramTangent] using! (hc 1).fun_neg
    | simpa [G, gram, gramTangent] using! (hc 2).fun_neg
    | simpa [G, gram, gramTangent] using! (hc 3).fun_neg
    | simpa [G, gram, gramTangent] using! (hc 4).fun_neg
    | simpa [G, gram, gramTangent] using! (hc 5).fun_neg

private def dA (x v : V) : Fin 4 → ℝ :=
  ![dLeft x v 4, dLeft x v 1, dRight x v 0, dLeft x v 0]

private theorem rad_directional (x v : V) (q : Fin 6) :
    HasDerivAt (fun t => leftRad (variationLine x v t) q) (dLeft x v q) 0 ∧
      HasDerivAt (fun t => rightRad (variationLine x v t) q) (dRight x v q) 0 := by
  have hc := variationLine_deriv x v
  constructor
  · have h : HasDerivAt (fun t => leftRad (variationLine x v t) q)
        (dLeft (variationLine x v 0) v q) 0 :=
      rad_hasDerivAt (hc (frame q 0)) (hc (frame q 1)) (hc (frame q 5))
    simpa only [variationLine_zero] using! h
  · have h : HasDerivAt (fun t => rightRad (variationLine x v t) q)
        (dRight (variationLine x v 0) v q) 0 :=
      rad_hasDerivAt (hc (frame q 0)) (hc (frame q 2)) (hc (frame q 4))
    simpa only [variationLine_zero] using! h

private theorem A_directional (x v : V) (i : Fin 4) :
    HasDerivAt (fun t => A (variationLine x v t) i) (dA x v i) 0 := by
  fin_cases i
  · simpa [A, dA] using! (rad_directional x v 4).1
  · simpa [A, dA] using! (rad_directional x v 1).1
  · simpa [A, dA] using! (rad_directional x v 0).2
  · simpa [A, dA] using! (rad_directional x v 0).1

/- Derivative tables follow from identities of functions on the whole line.
No permutation identity for the expanded dRad polynomial is assumed. -/
private theorem dLeft_table (x v : V) (q : Fin 6) :
    dLeft x v q = ![dA x v 3, dA x v 1, dA x v 1,
      dA x v 1, dA x v 0, dA x v 0] q := by
  have h : HasDerivAt (fun t => leftRad (variationLine x v t) q)
      (![dA x v 3, dA x v 1, dA x v 1,
        dA x v 1, dA x v 0, dA x v 0] q) 0 := by
    simp only [leftRad_table]
    fin_cases q
    · simpa using! A_directional x v 3
    · simpa using! A_directional x v 1
    · simpa using! A_directional x v 1
    · simpa using! A_directional x v 1
    · simpa using! A_directional x v 0
    · simpa using! A_directional x v 0
  exact (rad_directional x v q).1.unique h

private theorem dRight_table (x v : V) (q : Fin 6) :
    dRight x v q = ![dA x v 2, dA x v 3, dA x v 2,
      dA x v 0, dA x v 2, dA x v 3] q := by
  have h : HasDerivAt (fun t => rightRad (variationLine x v t) q)
      (![dA x v 2, dA x v 3, dA x v 2,
        dA x v 0, dA x v 2, dA x v 3] q) 0 := by
    simp only [rightRad_table]
    fin_cases q
    · simpa using! A_directional x v 2
    · simpa using! A_directional x v 3
    · simpa using! A_directional x v 2
    · simpa using! A_directional x v 0
    · simpa using! A_directional x v 2
    · simpa using! A_directional x v 3
  exact (rad_directional x v q).2.unique h

private def cofactorTangent (x v : V) : M4 :=
  !![dA x v 0, -dNum x v 3, -dNum x v 4, -dNum x v 5;
     -dNum x v 3, dA x v 1, -dNum x v 2, -dNum x v 1;
     -dNum x v 4, -dNum x v 2, dA x v 2, -dNum x v 0;
     -dNum x v 5, -dNum x v 1, -dNum x v 0, dA x v 3]

private theorem cofactorTangent_diag (x v : V) (i : Fin 4) :
    cofactorTangent x v i i = dA x v i := by
  fin_cases i <;> simp [cofactorTangent]

private theorem cofactorTangent_complement (x v : V) (q : Fin 6) :
    cofactorTangent x v (firstVertex (opposite q)) (secondVertex (opposite q)) =
      -dNum x v q := by
  fin_cases q <;> simp [cofactorTangent, firstVertex, secondVertex, opposite]

private theorem cofactorTangent_symm (x v : V) : (cofactorTangent x v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cofactorTangent]

private theorem cofactor_directional (x v : V) (i j : Fin 4) :
    HasDerivAt (fun t => cofactor (variationLine x v t) i j)
      (cofactorTangent x v i j) 0 := by
  have hn (q : Fin 6) :
      HasDerivAt (fun t => rawNum (variationLine x v t) q) (dNum x v q) 0 := by
    simpa only [variationLine_zero] using!
      num_hasDerivAt (variationLine x v) v 0 (variationLine_deriv x v) q
  have ha := A_directional x v
  fin_cases i <;> fin_cases j <;> first
    | simpa [cofactor_table, cofactorTangent] using! ha 0
    | simpa [cofactor_table, cofactorTangent] using! ha 1
    | simpa [cofactor_table, cofactorTangent] using! ha 2
    | simpa [cofactor_table, cofactorTangent] using! ha 3
    | simpa [cofactor_table, cofactorTangent] using! (hn 0).fun_neg
    | simpa [cofactor_table, cofactorTangent] using! (hn 1).fun_neg
    | simpa [cofactor_table, cofactorTangent] using! (hn 2).fun_neg
    | simpa [cofactor_table, cofactorTangent] using! (hn 3).fun_neg
    | simpa [cofactor_table, cofactorTangent] using! (hn 4).fun_neg
    | simpa [cofactor_table, cofactorTangent] using! (hn 5).fun_neg

private theorem cofactor_product_tangent (x v : V) :
    ∃ η : ℝ, gramTangent v * cofactor x + G x * cofactorTangent x v =
      η • (1 : M4) := by
  let B := gramTangent v * cofactor x + G x * cofactorTangent x v
  have hp (i j : Fin 4) :
      HasDerivAt (fun t => (G (variationLine x v t) *
        cofactor (variationLine x v t)) i j) (B i j) 0 := by
    have hs := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
      (fun k _ => (gram_directional x v i k).fun_mul (cofactor_directional x v k j))
    change HasDerivAt (fun t => ∑ k : Fin 4,
      G (variationLine x v t) i k * cofactor (variationLine x v t) k j)
      ((∑ k : Fin 4, gramTangent v i k * cofactor x k j) +
        ∑ k : Fin 4, G x i k * cofactorTangent x v k j) 0
    simpa only [variationLine_zero, Finset.sum_add_distrib] using! hs
  have heq (i j : Fin 4) :
      (fun t => (G (variationLine x v t) * cofactor (variationLine x v t)) i j) =
      (fun t => (G (variationLine x v t) * cofactor (variationLine x v t)) 0 0 *
        (1 : M4) i j) := by
    funext t
    rw [(cofactor_products (variationLine x v t)).1]
    simp [Matrix.smul_apply, smul_eq_mul]
  refine ⟨B 0 0, ?_⟩
  ext i j
  change B i j = B 0 0 * (1 : M4) i j
  have hij := hp i j
  rw [heq i j] at hij
  exact hij.unique ((hp 0 0).mul_const ((1 : M4) i j))

/- END SOURCE AND SCALAR-DERIVATIVE BRIDGES. -/

private def unitProjection (H M : M4) : M4 :=
  fun i j => M i j - H i j * (M i i + M j j) / 2

/- These entry lemmas also make the two diagonal corrections explicit.
Their proofs use only matrix multiplication, a diagonal, and finite sums. -/
private theorem diagonal_left_entry (t : Fin 4 → ℝ) (B : M4) (i j : Fin 4) :
    (Matrix.diagonal t * B) i j = t i * B i j := by
  simp [Matrix.mul_apply, Matrix.diagonal, eq_comm]

private theorem diagonal_right_entry (t : Fin 4 → ℝ) (B : M4) (i j : Fin 4) :
    (B * Matrix.diagonal t) i j = B i j * t j := by
  simp [Matrix.mul_apply, Matrix.diagonal]

private theorem scalar_identity_left (d : ℝ) (B : M4) :
    (d • (1 : M4)) * B = d • B := by
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, eq_comm]

private theorem scalar_identity_right (d : ℝ) (B : M4) :
    B * (d • (1 : M4)) = d • B := by
  ext i j
  simp [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, mul_comm]

/- Abstract identity valid at d = 0 as well. The scalar first variation η
and both diagonal correction terms are removed by the same projection. -/
private theorem unit_diagonal_contraction (H C X Y : M4) (d η : ℝ)
    (t : Fin 4 → ℝ) (hH : ∀ i, H i i = 1) (hX : ∀ i, X i i = 0)
    (hHC : H * C = d • (1 : M4)) (hCH : C * H = d • (1 : M4))
    (hfirst : X * C + H * Y = η • (1 : M4)) :
    unitProjection H
      (H * (Y - Matrix.diagonal t * C - C * Matrix.diagonal t) * H) =
      (-d) • X := by
  have hr := congrArg (fun B : M4 => B * H) hfirst
  rw [add_mul, mul_assoc X C H, hCH,
    scalar_identity_right, scalar_identity_left] at hr
  have hY : H * Y * H = η • H - d • X := by
    calc
      _ = (d • X + H * Y * H) - d • X := by abel
      _ = _ := by rw [hr]
  have hTC : H * (Matrix.diagonal t * C) * H =
      d • (H * Matrix.diagonal t) := by
    calc
      _ = (H * Matrix.diagonal t) * (C * H) := by simp only [mul_assoc]
      _ = _ := by rw [hCH, scalar_identity_right]
  have hCT : H * (C * Matrix.diagonal t) * H =
      d • (Matrix.diagonal t * H) := by
    calc
      _ = (H * C) * (Matrix.diagonal t * H) := by simp only [mul_assoc]
      _ = _ := by rw [hHC, scalar_identity_left]
  have hZ : H * (Y - Matrix.diagonal t * C - C * Matrix.diagonal t) * H =
      η • H - d • X - d • (H * Matrix.diagonal t) -
        d • (Matrix.diagonal t * H) := by
    simp only [mul_sub, sub_mul]
    rw [hY, hTC, hCT]
  ext i j
  simp only [unitProjection, hZ, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, diagonal_left_entry, diagonal_right_entry, hH, hX]
  ring

/- Only the abstract 4 by 4 entries are enumerated in the six-pair identity.
The arbitrary output vertices i,j are not expanded into source coordinates. -/
private theorem symmetric_sandwich_entry (H Z : M4) (hH : H.IsSymm)
    (i j : Fin 4) :
    (H * Z * H) i j =
      ∑ k : Fin 4, ∑ h : Fin 4, H i k * H j h * Z k h := by
  simp only [Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro h _
  rw [hH.apply j h]
  ring

private theorem six_pair_projection (H Z : M4) (hH : H.IsSymm)
    (hZ : Z.IsSymm) (hZ0 : ∀ i, Z i i = 0) (i j : Fin 4) :
    unitProjection H (H * Z * H) i j =
      ∑ q : Fin 6,
        (H i (firstVertex (opposite q)) * H j (secondVertex (opposite q)) +
         H i (secondVertex (opposite q)) * H j (firstVertex (opposite q)) -
         H i j * (H i (firstVertex (opposite q)) * H i (secondVertex (opposite q)) +
           H j (firstVertex (opposite q)) * H j (secondVertex (opposite q)))) *
        Z (firstVertex (opposite q)) (secondVertex (opposite q)) := by
  simp [unitProjection, symmetric_sandwich_entry H Z hH, Fin.sum_univ_succ,
    firstVertex, secondVertex, opposite, hZ0,
    hZ.apply 0 1, hZ.apply 0 2, hZ.apply 0 3,
    hZ.apply 1 2, hZ.apply 1 3, hZ.apply 2 3]
  <;> ring

private def normalizedTangent (x v : V) : M4 :=
  let T := Matrix.diagonal (fun i => cofactorTangent x v i i / (2 * A x i))
  cofactorTangent x v - T * cofactor x - cofactor x * T

private theorem normalizedTangent_symm (x v : V) : (normalizedTangent x v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [normalizedTangent, Matrix.sub_apply,
    diagonal_left_entry, diagonal_right_entry]
  rw [(cofactorTangent_symm x v).apply i j, (cofactor_symm x).apply i j]
  ring

private theorem normalizedTangent_diag (x v : V) (hx : ∀ q, 1 < x q)
    (i : Fin 4) : normalizedTangent x v i i = 0 := by
  simp only [normalizedTangent, Matrix.sub_apply,
    diagonal_left_entry, diagonal_right_entry, cofactor_diag]
  field_simp [(A_pos x hx i).ne']
  <;> ring

private theorem normalizedTangent_complement (x v : V) (hx : ∀ q, 1 < x q)
    (q : Fin 6) :
    normalizedTangent x v (firstVertex (opposite q)) (secondVertex (opposite q)) =
      -E x v q := by
  have h0 := (A_pos x hx 0).ne'
  have h1 := (A_pos x hx 1).ne'
  have h2 := (A_pos x hx 2).ne'
  have h3 := (A_pos x hx 3).ne'
  simp only [normalizedTangent, Matrix.sub_apply,
    diagonal_left_entry, diagonal_right_entry,
    cofactor_complement, cofactorTangent_complement, cofactorTangent_diag,
    E, leftRad_table, rightRad_table, dLeft_table, dRight_table]
  fin_cases q <;> simp [firstVertex, secondVertex, opposite]
  all_goals
    field_simp [h0, h1, h2, h3]
    <;> ring

/- END PRIVATE STRUCTURAL REPLACEMENT HELPERS. -/

/- This is the source-specific contraction of the normalized-inverse
differential, expressed without introducing an ambient matrix norm.
It is consumed by K_action below, never a standalone delivery.
No KJ hypothesis, inverse-map hypothesis, or nonsingularity hypothesis is used.
The source text asks Lean to normalize exact identities, not to sample them. -/
set_option maxHeartbeats 8000000 in
private theorem differential_contraction (x v : V) (hx : ∀ q, 1 < x q)
    (e : Fin 6) :
    (∑ q : Fin 6, Q x e q * E x v q) = -Delta x * v e := by
  obtain ⟨η, hfirst⟩ := cofactor_product_tangent x v
  have hp := unit_diagonal_contraction (G x) (cofactor x)
    (gramTangent v) (cofactorTangent x v) (Delta x) η
    (fun i => cofactorTangent x v i i / (2 * A x i))
    (gram_diag x) (gramTangent_diag v)
    (cofactor_products x).1 (cofactor_products x).2 hfirst
  change unitProjection (G x) (G x * normalizedTangent x v * G x) =
    (-Delta x) • gramTangent v at hp
  have hs := six_pair_projection (G x) (normalizedTangent x v) (gram_symm x)
    (normalizedTangent_symm x v) (normalizedTangent_diag x v hx)
    (firstVertex e) (secondVertex e)
  change unitProjection (G x) (G x * normalizedTangent x v * G x)
      (firstVertex e) (secondVertex e) =
    ∑ q : Fin 6, Q x e q *
      normalizedTangent x v (firstVertex (opposite q)) (secondVertex (opposite q)) at hs
  have he := congrArg (fun B : M4 => B (firstVertex e) (secondVertex e)) hp
  simp only [Matrix.smul_apply, smul_eq_mul, gramTangent_edge] at he
  rw [hs] at he
  simp only [normalizedTangent_complement x v hx, mul_neg,
    Finset.sum_neg_distrib] at he
  linarith only [he]

private theorem Q_eq (x : V) (hx : ∀ q, 1 < x q) (e q : Fin 6) :
    Q x e q = ((x e)^2-1) * W x e q := by
  have hu (i : Fin 6) : (x i)^2-1 ≠ 0 := by
    have h := hx i
    have hp : 0 < (x i)^2-1 := by nlinarith only [h, sq_nonneg (x i-1)]
    exact hp.ne'
  fin_cases e <;> fin_cases q <;>
    simp [Q, G, gram, firstVertex, secondVertex, opposite, W, p]
  all_goals field_simp [hu 0, hu 1, hu 2, hu 3, hu 4, hu 5] <;> ring

private theorem K_entry (l : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) (e q : Fin 6) :
    K l e q = sigma l q * Q (xOf l) e q /
      (sigma l e * Real.sqrt (Delta (xOf l))) := by
  rw [Q_eq (xOf l) (xOf_gt l hl), ← sigma_sq]
  unfold K
  field_simp [(sigma_pos l hl e).ne', (Real.sqrt_pos.mpr hΔ).ne']
  <;> ring

private theorem K_action (l v : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) (e : Fin 6) :
    (∑ q : Fin 6, K l e q * (fderiv ℝ alpha l v) q) = v e := by
  let w : V := fun i => sigma l i * v i
  have hs := (sigma_pos l hl e).ne'
  have ht := (Real.sqrt_pos.mpr hΔ).ne'
  have hterm (q : Fin 6) :
      K l e q * (fderiv ℝ alpha l v) q =
        -(Q (xOf l) e q * E (xOf l) w q) /
          (sigma l e * Delta (xOf l)) := by
    rw [K_entry l hl hΔ, original_directional_derivative l v hl hΔ]
    change sigma l q * Q (xOf l) e q /
      (sigma l e * Real.sqrt (Delta (xOf l))) *
        (-E (xOf l) w q / (sigma l q * Real.sqrt (Delta (xOf l)))) = _
    calc
      _ = -(Q (xOf l) e q * E (xOf l) w q) /
          (sigma l e * (Real.sqrt (Delta (xOf l)))^2) := by
        field_simp [hs, ht, (sigma_pos l hl q).ne']
        <;> ring
      _ = _ := by rw [Real.sq_sqrt hΔ.le]
  calc
    _ = ∑ q : Fin 6, -(Q (xOf l) e q * E (xOf l) w q) /
        (sigma l e * Delta (xOf l)) := Finset.sum_congr rfl (fun q _ => hterm q)
    _ = -(∑ q : Fin 6, Q (xOf l) e q * E (xOf l) w q) /
        (sigma l e * Delta (xOf l)) := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ = -(-Delta (xOf l) * w e) / (sigma l e * Delta (xOf l)) := by
      rw [differential_contraction (xOf l) w (xOf_gt l hl) e]
    _ = v e := by
      dsimp [w]
      field_simp [hs, hΔ.ne']
      <;> ring

/-- Proposed original theorem. This is UNCOMPILED source, not a kernel receipt.
There are exactly the original positive-length and determinant assumptions. -/
theorem original_six_angle_jacobian (l : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) :
    ContDiffAt ℝ ∞ alpha l ∧ K l * J l = (1 : M6) := by
  refine ⟨alpha_contDiffAt l hl hΔ, ?_⟩
  ext e f
  change (∑ q : Fin 6, K l e q * (fderiv ℝ alpha l (Pi.single f 1)) q) =
    (1 : M6) e f
  rw [K_action l (Pi.single f 1) hl hΔ e]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

/-- The same candidate also binds the signed cofactor normalization to the
original angles. Kept as a joint source check, with zero canonical retention. -/
theorem original_model_and_jacobian (l : V) (hl : ∀ i, 0 < l i)
    (hΔ : 0 < Delta (xOf l)) :
    G (xOf l) = D5.S3.Geometry.Hyperideal.LengthGramBody.lengthGram l ∧
    (ContDiffAt ℝ ∞ alpha l ∧ K l * J l = (1 : M6)) ∧
    (∀ i, normalizedInverse (G (xOf l)) i i = 1) ∧
    (∀ q, normalizedInverse (G (xOf l)) (firstVertex (opposite q))
        (secondVertex (opposite q)) = -Real.cos (alpha l q) ∧
      inverseRoot (xOf l) (firstVertex (opposite q)) *
        inverseRoot (xOf l) (secondVertex (opposite q)) * Real.sin (alpha l q) =
          sigma l q / Real.sqrt (Delta (xOf l))) :=
  ⟨rfl, original_six_angle_jacobian l hl hΔ,
    (normalized_source (xOf l) (xOf_gt l hl) hΔ).1,
    fun q => source_sine_scale l hl hΔ q⟩

end OriginalSixAngleJacobianTransient

#check OriginalSixAngleJacobianTransient.original_six_angle_jacobian
#print axioms OriginalSixAngleJacobianTransient.original_six_angle_jacobian
#check OriginalSixAngleJacobianTransient.original_model_and_jacobian
#print axioms OriginalSixAngleJacobianTransient.original_model_and_jacobian
