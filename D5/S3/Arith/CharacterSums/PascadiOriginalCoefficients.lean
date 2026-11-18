/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalCoefficients
   mirror-E: none(waiver:open-original-lattice-reduction)
   anchors: []
   utility: none
   digest: Literal original endpoint coordinates realize the prime-cube polynomial pencil. -/

import D5.S3.Arith.CharacterSums.PascadiMinusRows
import D5.S3.Arith.CharacterSums.PascadiPrimeCubeSingularCover

/-! # Actual coefficients of the original six-return pencil -/

open Polynomial
open scoped Matrix

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

abbrev Coordinate := ℤ × ℤ
abbrev Endpoint := Coordinate × Coordinate

/-- Physical integer coordinates in a chosen lattice basis; no independent residue lift. -/
def physical (R V z : Coordinate) : Coordinate :=
  (z.1 * R.1 + z.2 * V.1, z.1 * R.2 + z.2 * V.2)

/-- The original six letters reconstructed from two actual endpoints and the anchor. -/
def originalRows (R V q : Coordinate) (e : Endpoint) : ReturnRows :=
  (![ (physical R V e.1).1, (physical R V e.2).1, -(physical R V q).1 ],
   ![ (physical R V e.1).2, (physical R V e.2).2, -(physical R V q).2 ])

/-- Actual original word condition on reconstructed physical integer endpoints. -/
def WordSolution (c : ℕ) (a₁ a₂ : ZMod c) (R V q : Coordinate) (e : Endpoint) : Prop :=
  sixReturnWord a₁ a₂
    ((originalRows R V q e).1 0) ((originalRows R V q e).2 2)
    ((originalRows R V q e).1 1) ((originalRows R V q e).2 0)
    ((originalRows R V q e).1 2) ((originalRows R V q e).2 1) = scalarReturn (-1)

/-- Literal coefficient functions, including the anchor subtraction in L. -/
def coeffL (q : Coordinate) (e : Endpoint) : ℤ := e.1.1 + e.2.1 - q.1
def coeffM (q : Coordinate) (e : Endpoint) : ℤ := e.1.2 + e.2.2 - q.2
def coeffQ (e : Endpoint) : ℤ := e.1.1 * e.2.1
def coeffR (e : Endpoint) : ℤ := e.1.1 * e.2.2 + e.1.2 * e.2.1
def coeffS (e : Endpoint) : ℤ := e.1.2 * e.2.2

/-- The actual linear and quadratic endpoint polynomials of the paper. -/
def endpointL (q : Coordinate) (e : Endpoint) : ℤ[X] :=
  PrimeCube.linear (coeffL q e) (coeffM q e)
def endpointQ (e : Endpoint) : ℤ[X] :=
  PrimeCube.quadratic (coeffQ e) (coeffR e) (coeffS e)
def pencil (q : Coordinate) (base e : Endpoint) : ℤ[X] :=
  endpointL q base * endpointQ e - endpointL q e * endpointQ base

/-- Exact coefficients of the actual original pencil; the archived expansion is reused. -/
theorem pencil_expansion (q : Coordinate) (base e : Endpoint) :
    pencil q base e =
      C (coeffL q base * coeffQ e - coeffL q e * coeffQ base) +
      C (coeffL q base * coeffR e + coeffM q base * coeffQ e -
        coeffL q e * coeffR base - coeffM q e * coeffQ base) * X +
      C (coeffL q base * coeffS e + coeffM q base * coeffR e -
        coeffL q e * coeffS base - coeffM q e * coeffR base) * X^2 +
      C (coeffM q base * coeffS e - coeffM q e * coeffS base) * X^3 := by
  exact PrimeCube.pair_coefficients
    ![coeffL q base,coeffL q e,0] ![coeffM q base,coeffM q e,0]
    ![coeffQ base,coeffQ e,0] ![coeffR base,coeffR e,0] ![coeffS base,coeffS e,0] 1

/-- Evaluation of a physical coordinate uses the actual ratio of basis first entries. -/
private theorem physical_eval {R : Type*} [CommRing R] (r : Rˣ) (v : R) (z : Coordinate) :
    (z.1 : R) * (r : R) + (z.2 : R) * v =
      (r : R) * ((z.1 : R) + (z.2 : R) * (v * (↑r⁻¹ : R))) := by
  have hr : (r : R) * (↑r⁻¹ : R) = 1 := by simp
  calc
    _ = (z.1 : R) * (r : R) + (z.2 : R) * v * ((r : R) * (↑r⁻¹ : R)) := by rw [hr]; ring
    _ = _ := by ring

/-- The first original word equation realizes αL(β)+Q(β)=0. Only g,t,r are inverted;
no endpoint or polynomial nonzero assumption is used. -/
theorem original_endpoint_identity {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (e : Endpoint)
    (hr : IsUnit (R.1 : ZMod c)) (ht : IsUnit (-(physical R V q).2 : ZMod c))
    (hword : WordSolution c a₁ a₂ R V q e) :
    let β := (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)
    let α := -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c)
    α * (endpointL q e).eval₂ (Int.castRingHom _) β +
      (endpointQ e).eval₂ (Int.castRingHom _) β = 0 := by
  dsimp only
  let r := hr.unit
  let t := ht.unit
  let g := ha₁.unit * ha₂.unit
  let β : ZMod c := (V.1 : ZMod c) * (↑r⁻¹ : ZMod c)
  let α : ZMod c := -(↑((g * t * r)⁻¹) : ZMod c)
  let x : ZMod c := (e.1.1 : ZMod c) + (e.1.2 : ZMod c) * β
  let y : ZMod c := (e.2.1 : ZMod c) + (e.2.2 : ZMod c) * β
  let z : ZMod c := (q.1 : ZMod c) + (q.2 : ZMod c) * β
  have hphys (u : Coordinate) : ((physical R V u).1 : ZMod c) =
      (r : ZMod c) * ((u.1 : ZMod c) + (u.2 : ZMod c) * β) := by
    simpa [physical,β,r,hr.unit_spec] using physical_eval hr.unit (V.1 : ZMod c) u
  have hfour := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp hword
  have hfirst : (r : ZMod c) * (x+y-z) =
      (g : ZMod c) * (t : ZMod c) * (r : ZMod c)^2 * x*y := by
    have h := hfour.1
    simp only [originalRows, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue, Int.cast_neg, hphys] at h
    convert h using 1 <;>
      simp only [x,y,z,g,t,Units.val_mul,ha₁.unit_spec,ha₂.unit_spec,ht.unit_spec] <;> ring
  have hnorm : x+y-z = (g*t*r : (ZMod c)ˣ) * (x*y) := by
    apply r.isUnit.mul_left_cancel
    convert hfirst using 1; simp only [Units.val_mul]; ring
  have halpha : α * ((g*t*r : (ZMod c)ˣ) : ZMod c) = -1 := by
    change -(↑((g*t*r)⁻¹) : ZMod c) * ↑(g*t*r) = -1
    rw [neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hzero : α*(x+y-z)+x*y = 0 := by
    rw [hnorm,← mul_assoc,halpha]
    ring
  have heval (n : ℤ) (β : ZMod c) :
      (n : ℤ[X]).eval₂ (Int.castRingHom _) β = (n : ZMod c) :=
    map_intCast (Polynomial.eval₂RingHom (Int.castRingHom (ZMod c)) β) n
  convert hzero using 1;
    simp [endpointL,endpointQ,PrimeCube.linear,PrimeCube.quadratic,
      coeffL,coeffM,coeffQ,coeffR,coeffS,α,g,t,r,x,y,z,β,
      heval]; ring

/-- Actual word solutions at two endpoints give the actual pencil root modulo c. -/
theorem original_pencil_root {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base e : Endpoint)
    (hr : IsUnit (R.1 : ZMod c)) (ht : IsUnit (-(physical R V q).2 : ZMod c))
    (hb : WordSolution c a₁ a₂ R V q base)
    (he : WordSolution c a₁ a₂ R V q e) :
    (pencil q base e).eval₂ (Int.castRingHom (ZMod c))
      ((V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)) = 0 := by
  have h₁ := original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q base hr ht hb
  have h₂ := original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q e hr ht he
  dsimp only at h₁ h₂
  simp only [pencil,eval₂_sub,eval₂_mul]
  linear_combination (endpointL q base).eval₂ (Int.castRingHom (ZMod c))
      ((V.1 : ZMod c)*(↑hr.unit⁻¹ : ZMod c))*h₂ -
    (endpointL q e).eval₂ (Int.castRingHom (ZMod c))
      ((V.1 : ZMod c)*(↑hr.unit⁻¹ : ZMod c))*h₁

/-- An actual residue representative of β gives full p³ divisibility of the original pencil. -/
theorem original_pencil_dvd {p : ℕ} (hp : p.Prime)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base e : Endpoint)
    (hr : IsUnit (R.1 : ZMod (p^3)))
    (ht : IsUnit (-(physical R V q).2 : ZMod (p^3)))
    (hb : WordSolution (p^3) a₁ a₂ R V q base)
    (he : WordSolution (p^3) a₁ a₂ R V q e) :
    let b : ℤ := ((V.1 : ZMod (p^3)) * (↑hr.unit⁻¹ : ZMod (p^3))).val
    (p : ℤ)^3 ∣ (pencil q base e).eval b := by
  have : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h := original_pencil_root a₁ a₂ ha₁ ha₂ R V q base e hr ht hb he
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change (Int.castRingHom (ZMod (p^3)))
    ((pencil q base e).eval (((V.1 : ZMod (p^3)) * (↑hr.unit⁻¹ : ZMod (p^3))).val : ℤ)) = 0
  rw [← Polynomial.eval₂_at_apply]
  simpa using h

/-- Literal coordinate bounds in the actual chosen integer basis. -/
def CoordinateBound (J₁ J₂ : ℝ) (z : Coordinate) : Prop :=
  |(z.1 : ℝ)| ≤ J₁ ∧ |(z.2 : ℝ)| ≤ J₂

/-- Actual endpoint coefficients satisfy the paper bounds with the absolute constant three. -/
theorem actual_coefficient_bounds (J₁ J₂ : ℝ) (q : Coordinate) (e : Endpoint)
    (hq : CoordinateBound J₁ J₂ q)
    (hx : CoordinateBound J₁ J₂ e.1) (hy : CoordinateBound J₁ J₂ e.2) :
    |(coeffL q e : ℝ)| ≤ 3*J₁ ∧ |(coeffM q e : ℝ)| ≤ 3*J₂ ∧
    |(coeffQ e : ℝ)| ≤ J₁^2 ∧ |(coeffR e : ℝ)| ≤ 2*J₁*J₂ ∧
    |(coeffS e : ℝ)| ≤ J₂^2 := by
  have h₁ : 0 ≤ J₁ := (abs_nonneg _).trans hq.1
  have h₂ : 0 ≤ J₂ := (abs_nonneg _).trans hq.2
  have sum_bound (a b c J : ℝ) (ha : |a| ≤ J) (hb : |b| ≤ J) (hc : |c| ≤ J) :
      |a+b-c| ≤ 3*J := by
    calc
      _ ≤ |a+b|+|c| := abs_sub _ _
      _ ≤ |a|+|b|+|c| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  dsimp [coeffL,coeffM,coeffQ,coeffR,coeffS]
  push_cast
  refine ⟨sum_bound _ _ _ _ hx.1 hy.1 hq.1,
    sum_bound _ _ _ _ hx.2 hy.2 hq.2, ?_, ?_, ?_⟩
  · rw [abs_mul,pow_two]
    exact mul_le_mul hx.1 hy.1 (abs_nonneg _) h₁
  · calc
      _ ≤ |(e.1.1 : ℝ)*(e.2.2 : ℝ)| + |(e.1.2 : ℝ)*(e.2.1 : ℝ)| := abs_add_le _ _
      _ ≤ J₁*J₂+J₂*J₁ := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul hx.1 hy.2 (abs_nonneg _) h₁)
          (mul_le_mul hx.2 hy.1 (abs_nonneg _) h₂)
      _ = _ := by ring
  · rw [abs_mul,pow_two]
    exact mul_le_mul hx.2 hy.2 (abs_nonneg _) h₂

/-- The actual original pencil has degree at most three, including the zero pencil. -/
theorem pencil_natDegree (q : Coordinate) (base e : Endpoint) :
    (pencil q base e).natDegree ≤ 3 := by
  rw [pencil_expansion]
  compute_degree

private theorem bounded_mul {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a*b| ≤ A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

private theorem bounded_sub {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a-b| ≤ A+B := (abs_sub _ _).trans (add_le_add ha hb)

private theorem bounded_four {a b c d A B C D : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    |a+b-c-d| ≤ A+B+C+D := by
  exact (abs_sub _ _).trans (add_le_add
    (bounded_sub ((abs_add_le _ _).trans (add_le_add ha hb)) hc) hd)

/-- The four literal original pencil coefficients have the exact paper bounds 6,18,18,6. -/
theorem actual_pencil_coefficient_bounds (J₁ J₂ : ℝ) (q : Coordinate) (base e : Endpoint)
    (hq : CoordinateBound J₁ J₂ q)
    (hb₁ : CoordinateBound J₁ J₂ base.1) (hb₂ : CoordinateBound J₁ J₂ base.2)
    (he₁ : CoordinateBound J₁ J₂ e.1) (he₂ : CoordinateBound J₁ J₂ e.2) :
    |((pencil q base e).coeff 0 : ℝ)| ≤ 6*J₁^3 ∧
    |((pencil q base e).coeff 1 : ℝ)| ≤ 18*J₁^2*J₂ ∧
    |((pencil q base e).coeff 2 : ℝ)| ≤ 18*J₁*J₂^2 ∧
    |((pencil q base e).coeff 3 : ℝ)| ≤ 6*J₂^3 := by
  obtain ⟨hlb,hmb,hqb,hrb,hsb⟩ := actual_coefficient_bounds J₁ J₂ q base hq hb₁ hb₂
  obtain ⟨hle,hme,hqe,hre,hse⟩ := actual_coefficient_bounds J₁ J₂ q e hq he₁ he₂
  rw [pencil_expansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  norm_num
  refine ⟨?_,?_,?_,?_⟩
  · have h := bounded_sub (bounded_mul hlb hqe) (bounded_mul hle hqb)
    convert h using 1; ring
  · have h := bounded_four (bounded_mul hlb hre) (bounded_mul hmb hqe)
      (bounded_mul hle hrb) (bounded_mul hme hqb)
    convert h using 1; ring
  · have h := bounded_four (bounded_mul hlb hse) (bounded_mul hmb hre)
      (bounded_mul hle hsb) (bounded_mul hme hrb)
    convert h using 1; ring
  · have h := bounded_sub (bounded_mul hmb hse) (bounded_mul hme hsb)
    convert h using 1; ring

/-- The actual integer pencil satisfies the archived endpoint's H=18 height hypothesis. -/
theorem actual_pencil_height (J₁ J₂ : ℝ) (q : Coordinate) (base e : Endpoint)
    (hq : CoordinateBound J₁ J₂ q)
    (hb₁ : CoordinateBound J₁ J₂ base.1) (hb₂ : CoordinateBound J₁ J₂ base.2)
    (he₁ : CoordinateBound J₁ J₂ e.1) (he₂ : CoordinateBound J₁ J₂ e.2) :
    ∀ j ≤ (pencil q base e).natDegree,
      |((pencil q base e).coeff j : ℝ)| ≤ 18*J₁^(3-j)*J₂^j := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := actual_pencil_coefficient_bounds J₁ J₂ q base e hq hb₁ hb₂ he₁ he₂
  have hJ₁ : 0 ≤ J₁ := (abs_nonneg _).trans hq.1
  have hJ₂ : 0 ≤ J₂ := (abs_nonneg _).trans hq.2
  intro j hj
  have hdeg := pencil_natDegree q base e
  have hj3 : j ≤ 3 := hj.trans hdeg
  interval_cases j <;> norm_num at *
  · nlinarith [pow_nonneg hJ₁ 3]
  · exact h₁
  · exact h₂
  · nlinarith [pow_nonneg hJ₂ 3]

end
end D5.S3.Arith.CharacterSums.Original
