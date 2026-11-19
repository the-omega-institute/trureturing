/- GID: D5/S3/Arith/CharacterSums/PascadiPrimeCubeSingularCover
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiPrimeCubeSingularCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-cube localization and degree-sensitive singular resultants. -/
/- Provenance: integrated from the completed 2026-11-16 singular-cover research archive.
Original source SHA256: b41d415ccf6f20adf7b23aad0d6ed2dd09bf9628cf2a0eb37faba3ceaa13572e.
Canonical integration preserves the archived proofs; see the Pascadi Library note. -/

import D5.S3.Arith.CharacterSums.PascadiLocalizedFactor

/-! Primitive root-relevant factors cover the actual prime-cube singular pencil at paper height. -/

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.PrimeCube
noncomputable section

-- Fixed cubic identities need expanded polynomial normalization.
set_option maxRecDepth 10000

/-- The actual primitive localized factor inherits the full prime-cube value,
not just its square, from the original polynomial. -/
theorem localized_factor_cube (P : ℤ[X]) (p : ℕ) [Fact p.Prime] (b : ℤ)
    (hP : P.map (Int.castRingHom (ZMod p)) ≠ 0) (hd : P.natDegree ≤ 3)
    (hv : (p : ℤ) ^ 3 ∣ P.eval b) (hdv : (p : ℤ) ∣ P.derivative.eval b)
    (J₁ J₂ C : ℝ) (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 0 ≤ C)
    (hb : ∀ j ≤ P.natDegree, |(P.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j) :
    ∃ R U : ℤ[X], P = R * U ∧ R.IsPrimitive ∧
      IsUnit ((U.eval b : ℤ) : ZMod p) ∧ R.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      (p : ℤ) ^ 3 ∣ R.eval b ∧ (p : ℤ) ∣ R.derivative.eval b ∧
      (R.natDegree = 2 ∨ R.natDegree = 3) ∧
      (∀ q : ℤ[X], Irreducible q → q ∣ R → ((q.eval b : ℤ) : ZMod p) = 0) ∧
      (∀ j ≤ R.natDegree, |(R.coeff j : ℝ)| ≤ 8 * C * J₁ ^ (3 - j) * J₂ ^ j) := by
  obtain ⟨R,U,heq,hprim,hU,hRn,_,hdR,hdeg,hrel,hcoeff⟩ :=
    weighted_primitive_localized_factor P p b hP hd
      ((pow_dvd_pow (p : ℤ) (by decide : 2 ≤ 3)).trans hv) hdv
      J₁ J₂ C h₁₂ h₂ hC hb
  have hcop : IsCoprime (p : ℤ) (U.eval b) :=
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr
      (by simpa only [← ZMod.intCast_zmod_eq_zero_iff_dvd] using hU.ne_zero)
  have hvR : (p : ℤ) ^ 3 ∣ R.eval b := by
    rw [heq, eval_mul] at hv
    exact (hcop.pow_left (m := 3)).dvd_of_dvd_mul_right hv
  exact ⟨R,U,heq,hprim,hU,hRn,hvR,hdR,hdeg,hrel,hcoeff⟩

/-- The padded quadratic resultant formula also holds when a leading coefficient vanishes. -/
theorem quadratic_resultant_formula {R : Type*} [CommRing R] (f g : R[X]) :
    f.resultant g 2 2 =
      (f.coeff 2 * g.coeff 0 - g.coeff 2 * f.coeff 0) ^ 2 -
      (f.coeff 2 * g.coeff 1 - g.coeff 2 * f.coeff 1) *
      (f.coeff 1 * g.coeff 0 - f.coeff 0 * g.coeff 1) := by
  have hs : f.sylvester g 2 2 =
      !![g.coeff 0, 0, f.coeff 0, 0;
         g.coeff 1, g.coeff 0, f.coeff 1, f.coeff 0;
         g.coeff 2, g.coeff 1, f.coeff 2, f.coeff 1;
         0, g.coeff 2, 0, f.coeff 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Polynomial.sylvester, Fin.addCases]
  rw [Polynomial.resultant, hs]
  simp [Matrix.det_succ_row_zero, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove]
  ring

private theorem quadratic_fifth_coeff (f g : ℤ[X]) (p : ℤ)
    (he : p ^ 3 ∣ f.coeff 0) (hk : p ^ 3 ∣ g.coeff 0)
    (hd : p ∣ f.coeff 1) (hf : p ∣ g.coeff 1) :
    p ^ 5 ∣ f.resultant g 2 2 := by
  rw [quadratic_resultant_formula]
  have hx : p ^ 3 ∣ f.coeff 2 * g.coeff 0 - g.coeff 2 * f.coeff 0 :=
    dvd_sub (hk.mul_left _) (he.mul_left _)
  have hy : p ∣ f.coeff 2 * g.coeff 1 - g.coeff 2 * f.coeff 1 :=
    dvd_sub (hf.mul_left _) (hd.mul_left _)
  have hz : p ^ 4 ∣ f.coeff 1 * g.coeff 0 - f.coeff 0 * g.coeff 1 := by
    have h₁ := mul_dvd_mul hd hk
    have h₂ := mul_dvd_mul he hf
    simp only [← pow_succ', ← pow_succ] at h₁ h₂
    exact dvd_sub h₁ h₂
  apply dvd_sub
  · exact (pow_dvd_pow p (by decide : 5 ≤ 6)).trans (by
      simpa only [← pow_mul] using pow_dvd_pow_of_dvd hx 2)
  · simpa only [← pow_succ'] using mul_dvd_mul hy hz

/-- Actual quadratic prime-cube singularity forces fifth-power resultant divisibility. -/
theorem quadratic_resultant_dvd_fifth (f g : ℤ[X]) (b p : ℤ)
    (hf : f.natDegree = 2) (hg : g.natDegree = 2)
    (he : p ^ 3 ∣ f.eval b) (hk : p ^ 3 ∣ g.eval b)
    (hd : p ∣ f.derivative.eval b) (hfv : p ∣ g.derivative.eval b) :
    p ^ 5 ∣ f.resultant g f.natDegree g.natDegree := by
  rw [← Polynomial.resultant_taylor f g b]
  simpa only [Polynomial.natDegree_taylor, hf, hg] using
    quadratic_fifth_coeff (f.taylor b) (g.taylor b) p
      (by simpa only [Polynomial.taylor_coeff_zero] using he)
      (by simpa only [Polynomial.taylor_coeff_zero] using hk)
      (by simpa only [Polynomial.taylor_coeff_one] using hd)
      (by simpa only [Polynomial.taylor_coeff_one] using hfv)

/-- The quadratic branch uses its exact weighted exponents eight and four. -/
theorem quadratic_resultant_height (f g : ℤ[X]) (J₁ J₂ C : ℝ)
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 1 ≤ C)
    (hd : f.natDegree = 2) (he : g.natDegree = 2)
    (hf : ∀ j ≤ f.natDegree, |(f.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hg : ∀ j ≤ g.natDegree, |(g.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j) :
    |(f.resultant g f.natDegree g.natDegree : ℝ)| ≤ 24 * C ^ 4 * J₁ ^ 8 * J₂ ^ 4 := by
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hb := weighted_resultant_estimate
    (f.map (Int.castRingHom ℝ)) (g.map (Int.castRingHom ℝ)) J₁ J₂ C h₁ h₂ hC
    (by simp [natDegree_map_eq_of_injective hinj, hd])
    (by simp [natDegree_map_eq_of_injective hinj, he])
    (by simpa only [natDegree_map_eq_of_injective hinj, coeff_map, Int.coe_castRingHom] using hf)
    (by simpa only [natDegree_map_eq_of_injective hinj, coeff_map, Int.coe_castRingHom] using hg)
  simp only [natDegree_map_eq_of_injective hinj, resultant_map_map,
    Int.coe_castRingHom, hd, he] at hb
  norm_num at hb
  simpa only [hd, he, mul_assoc] using hb

theorem quadratic_singular_resultant_zero (f g : ℤ[X]) (b p : ℤ) (J₁ J₂ C : ℝ)
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 1 ≤ C)
    (hd : f.natDegree = 2) (he : g.natDegree = 2)
    (hf : ∀ j ≤ f.natDegree, |(f.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hg : ∀ j ≤ g.natDegree, |(g.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hf₀ : p ^ 3 ∣ f.eval b) (hg₀ : p ^ 3 ∣ g.eval b)
    (hf₁ : p ∣ f.derivative.eval b) (hg₁ : p ∣ g.derivative.eval b)
    (hgap : 24 * C ^ 4 * J₁ ^ 8 * J₂ ^ 4 < (p : ℝ) ^ 5) :
    f.resultant g f.natDegree g.natDegree = 0 := by
  have hdiv := quadratic_resultant_dvd_fifth f g b p hd he hf₀ hg₀ hf₁ hg₁
  have hbnd := quadratic_resultant_height f g J₁ J₂ C h₁ h₂ hC hd he hf hg
  by_contra hn
  have hle := Int.le_abs_of_dvd hn hdiv
  have hle' : (p : ℝ) ^ 5 ≤ |(f.resultant g f.natDegree g.natDegree : ℝ)| := by
    exact_mod_cast hle
  exact (not_lt_of_ge hle') (hbnd.trans_lt hgap)


def bracket {R : Type*} [CommRing R] (a b c : Fin 3 → R) : R :=
  Matrix.det !![a 0, b 0, c 0; a 1, b 1, c 1; a 2, b 2, c 2]

/-- A fixed Dixon matrix gives the universal integer residual, including Δ = 0. -/
def residualMatrix {R : Type*} [CommRing R] (l m q r s : Fin 3 → R) :
    Matrix (Fin 3) (Fin 3) R :=
  !![bracket r q l, bracket s q l + bracket r q m, bracket s q m;
     bracket s q l, bracket s r l + bracket s q m, bracket s r m;
     bracket m q l, bracket m r l, bracket m s l]

def residual {R : Type*} [CommRing R] (l m q r s : Fin 3 → R) : R :=
  (residualMatrix l m q r s).det

def linear {R : Type*} [CommRing R] (a b : R) : R[X] := C a + C b * X

def quadratic {R : Type*} [CommRing R] (a b c : R) : R[X] :=
  C a + C b * X + C c * X ^ 2

def pair {R : Type*} [CommRing R] (l m q r s : Fin 3 → R) (i : Fin 3) : R[X] :=
  linear (l 0) (m 0) * quadratic (q i) (r i) (s i) -
    linear (l i) (m i) * quadratic (q 0) (r 0) (s 0)

theorem pair_coefficients {R : Type*} [CommRing R]
    (l m q r s : Fin 3 → R) (i : Fin 3) :
    pair l m q r s i =
      C (l 0 * q i - l i * q 0) +
      C (l 0 * r i + m 0 * q i - l i * r 0 - m i * q 0) * X +
      C (l 0 * s i + m 0 * r i - l i * s 0 - m i * r 0) * X ^ 2 +
      C (m 0 * s i - m i * s 0) * X ^ 3 := by
  simp only [pair, linear, quadratic, map_add, map_sub, map_mul]
  ring

set_option maxHeartbeats 2000000 in
-- Normalize the fixed-degree determinant identity.
private theorem cubic_resultant_formula {R : Type*} [CommRing R] (f g : R[X]) :
    f.resultant g 3 3 = -Matrix.det
      !![f.coeff 1 * g.coeff 0 - f.coeff 0 * g.coeff 1,
         f.coeff 2 * g.coeff 0 - f.coeff 0 * g.coeff 2,
         f.coeff 3 * g.coeff 0 - f.coeff 0 * g.coeff 3;
         f.coeff 2 * g.coeff 0 - f.coeff 0 * g.coeff 2,
         f.coeff 2 * g.coeff 1 - f.coeff 1 * g.coeff 2 +
           (f.coeff 3 * g.coeff 0 - f.coeff 0 * g.coeff 3),
         f.coeff 3 * g.coeff 1 - f.coeff 1 * g.coeff 3;
         f.coeff 3 * g.coeff 0 - f.coeff 0 * g.coeff 3,
         f.coeff 3 * g.coeff 1 - f.coeff 1 * g.coeff 3,
         f.coeff 3 * g.coeff 2 - f.coeff 2 * g.coeff 3] := by
  have hs : f.sylvester g 3 3 =
      !![g.coeff 0, 0, 0, f.coeff 0, 0, 0;
         g.coeff 1, g.coeff 0, 0, f.coeff 1, f.coeff 0, 0;
         g.coeff 2, g.coeff 1, g.coeff 0, f.coeff 2, f.coeff 1, f.coeff 0;
         g.coeff 3, g.coeff 2, g.coeff 1, f.coeff 3, f.coeff 2, f.coeff 1;
         0, g.coeff 3, g.coeff 2, 0, f.coeff 3, f.coeff 2;
         0, 0, g.coeff 3, 0, 0, f.coeff 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Polynomial.sylvester, Fin.addCases]
  rw [Polynomial.resultant, hs]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
-- Normalize the fixed-degree determinant identity.
/-- An identity for the actual LQᵢ − LᵢQ pair, without cancelling a specialization of Δ. -/
theorem actual_residual_resultant {R : Type*} [CommRing R] (l m q r s : Fin 3 → R) :
    (pair l m q r s 1).resultant (pair l m q r s 2) 3 3 =
      ((m 0) ^ 2 * q 0 - l 0 * m 0 * r 0 + (l 0) ^ 2 * s 0) *
        residual l m q r s := by
  rw [cubic_resultant_formula]
  simp only [pair_coefficients, coeff_add, coeff_C_mul, coeff_C, coeff_X,
    coeff_X_pow, Matrix.det_fin_three, residual, residualMatrix, bracket]
  norm_num
  ring

theorem bracket_scale {R : Type*} [CommRing R] (a b c : Fin 3 → R)
    (x y z : R) : bracket (fun i => x * a i) (fun i => y * b i) (fun i => z * c i) =
      x * y * z * bracket a b c := by
  simp [bracket, Matrix.det_fin_three]
  ring

private theorem residual_scale {R : Type*} [CommRing R] (l m q r s : Fin 3 → R)
    (a b : R) :
    residual (fun i => a * l i) (fun i => b * m i) (fun i => a ^ 2 * q i)
      (fun i => (a * b) * r i) (fun i => b ^ 2 * s i) =
        (a * b) ^ 7 * residual l m q r s := by
  simp [residual, residualMatrix, bracket_scale, Matrix.det_fin_three]
  ring

set_option maxHeartbeats 1000000 in
-- Normalize the fixed-degree determinant identity.
theorem residual_translate {R : Type*} [CommRing R] (l m q r s : Fin 3 → R)
    (b : R) :
    residual (fun i => l i + b * m i) m (fun i => q i + b * r i + b ^ 2 * s i)
      (fun i => r i + 2 * b * s i) s = residual l m q r s := by
  have hM : residualMatrix (fun i => l i + b * m i) m
      (fun i => q i + b * r i + b ^ 2 * s i) (fun i => r i + 2 * b * s i) s =
      !![1,b,0; 0,1,0; 0,0,1] * residualMatrix l m q r s *
        !![1,0,0; b,1,0; b^2,2*b,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [residualMatrix, bracket, Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  unfold residual
  rw [hM, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fin_three]

set_option maxHeartbeats 1000000 in
-- Normalize the fixed-degree determinant identity.
private theorem residual_shear {R : Type*} [CommRing R] (l m q r s : Fin 3 → R)
    (b : R) :
    residual l (fun i => m i + b * l i) q (fun i => r i + 2 * b * q i)
      (fun i => s i + b * r i + b ^ 2 * q i) = residual l m q r s := by
  have hM : residualMatrix l (fun i => m i + b * l i) q
      (fun i => r i + 2 * b * q i) (fun i => s i + b * r i + b ^ 2 * q i) =
      !![1,0,0; b,1,0; 0,0,1] * residualMatrix l m q r s *
        !![1,2*b,b^2; 0,1,b; 0,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [residualMatrix, bracket, Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  unfold residual
  rw [hM, Matrix.det_mul, Matrix.det_mul]
  simp [Matrix.det_fin_three]

/-- The explicit residual in a chart with common leading cubic factor A. -/
def chartResidual {R : Type*} [CommRing R] (A a b C D E F G K : R) : R :=
  let x := D * K - E * G
  let y := C * K - E * F
  let z := a * K - b * E
  let u := C * G - D * F + A * z
  let v := a * G - b * D
  let w := a * F - b * C;
  -(w * (x * u - y ^ 2) - A * x * v ^ 2 + 2 * A * y * z * v - A * u * z ^ 2)

set_option maxHeartbeats 2000000 in
-- Normalize the fixed-degree determinant identity.
private theorem residual_chart {R : Type*} [CommRing R] (l m q r s : Fin 3 → R)
    (hm : m 0 = 0) :
    (l 0) ^ 2 * residual l m q r s =
      chartResidual (s 0) (-m 1) (-m 2)
        (l 0 * s 1 - l 1 * s 0 - m 1 * r 0)
        (l 0 * r 1 - l 1 * r 0 - m 1 * q 0)
        (l 0 * q 1 - l 1 * q 0)
        (l 0 * s 2 - l 2 * s 0 - m 2 * r 0)
        (l 0 * r 2 - l 2 * r 0 - m 2 * q 0)
        (l 0 * q 2 - l 2 * q 0) := by
  simp [residual, residualMatrix, bracket, Matrix.det_fin_three, chartResidual, hm]
  ring

set_option maxHeartbeats 500000 in
-- Normalize the fixed-degree determinant identity.
private theorem chartResidual_dvd_fifth (A a b C D E F G K p : ℤ)
    (hD : p ∣ D) (hG : p ∣ G) (hE : p ^ 3 ∣ E) (hK : p ^ 3 ∣ K) :
    p ^ 5 ∣ chartResidual A a b C D E F G K := by
  obtain ⟨d, rfl⟩ := hD
  obtain ⟨g, rfl⟩ := hG
  obtain ⟨e, rfl⟩ := hE
  obtain ⟨k, rfl⟩ := hK
  use -( (a * F - b * C) *
      ((d * k - e * g) * (C * g - d * F + A * p ^ 2 * (a * k - b * e)) -
        p * (C * k - e * F) ^ 2) -
      A * p * (d * k - e * g) * (a * g - b * d) ^ 2 +
      2 * A * p ^ 2 * (C * k - e * F) * (a * k - b * e) * (a * g - b * d) -
      A * p ^ 2 * (C * g - d * F + A * p ^ 2 * (a * k - b * e)) * (a * k - b * e) ^ 2)
  simp only [chartResidual]
  ring

/-- The chart transfer uses only powers of L(β), never a division by Δ. -/
theorem actual_residual_dvd_fifth (l m q r s : Fin 3 → ℤ) (p : ℕ)
    [Fact p.Prime] (b : ℤ)
    (hunit : IsUnit (((l 0 + b * m 0 : ℤ) : ZMod p)))
    (he : (p : ℤ) ^ 3 ∣ (pair l m q r s 1).eval b)
    (hk : (p : ℤ) ^ 3 ∣ (pair l m q r s 2).eval b)
    (hd : (p : ℤ) ∣ (pair l m q r s 1).derivative.eval b)
    (hg : (p : ℤ) ∣ (pair l m q r s 2).derivative.eval b) :
    (p : ℤ) ^ 5 ∣ residual l m q r s := by
  let L : Fin 3 → ℤ := fun i => l i + b * m i
  let Q : Fin 3 → ℤ := fun i => q i + b * r i + b ^ 2 * s i
  let R : Fin 3 → ℤ := fun i => r i + 2 * b * s i
  let u := L 0
  let M' : Fin 3 → ℤ := fun i => u * m i - m 0 * L i
  let R' : Fin 3 → ℤ := fun i => u * R i - 2 * m 0 * Q i
  let S' : Fin 3 → ℤ := fun i => u ^ 2 * s i - u * m 0 * R i + (m 0) ^ 2 * Q i
  have hs : residual L M' Q R' S' = u ^ 7 * residual l m q r s := by
    have hsh := residual_shear L (fun i => u * m i) Q
      (fun i => u * R i) (fun i => u ^ 2 * s i) (-m 0)
    have hsc := residual_scale L m Q R s 1 u
    have htr := residual_translate l m q r s b
    have heq : residual L M' Q R' S' =
        residual L (fun i => u * m i + -m 0 * L i) Q
          (fun i => u * R i + 2 * -m 0 * Q i)
          (fun i => u ^ 2 * s i + -m 0 * (u * R i) + (-m 0) ^ 2 * Q i) := by
      congr 1 <;> funext i <;> dsimp [M', R', S'] <;> ring
    rw [heq, hsh]
    simp only [one_pow, one_mul] at hsc
    exact hsc.trans (congrArg (fun x => u ^ 7 * x) htr)
  have hc := residual_chart L M' Q R' S' (by dsimp [M',u]; ring)
  have hc' : u ^ 9 * residual l m q r s =
      chartResidual (S' 0) (-M' 1) (-M' 2)
        (u * S' 1 - L 1 * S' 0 - M' 1 * R' 0)
        (u * R' 1 - L 1 * R' 0 - M' 1 * Q 0)
        (u * Q 1 - L 1 * Q 0)
        (u * S' 2 - L 2 * S' 0 - M' 2 * R' 0)
        (u * R' 2 - L 2 * R' 0 - M' 2 * Q 0)
        (u * Q 2 - L 2 * Q 0) := by
    rw [hs] at hc
    convert hc using 1 <;> dsimp [u] <;> ring
  have hE (i : Fin 3) : u * Q i - L i * Q 0 = (pair l m q r s i).eval b := by
    simp [pair,linear,quadratic,L,Q,u]
    ring
  have hD (i : Fin 3) : u * R' i - L i * R' 0 - M' i * Q 0 =
      u * (pair l m q r s i).derivative.eval b -
        3 * m 0 * (pair l m q r s i).eval b := by
    simp [pair,linear,quadratic,M',R',L,Q,R,u,derivative_add,derivative_sub,
      derivative_mul,derivative_pow]
    ring
  have hdiv : (p : ℤ) ^ 5 ∣ u ^ 9 * residual l m q r s := by
    rw [hc']
    apply chartResidual_dvd_fifth
    · rw [hD]
      exact dvd_sub (hd.mul_left _) (by simpa only [pow_one] using (((pow_dvd_pow (p : ℤ) (by decide : 1 ≤ 3)).trans he).mul_left (3 * m 0)))
    · rw [hD]
      exact dvd_sub (hg.mul_left _) (by simpa only [pow_one] using (((pow_dvd_pow (p : ℤ) (by decide : 1 ≤ 3)).trans hk).mul_left (3 * m 0)))
    · rwa [hE]
    · rwa [hE]
  have hcop : IsCoprime (p : ℤ) u :=
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr
      (by simpa only [← ZMod.intCast_zmod_eq_zero_iff_dvd] using hunit.ne_zero)
  exact (hcop.pow (m := 5) (n := 9)).dvd_of_dvd_mul_left hdiv

theorem bracket_uniform_bound (a b c : Fin 3 → ℝ) (C : ℝ)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ i, |b i| ≤ C) (hc : ∀ i, |c i| ≤ C) :
    |bracket a b c| ≤ 6 * C ^ 3 := by
  have h := Matrix.det_le (A := (!![a 0,b 0,c 0; a 1,b 1,c 1; a 2,b 2,c 2]))
    (abv := AbsoluteValue.abs) (x := C) (by
      intro i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc])
  norm_num [bracket] at h ⊢
  exact h

private theorem residual_uniform_bound (l m q r s : Fin 3 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hl : ∀ i, |l i| ≤ C) (hm : ∀ i, |m i| ≤ C) (hq : ∀ i, |q i| ≤ C)
    (hr : ∀ i, |r i| ≤ C) (hs : ∀ i, |s i| ≤ C) :
    |residual l m q r s| ≤ 10368 * C ^ 9 := by
  have H (a b c : Fin 3 → ℝ) (ha : ∀ i, |a i| ≤ C)
      (hb : ∀ i, |b i| ≤ C) (hc : ∀ i, |c i| ≤ C) :=
    bracket_uniform_bound a b c C ha hb hc
  have tri (x y : ℝ) : |x + y| ≤ |x| + |y| := by
    simpa only [Real.norm_eq_abs] using norm_add_le x y
  have h := Matrix.det_le (A := residualMatrix l m q r s)
    (abv := AbsoluteValue.abs) (x := 12 * C ^ 3) (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [residualMatrix]
      all_goals
        nlinarith only [pow_nonneg hC 3,
          H r q l hr hq hl, H s q l hs hq hl, H r q m hr hq hm,
          H s q m hs hq hm, H s r l hs hr hl, H s r m hs hr hm,
          H m q l hm hq hl, H m r l hm hr hl, H m s l hm hs hl,
          tri (bracket s q l) (bracket r q m),
          tri (bracket s r l) (bracket s q m)])
  norm_num at h
  change |residual l m q r s| ≤ _ at h
  convert h using 1 <;> ring

/-- Explicit binary-weight seven height of the universal integer residual. -/
theorem actual_residual_height (l m q r s : Fin 3 → ℤ) (J₁ J₂ C : ℝ)
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 0 ≤ C)
    (hl : ∀ i, |(l i : ℝ)| ≤ C * J₁) (hm : ∀ i, |(m i : ℝ)| ≤ C * J₂)
    (hq : ∀ i, |(q i : ℝ)| ≤ C * J₁ ^ 2)
    (hr : ∀ i, |(r i : ℝ)| ≤ C * J₁ * J₂)
    (hs : ∀ i, |(s i : ℝ)| ≤ C * J₂ ^ 2) :
    |((residual l m q r s : ℤ) : ℝ)| ≤ 10368 * C ^ 9 * (J₁ * J₂) ^ 7 := by
  have h₁p : 0 < J₁ := lt_of_lt_of_le zero_lt_one h₁
  have h₂p : 0 < J₂ := lt_of_lt_of_le zero_lt_one h₂
  let L : Fin 3 → ℝ := fun i => (l i : ℝ) / J₁
  let M : Fin 3 → ℝ := fun i => (m i : ℝ) / J₂
  let Q : Fin 3 → ℝ := fun i => (q i : ℝ) / J₁ ^ 2
  let R : Fin 3 → ℝ := fun i => (r i : ℝ) / (J₁ * J₂)
  let S : Fin 3 → ℝ := fun i => (s i : ℝ) / J₂ ^ 2
  have hb := residual_uniform_bound L M Q R S C hC
    (fun i => by simpa [L, abs_div, abs_of_pos h₁p] using (div_le_iff₀ h₁p).mpr (hl i))
    (fun i => by simpa [M, abs_div, abs_of_pos h₂p] using (div_le_iff₀ h₂p).mpr (hm i))
    (fun i => by simpa [Q, abs_div, abs_of_pos (pow_pos h₁p 2)] using
      (div_le_iff₀ (pow_pos h₁p 2)).mpr (hq i))
    (fun i => by simpa [R, abs_div, abs_of_pos (mul_pos h₁p h₂p), mul_assoc] using
      (div_le_iff₀ (mul_pos h₁p h₂p)).mpr (by simpa [mul_assoc] using hr i))
    (fun i => by simpa [S, abs_div, abs_of_pos (pow_pos h₂p 2)] using
      (div_le_iff₀ (pow_pos h₂p 2)).mpr (hs i))
  have heq := residual_scale L M Q R S J₁ J₂
  have hc : ((residual l m q r s : ℤ) : ℝ) =
      residual (fun i => (l i : ℝ)) (fun i => (m i : ℝ))
        (fun i => (q i : ℝ)) (fun i => (r i : ℝ)) (fun i => (s i : ℝ)) := by
    simp [residual,residualMatrix,bracket,Matrix.det_fin_three]
  have heq' : ((residual l m q r s : ℤ) : ℝ) = (J₁ * J₂) ^ 7 * residual L M Q R S := by
    rw [hc]
    convert heq using 1
    congr 1 <;> funext i <;> dsimp [L,M,Q,R,S] <;> field_simp
  rw [heq', abs_mul, abs_of_pos (pow_pos (mul_pos h₁p h₂p) 7)]
  calc _ ≤ (J₁ * J₂) ^ 7 * (10368 * C ^ 9) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
       _ = _ := by ring

/-- Smallness and the proved fifth-power divisor force the actual padded resultant to vanish. -/
theorem actual_pair_resultant_zero (l m q r s : Fin 3 → ℤ) (p : ℕ)
    [Fact p.Prime] (b : ℤ) (J₁ J₂ C : ℝ)
    (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 0 ≤ C)
    (hl : ∀ i, |(l i : ℝ)| ≤ C * J₁) (hm : ∀ i, |(m i : ℝ)| ≤ C * J₂)
    (hq : ∀ i, |(q i : ℝ)| ≤ C * J₁ ^ 2)
    (hr : ∀ i, |(r i : ℝ)| ≤ C * J₁ * J₂)
    (hs : ∀ i, |(s i : ℝ)| ≤ C * J₂ ^ 2)
    (hunit : IsUnit (((l 0 + b * m 0 : ℤ) : ZMod p)))
    (he : (p : ℤ) ^ 3 ∣ (pair l m q r s 1).eval b)
    (hk : (p : ℤ) ^ 3 ∣ (pair l m q r s 2).eval b)
    (hd : (p : ℤ) ∣ (pair l m q r s 1).derivative.eval b)
    (hg : (p : ℤ) ∣ (pair l m q r s 2).derivative.eval b)
    (hgap : 10368 * C ^ 9 * (J₁ * J₂) ^ 7 < (p : ℝ) ^ 5) :
    (pair l m q r s 1).resultant (pair l m q r s 2) 3 3 = 0 := by
  have hdiv := actual_residual_dvd_fifth l m q r s p b hunit he hk hd hg
  have hbound := actual_residual_height l m q r s J₁ J₂ C h₁ h₂ hC hl hm hq hr hs
  have hz : residual l m q r s = 0 := by
    by_contra hn
    have hv := Int.le_abs_of_dvd hn hdiv
    have hv' : (p : ℝ) ^ 5 ≤ |((residual l m q r s : ℤ) : ℝ)| := by exact_mod_cast hv
    exact (not_lt_of_ge hv') (hbound.trans_lt hgap)
  rw [actual_residual_resultant, hz, mul_zero]

private theorem cubic_local_common (P H R U S V : ℤ[X]) (p : ℕ) [Fact p.Prime] (b : ℤ)
    (hP : P ≠ 0) (hPU : P = R * U) (hSV : H = S * V)
    (hR : R.IsPrimitive)
    (hdeg : P.natDegree ≤ 3) (hHdeg : H.natDegree ≤ 3) (hRd : R.natDegree = 3)
    (hrel : ∀ q : ℤ[X], Irreducible q → q ∣ R → ((q.eval b : ℤ) : ZMod p) = 0)
    (hV : IsUnit ((V.eval b : ℤ) : ZMod p)) (hz : P.resultant H 3 3 = 0) :
    (R.map (Int.castRingHom ℚ)).resultant (S.map (Int.castRingHom ℚ)) = 0 := by
  have hU : U ≠ 0 := by intro h; simp [hPU,h] at hP
  have hpd := Polynomial.natDegree_mul hR.ne_zero hU
  rw [← hPU, hRd] at hpd
  have hUd : U.natDegree = 0 := by omega
  have hPd : P.natDegree = 3 := by omega
  have inj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hPQ : P.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff inj).mpr hP
  have hUQ : U.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff inj).mpr hU
  have hu : IsUnit (U.map (Int.castRingHom ℚ)) := by
    apply Polynomial.isUnit_iff_degree_eq_zero.mpr
    rw [degree_eq_natDegree hUQ, natDegree_map_eq_of_injective inj, hUd]
    rfl
  have hqdeg : (H.map (Int.castRingHom ℚ)).natDegree ≤ 3 := by
    simpa only [natDegree_map_eq_of_injective inj] using hHdeg
  have hqpd : (P.map (Int.castRingHom ℚ)).natDegree = 3 := by
    simpa only [natDegree_map_eq_of_injective inj] using hPd
  have heq := Polynomial.resultant_add_right_deg
    (P.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)) 3
    (H.map (Int.castRingHom ℚ)).natDegree (3 - (H.map (Int.castRingHom ℚ)).natDegree) le_rfl
  rw [Nat.add_sub_of_le hqdeg] at heq
  have hzQ : (P.map (Int.castRingHom ℚ)).resultant (H.map (Int.castRingHom ℚ)) 3 3 = 0 := by
    rw [resultant_map_map, hz, map_zero]
  rw [hzQ] at heq
  have hlc : (P.map (Int.castRingHom ℚ)).coeff 3 ≠ 0 := by
    rw [← hqpd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hPQ
  have hraw : (P.map (Int.castRingHom ℚ)).resultant (H.map (Int.castRingHom ℚ)) = 0 := by
    rw [hqpd]
    exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hlc)
  obtain ⟨t,_,ht,htP,htH⟩ := rational_common_factor_of_resultant_zero
    (P.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)) hPQ hraw
  have htR : t ∣ R.map (Int.castRingHom ℚ) := by
    rw [hPU, Polynomial.map_mul] at htP
    rcases (irreducible_iff_prime.mp ht).dvd_mul.mp htP with h | h
    · exact h
    · exact False.elim (ht.not_isUnit (isUnit_iff_dvd_one.mpr (h.trans hu.dvd)))
  obtain ⟨q,hqi,hqp,hqR,ha⟩ := lift_primitive_rational_factor R hR t ht htR
  have hqH : q ∣ H := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast q H hqp).mpr
    (ha.symm.dvd.trans htH)
  have hqS : q ∣ S := by
    rw [hSV] at hqH
    rcases (irreducible_iff_prime.mp hqi).dvd_mul.mp hqH with h | h
    · exact h
    · obtain ⟨W,hW⟩ := h
      have he := hrel q hqi hqR
      have hvz : ((V.eval b : ℤ) : ZMod p) = 0 := by
        rw [hW, eval_mul, Int.cast_mul, he, zero_mul]
      exact False.elim (hV.ne_zero hvz)
  apply Polynomial.resultant_eq_zero_iff.mpr
  refine ⟨Or.inl ((Polynomial.map_ne_zero_iff inj).mpr hR.ne_zero), ?_⟩
  intro hc
  exact ((Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hqp).mp hqi).not_isUnit
    (hc.isUnit_of_dvd' (Polynomial.map_dvd (Int.castRingHom ℚ) hqR)
      (Polynomial.map_dvd (Int.castRingHom ℚ) hqS))

private theorem paper_height_gaps (B M A D t : ℝ)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D) (ht : 0 < t)
    (hcap : B ^ 5 ≤ M ^ 5 * t ^ 3)
    (hlargeA : A ^ 5 * M ^ 35 < t ^ 4)
    (hlargeD : D ^ 5 * M ^ 40 < t) :
    A * B ^ 7 < t ^ 5 ∧ D * B ^ 8 < t ^ 5 := by
  have ha : (A * B ^ 7) ^ 5 ≤ A ^ 5 * M ^ 35 * t ^ 21 := by
    calc _ = A ^ 5 * (B ^ 5) ^ 7 := by ring
         _ ≤ A ^ 5 * (M ^ 5 * t ^ 3) ^ 7 := by gcongr
         _ = _ := by ring
  have hd : (D * B ^ 8) ^ 5 ≤ D ^ 5 * M ^ 40 * t ^ 24 := by
    calc _ = D ^ 5 * (B ^ 5) ^ 8 := by ring
         _ ≤ D ^ 5 * (M ^ 5 * t ^ 3) ^ 8 := by gcongr
         _ = _ := by ring
  have ha' : A ^ 5 * M ^ 35 * t ^ 21 < (t ^ 5) ^ 5 := by
    calc _ < t ^ 4 * t ^ 21 := mul_lt_mul_of_pos_right hlargeA (pow_pos ht _)
         _ = _ := by ring
  have hd' : D ^ 5 * M ^ 40 * t ^ 24 < (t ^ 5) ^ 5 := by
    calc _ < t * t ^ 24 := mul_lt_mul_of_pos_right hlargeD (pow_pos ht _)
         _ = _ := by ring
  exact ⟨(pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 5 ≠ 0)).mp
      (ha.trans_lt ha'),
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 5 ≠ 0)).mp
      (hd.trans_lt hd')⟩

/-- Actual integer pencil member with a distinguished baseline L and Q. -/
def familyPolynomial {ι : Type*} (l m q r s : Option ι → ℤ) (i : ι) : ℤ[X] :=
  linear (l none) (m none) * quadratic (q (some i)) (r (some i)) (s (some i)) -
    linear (l (some i)) (m (some i)) * quadratic (q none) (r none) (s none)

/-- A root-relevant primitive integer factor cover of the actual singular pencil.
Both the quadratic and residual height gaps use fifth-power divisibility. -/
theorem actual_singular_factor_cover {ι : Type*} (l m q r s : Option ι → ℤ)
    (i₀ : ι) (p : ℕ) [Fact p.Prime] (b : ℤ) (J₁ J₂ C H M : ℝ)
    (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hl : ∀ i, |(l i : ℝ)| ≤ C * J₁) (hm : ∀ i, |(m i : ℝ)| ≤ C * J₂)
    (hq : ∀ i, |(q i : ℝ)| ≤ C * J₁ ^ 2)
    (hr : ∀ i, |(r i : ℝ)| ≤ C * J₁ * J₂)
    (hs : ∀ i, |(s i : ℝ)| ≤ C * J₂ ^ 2)
    (hunit : IsUnit (((l none + b * m none : ℤ) : ZMod p)))
    (hred : ∀ i, (familyPolynomial l m q r s i).map (Int.castRingHom (ZMod p)) ≠ 0)
    (hdeg : ∀ i, (familyPolynomial l m q r s i).natDegree ≤ 3)
    (hcoeff : ∀ i, ∀ j ≤ (familyPolynomial l m q r s i).natDegree,
      |((familyPolynomial l m q r s i).coeff j : ℝ)| ≤ H * J₁ ^ (3 - j) * J₂ ^ j)
    (hroot : ∀ i, (p : ℤ) ^ 3 ∣ (familyPolynomial l m q r s i).eval b)
    (hderiv : ∀ i, (p : ℤ) ∣ (familyPolynomial l m q r s i).derivative.eval b)
    (hcap : (J₁ * J₂) ^ 5 ≤ M ^ 5 * (p : ℝ) ^ 3)
    (hlargeR : (10368 * C ^ 9) ^ 5 * M ^ 35 < (p : ℝ) ^ 4)
    (hlargeQ : (24 * (8 * H) ^ 4) ^ 5 * M ^ 40 < (p : ℝ)) :
    ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
      (∀ f ∈ F, Irreducible f ∧ f.IsPrimitive ∧ f ∣ familyPolynomial l m q r s i₀ ∧
        ((f.eval b : ℤ) : ZMod p) = 0 ∧ f.map (Int.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ i, ∃ f ∈ F, f ∣ familyPolynomial l m q r s i) := by
  classical
  have h₁ : 1 ≤ J₁ := h₂.trans h₁₂
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hgaps := paper_height_gaps (J₁ * J₂) M (10368 * C ^ 9) (24 * (8 * H) ^ 4)
    (p : ℝ) (by positivity) (by positivity) (by positivity) hp hcap hlargeR hlargeQ
  have hgapR := hgaps.1
  have hgapQ : 24 * (8 * H) ^ 4 * J₁ ^ 8 * J₂ ^ 4 < (p : ℝ) ^ 5 := by
    calc _ ≤ (24 * (8 * H) ^ 4 * J₁ ^ 8) * J₂ ^ 8 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h₂ (by decide : 4 ≤ 8))
            (by positivity)
         _ = (24 * (8 * H) ^ 4) * (J₁ * J₂) ^ 8 := by ring
         _ < _ := hgaps.2
  let P := familyPolynomial l m q r s
  have hlocal := fun i => localized_factor_cube (P i) p b (hred i) (hdeg i)
    (hroot i) (hderiv i) J₁ J₂ H h₁₂ h₂ (by linarith) (hcoeff i)
  choose R U hRU hprim hUnit hRed hRoot hDeriv hDeg hRel hCoeff using hlocal
  have hPn (i : ι) : P i ≠ 0 := by
    intro h
    apply hred i
    change (P i).map (Int.castRingHom (ZMod p)) = 0
    rw [h, Polynomial.map_zero]
  have hres (i j : ι) : (P i).resultant (P j) 3 3 = 0 := by
    let L : Fin 3 → ℤ := ![l none, l (some i), l (some j)]
    let M : Fin 3 → ℤ := ![m none, m (some i), m (some j)]
    let Q : Fin 3 → ℤ := ![q none, q (some i), q (some j)]
    let A : Fin 3 → ℤ := ![r none, r (some i), r (some j)]
    let B : Fin 3 → ℤ := ![s none, s (some i), s (some j)]
    exact actual_pair_resultant_zero L M Q A B p b J₁ J₂ C (h₂.trans h₁₂) h₂ hC
      (by intro k; fin_cases k <;> simp [L,hl])
      (by intro k; fin_cases k <;> simp [M,hm])
      (by intro k; fin_cases k <;> simp [Q,hq])
      (by intro k; fin_cases k <;> simp [A,hr])
      (by intro k; fin_cases k <;> simp [B,hs])
      hunit (hroot i) (hroot j) (hderiv i) (hderiv j) hgapR
  have inj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hresR (i j : ι) : (R i |>.map (Int.castRingHom ℚ)).resultant
      (R j |>.map (Int.castRingHom ℚ)) = 0 := by
    by_cases hi : (R i).natDegree = 3
    · exact cubic_local_common (P i) (P j) (R i) (U i) (R j) (U j) p b
        (hPn i) (hRU i) (hRU j) (hprim i) (hdeg i) (hdeg j) hi (hRel i) (hUnit j) (hres i j)
    by_cases hj : (R j).natDegree = 3
    · have hz := cubic_local_common (P j) (P i) (R j) (U j) (R i) (U i) p b
        (hPn j) (hRU j) (hRU i) (hprim j) (hdeg j) (hdeg i) hj (hRel j) (hUnit i) (hres j i)
      apply Polynomial.resultant_eq_zero_iff.mpr
      refine ⟨Or.inl ((Polynomial.map_ne_zero_iff inj).mpr (hprim i).ne_zero), ?_⟩
      intro hc
      exact (Polynomial.resultant_eq_zero_iff.mp hz).2 hc.symm
    · have hd : (R i).natDegree = 2 := (hDeg i).resolve_right hi
      have he : (R j).natDegree = 2 := (hDeg j).resolve_right hj
      have hz := quadratic_singular_resultant_zero (R i) (R j) b (p : ℤ) J₁ J₂ (8 * H)
        (h₂.trans h₁₂) h₂ (by linarith) hd he (hCoeff i) (hCoeff j)
        (hRoot i) (hRoot j) (hDeriv i) (hDeriv j) (by exact_mod_cast hgapQ)
      simp only [natDegree_map_eq_of_injective inj, resultant_map_map, hz, map_zero]
  let Fq := (normalizedFactors ((R i₀).map (Int.castRingHom ℚ))).toFinset
  have hFq (t : ℚ[X]) (ht : t ∈ Fq) : Irreducible t ∧ t ∣ (R i₀).map (Int.castRingHom ℚ) :=
    ⟨irreducible_of_normalized_factor t (Multiset.mem_toFinset.mp ht),
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp ht)⟩
  have hcard : Fq.card ≤ 3 := by
    have hc := rational_factor_card_le ((R i₀).map (Int.castRingHom ℚ))
      ((Polynomial.map_ne_zero_iff inj).mpr (hprim i₀).ne_zero)
    rw [natDegree_map_eq_of_injective inj] at hc
    exact hc.trans (by have := hDeg i₀; omega)
  have hlift := fun t : {t // t ∈ Fq} => lift_primitive_rational_factor (R i₀) (hprim i₀) t.val
    (hFq t.val t.property).1 (hFq t.val t.property).2
  choose L hLirr hLprim hLdvd hLassoc using hlift
  refine ⟨Fq.attach.image L, Finset.card_image_le.trans (by simpa using hcard), ?_, ?_⟩
  · intro f hf
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hf
    refine ⟨hLirr t, hLprim t, (hLdvd t).trans ⟨U i₀, hRU i₀⟩,
      hRel i₀ _ (hLirr t) (hLdvd t), ?_⟩
    intro hz
    obtain ⟨V,hV⟩ := hLdvd t
    apply hRed i₀
    rw [hV, Polynomial.map_mul, hz, zero_mul]
  · intro i
    obtain ⟨t, ht, _, _, htR⟩ := rational_common_factor_of_resultant_zero
      ((R i₀).map (Int.castRingHom ℚ)) ((R i).map (Int.castRingHom ℚ))
      ((Polynomial.map_ne_zero_iff inj).mpr (hprim i₀).ne_zero) (hresR i₀ i)
    let x : {t // t ∈ Fq} := ⟨t,ht⟩
    refine ⟨L x, Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have hq : (L x).map (Int.castRingHom ℚ) ∣ (R i).map (Int.castRingHom ℚ) :=
      (hLassoc x).symm.dvd.trans htR
    have hz := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (hLprim x)).mpr hq
    exact hz.trans ⟨U i, hRU i⟩


end
end D5.S3.Arith.CharacterSums.PrimeCube
