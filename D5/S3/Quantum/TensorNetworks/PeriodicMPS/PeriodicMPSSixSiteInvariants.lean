/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteInvariants
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteInvariants
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal]
   utility: none
   digest: Three real invariants determine the projective six-site boundary equations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMarginal

/-! Phase-invariant polynomial entries of the six-site independent-set marginal. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteInvariants

open PeriodicMPSSixSiteMarginal
open scoped ComplexConjugate

/-- Vacuum diagonal entry in the three phase-invariant variables. -/
def entry00 (u v w : ℝ) : ℝ :=
  4 * u ^ 3 + 57 * u ^ 2 * v - 36 * u ^ 2 * w + 4 * u ^ 2 + 18 * u * v ^ 2 - 96 * u * v * w + 28
    * u * v + 48 * u * w ^ 2 - 24 * u * w + 2 * u + v ^ 3 - 12 * v ^ 2 * w + 4 * v ^ 2 + 36 * v
    * w ^ 2 - 24 * v * w + 3 * v - 16 * w ^ 3 + 16 * w ^ 2 - 4 * w

/-- Exchange entry in the one-excitation block in the three phase-invariant variables. -/
def entry12 (u v w : ℝ) : ℝ :=
  u ^ 2 + 7 * u * v - 6 * u * w + v ^ 2 - 6 * v * w + 2 * v + 4 * w ^ 2 - 2 * w

/-- Squared modulus of the vacuum-to-singleton entry in the three phase-invariant variables. -/
def entry01NormSq (u v w : ℝ) : ℝ :=
  4 * u ^ 5 + 85 * u ^ 4 * v - 60 * u ^ 4 * w + 8 * u ^ 4 + 421 * u ^ 3 * v ^ 2 - 714 * u ^ 3 *
    v * w + 122 * u ^ 3 * v + 280 * u ^ 3 * w ^ 2 - 96 * u ^ 3 * w + 8 * u ^ 3 + 184 * u ^ 2 * v
    ^ 3 - 1170 * u ^ 2 * v ^ 2 * w + 344 * u ^ 2 * v ^ 2 + 1392 * u ^ 2 * v * w ^ 2 - 732 * u ^
    2 * v * w + 81 * u ^ 2 * v - 448 * u ^ 2 * w ^ 3 + 332 * u ^ 2 * w ^ 2 - 70 * u ^ 2 * w + 4
    * u ^ 2 + 25 * u * v ^ 4 - 294 * u * v ^ 3 * w + 96 * u * v ^ 3 + 1020 * u * v ^ 2 * w ^ 2 -
    656 * u * v ^ 2 * w + 89 * u * v ^ 2 - 1000 * u * v * w ^ 3 + 944 * u * v * w ^ 2 - 264 * u
    * v * w + 20 * u * v + 288 * u * w ^ 4 - 352 * u * w ^ 3 + 144 * u * w ^ 2 - 22 * u * w + u
    + v ^ 5 - 18 * v ^ 4 * w + 6 * v ^ 4 + 112 * v ^ 3 * w ^ 2 - 76 * v ^ 3 * w + 11 * v ^ 3 -
    280 * v ^ 2 * w ^ 3 + 288 * v ^ 2 * w ^ 2 - 86 * v ^ 2 * w + 6 * v ^ 2 + 240 * v * w ^ 4 -
    336 * v * w ^ 3 + 160 * v * w ^ 2 - 28 * v * w + v - 64 * w ^ 5 + 112 * w ^ 4 - 72 * w ^ 3 +
    20 * w ^ 2 - 2 * w

/-- Difference between diagonal and exchange entries in the single-excitation block. -/
def entryDifference (u v w : ℝ) : ℝ :=
  2 * u + v - 2 * w + 1

/-- Real part of the overlap of the two complex chart coordinates. -/
def overlap (x y : ℂ) : ℝ := (x * conj y).re

private theorem g00_eq (x y : ℂ) :
    (gram (nilpotentRay x y) 0 0).re =
      entry00 (Complex.normSq y) (Complex.normSq x) (overlap x y) := by
  unfold nilpotentRay
  rw [(independent_gram _ _ _ _ _).1]
  norm_num [entry00, overlap, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    pow_succ]
  ring

private theorem g12_eq (x y : ℂ) :
    (gram (nilpotentRay x y) 1 2).re =
      entry12 (Complex.normSq y) (Complex.normSq x) (overlap x y) := by
  unfold nilpotentRay
  rw [(independent_gram _ _ _ _ _).2.2.2.1]
  norm_num [entry12, overlap, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    pow_succ]
  ring

set_option maxHeartbeats 2000000 in
-- Expand the squared modulus in the four real coordinates of the two chart variables.
/-- The off-diagonal squared modulus is constant on common phase orbits. -/
theorem g01_normSq_eq (x y : ℂ) :
    Complex.normSq (gram (nilpotentRay x y) 0 1) =
      entry01NormSq (Complex.normSq y) (Complex.normSq x) (overlap x y) := by
  unfold nilpotentRay
  rw [(independent_gram _ _ _ _ _).2.1]
  norm_num [entry01NormSq, overlap, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    pow_succ]
  ring

theorem difference_eq (x y : ℂ) :
    (gram (nilpotentRay x y) 1 1 - gram (nilpotentRay x y) 1 2).re =
      entryDifference (Complex.normSq y) (Complex.normSq x) (overlap x y) := by
  unfold nilpotentRay
  rw [(independent_gram _ _ _ _ _).2.2.1, (independent_gram _ _ _ _ _).2.2.2.1]
  norm_num [entryDifference, overlap, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    pow_succ]
  ring

/-- Two real diagonal coordinates and the squared off-diagonal modulus, after
clearing the common difference scale, give the special fiber equations. -/
def specialEquation (i : Fin 3) (u v w : ℝ) : ℝ :=
  ![4 * entry00 u v w - 121 * entryDifference u v w,
    4 * entry12 u v w - 11 * entryDifference u v w,
    16 * entry01NormSq u v w - 1517 * entryDifference u v w ^ 2] i

/-- Matching the special marginal up to a real gain forces all three invariant equations. -/
theorem specialEquation_eq_zero {x y : ℂ} {g : ℝ}
    (h : g • gram (nilpotentRay x y) = gram (nilpotentRay 1 Complex.I)) (i : Fin 3) :
    specialEquation i (Complex.normSq y) (Complex.normSq x) (overlap x y) = 0 := by
  have h₀ := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => (G 0 0).re) h
  have h₂ := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => (G 1 2).re) h
  have hD := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => (G 1 1 - G 1 2).re) h
  have h₁ := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => Complex.normSq (G 0 1)) h
  have hnorm (z : ℂ) : Complex.normSq (g • z) = g ^ 2 * Complex.normSq z := by
    rw [Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal, pow_two]
  simp only [Matrix.smul_apply, Complex.smul_re, smul_eq_mul, ← smul_sub,
    g00_eq, g12_eq, difference_eq, hnorm, g01_normSq_eq] at h₀ h₂ hD h₁
  have hcoords : Complex.normSq Complex.I = 1 ∧ Complex.normSq (1 : ℂ) = 1 ∧
      overlap 1 Complex.I = 0 := by
    norm_num [overlap, Complex.normSq_apply, Complex.mul_re]
  obtain ⟨hI, hOne, hOverlap⟩ := hcoords
  have h₀' : entry00 1 1 0 = 121 := by norm_num [entry00]
  have h₂' : entry12 1 1 0 = 11 := by norm_num [entry12]
  have hD' : entryDifference 1 1 0 = 4 := by norm_num [entryDifference]
  have h₁' : entry01NormSq 1 1 0 = 1517 := by norm_num [entry01NormSq]
  simp only [hI, hOne, hOverlap, h₀', h₂', hD', h₁'] at h₀ h₂ hD h₁
  let u := Complex.normSq y
  let v := Complex.normSq x
  let w := overlap x y
  have hg : g ≠ 0 := by intro hg; simp [hg] at hD
  have hg₂ : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  fin_cases i
  · change 4 * entry00 u v w - 121 * entryDifference u v w = 0
    apply (mul_eq_zero.mp _).resolve_left hg
    linear_combination 4 * h₀ - 121 * hD
  · change 4 * entry12 u v w - 11 * entryDifference u v w = 0
    apply (mul_eq_zero.mp _).resolve_left hg
    linear_combination 4 * h₂ - 11 * hD
  · change 16 * entry01NormSq u v w - 1517 * entryDifference u v w ^ 2 = 0
    apply (mul_eq_zero.mp _).resolve_left hg₂
    have hD₂ : g ^ 2 * entryDifference u v w ^ 2 = 16 := by
      rw [← mul_pow, hD]
      norm_num
    linear_combination 16 * h₁ - 1517 * hD₂

/-- The elimination coordinate is a squared norm on physical amplitudes. -/
theorem projectedInvariant_eq (x y : ℂ) :
    Complex.normSq y + 25 * Complex.normSq x - 10 * overlap x y =
      Complex.normSq (y - 5 * x) := by
  norm_num [overlap, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im]
  ring

private theorem phase_ratio {x y : ℂ} (hx : Complex.normSq x = 1)
    (hy : Complex.normSq y = 1) (hxy : overlap x y = 0) :
    y = x * Complex.I ∨ y = x * (-Complex.I) := by
  let z := y * conj x
  have hz : Complex.normSq z = 1 := by
    simp [z, Complex.normSq_mul, Complex.normSq_conj, hx, hy]
  have hre : z.re = 0 := by
    simpa [z, overlap, Complex.mul_re, mul_comm] using hxy
  have him : z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, hre, pow_two] using hz
  have hyz : y = x * z := by
    calc
      y = y * (x * conj x) := by simp [Complex.mul_conj, hx]
      _ = x * z := by unfold z; ring
  have hsplit : (z.im - 1) * (z.im + 1) = 0 := by linear_combination him
  rcases mul_eq_zero.mp hsplit with hi | hi
  · left
    have he : z = Complex.I := Complex.ext (by simpa using hre) (by simpa using sub_eq_zero.mp hi)
    simpa [he] using hyz
  · right
    have he : z = -Complex.I := Complex.ext (by simpa using hre) (by simp; linarith)
    simpa [he] using hyz

private theorem g01_common_phase {x : ℂ} (hx : Complex.normSq x = 1) (z : ℂ) :
    gram (nilpotentRay x (x * z)) 0 1 = x * gram (nilpotentRay 1 z) 0 1 := by
  let a := 1 - 6 * z + 9 * z ^ 2 - 2 * z ^ 3
  let b := 1 - 3 * z + z ^ 2
  let c := 1 - z
  have hchart :
      nilpotentRay x (x * z) = independentSlice (x ^ 3 * a) (x ^ 2 * b) (x * c) x 1 := by
    unfold nilpotentRay
    congr 1 <;> dsimp [a, b, c] <;> ring
  have hunit : nilpotentRay 1 z = independentSlice a b c 1 1 := by
    simp [nilpotentRay, a, b, c]
  rw [hchart, hunit, (independent_gram _ _ _ _ _).2.1, (independent_gram _ _ _ _ _).2.1]
  simp only [map_mul, map_pow, map_one, mul_one]
  calc
    _ = x * ((x * conj x) ^ 2 * (a * conj b) +
        (x * conj x) * (2 * (b * conj c) + b) + c) := by ring
    _ = _ := by simp [Complex.mul_conj, hx, add_assoc]

/-- On the physical invariant triple, the complex off-diagonal entry fixes the
phase on each of the two possible relative orientations. -/
theorem special_chart_of_invariants {x y : ℂ} {g : ℝ}
    (h : g • gram (nilpotentRay x y) = gram (nilpotentRay 1 Complex.I))
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1) (hxy : overlap x y = 0) :
    (x = 1 ∧ y = Complex.I) ∨
      (x = (19 - 34 * Complex.I) / (19 + 34 * Complex.I) ∧ y = x * (-Complex.I)) := by
  have hd := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => (G 1 1 - G 1 2).re) h
  have htarget : entryDifference (Complex.normSq Complex.I) (Complex.normSq (1 : ℂ))
      (overlap 1 Complex.I) = 4 := by
    norm_num [entryDifference, overlap, Complex.normSq_apply, Complex.mul_re]
  simp only [Matrix.smul_apply, ← smul_sub, Complex.smul_re, smul_eq_mul,
    difference_eq, hx, hy, hxy, htarget] at hd
  norm_num [entryDifference] at hd
  have hg : g = 1 := hd
  have hoff := congrArg (fun G : Matrix (Fin 4) (Fin 4) ℂ => G 0 1) h
  simp only [hg, one_smul] at hoff
  have hp : gram (nilpotentRay 1 Complex.I) 0 1 = 19 - 34 * Complex.I := by
    rw [nilpotentRay, (independent_gram _ _ _ _ _).2.1]
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, Complex.conj_I]
    simp [pow_succ]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hn : gram (nilpotentRay 1 (-Complex.I)) 0 1 = 19 + 34 * Complex.I := by
    rw [nilpotentRay, (independent_gram _ _ _ _ _).2.1]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat, Complex.conj_I]
    simp [pow_succ]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hpne : (19 - 34 * Complex.I : ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    norm_num [Complex.mul_re] at hr
  have hnne : (19 + 34 * Complex.I : ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    norm_num [Complex.mul_re] at hr
  rcases phase_ratio hx hy hxy with hplus | hminus
  · rw [hplus, g01_common_phase hx, hp] at hoff
    have he : x = 1 := (mul_right_cancel₀ hpne) (by simpa using hoff)
    exact Or.inl ⟨he, by simpa [he] using hplus⟩
  · rw [hminus, g01_common_phase hx, hp, hn] at hoff
    exact Or.inr ⟨(eq_div_iff hnne).2 hoff, hminus⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteInvariants
