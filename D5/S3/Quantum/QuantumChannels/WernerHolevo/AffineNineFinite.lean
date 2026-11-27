/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineFinite
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An order-nine flat hollow symmetric unitary and a bijection between the edges of nine blocks and additive character labels. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Sym.Sym2
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import D5.S3.Weil.ZetaLinear.VonNeumann

open scoped ComplexConjugate
open Matrix

namespace AffineNineFinite

/-- The coordinates in the basis (1,i) of `𝔽₃[i]`, with `i² = -1`. -/
abbrev F9 := QuadraticAlgebra (ZMod 3) (-1 : ZMod 3) 0

instance : Fact (¬ IsSquare (-1 : ZMod 3)) :=
  ⟨by
    rintro ⟨x, hx⟩
    exact (show ∀ y : ZMod 3, (-1 : ZMod 3) ≠ y * y by decide) x hx⟩

instance : Fintype F9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3) (QuadraticAlgebra.equivProd _ _).symm

theorem card_f9 : Fintype.card F9 = 9 :=
  Fintype.card_congr (QuadraticAlgebra.equivProd _ _) |>.trans (by decide)

theorem two_ne_zero : (2 : F9) ≠ 0 := by decide

/-- The imaginary basis element of the chosen finite field model. -/
def ι : F9 := ⟨0, 1⟩

abbrev Bits := ZMod 2 × ZMod 2

/-- The additive group on which the character basis is indexed. -/
abbrev LabelGroup := F9 × F9 × Bits

/-- A block index and an unordered pair of distinct vertices in that block. -/
abbrev BlockEdge := F9 × {e : Sym2 F9 // ¬ e.IsDiag}

def blockEdge (t x y : F9) (h : x ≠ y) : BlockEdge :=
  (t, ⟨s(x, y), fun hd => h (Sym2.mk_isDiag_iff.mp hd)⟩)

private def bitPair (a b : ZMod 3) : Bits :=
  (if a = b then 1 else 0, if a = b + 1 then 1 else 0)

/-- The exact vertex labeling, with the two tests in the real coordinate of
the vertex and the imaginary coordinate of the block index. -/
def vertexLabel (t x : F9) : LabelGroup :=
  (x, t / 2 + x ^ 2, bitPair x.re t.im)

/-- Sum of the two endpoint labels, descended to unordered edges. -/
def edgeLabel (e : BlockEdge) : LabelGroup :=
  Sym2.lift ⟨fun x y => vertexLabel e.1 x + vertexLabel e.1 y, fun _ _ => add_comm _ _⟩
    e.2.1

@[simp]
theorem edgeLabel_blockEdge (t x y : F9) (h : x ≠ y) :
    edgeLabel (blockEdge t x y h) = vertexLabel t x + vertexLabel t y := rfl

private def radius : Fin 4 → F9 := ![ι, 1, 1 + ι, 1 - ι]

private theorem radius_ne_zero : ∀ k, radius k ≠ 0 := by decide

-- The four half-differences are taken modulo sign.
private theorem radius_representative : ∀ z : F9, z ≠ 0 →
    ∃ k, z = radius k ∨ z = -radius k := by decide

private def radiusBits (δ : ZMod 3) (k : Fin 4) : Bits :=
  if k = 0 then (0, 0) else
    (if δ = 0 then 0 else 1, if δ = 1 then 0 else 1)

-- For a vertical pair the real coordinates coincide. For the other three
-- radii the real coordinates are the two residues different from the midpoint.
private theorem bitPair_endpoints : ∀ (a b : ZMod 3) (k : Fin 4),
    bitPair (a + (radius k).re) b + bitPair (a - (radius k).re) b =
      radiusBits (a - b) k := by decide

private def pattern (u : ZMod 3) (k : Fin 4) : Bits :=
  radiusBits (u + (2 * radius k ^ 2).im) k

-- The three nonvertical radii give all three imaginary shifts.
private theorem pattern_injective : ∀ (u : ZMod 3) (j k : Fin 4),
    pattern u j = pattern u k → j = k := by decide

private theorem pattern_surjective : ∀ (u : ZMod 3) (b : Bits),
    ∃ k, pattern u k = b := by decide

private def baseline (c d : F9) : F9 := d - 2 * (c / 2) ^ 2

private def blockAt (c d : F9) (k : Fin 4) : F9 :=
  baseline c d - 2 * radius k ^ 2

private theorem endpoint_ne (h r : F9) (hr : r ≠ 0) : h + r ≠ h - r := by
  intro he
  have hz : (2 : F9) * r = 0 := by linear_combination he
  exact (mul_ne_zero two_ne_zero hr) hz

private def edgeAt (c d : F9) (k : Fin 4) : BlockEdge :=
  blockEdge (blockAt c d k) (c / 2 + radius k) (c / 2 - radius k)
    (endpoint_ne _ _ (radius_ne_zero k))

private theorem edgeLabel_edgeAt (c d : F9) (k : Fin 4) :
    edgeLabel (edgeAt c d k) =
      (c, d, pattern ((c / 2).re - (baseline c d).im) k) := by
  rw [edgeAt, edgeLabel_blockEdge]
  apply Prod.ext
  · change c / 2 + radius k + (c / 2 - radius k) = c
    field_simp [two_ne_zero]
    ring
  · apply Prod.ext
    · change blockAt c d k / 2 + (c / 2 + radius k) ^ 2 +
          (blockAt c d k / 2 + (c / 2 - radius k) ^ 2) = d
      unfold blockAt baseline
      field_simp [two_ne_zero]
      ring
    · change bitPair (c / 2 + radius k).re (blockAt c d k).im +
          bitPair (c / 2 - radius k).re (blockAt c d k).im = _
      rw [QuadraticAlgebra.re_add, QuadraticAlgebra.re_sub, bitPair_endpoints]
      simp only [pattern, blockAt, QuadraticAlgebra.im_sub]
      congr 1
      ring

private theorem edgeAt_surjective (e : BlockEdge) :
    ∃ (c d : F9) (k : Fin 4), edgeAt c d k = e := by
  obtain ⟨t, s, hs⟩ := e
  revert hs
  refine Sym2.inductionOn s (fun x y hs => ?_)
  have hxy : x ≠ y := fun h => hs (Sym2.mk_isDiag_iff.mpr h)
  let c := x + y
  let d := t + x ^ 2 + y ^ 2
  let r := (x - y) / 2
  have hr : r ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxy) two_ne_zero
  have hx : c / 2 + r = x := by
    dsimp [c, r]
    field_simp [two_ne_zero]
    ring
  have hy : c / 2 - r = y := by
    dsimp [c, r]
    field_simp [two_ne_zero]
    ring
  have ht : baseline c d - 2 * r ^ 2 = t := by
    dsimp [baseline, c, d, r]
    field_simp [two_ne_zero]
    ring
  obtain ⟨k, hk | hk⟩ := radius_representative r hr
  · refine ⟨c, d, k, ?_⟩
    apply Prod.ext
    · change blockAt c d k = t
      simpa only [blockAt, hk] using ht
    · apply Subtype.ext
      change s(c / 2 + radius k, c / 2 - radius k) = s(x, y)
      rw [← hk, hx, hy]
  · refine ⟨c, d, k, ?_⟩
    apply Prod.ext
    · change blockAt c d k = t
      simpa only [blockAt, hk, even_two.neg_pow] using ht
    · apply Subtype.ext
      change s(c / 2 + radius k, c / 2 - radius k) = s(x, y)
      have hneg : radius k = -r := by rw [hk, neg_neg]
      rw [hneg, ← sub_eq_add_neg, sub_neg_eq_add, hx, hy, Sym2.eq_swap]

theorem edgeLabel_bijective : Function.Bijective edgeLabel := by
  constructor
  · intro e e' he
    obtain ⟨c, d, k, rfl⟩ := edgeAt_surjective e
    obtain ⟨c', d', k', rfl⟩ := edgeAt_surjective e'
    simp only [edgeLabel_edgeAt, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, hk⟩ := he
    rw [pattern_injective _ _ _ hk]
  · rintro ⟨c, d, b⟩
    obtain ⟨k, hk⟩ := pattern_surjective ((c / 2).re - (baseline c d).im) b
    exact ⟨edgeAt c d k, by rw [edgeLabel_edgeAt, hk]⟩

/-- The equivalence sends each unordered block edge to its actual label sum. -/
noncomputable def edgeLabelEquiv : BlockEdge ≃ LabelGroup :=
  Equiv.ofBijective edgeLabel edgeLabel_bijective

@[simp]
theorem edgeLabelEquiv_blockEdge (t x y : F9) (h : x ≠ y) :
    edgeLabelEquiv (blockEdge t x y h) = vertexLabel t x + vertexLabel t y := rfl

/-- The integer quadratic character, with value zero at the origin. -/
def χ (z : F9) : ℤ :=
  if z = 0 then 0 else if z.re = 0 ∨ z.im = 0 then 1 else -1

private theorem chi_one_iff_square : ∀ z : F9, z ≠ 0 →
    (χ z = 1 ↔ ∃ u : F9, u ^ 2 = z) := by decide

theorem chi_eq_quadraticChar (z : F9) : χ z = quadraticChar F9 z := by
  by_cases hz : z = 0
  · subst z
    simp [χ]
  have hs : χ z = 1 ↔ IsSquare z := by
    rw [chi_one_iff_square z hz]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, by simpa [pow_two] using hu.symm⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by simpa [pow_two] using hu.symm⟩
  by_cases h : IsSquare z
  · exact (hs.mpr h).trans ((quadraticChar_one_iff_isSquare hz).mpr h).symm
  · have haxes : ¬ (z.re = 0 ∨ z.im = 0) := by
      intro ha
      exact h (hs.mp (by simp [χ, hz, ha]))
    rw [show χ z = -1 by simp [χ, hz, haxes],
      (quadraticChar_neg_one_iff_not_isSquare (a := z)).mpr h]

def K : Matrix F9 F9 ℤ := Matrix.of fun x y => χ (x - y)

def J : Matrix F9 F9 ℤ := Matrix.of fun _ _ => 1

def A : Matrix F9 F9 ℤ := J - 1

theorem K_isSymm : K.IsSymm := by decide
theorem A_isSymm : A.IsSymm := by decide

set_option maxRecDepth 4000 in
theorem K_mul_K : K * K = (9 : ℤ) • (1 : Matrix F9 F9 ℤ) - J := by decide

set_option maxRecDepth 4000 in
theorem A_mul_A : A * A = (1 : Matrix F9 F9 ℤ) + (7 : ℤ) • J := by decide

set_option maxRecDepth 4000 in
theorem K_mul_A : K * A = A * K := by decide

private theorem K_offDiag_sq : ∀ x y : F9, x ≠ y → K x y ^ 2 = 1 := by decide

private def complexify (M : Matrix F9 F9 ℤ) : Matrix F9 F9 ℂ :=
  M.map (Int.castRingHom ℂ)

private theorem complexify_star (M : Matrix F9 F9 ℤ) (h : M.IsSymm) :
    (complexify M)ᴴ = complexify M := by
  ext i j
  simp [complexify, h.apply i j]

private theorem complexify_mul (M N : Matrix F9 F9 ℤ) :
    complexify (M * N) = complexify M * complexify N :=
  Matrix.map_mul

noncomputable section

/-- The flat hollow line unitary `(√7 K + i (J - I))/8`. -/
def C : Matrix F9 F9 ℂ :=
  ((8 : ℂ)⁻¹) • ((Real.sqrt 7 : ℂ) • complexify K + Complex.I • complexify A)

theorem C_apply (x y : F9) :
    C x y = ((Real.sqrt 7 : ℂ) * (K x y : ℂ) + Complex.I * (A x y : ℂ)) / 8 := by
  simp only [C, complexify, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Matrix.map_apply]
  change (8 : ℂ)⁻¹ * _ = _ / 8
  rw [div_eq_mul_inv, mul_comm ((8 : ℂ)⁻¹)]
  rfl

theorem C_isSymm : C.IsSymm := by
  apply Matrix.IsSymm.ext
  intro x y
  rw [C_apply, C_apply, K_isSymm.apply x y, A_isSymm.apply x y]

theorem C_diag (x : F9) : C x x = 0 := by
  simp [C_apply, K, χ, A, J]

private theorem sqrt_seven_sq : (Real.sqrt 7 : ℂ) ^ 2 = 7 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)

theorem C_unitary : C ∈ Matrix.unitaryGroup F9 ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change C * Cᴴ = 1
  let S : ℂ := Real.sqrt 7
  have hS : S ^ 2 = 7 := sqrt_seven_sq
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hK := complexify_star K K_isSymm
  have hA := complexify_star A A_isSymm
  have hKK : complexify K * complexify K =
      (9 : ℂ) • (1 : Matrix F9 F9 ℂ) - complexify J := by
    rw [← complexify_mul, K_mul_K]
    ext i j
    simp only [complexify, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    change ((↑((9 : ℤ) * (1 : Matrix F9 F9 ℤ) i j - J i j) : ℂ)) =
      9 * (1 : Matrix F9 F9 ℂ) i j - (J i j : ℂ)
    push_cast
    simp [Matrix.one_apply]
  have hAA : complexify A * complexify A =
      (1 : Matrix F9 F9 ℂ) + (7 : ℂ) • complexify J := by
    rw [← complexify_mul, A_mul_A]
    ext i j
    simp only [complexify, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    change ((↑((1 : Matrix F9 F9 ℤ) i j + (7 : ℤ) * J i j) : ℂ)) =
      (1 : Matrix F9 F9 ℂ) i j + 7 * (J i j : ℂ)
    push_cast
    simp [Matrix.one_apply]
  have hKA : complexify K * complexify A = complexify A * complexify K := by
    rw [← complexify_mul, ← complexify_mul, K_mul_A]
  have hstarS : star S = S := Complex.conj_ofReal _
  have hstarI : star Complex.I = -Complex.I := Complex.conj_I
  have hstar8 : star ((8 : ℂ)⁻¹) = (8 : ℂ)⁻¹ := by simp
  change ((8 : ℂ)⁻¹ • (S • complexify K + Complex.I • complexify A)) *
    ((8 : ℂ)⁻¹ • (S • complexify K + Complex.I • complexify A))ᴴ = 1
  rw [Matrix.conjTranspose_smul, hstar8, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hstarS, hstarI, hK, hA]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, smul_smul,
    hKK, hAA, hKA, smul_sub, smul_add]
  match_scalars <;> ring_nf <;> norm_num [hS, hI]

theorem C_offDiag_normSq (x y : F9) (h : x ≠ y) : ‖C x y‖ ^ 2 = 1 / 8 := by
  have hA : A x y = 1 := by simp [A, J, h]
  have hK : (K x y : ℝ) ^ 2 = 1 := by exact_mod_cast K_offDiag_sq x y h
  have hS := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  rw [C_apply, hA, ← Complex.normSq_eq_norm_sq, Complex.normSq_div]
  rw [show (Complex.normSq (8 : ℂ)) = 64 by norm_num]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
    Int.cast_one, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
    add_zero, zero_add, mul_one]
  rw [← pow_two (Real.sqrt 7 * (K x y : ℝ)), mul_pow, hS, hK]
  norm_num

end

end AffineNineFinite
