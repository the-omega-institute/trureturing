/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream finite multiplicative/additive character API. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/FiniteField/CharacterAPI.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.Basic.FiniteProducts
import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField.ResidueField

/-!
# Finite-field characters and Langlands-normalized Gauss sums

Mathlib's `AddChar k ℂ` and `MulChar k ℂ` are the additive characters of `k` and the
zero-extended multiplicative characters of `kˣ`.  This file records the conventions used in
the manuscript, in particular

`τₖ(χ, ψ) = -Gₖ(χ⁻¹, ψ)`.

The ordinary Mathlib Gauss sum is indexed by all of `k`; the value of a multiplicative
character at zero is zero, and `gaussSum_eq_sum_units` makes the equivalent `kˣ`-indexed
formula explicit.  The trace and norm pullbacks below use the maps exported by the residue
field API and are the character inputs for the Hasse--Davenport lift.
-/

open scoped BigOperators ComplexConjugate

namespace LanglandsFirstMainLemma

noncomputable local instance finiteFieldUnitsFintype
    {k : Type*} [Field k] [Finite k] : Fintype kˣ :=
  Fintype.ofFinite kˣ

section Characters

variable (k : Type*) [Field k]

/-- Complex-valued additive characters of a finite field. -/
abbrev FiniteAddChar := AddChar k ℂ

/-- Complex-valued multiplicative characters of a finite field, extended by zero at zero. -/
abbrev FiniteMulChar := MulChar k ℂ

end Characters

section Orthogonality

variable {k : Type*} [Field k] [Fintype k]

/-- Orthogonality for a nontrivial additive character of a finite field. -/
theorem finiteAddChar_sum_eq_zero {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    ∑ x : k, ψ x = 0 :=
  AddChar.sum_eq_zero_of_ne_one hψ

/-- Orthogonality for a nontrivial multiplicative character, extended by zero at zero. -/
theorem finiteMulChar_sum_eq_zero {χ : FiniteMulChar k} (hχ : χ ≠ 1) :
    ∑ x : k, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

/-- Mathlib's ordinary Gauss sum is exactly the manuscript's sum over `kˣ`. -/
theorem gaussSum_eq_sum_units (χ : FiniteMulChar k) (ψ : FiniteAddChar k) :
    gaussSum χ ψ = ∑ x : kˣ, χ x * ψ (x : k) := by
  classical
  rw [gaussSum, Fintype.sum_eq_add_sum_subtype_ne _ 0]
  simp only [MulChar.map_zero, zero_mul, zero_add]
  simpa using
    (Equiv.sum_comp unitsEquivNeZero
      (fun x : {x : k // x ≠ 0} ↦ χ (x : k) * ψ (x : k))).symm

end Orthogonality

section GaussSums

variable {k : Type*} [Field k] [Fintype k]

/-- Langlands's normalized finite-field Gauss sum
`τₖ(χ, ψ) = -∑ x : kˣ, χ(x)⁻¹ ψ(x)`. -/
noncomputable def langlandsGaussSum (χ : FiniteMulChar k) (ψ : FiniteAddChar k) : ℂ :=
  -gaussSum χ⁻¹ ψ

@[simp]
theorem langlandsGaussSum_eq_neg_gaussSum_inv
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) :
    langlandsGaussSum χ ψ = -gaussSum χ⁻¹ ψ :=
  rfl

/-- The explicit `kˣ`-indexed form of Langlands's normalization. -/
theorem langlandsGaussSum_eq_neg_sum_units
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) :
    langlandsGaussSum χ ψ = -∑ x : kˣ, χ⁻¹ x * ψ (x : k) := by
  rw [langlandsGaussSum, gaussSum_eq_sum_units]

/-- The ordinary Gauss sum of the trivial multiplicative character is `-1`. -/
theorem gaussSum_trivial_mulChar {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    gaussSum (1 : FiniteMulChar k) ψ = -1 :=
  gaussSum_one_left hψ

/-- Ueda's normalization has `τₖ(1, ψ) = 1`. -/
@[simp]
theorem langlandsGaussSum_trivial_mulChar {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    langlandsGaussSum (1 : FiniteMulChar k) ψ = 1 := by
  rw [langlandsGaussSum, inv_one, gaussSum_one_left hψ, neg_neg]

/-- Product with the complex conjugate form of the finite-field Gauss-sum magnitude identity. -/
theorem gaussSum_mul_conj {χ : FiniteMulChar k} (hχ : χ ≠ 1)
    {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card k : ℂ) := by
  rw [star_gaussSum_eq]
  exact gaussSum_mul_gaussSum_eq_card hχ (AddChar.IsPrimitive.of_ne_one hψ)

/-- The manuscript's exact magnitude formula `|Gₖ(χ, ψ)|² = |k|`. -/
theorem gaussSum_norm_sq {χ : FiniteMulChar k} (hχ : χ ≠ 1)
    {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card k : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_inj]
  rw [Complex.normSq_eq_conj_mul_self, mul_comm]
  simpa using gaussSum_mul_conj hχ hψ

/-- Every ordinary Gauss sum for a nontrivial additive character is nonzero, including the
trivial multiplicative-character case. -/
theorem gaussSum_ne_zero {χ : FiniteMulChar k} {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    gaussSum χ ψ ≠ 0 := by
  by_cases hχ : χ = 1
  · rw [hχ, gaussSum_one_left hψ]
    exact neg_ne_zero.mpr one_ne_zero
  · have hcard : (Fintype.card k : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card k ≠ 0)
    exact gaussSum_ne_zero_of_nontrivial hcard hχ
      (AddChar.IsPrimitive.of_ne_one hψ)

/-- Every Langlands-normalized Gauss sum for a nontrivial additive character is nonzero. -/
theorem langlandsGaussSum_ne_zero
    (χ : FiniteMulChar k) {ψ : FiniteAddChar k} (hψ : ψ ≠ 1) :
    langlandsGaussSum χ ψ ≠ 0 := by
  rw [langlandsGaussSum]
  exact neg_ne_zero.mpr (gaussSum_ne_zero hψ)

/-- Scaling the additive argument in an ordinary Gauss sum. -/
theorem gaussSum_mulShift_unit (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (a : kˣ) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ :=
  gaussSum_mulShift_eq χ ψ a

/-- Scaling the additive argument in Langlands's normalization contributes `χ(a)`. -/
theorem langlandsGaussSum_mulShift_unit
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (a : kˣ) :
    langlandsGaussSum χ (ψ.mulShift a) = χ a * langlandsGaussSum χ ψ := by
  rw [langlandsGaussSum, langlandsGaussSum, gaussSum_mulShift_eq]
  simp only [inv_inv]
  ring

end GaussSums

section TraceNormPullback

variable (k K : Type*) [Field k] [Field K] [Finite K] [Algebra k K]

/-- Pull an additive character back along the finite-field trace. -/
noncomputable def traceAddChar (ψ : FiniteAddChar k) : FiniteAddChar K :=
  ψ.compAddMonoidHom (residueTrace k K).toAddMonoidHom

omit [Finite K] in
@[simp]
theorem traceAddChar_apply (ψ : FiniteAddChar k) (x : K) :
    traceAddChar k K ψ x = ψ (residueTrace k K x) :=
  rfl

/-- Pull a multiplicative character back along the finite-field norm, with the Mathlib
`MulChar` extension by zero at the unique nonunit of the field. -/
noncomputable def normMulChar (χ : FiniteMulChar k) : FiniteMulChar K :=
  { toFun := fun x ↦ χ (residueNorm k K x)
    map_one' := by simp
    map_mul' := by simp
    map_nonunit' := by
      intro x hx
      have hx0 : x = 0 := by simpa [isUnit_iff_ne_zero] using hx
      subst x
      rw [Algebra.norm_zero]
      exact MulChar.map_zero χ }

@[simp]
theorem normMulChar_apply (χ : FiniteMulChar k) (x : K) :
    normMulChar k K χ x = χ (residueNorm k K x) :=
  rfl

/-- Trace pullback preserves and reflects nontriviality. -/
theorem traceAddChar_ne_one_iff (ψ : FiniteAddChar k) :
    traceAddChar k K ψ ≠ 1 ↔ ψ ≠ 1 := by
  constructor
  · intro h hψ
    apply h
    subst ψ
    ext x
    simp
  · intro hψ h
    apply hψ
    ext y
    obtain ⟨x, hx⟩ := Algebra.trace_surjective k K y
    have hxy := DFunLike.congr_fun h x
    simpa [traceAddChar, hx] using hxy

/-- Norm pullback preserves and reflects nontriviality. -/
theorem normMulChar_ne_one_iff (χ : FiniteMulChar k) :
    normMulChar k K χ ≠ 1 ↔ χ ≠ 1 := by
  constructor
  · intro h hχ
    apply h
    subst χ
    ext x
    simp [normMulChar, MulChar.one_apply (IsUnit.map (residueNorm k K) x.isUnit)]
  · intro hχ h
    apply hχ
    ext a
    obtain ⟨b, hb⟩ := FiniteField.unitsMap_norm_surjective k K a
    have hb' := DFunLike.congr_fun h (b : K)
    have hbval : residueNorm k K (b : K) = (a : k) := congrArg Units.val hb
    simpa [normMulChar, hbval] using hb'

@[simp]
theorem normMulChar_inv (χ : FiniteMulChar k) :
    normMulChar k K χ⁻¹ = (normMulChar k K χ)⁻¹ := by
  ext x
  change χ⁻¹ (residueNorm k K (x : K)) = (normMulChar k K χ)⁻¹ (x : K)
  rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv']
  rfl

end TraceNormPullback

end LanglandsFirstMainLemma
