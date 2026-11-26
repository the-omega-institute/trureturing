import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.ExpSurjective
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Discrete series character on the compact Cartan by orbital integrals; formal degree
(known result; see Lib.DiscreteSeries.Character.FormalDegree).

Part of: Weyl character and dimension formulas for U(n) and products of unitary groups (known
result; see Lib.DiscreteSeries.Character.KTypeMultiplicity).

This file: Laurent polynomials on the torus, Weyl denominators, alternants, leading monomials,
density. -/

noncomputable section

namespace Orbital

open Matrix Finset Int AddMonoidAlgebra UnitAddTorus AddCircle Equiv Function HCParam
variable {n} [Fintype.{0} n] (ε : n → ℤˣ) (l : n → ℤ)

/-- For a tuple x of unit complex numbers, the algebra homomorphism from Laurent polynomials to
ℂ sending the monomial of exponent ν to ∏ x_a^{ν_a}. -/
def torusEval (x : n → Circle) : ℂ[n → ℤ] →ₐ[ℂ] ℂ := lift ℂ ℂ _
  ⟨⟨(∏ a, x a ^ ·.toAdd a), by simp⟩, by simp [zpow_add₀]⟩

/-- The finite set of pairs of indices (a,b) with ε_a = +1 and ε_b = −1. -/
def oppositePairs := univ.filter (ε · = 1) ×ˢ univ.filter (ε · ≠ 1)

/-- The Laurent polynomial Σ sgn(w) x^(l∘w), summed over the permutations w that preserve the
signs ε (the Weyl group of K). -/
def alternant : ℂ[n → ℤ] := ∑ w : Perm n, ite (ε ∘ w = ε) (.single (l ∘ w) w.sign) 0

/-- The function t on ℤⁿ is antisymmetric under the Weyl group of K: t(γ∘w) = sgn(w) t(γ) for
permutations w preserving ε. -/
def IsWeylAntisymm (t : (n → ℤ) → ℂ) := ∀ w : Perm n, ε ∘ w = ε → ∀ γ, t (γ ∘ w) = w.sign * t γ

/-- The monoid of pairs (a, P), P a Laurent polynomial with coefficient 1 at x^a whose exponents
γ are all ≥ 0 and satisfy ⟨l,γ⟩ < ⟨l,a⟩ unless γ = a. -/
def leadingMonomials : Submonoid (Multiplicative (n → ℤ) × ℂ[n → ℤ]) := ⟨⟨{p | p.2.1 p.1.toAdd = 1 ∧
  ∀ γ, p.2.1 γ ≠ 0 → 0 ≤ γ ∧ (γ = p.1.toAdd ∨ l ⬝ᵥ γ < l ⬝ᵥ p.1.toAdd)}, @fun a b ↦ by simp; grind
  [by simpa [subset_iff, mem_add] using a.2.support_coeff_mul_subset b.2, UniqueAdd, add_nonneg,
  coeff_mul_add_of_uniqueAdd, dotProduct_add, dotProduct_add l a.1.toAdd b.1.toAdd]⟩,
  by simp [← Finsupp.mem_support_iff]⟩

variable {ε} (l : HCParam ε) (r) [DecidableRel r] {ν ν'} {P Q : ℂ[n → ℤ]} (w : Perm n)

/-- The Laurent polynomial ∏ (x_a − x_b) over the pairs (a, b) with r(ε_a, ε_b) and l_b < l_a,
for a relation r on signs. -/
def _root_.HCParam.rootProd : ℂ[n → ℤ] := ∏ a, ∏ b with r (ε a) (ε b) ∧ l b < l a,
  (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1)

/-- For a relation r on signs and an index a, the number of indices b with r(ε_a, ε_b) and l_b <
l_a, as an integer. -/
def _root_.HCParam.lowerCount a := (#{b | r (ε a) (ε b) ∧ l b < l a} : ℤ)

attribute [local simp low] lift_apply' Finsupp.sum funext_iff torusEval IsKDominant IsWeylAntisymm
  mFourier rootProd toCircle_zsmul
  oppositePairs Finsupp.linearCombination sum_ite Matrix.mul_apply diagonal

lemma rootProd_mem_leadingMonomials o (h : ∀ a b, l b < l a → o b < o a := by simp_all) : (.ofAdd
  (l.lowerCount r), l.rootProd r) ∈ leadingMonomials o := pi_eq_sum_univ' (l.lowerCount r) ▸ by
  simp_rw [rootProd, lowerCount, cast_card, sum_smul, ofAdd_sum, prod_mk_prod, prod_sigma']
  exact prod_mem (by simp [leadingMonomials, -funext_iff]; grind [=_ dotProduct_single_one o,
    Pi.single_nonneg])

lemma torusEval_rootProd_ne_zero {x} : Injective x →
  torusEval x (l.rootProd r) ≠ 0 := by simp [prod_eq_zero_iff]; grind [Circle.ext]

lemma alternant_apply γ : (alternant ε ν).1 γ = ∑ w : Perm n,
  ite (ε ∘ w = ε ∧ ν ∘ w = γ) ↑w.sign 0 := by simp [alternant, ite_and, Finsupp.single_apply]

/-- At a point x of the torus, the alternant Σ sgn(w) x^{ν∘w} over the permutations w preserving ε
equals the determinant of the matrix with (a,b) entry x_a^{ν_b} if ε_a = ε_b and 0 otherwise. -/
lemma torusEval_alternant x : torusEval x (alternant ε ν) = det (of fun a b ↦ ite (ε a = ε b) ((x
  a).1 ^ ν b) 0) := .trans (by simp [alternant, det_apply', prod_ite_zero, comm]) (det_transpose _)

@[fun_prop] lemma continuous_torusEval : Continuous (torusEval · P) := by continuity

lemma eq_of_torusEval_eq (h : ∀ x, torusEval x P = torusEval x Q) : P = Q :=
  ext (orthonormal_mFourier.linearIndependent.of_comp _ (by aesop))

/-- Weierstrass approximation on a torus: Laurent polynomials are uniformly dense in the
continuous complex functions on (S¹)ⁿ. -/
lemma denseRange_torusEval : DenseRange fun P ↦ ContinuousMap.mk (@torusEval n _ · P) :=
  ((Homeomorph.arrowCongr
  (.piCongrRight fun _ ↦ homeomorphCircle (by simp)) 1).isDenseEmbedding.dense_image.2
  fun _ ↦ span_mFourier_closure_eq_top.ge ⟨⟩).mono (by simpa [Set.subset_def, Homeomorph.arrowCongr,
  ← Finsupp.range_linearCombination] using (⟨⟨·⟩, by ext; simp [← homeomorphCircle_apply]⟩))

lemma torusEval_comp_perm x : torusEval (x ∘ w) P =
  torusEval x ⟨P.1.equivMapDomain (w.arrowCongr 1)⟩ := by simp [-Finsupp.sum]; grind [w.prod_comp]

lemma torusEval_comp_eq_mul_iff {c} : (∀ x, torusEval (x ∘ w) P = c * torusEval x P) ↔ ∀ ν,
  P.1 (ν ∘ w) = c * P.1 ν := by simpa [↓torusEval_comp_perm, ← coeff_inj,
  Finsupp.ext_iff] using! Iff.intro (eq_of_torusEval_eq (Q := c • P)) (by lia)

lemma isWeylAntisymm_alternant : IsWeylAntisymm ε (alternant ε ν).1 := by simp_all
  [↓torusEval_alternant, ← torusEval_comp_eq_mul_iff, ← det_permute, submatrix]

variable {l w} (hl : l.Injective) (x)

/-- If f on the diagonal torus and d on K satisfy d(yxy⁻¹) = f(x) for all y in K and x in the
torus, then f is invariant under every permutation w of the coordinates that preserves the
signs ε. -/
lemma apply_comp_perm_of_conj_invariant (hw : ε ∘ w = ε) {d f : _ → ℂ} (h : ∀ (y : maxCompactU ε) x,
  d (y * diagTorusK x * y⁻¹) = f x) :
  f (x ∘ w) = f x := h ⟨⟨permMatrixHom.toHomUnits w, ext (by simp_all [signMatrix])⟩,
  ext (by simp)⟩ _ ▸ h 1 _ ▸ congr(d $(by ext; simp [diagTorus, ← map_inv]))

include hl

lemma torusEval_rootProd_noncompact : torusEval x (l.rootProd Ne) =
  (∏ p ∈ oppositePairs ε, ite (l p.2 < l p.1) 1 (-1)) * ∏ p ∈ oppositePairs ε, (x p.1 - x
  p.2 : ℂ) := by simp [← prod_mul_distrib, prod_sigma']; apply prod_bij fun ⟨a, b⟩ _ ↦ ite (ε a = 1)
                   (a, b) (b, a) <;> simp <;> grind [units_eq_one_or (ε _)]

lemma torusEval_rootProd_noncompact_comp (hw : ε ∘ w = ε) x : torusEval (x ∘ w) (l.rootProd Ne) =
  torusEval x (l.rootProd Ne) :=
  by simp_all [↓torusEval_rootProd_noncompact]; rw [prod_equiv (w.prodCongr w)] <;> aesop

lemma alternant_coeff_of_isKDominant (h : IsKDominant ε (-l) ν) (h' : IsKDominant ε (-l) ν') :
    (alternant ε (ν + l.lowerCount Eq)).1 (ν' + l.lowerCount Eq) = ite (ν' = ν) 1 0 := by
  rw [alternant_apply, sum_eq_single 1 fun w _ _ ↦ ?_] <;> simp [comm]
  have ⟨i, k⟩ := w.support.exists_max_image l (by_contra (by simpa))
  have (i j) h : (_ on l.lowerCount Eq) j i :=
    ofNat_lt.2 (card_lt_card ⟨by grind, mt (@· j h) (by simp)⟩)
  simp_all; grind -ext [w.surjective i]

lemma exists_sign_isKDominant γ : ∃ᵉ (s : ℤ) (ν), IsKDominant ε (-l) ν ∧
    ∀ t, IsWeylAntisymm ε t → t γ = s * t (ν + l.lowerCount Eq) := by
  obtain ⟨i, j, c⟩ | c := em (∃ i j, ε i = ε j ∧ γ i = γ j ∧ i ≠ j)
  use 0, 0, by simp, fun t h ↦ by
    simpa [*, self_eq_neg, comp_def, apply_swap_eq_self] using (h (swap i j) · γ)
  let := LinearOrder.lift' l hl
  have ⟨w, h⟩ := exists_min_image {w : Perm n | ε ∘ w = ε} (toLex <| γ ∘ ·) ⟨1, by simp⟩
  have (a b) (e : ε a = ε b ∧ l a ≤ l b) :=
    (h.2 (w * _) (by simp_all [apply_swap_eq_self])).not_gt ∘ Pi.lex_desc (f := γ ∘ w) e.2
  use w.sign, γ ∘ w - l.lowerCount Eq
  simp_all [lowerCount, ← mul_assoc, ← cast_mul]; intros
  grw [sub_add, ← cast_card_sdiff, card_le_card_of_injOn (γ ∘ w), card_Ico_of_le, sub_sub_cancel]
    <;> (try intro) <;> grind [w.injective]
