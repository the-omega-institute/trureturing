/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical natural-basis derivation equations and normalized diagonal action. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22095
The existing canonical proof bodies are factored from NondegenerateDerivationBlocks.
Only the original helpers required by that live consumer are exposed. Their old
hypotheses and mathematical meanings are retained; this is no new foundation.
The full dependent-family audits remain unfinished; no blanket exception claimed.
utility none: exact structural derivation equations and Lie maps.
-/

import Mathlib.Algebra.Lie.DirectSum
import D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
import D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers

/-! Natural-basis equations for the actual derivation Lie algebra. The source
bodies and classical ingredients retain their prior credits; the KMV application
is credited to Haobo Ma, then Wenlin Zhang. Semisimple-only implications keep
their semisimplicity hypothesis. -/

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (μ : V →ₗ[k] V →ₗ[k] V) {ι : Type*} (b : Module.Basis ι k V)
private def defect (D : Module.End k V) : V →ₗ[k] V →ₗ[k] V :=
  (LinearMap.compr₂ μ D) - μ.comp D - μ.compl₂ D
private theorem mem_derivations_iff_basis (D : Module.End k V) :
    D ∈ derivations μ ↔ ∀ i j, D (μ (b i) (b j)) = μ (D (b i)) (b j) + μ (b i) (D (b j)) := by
  constructor
  · intro h i j
    exact h (b i) (b j)
  · intro h x y
    have hd : defect μ D = 0 := by
      apply b.ext
      intro i
      apply b.ext
      intro j
      change D (μ (b i) (b j)) - μ (D (b i)) (b j) - μ (b i) (D (b j)) = 0
      rw [h i j]
      abel
    have hh := LinearMap.congr_fun (LinearMap.congr_fun hd x) y
    change D (μ x y) - μ (D x) y - μ x (D y) = 0 at hh
    exact sub_eq_zero.mp (by simpa only [sub_sub] using hh)

variable (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)

include hn in
theorem mul_basis_right [Fintype ι] (x : V) (j : ι) :
    μ x (b j) = b.repr x j • μ (b j) (b j) := by
  classical
  calc
    μ x (b j) = μ (∑ i, b.repr x i • b i) (b j) := by rw [b.sum_repr]
    _ = ∑ i, b.repr x i • μ (b i) (b j) := by
      rw [map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smul₂]
    _ = b.repr x j • μ (b j) (b j) := by
      apply Finset.sum_eq_single j
      · intro i hi hij
        rw [hn i j hij, smul_zero]
      · simp

include hn in
theorem mul_basis_left [Fintype ι] (x : V) (i : ι) :
    μ (b i) x = b.repr x i • μ (b i) (b i) := by
  classical
  calc
    μ (b i) x = μ (b i) (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr x j • μ (b i) (b j) := by
      rw [map_sum]
      simp only [map_smul]
    _ = b.repr x i • μ (b i) (b i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [hn i j hji.symm, smul_zero]
      · simp

include hn in
private theorem off_diagonal_equation [Fintype ι] (D : derivations μ) (i j : ι) (hij : i ≠ j) :
    b.repr (D.val (b i)) j • μ (b j) (b j) +
      b.repr (D.val (b j)) i • μ (b i) (b i) = 0 := by
  have hh := D.property (b i) (b j)
  rw [hn i j hij, map_zero, mul_basis_right μ b hn (D.val (b i)) j,
    mul_basis_left μ b hn (D.val (b j)) i] at hh
  exact hh.symm

include hn in
theorem square_equation [Fintype ι] (D : derivations μ) (i : ι) :
    D.val (μ (b i) (b i)) = (2 * b.repr (D.val (b i)) i) • μ (b i) (b i) := by
  rw [D.property, mul_basis_right μ b hn (D.val (b i)) i,
    mul_basis_left μ b hn (D.val (b i)) i]
  rw [two_mul, add_smul]

include hn in
private theorem natural_derivation_iff_equations [Fintype ι] (D : Module.End k V) :
    D ∈ derivations μ ↔
      (∀ i j, i ≠ j → b.repr (D (b i)) j • μ (b j) (b j) +
        b.repr (D (b j)) i • μ (b i) (b i) = 0) ∧
      (∀ i, D (μ (b i) (b i)) = (2 * b.repr (D (b i)) i) • μ (b i) (b i)) := by
  constructor
  · intro h
    exact ⟨fun i j hij => off_diagonal_equation μ b hn ⟨D, h⟩ i j hij,
      fun i => square_equation μ b hn ⟨D, h⟩ i⟩
  · rintro ⟨hoff, hsq⟩
    apply (mem_derivations_iff_basis μ b D).mpr
    intro i j
    by_cases hij : i = j
    · subst j
      rw [hsq, mul_basis_right μ b hn (D (b i)) i,
        mul_basis_left μ b hn (D (b i)) i, two_mul, add_smul]
    · rw [hn i j hij, map_zero, mul_basis_right μ b hn (D (b i)) j,
        mul_basis_left μ b hn (D (b j)) i]
      exact (hoff i j hij).symm

end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V ι α : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [Fintype ι] (μ : V →ₗ[k] V →ₗ[k] V) (b : Module.Basis ι k V)
variable (label : ι → α) (w : α → V)
variable (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
variable (hsq : ∀ i, μ (b i) (b i) = w (label i))
variable (hw : ∀ a, w a ≠ 0)
variable (hsep : ∀ a c, a ≠ c → ∀ s t : k, s • w a + t • w c = 0 → s = 0 ∧ t = 0)
theorem separate_of_distinct_lines (x y : V) (hx : x ≠ 0) (hy : y ≠ 0)
    (hline : k ∙ x ≠ k ∙ y) (s t : k) (h : s • x + t • y = 0) : s = 0 ∧ t = 0 := by
  have hs : s = 0 := by
    by_contra hs
    have he : x = (-s⁻¹ * t) • y := by
      have hh := congrArg (fun z : V => s⁻¹ • z) (eq_neg_of_add_eq_zero_left h)
      simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul, smul_neg, neg_mul, neg_smul] using hh
    have hcoef : -s⁻¹ * t ≠ 0 := by
      intro hz
      exact hx (by simpa only [hz, zero_smul] using he)
    apply hline
    rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcoef)]
  refine ⟨hs, ?_⟩
  rw [hs, zero_smul, zero_add] at h
  exact (smul_eq_zero.mp h).resolve_right hy

include hn hsq hsep in
theorem derivation_cross_zero (D : derivations μ) (i j : ι) (hij : label i ≠ label j) :
    b.repr (D.val (b i)) j = 0 := by
  have hne : i ≠ j := fun h => hij (congrArg label h)
  have hh := off_diagonal_equation μ b hn D i j hne
  rw [hsq, hsq] at hh
  exact (hsep (label j) (label i) hij.symm _ _ hh).1

include hn hsq hw hsep in
theorem derivation_off_diagonal_skew (D : derivations μ) (i j : ι) (hij : i ≠ j) :
    b.repr (D.val (b i)) j = - b.repr (D.val (b j)) i := by
  by_cases hc : label i = label j
  · have hh := off_diagonal_equation μ b hn D i j hij
    rw [hsq, hsq, hc, ← add_smul] at hh
    exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp hh).resolve_right (hw _))
  · rw [derivation_cross_zero μ b label w hn hsq hsep D i j hc,
      derivation_cross_zero μ b label w hn hsq hsep D j i (Ne.symm hc), neg_zero]

include hn hsq hw in
theorem derivation_diagonal_eq_on_class [CharZero k]
    (D : derivations μ) (i j : ι) (hc : label i = label j) :
    b.repr (D.val (b i)) i = b.repr (D.val (b j)) j := by
  have hi := square_equation μ b hn D i
  have hj := square_equation μ b hn D j
  rw [hsq, hc] at hi
  rw [hsq] at hj
  have hh : (2 * (b.repr (D.val (b i)) i - b.repr (D.val (b j)) j)) •
      w (label j) = 0 := by
    calc
      _ = (2 * b.repr (D.val (b i)) i) • w (label j) -
          (2 * b.repr (D.val (b j)) j) • w (label j) := by rw [mul_sub, sub_smul]
      _ = 0 := by rw [← hi, ← hj, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp
    ((smul_eq_zero.mp hh).resolve_right (hw _))).resolve_left two_ne_zero)

include hn hsq hw hsep in
theorem derivation_bracket_diagonal_zero (D E : derivations μ) (i : ι) :
    b.repr ((⁅D, E⁆ : derivations μ).val (b i)) i = 0 := by
  classical
  have hexp (F G : derivations μ) :
      b.repr (F.val (G.val (b i))) i =
        ∑ j, b.repr (G.val (b i)) j * b.repr (F.val (b j)) i := by
    change b.coord i (F.val (G.val (b i))) = _
    conv_lhs => rw [← b.sum_repr (G.val (b i))]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
  change b.repr (D.val (E.val (b i)) - E.val (D.val (b i))) i = 0
  rw [map_sub, Finsupp.sub_apply, hexp, hexp, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hij : i = j
  · subst j
    ring
  · rw [derivation_off_diagonal_skew μ b label w hn hsq hw hsep E i j hij,
      derivation_off_diagonal_skew μ b label w hn hsq hw hsep D i j hij]
    ring

include hn hsq hw hsep in
theorem semisimple_diagonal_zero [LieAlgebra.IsSemisimple k (derivations μ)]
    (D : derivations μ) (i : ι) : b.repr (D.val (b i)) i = 0 := by
  have hD : D ∈ (⁅(⊤ : LieIdeal k (derivations μ)), (⊤ : LieIdeal k (derivations μ))⁆ :
      LieIdeal k (derivations μ)).toSubmodule := by
    rw [D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.Perfectness.semisimple_perfect]
    trivial
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at hD
  induction hD using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F, G, rfl⟩ := hz
      exact derivation_bracket_diagonal_zero μ b label w hn hsq hw hsep F.val G.val i
  | zero => simp
  | add F G hF hG ihF ihG => simp [ihF, ihG]
  | smul c F hF ihF => simp [ihF]

include hn hsq hw hsep in
theorem properties_of_diagonal_zero
    (D : derivations μ) (hdiag : ∀ i, b.repr (D.val (b i)) i = 0) :
      (∀ i j, label i ≠ label j → b.repr (D.val (b i)) j = 0) ∧
      (∀ i j, b.repr (D.val (b i)) j = - b.repr (D.val (b j)) i) ∧
      (∀ a ∈ Set.range label, D.val (w a) = 0) := by
  refine ⟨fun i j hij => derivation_cross_zero μ b label w hn hsq hsep D i j hij,
    ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [hdiag, neg_zero]
    · exact derivation_off_diagonal_skew μ b label w hn hsq hw hsep D i j hij
  · rintro a ⟨i,rfl⟩
    have hh := square_equation μ b hn D i
    rw [hsq, hdiag, mul_zero, zero_smul] at hh
    exact hh

include hn hsq in
theorem derivation_of_skew_killing (D : Module.End k V)
    (hcross : ∀ i j, label i ≠ label j → b.repr (D (b i)) j = 0)
    (hskew : ∀ i j, b.repr (D (b i)) j = - b.repr (D (b j)) i)
    (hkill : ∀ a ∈ Set.range label, D (w a) = 0) : D ∈ derivations μ := by
  apply (natural_derivation_iff_equations μ b hn D).mpr
  constructor
  · intro i j hij
    by_cases hc : label i = label j
    · rw [hsq, hsq, hc, hskew i j, ← add_smul, neg_add_cancel, zero_smul]
    · rw [hcross i j hc, hcross j i (Ne.symm hc), zero_smul, zero_smul, add_zero]
  · intro i
    rw [hsq, hkill _ ⟨i,rfl⟩]
    have hm : 2 * b.repr (D (b i)) i = 0 := by
      simpa only [two_mul] using eq_neg_iff_add_eq_zero.mp (hskew i i)
    rw [hm, zero_smul]

include hn hsq hw hsep in
theorem semisimple_normalized_derivation_iff [LieAlgebra.IsSemisimple k (derivations μ)]
    (D : Module.End k V) : D ∈ derivations μ ↔
      (∀ i j, label i ≠ label j → b.repr (D (b i)) j = 0) ∧
      (∀ i j, b.repr (D (b i)) j = - b.repr (D (b j)) i) ∧
      (∀ a ∈ Set.range label, D (w a) = 0) := by
  constructor
  · intro hD
    exact properties_of_diagonal_zero μ b label w hn hsq hw hsep ⟨D,hD⟩
      (semisimple_diagonal_zero μ b label w hn hsq hw hsep ⟨D,hD⟩)
  · rintro ⟨hcross,hskew,hkill⟩
    exact derivation_of_skew_killing μ b label w hn hsq D hcross hskew hkill

include hn hsq hw hsep in
/-- The diagonal coefficients of normalized nonzero-square derivations form an
abelian Lie-algebra quotient. No semisimplicity assumption is used. -/
noncomputable def diagonalHom : derivations μ →ₗ⁅k⁆ (ι → k) where
  toFun D i := b.repr (D.val (b i)) i
  map_add' := by intro D E; funext i; simp
  map_smul' := by intro c D; funext i; simp
  map_lie' := by
    intro D E
    funext i
    change b.repr ((⁅D,E⁆ : derivations μ).val (b i)) i = _
    rw [derivation_bracket_diagonal_zero μ b label w hn hsq hw hsep D E i]
    simp [Ring.lie_def, mul_comm]

end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockForm
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
private theorem form_single_left (x : ι → k) (i : ι) :
    (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) (Pi.single i 1) x = x i := by
  simp [Matrix.toLinearMap₂'_apply', dotProduct, Pi.single_apply, Matrix.one_apply]
private theorem form_single_right (x : ι → k) (i : ι) :
    (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) x (Pi.single i 1) = x i := by
  simp [Matrix.toLinearMap₂'_apply', dotProduct, Pi.single_apply, Matrix.one_apply]
theorem skew_iff_coefficients (D : Module.End k (ι → k)) :
    (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k) : LinearMap.BilinForm k (ι → k)).IsSkewAdjoint D ↔
      ∀ i j, D (Pi.single i 1) j = - D (Pi.single j 1) i := by
  constructor
  · intro h i j
    have hh := h (Pi.single i 1) (Pi.single j 1)
    change (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) (D (Pi.single i 1)) (Pi.single j 1) =
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) (Pi.single i 1) (-(D (Pi.single j 1))) at hh
    simpa only [form_single_left, form_single_right, Pi.neg_apply] using hh
  · intro h
    have hz : (LinearMap.comp (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k) : LinearMap.BilinForm k (ι → k)) D) + LinearMap.compl₂ (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k) : LinearMap.BilinForm k (ι → k)) D = 0 := by
      apply (Pi.basisFun k ι).ext
      intro i
      apply (Pi.basisFun k ι).ext
      intro j
      simp only [Pi.basisFun_apply]
      change (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) (D (Pi.single i 1)) (Pi.single j 1) +
        (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) (Pi.single i 1) (D (Pi.single j 1)) = 0
      rw [form_single_left, form_single_right]
      exact eq_neg_iff_add_eq_zero.mp (h i j)
    intro x y
    have hh := LinearMap.congr_fun (LinearMap.congr_fun hz x) y
    change (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) (D x) y + (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) x (D y) = 0 at hh
    change (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) (D x) y = (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix ι ι k)) x (-(D y))
    rw [map_neg]
    exact eq_neg_iff_add_eq_zero.mpr hh

end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockForm

