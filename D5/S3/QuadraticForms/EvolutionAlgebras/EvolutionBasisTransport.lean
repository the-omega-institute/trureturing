/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Basis transport conjugates all bilinear multiplication automorphisms and transfers joint quotient control to arbitrary finite dimensional modules. -/

import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl

/- Escape audit for the newly public owner lemmas is unfinished: https://github.com/the-omega-institute/trureturing/issues/22095 -/

/-! Pair-product spans, natural bases and complete automorphism groups are invariant under linear transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport

open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open D5.S3.FiniteGroups.SuccessorQuotient
open D5.S3.FiniteGroups.SuccessorPowerAssignments

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- All pair products span this subspace; no associativity or unit is assumed. -/
def productSpan (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) : Submodule ℂ A :=
  Submodule.span ℂ {z | ∃ x y, μ x y = z}

/-- Bilinear multiplication transported by a complex linear equivalence. -/
def transportProduct (e : A ≃ₗ[ℂ] B) (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) : B →ₗ[ℂ] B →ₗ[ℂ] B :=
  (μ.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap).compr₂ e.toLinearMap

private theorem transport_apply (e : A ≃ₗ[ℂ] B) (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : B) :
    transportProduct e μ x y = e (μ (e.symm x) (e.symm y)) := rfl

/-- The full pair-product span is transported exactly. -/
theorem product_span_transport (e : A ≃ₗ[ℂ] B) (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) :
    (productSpan μ).map e.toLinearMap = productSpan (transportProduct e μ) := by
  rw [productSpan, Submodule.map_span, productSpan]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨x, y, rfl⟩, rfl⟩
    exact ⟨e x, e y, by simp [transportProduct]⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨μ (e.symm x) (e.symm y), ⟨_, _, rfl⟩, rfl⟩

/-- Conjugation is a group equivalence on all multiplication-preserving linear equivalences. -/
noncomputable def automorphismConjugacy (e : A ≃ₗ[ℂ] B)
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) : Aut μ ≃* Aut (transportProduct e μ) where
  toFun f := ⟨e.symm.trans (f.val.trans e), by
    intro x y
    change e (f.val (e.symm (transportProduct e μ x y))) =
      transportProduct e μ (e (f.val (e.symm x))) (e (f.val (e.symm y)))
    simp only [transport_apply, LinearEquiv.symm_apply_apply]
    exact congrArg e (f.property (e.symm x) (e.symm y))⟩
  invFun g := ⟨e.trans (g.val.trans e.symm), by
    intro x y
    have h := g.property (e x) (e y)
    apply e.injective
    simpa [transportProduct, LinearEquiv.trans_apply] using h⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    simp
  right_inv g := by
    apply Subtype.ext
    ext x
    simp
  map_mul' f g := by
    apply Subtype.ext
    ext x
    simp

private theorem coordinate_perfect_iff {n : ℕ} (μ : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (b : Module.Basis (Fin n) ℂ A) :
    perfect (transportProduct b.equivFun μ) ↔ productSpan μ = ⊤ := by
  have hn : square (transportProduct b.equivFun μ) ⊤ =
      productSpan (transportProduct b.equivFun μ) := by
    simp only [square, productSpan, Submodule.mem_top, true_and]
  rw [perfect, hn, ← product_span_transport]
  simpa using (Submodule.map_eq_top_iff b.equivFun.range (p := productSpan μ))

/-- A basis is natural precisely when its coordinate basis is natural for the transported product. -/
theorem natural_basis_transport_iff {n : ℕ} (μ : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (b : Module.Basis (Fin n) ℂ A) :
    (∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) ↔
      (∀ i j : Fin n, i ≠ j → transportProduct b.equivFun μ
        (Pi.basisFun ℂ (Fin n) i) (Pi.basisFun ℂ (Fin n) j) = 0) := by
  classical
  have hb (i : Fin n) : b.equivFun (b i) = Pi.basisFun ℂ (Fin n) i := by
    ext j
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have he (i j : Fin n) : transportProduct b.equivFun μ
      (Pi.basisFun ℂ (Fin n) i) (Pi.basisFun ℂ (Fin n) j) =
        b.equivFun (μ (b i) (b j)) := by
    rw [← hb i, ← hb j, transport_apply]
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  constructor
  · intro h i j hij
    rw [he, h i j hij, map_zero]
  · intro h i j hij
    apply b.equivFun.injective
    rw [map_zero, ← he]
    exact h i j hij


/-- Reindex an arbitrary finite natural basis by the declared dimension. -/
noncomputable def dimensionBasis [FiniteDimensional ℂ A] {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : Module.finrank ℂ A = n) (b : Module.Basis ι ℂ A) :
    Module.Basis (Fin n) ℂ A :=
  b.reindex (Fintype.equivFinOfCardEq ((Module.finrank_eq_card_basis b).symm.trans hn))

theorem dimensionBasis_natural [FiniteDimensional ℂ A] {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : Module.finrank ℂ A = n) (μ : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (b : Module.Basis ι ℂ A) (hb : ∀ i j : ι, i ≠ j → μ (b i) (b j) = 0) :
    ∀ i j : Fin n, i ≠ j → μ (dimensionBasis hn b i) (dimensionBasis hn b j) = 0 := by
  intro i j hij
  simp only [dimensionBasis, Module.Basis.reindex_apply]
  apply hb
  exact (Equiv.injective _).ne hij

/-- Joint quotient control for every n-dimensional complex module and every finite natural basis.
The whole algebra group is finite before its natural cardinality is bounded. -/
theorem finite_and_joint_bound [FiniteDimensional ℂ A] {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : Module.finrank ℂ A = n) (μ : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (b : Module.Basis ι ℂ A)
    (hb : ∀ i j : ι, i ≠ j → μ (b i) (b j) = 0)
    (hp : productSpan μ = ⊤) :
    let bₙ := dimensionBasis hn b
    let ν := transportProduct bₙ.equivFun μ
    let c := Pi.basisFun ℂ (Fin n)
    let hc := (natural_basis_transport_iff μ bₙ).mp (dimensionBasis_natural hn μ b hb)
    let hν := (coordinate_perfect_iff μ bₙ).mpr hp
    let R := supportRelation ν c
    let β := beta R (support_positive_degrees ν c hc hν).1
      (support_positive_degrees ν c hc hν).2
    letI := Fintype.ofFinite (Blocks R)
    Finite (Aut μ) ∧ Nat.card (Aut μ) ≤
      cycleWeight β * Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm (Blocks R)))) *
        ∏ q : Blocks R, (Nat.card (Fiber R q)).factorial := by
  classical
  dsimp only
  let bₙ := dimensionBasis hn b
  let ν := transportProduct bₙ.equivFun μ
  let c := Pi.basisFun ℂ (Fin n)
  have hc := (natural_basis_transport_iff μ bₙ).mp (dimensionBasis_natural hn μ b hb)
  have hν := (coordinate_perfect_iff μ bₙ).mpr hp
  haveI : Finite (Aut ν) := automorphism_finite ν c hc hν
  haveI : Finite (Aut μ) := Finite.of_equiv (Aut ν) (automorphismConjugacy bₙ.equivFun μ).toEquiv.symm
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr (automorphismConjugacy bₙ.equivFun μ).toEquiv]
  exact automorphism_quotient_bound ν c hc hν

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
