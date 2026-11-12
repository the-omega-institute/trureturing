/- GID: D5/S3/Topology/EJADefiniteDomain
   generality: G
   mirror-B: D5/B/S3/Topology/EJADefiniteDomain
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic]
   utility: none
   digest: Positive unital maps of original finite real EJAs have Jordan definite domains. -/

module

public import D5.S3.Topology.EJASpectralNorm
public import D5.S3.Topology.JBSquareDefect

/-! The complete zero-square-defect domain and Jordan-generating propagation. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.EJADefiniteDomain
open scoped BigOperators
open JBPositiveShift

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y]
  {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}
  {T : Y →ₗ[ℝ] Y →ₗ[ℝ] Y} {v : Y}

/-- Jordan generation is closure under real linear combinations, the unit and products.
The generating set need not linearly span the original carrier. -/
def JordanGenerates (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (u : X) (s : Set X) : Prop :=
  ∀ V : Submodule ℝ X, u ∈ V → s ⊆ V →
    (∀ a ∈ V, ∀ b ∈ V, S a b ∈ V) → V = ⊤

/-- The full mixed multiplicative domain as a real submodule. -/
def mixedDomain (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y →ₗ[ℝ] Y)
    (Φ : X →ₗ[ℝ] Y) : Submodule ℝ X where
  carrier := {a | ∀ x, Φ (S a x) = T (Φ a) (Φ x)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    simp only [map_add, LinearMap.add_apply, ha x, hb x]
  smul_mem' := by
    intro t a ha x
    simp only [map_smul, LinearMap.smul_apply, ha x]

/-- Quadratic representations preserve actual squares on the original EJA carrier.
The JB norm is constructed on a type copy and is not an extra hypothesis on Y. -/
theorem quadratic_preserves_squares (B : EJAFiniteSpectral.Data Y T v) (a x : Y) :
    ∃ y, T y y = quadratic T a (T x x) := by
  obtain ⟨y, hy⟩ := JBComplexification.quadratic_preserves_squares
    (EJASpectralNorm.jb_data B) ((EJASpectralNorm.equiv B).symm a)
    ((EJASpectralNorm.equiv B).symm x)
  exact ⟨EJASpectralNorm.equiv B y, hy.symm⟩

private theorem finite_spectra (A : EJAFiniteSpectral.Data X S u) :
    JBSquareDefect.HasFiniteSpectralResolutions S u := by
  intro a
  obtain ⟨n, e, r, he, _, heu, hea, heaa, _⟩ := EJAFiniteSpectral.finite_spectral_resolution A a
  exact ⟨n, e, r, he, heu, hea, by simpa only [pow_two] using heaa⟩

/-- Square-defect positivity for every real element of the original source EJA. -/
theorem square_defect (A : EJAFiniteSpectral.Data X S u)
    (B : EJAFiniteSpectral.Data Y T v) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (hpos : ∀ x, ∃ y, T y y = Φ (S x x)) (a : X) :
    ∃ z, T z z = Φ (S a a) - T (Φ a) (Φ a) := by
  let Ψ : X →ₗ[ℝ] EJASpectralNorm.Space B := (EJASpectralNorm.equiv B).symm.toLinearMap.comp Φ
  obtain ⟨z, hz⟩ := JBSquareDefect.square_defect_of_spectral
    (EJASpectralNorm.jb_data B) (finite_spectra A) Ψ hunit hpos a
  exact ⟨EJASpectralNorm.equiv B z, hz⟩

/-- Zero square defect forces the full mixed identity, with no restriction on x. -/
theorem mixed_of_zero_defect (A : EJAFiniteSpectral.Data X S u)
    (B : EJAFiniteSpectral.Data Y T v) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (hpos : ∀ x, ∃ y, T y y = Φ (S x x))
    (a : X) (ha : Φ (S a a) - T (Φ a) (Φ a) = 0) (x : X) :
    Φ (S a x) = T (Φ a) (Φ x) := by
  let Ψ : X →ₗ[ℝ] EJASpectralNorm.Space B := (EJASpectralNorm.equiv B).symm.toLinearMap.comp Φ
  exact JBSquareDefect.zero_defect_cross (EJASpectralNorm.jb_data B) A.symm Ψ
    (fun a => square_defect A B Φ hunit hpos a) a ha x

private theorem domain_square (A : EJAFiniteSpectral.Data X S u)
    (B : EJAFiniteSpectral.Data Y T v) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (hpos : ∀ x, ∃ y, T y y = Φ (S x x))
    {a : X} (ha : a ∈ mixedDomain S T Φ) : S a a ∈ mixedDomain S T Φ := by
  intro x
  apply mixed_of_zero_defect A B Φ hunit hpos
  have h1 : Φ (S a a) = T (Φ a) (Φ a) := ha a
  rw [A.jordan a a, ha, ha, h1, ← B.jordan (Φ a) (Φ a), sub_self]

/-- The zero-square-defect domain is a unital real Jordan subalgebra.
Here it is represented by its equivalent full mixed multiplicative-domain submodule. -/
theorem domain_jordan_closed (A : EJAFiniteSpectral.Data X S u)
    (B : EJAFiniteSpectral.Data Y T v) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (hpos : ∀ x, ∃ y, T y y = Φ (S x x)) :
    u ∈ mixedDomain S T Φ ∧
      ∀ a ∈ mixedDomain S T Φ, ∀ b ∈ mixedDomain S T Φ,
        S a b ∈ mixedDomain S T Φ := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [A.unit_mul, hunit, B.unit_mul]
  · intro a ha b hb
    let V := mixedDomain S T Φ
    have hab := domain_square A B Φ hunit hpos (V.add_mem ha hb)
    have haa := domain_square A B Φ hunit hpos ha
    have hbb := domain_square A B Φ hunit hpos hb
    have he : S a b = (1 / 2 : ℝ) • (S (a + b) (a + b) - S a a - S b b) := by
      simp only [map_add, LinearMap.add_apply, A.symm b a]
      module
    rw [he]
    exact V.smul_mem _ (V.sub_mem (V.sub_mem hab haa) hbb)

/-- Preserving idempotents on a Jordan-generating set propagates to all real products.
No linear-spanning, matrix, simplicity, injectivity or nonzero-image assumption is added. -/
theorem multiplicative_of_jordan_generating (A : EJAFiniteSpectral.Data X S u)
    (B : EJAFiniteSpectral.Data Y T v) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (hpos : ∀ x, ∃ y, T y y = Φ (S x x))
    (s : Set X) (hgen : JordanGenerates S u s)
    (hid : ∀ e ∈ s, S e e = e ∧ T (Φ e) (Φ e) = Φ e) :
    ∀ a x, Φ (S a x) = T (Φ a) (Φ x) := by
  obtain ⟨hu, hmul⟩ := domain_jordan_closed A B Φ hunit hpos
  have hs : s ⊆ mixedDomain S T Φ := by
    intro e he x
    apply mixed_of_zero_defect A B Φ hunit hpos e _ x
    rw [(hid e he).1, (hid e he).2, sub_self]
  have htop := hgen (mixedDomain S T Φ) hu hs hmul
  intro a x
  have ha : a ∈ mixedDomain S T Φ := by rw [htop]; trivial
  exact ha x

#print axioms multiplicative_of_jordan_generating

end D5.S3.Topology.EJADefiniteDomain
