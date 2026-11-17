/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.claim; result=D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.result; claim=D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.claim
   digest: Hereditary evolution algebras need not have a hereditary direct sum. -/

/-
admission_basis: open-problem-resolution (#21985; Refuted)
escape_witness: none
Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  declaration statement_id:
  sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The source definitions retain the intrinsic natural-basis and componentwise-product
expressions of Question 12; proofs use Mathlib restriction, product and orthogonal-basis owners.
inheritedProduct:
  proof_shape: bind-only
  escape_witness: none
  consumers: Hereditary, inheritedProduct_val, subProd.
  Direct frozen dependencies: none.
Hereditary:
  proof_shape: bind-only
  escape_witness: none
  consumers: claim, rank_one_hereditary, result.
  Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  declaration statement_id:
  sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d.
directSumProduct:
  proof_shape: bind-only
  escape_witness: none
  consumers: claim, prod.
  Direct frozen dependencies: none.
claim:
  proof_shape: bind-only
  escape_witness: none
  consumers: result.
  Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  declaration statement_id:
  sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d.
inheritedProduct_val:
  proof_shape: bind-only
  escape_witness: none
  consumers: rank_one_hereditary, product_readouts.
  Direct frozen dependencies: none.
rank_one_hereditary:
  proof_shape: bind-only
  escape_witness: none
  consumers: result.
  Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  declaration statement_id:
  sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d.
rank_one_evolution:
  proof_shape: bind-only
  escape_witness: none
  consumers: result.
  Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  declaration statement_id:
  sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d.
readouts_proportional:
  proof_shape: bind-only
  escape_witness: none
  consumers: coupled_not_evolution.
  Direct frozen dependencies: none.
scalarA:
  proof_shape: bind-only
  escape_witness: none
  consumers: mu, result.
  Direct frozen dependencies: none.
scalarB:
  proof_shape: bind-only
  escape_witness: none
  consumers: nu, result.
  Direct frozen dependencies: none.
u:
  proof_shape: bind-only
  escape_witness: none
  consumers: mu, coupled_closed, result.
  Direct frozen dependencies: none.
v:
  proof_shape: bind-only
  escape_witness: none
  consumers: nu, coupled_closed, result.
  Direct frozen dependencies: none.
mu:
  proof_shape: bind-only
  escape_witness: none
  consumers: prod, result.
  Direct frozen dependencies: none.
nu:
  proof_shape: bind-only
  escape_witness: none
  consumers: prod, result.
  Direct frozen dependencies: none.
prod:
  proof_shape: bind-only
  escape_witness: none
  consumers: coupled_closed, subProd, result.
  Direct frozen dependencies: none.
coupled:
  proof_shape: bind-only
  escape_witness: none
  consumers: coupled_closed, subProd, f, g, x, y, result.
  Direct frozen dependencies: none.
coupled_closed:
  proof_shape: bind-only
  escape_witness: none
  consumers: subProd, result.
  Direct frozen dependencies: none.
subProd:
  proof_shape: bind-only
  escape_witness: none
  consumers: product_readouts, coupled_not_evolution.
  Direct frozen dependencies: none.
f:
  proof_shape: bind-only
  escape_witness: none
  consumers: product_readouts, coupled_not_evolution.
  Direct frozen dependencies: none.
g:
  proof_shape: bind-only
  escape_witness: none
  consumers: product_readouts, coupled_not_evolution.
  Direct frozen dependencies: none.
product_readouts:
  proof_shape: bind-only
  escape_witness: none
  consumers: coupled_not_evolution.
  Direct frozen dependencies: none.
x:
  proof_shape: bind-only
  escape_witness: none
  consumers: coupled_not_evolution.
  Direct frozen dependencies: none.
y:
  proof_shape: bind-only
  escape_witness: none
  consumers: coupled_not_evolution.
  Direct frozen dependencies: none.
coupled_not_evolution:
  proof_shape: bind-only
  escape_witness: none
  consumers: result.
  Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  declaration statement_id:
  sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d.
result:
  proof_shape: bind-only
  escape_witness: none
  consumers: none.
  Direct frozen dependencies:
  D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  declaration statement_id:
  sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d.
-/

import D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic

set_option autoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DirectSumHeredityRefutation

open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction

variable {K V W : Type} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The inherited multiplication on a linear subspace closed under multiplication.
No associativity, identity element, or extension of a natural basis is imposed. -/
noncomputable def inheritedProduct (μ : V →ₗ[K] V →ₗ[K] V) (S : Submodule K V)
    (closed : ∀ (x y : V), x ∈ S → y ∈ S → μ x y ∈ S) :
    S →ₗ[K] S →ₗ[K] S :=
  (μ.domRestrict₁₂ S S).codRestrict₂ S.subtype Subtype.val_injective
    (fun x y => ⟨⟨μ x.val y.val, closed x.val y.val x.property y.property⟩, rfl⟩)

/-- Question 12: every subalgebra is intrinsically an evolution algebra.
`IsEvolutionAlgebra` is the existing D5 definition using an actual `Module.Basis`.
The quantification includes the zero subalgebra and the whole algebra. -/
def Hereditary (μ : V →ₗ[K] V →ₗ[K] V) : Prop :=
  ∀ (S : Submodule K V)
    (closed : ∀ (x y : V), x ∈ S → y ∈ S → μ x y ∈ S),
    IsEvolutionAlgebra (inheritedProduct μ S closed)

/-- The finite direct sum, with componentwise bilinear multiplication. -/
def directSumProduct (μ : V →ₗ[K] V →ₗ[K] V) (ν : W →ₗ[K] W →ₗ[K] W) :
    (V × W) →ₗ[K] (V × W) →ₗ[K] (V × W) :=
  (LinearMap.prodMapLinear K V W V W (S := K)).comp (μ.prodMap ν)

/-- The affirmative assertion in the direct-sum clause of Question 12 only.
Every finite-dimensional vector space has a coordinate presentation `Fin m → K`.
The field is arbitrary; the counterexample is over the rational field. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] (m n : ℕ)
    (μ : (Fin m → K) →ₗ[K] (Fin m → K) →ₗ[K] (Fin m → K))
    (ν : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K)),
    IsEvolutionAlgebra μ → IsEvolutionAlgebra ν →
      Hereditary μ → Hereditary ν → Hereditary (directSumProduct μ ν)

end D5.S3.QuadraticForms.EvolutionAlgebras.DirectSumHeredityRefutation

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DirectSumHeredityRefutation
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private theorem inheritedProduct_val (μ : V →ₗ[K] V →ₗ[K] V) (S : Submodule K V)
    (closed : ∀ (x y : V), x ∈ S → y ∈ S → μ x y ∈ S) (x y : S) :
    (inheritedProduct μ S closed x y).val = μ x.val y.val := by
  exact LinearMap.codRestrict₂_apply (μ.domRestrict₁₂ S S) S.subtype
    Subtype.val_injective
    (fun a b => ⟨⟨μ a.val b.val, closed a.val b.val a.property b.property⟩, rfl⟩) x y

private theorem rank_one_hereditary [FiniteDimensional K V] [Invertible (2 : K)]
    (B : LinearMap.BilinForm K V) (w : V) (hB : LinearMap.IsSymm B) :
    Hereditary ((B.compr₂ ((LinearMap.id : K →ₗ[K] K).smulRight w))) := by
  classical
  intro S closed
  let C := B.domRestrict₁₂ S S
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (hB.domRestrict S :
    LinearMap.IsSymm C)
  constructor
  · intro x y
    apply Subtype.ext
    rw [inheritedProduct_val, inheritedProduct_val]
    change B x.val y.val • w = B y.val x.val • w
    exact congrArg (fun c : K => c • w) (by simpa using hB.eq _ _)
  · refine ⟨Fin (Module.finrank K S), b, ?_⟩
    intro i j hij
    apply Subtype.ext
    rw [inheritedProduct_val]
    change C (b i) (b j) • w = 0
    rw [hb hij, zero_smul]

private theorem rank_one_evolution [FiniteDimensional K V] [Invertible (2 : K)]
    (B : LinearMap.BilinForm K V) (w : V) (hB : LinearMap.IsSymm B) :
    IsEvolutionAlgebra ((B.compr₂ ((LinearMap.id : K →ₗ[K] K).smulRight w))) := by
  classical
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  refine ⟨?_, Fin (Module.finrank K V), b, ?_⟩
  · intro x y
    change B x y • w = B y x • w
    exact congrArg (fun c : K => c • w) (by simpa using hB.eq _ _)
  · intro i j hij
    change B (b i) (b j) • w = 0
    rw [hb hij, zero_smul]


-- Basis orthogonality forces proportional scalar readouts.
private theorem readouts_proportional {ι : Type} (b : Module.Basis ι K V)
    (f g : V →ₗ[K] K) (hf : f ≠ 0)
    (horth : ∀ i j, i ≠ j →
      f (b i) * f (b j) = 0 ∧
        g (b i) * f (b j) + f (b i) * g (b j) = 0) :
    ∃ c : K, g = c • f := by
  classical
  have hex : ∃ i, f (b i) ≠ 0 := by
    by_contra h
    apply hf
    apply b.ext
    intro i
    simpa using (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hex
  refine ⟨g (b i) / f (b i), ?_⟩
  apply b.ext
  intro j
  by_cases hij : i = j
  · subst j
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp
  · obtain ⟨hff, hgf⟩ := horth i j hij
    have hfj : f (b j) = 0 := (mul_eq_zero.mp hff).resolve_left hi
    have hgj : g (b j) = 0 := by
      rw [hfj, mul_zero, zero_add] at hgf
      exact (mul_eq_zero.mp hgf).resolve_left hi
    simp [hfj, hgj]


private def scalarA : LinearMap.BilinForm ℚ (Fin 4 → ℚ) where
  toFun x :=
    { toFun := fun y => x 0 * y 0 - x 1 * y 1 + x 2 * y 2 - x 3 * y 3
      map_add' := by intros; simp only [Pi.add_apply]; ring
      map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' := by
    intros p q
    apply LinearMap.ext
    intro z
    dsimp
    ring
  map_smul' := by
    intros c p
    apply LinearMap.ext
    intro z
    dsimp
    ring

private def scalarB : LinearMap.BilinForm ℚ (Fin 3 → ℚ) where
  toFun x :=
    { toFun := fun y => x 0 * y 0 - x 1 * y 1 + x 2 * y 2
      map_add' := by intros; simp only [Pi.add_apply]; ring
      map_smul' := by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_add' := by
    intros p q
    apply LinearMap.ext
    intro z
    dsimp
    ring
  map_smul' := by
    intros c p
    apply LinearMap.ext
    intro z
    dsimp
    ring

private def u : (Fin 4 → ℚ) := ![1, 1, 0, 0]
private def v : (Fin 3 → ℚ) := ![1, 1, 0]
private noncomputable def mu : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) := scalarA.compr₂
  ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight u)
private noncomputable def nu : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) := scalarB.compr₂
  ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight v)
private noncomputable def prod : ((Fin 4 → ℚ) × (Fin 3 → ℚ)) →ₗ[ℚ] ((Fin 4 → ℚ) × (Fin 3 → ℚ))
  →ₗ[ℚ] ((Fin 4 → ℚ) × (Fin 3 → ℚ)) := directSumProduct mu nu

private def coupled : Submodule ℚ ((Fin 4 → ℚ) × (Fin 3 → ℚ)) where
  carrier := {p | p.1 0 = p.1 1 ∧ p.2 0 = p.2 1 ∧ p.2 2 = p.1 2 + p.1 3}
  zero_mem' := by simp
  add_mem' := by
    rintro p q ⟨hp, hp', hp''⟩ ⟨hq, hq', hq''⟩
    change p.1 0 + q.1 0 = p.1 1 + q.1 1 ∧
      p.2 0 + q.2 0 = p.2 1 + q.2 1 ∧
      p.2 2 + q.2 2 = (p.1 2 + q.1 2) + (p.1 3 + q.1 3)
    rw [hp, hq, hp', hq', hp'', hq'']
    exact ⟨rfl, rfl, by ring⟩
  smul_mem' := by
    rintro c p ⟨hp, hp', hp''⟩
    change c * p.1 0 = c * p.1 1 ∧ c * p.2 0 = c * p.2 1 ∧
      c * p.2 2 = c * p.1 2 + c * p.1 3
    rw [hp, hp', hp'']
    exact ⟨rfl, rfl, mul_add _ _ _⟩

private theorem coupled_closed : ∀ (p q : ((Fin 4 → ℚ) × (Fin 3 → ℚ))), p ∈ coupled → q ∈ coupled
  → prod p q ∈ coupled := by
  intros p q hp hq
  change (scalarA p.1 q.1) * u 0 = (scalarA p.1 q.1) * u 1 ∧
    (scalarB p.2 q.2) * v 0 = (scalarB p.2 q.2) * v 1 ∧
    (scalarB p.2 q.2) * v 2 = (scalarA p.1 q.1) * u 2 + (scalarA p.1 q.1) * u 3
  simp [u, v]

private noncomputable def subProd := inheritedProduct prod coupled coupled_closed

private def f : coupled →ₗ[ℚ] ℚ :=
  ((LinearMap.proj (R := ℚ) (φ := fun _ : Fin 4 => ℚ) 2 + LinearMap.proj (R := ℚ) (φ := fun _ : Fin 4 => ℚ) 3) : (Fin 4 → ℚ) →ₗ[ℚ] ℚ).comp
    ((LinearMap.fst ℚ (Fin 4 → ℚ) (Fin 3 → ℚ)).comp coupled.subtype)

private def g : coupled →ₗ[ℚ] ℚ :=
  ((LinearMap.proj (R := ℚ) (φ := fun _ : Fin 4 => ℚ) 2 - LinearMap.proj (R := ℚ) (φ := fun _ : Fin 4 => ℚ) 3) : (Fin 4 → ℚ) →ₗ[ℚ] ℚ).comp
    ((LinearMap.fst ℚ (Fin 4 → ℚ) (Fin 3 → ℚ)).comp coupled.subtype)

private theorem product_readouts (p q : coupled) (h : subProd p q = 0) :
    f p * f q = 0 ∧ g p * f q + f p * g q = 0 := by
  have hA := congrArg (fun z : coupled => z.val.1 0) h
  have hB := congrArg (fun z : coupled => z.val.2 0) h
  change (coupled.subtype (subProd p q)).1 0 = 0 at hA
  change (coupled.subtype (subProd p q)).2 0 = 0 at hB
  change (subProd p q).val.1 0 = 0 at hA
  change (subProd p q).val.2 0 = 0 at hB
  rw [show subProd p q = inheritedProduct prod coupled coupled_closed p q from rfl,
    inheritedProduct_val] at hA hB
  change (scalarA p.val.1 q.val.1) * u 0 = 0 at hA
  change (scalarB p.val.2 q.val.2) * v 0 = 0 at hB
  simp only [u, v, Matrix.cons_val_zero, mul_one] at hA hB
  change p.val.1 0 * q.val.1 0 - p.val.1 1 * q.val.1 1 +
    p.val.1 2 * q.val.1 2 - p.val.1 3 * q.val.1 3 = 0 at hA
  change p.val.2 0 * q.val.2 0 - p.val.2 1 * q.val.2 1 +
    p.val.2 2 * q.val.2 2 = 0 at hB
  rcases p.property with ⟨hp, hp', hp''⟩
  rcases q.property with ⟨hq, hq', hq''⟩
  rw [hp, hq] at hA
  rw [hp', hq', hp'', hq''] at hB
  change (p.val.1 2 + p.val.1 3) * (q.val.1 2 + q.val.1 3) = 0 ∧
    (p.val.1 2 - p.val.1 3) * (q.val.1 2 + q.val.1 3) +
      (p.val.1 2 + p.val.1 3) * (q.val.1 2 - q.val.1 3) = 0
  constructor
  · linear_combination hB
  · linear_combination 2 * hA

private def x : coupled := ⟨(![0, 0, 1, 0], ![0, 0, 1]), by norm_num [coupled]⟩
private def y : coupled := ⟨(![0, 0, 0, 1], ![0, 0, 1]), by norm_num [coupled]⟩

private theorem coupled_not_evolution : ¬ IsEvolutionAlgebra subProd := by
  rintro ⟨_, ι, b, hb⟩
  have hf : f ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h x
    norm_num [f, x] at hh
  obtain ⟨c, hc⟩ := readouts_proportional b f g hf
    (fun i j hij => product_readouts (b i) (b j) (hb i j hij))
  have hx := LinearMap.congr_fun hc x
  have hy := LinearMap.congr_fun hc y
  norm_num [f, g, x, y] at hx hy
  linarith

theorem result : ¬ claim := by
  letI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  intro h
  have hA : LinearMap.IsSymm scalarA := by
    have heq : scalarA = (Matrix.diagonal (![1, -1, 1, -1] : Fin 4 → ℚ)).toBilin' := by
      ext p q
      simp [scalarA, Matrix.toBilin'_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]
      <;> ring
    rw [heq]
    exact LinearMap.BilinForm.isSymm_iff.mp ((Matrix.isSymm_toBilin'_iff_isSymm (M := Matrix.diagonal (![1, -1, 1, -1] : Fin 4 → ℚ))).mpr (Matrix.isSymm_diagonal _))
  have hB : LinearMap.IsSymm scalarB := by
    have heq : scalarB = (Matrix.diagonal (![1, -1, 1] : Fin 3 → ℚ)).toBilin' := by
      ext p q
      simp [scalarB, Matrix.toBilin'_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]
      <;> ring
    rw [heq]
    exact LinearMap.BilinForm.isSymm_iff.mp ((Matrix.isSymm_toBilin'_iff_isSymm (M := Matrix.diagonal (![1, -1, 1] : Fin 3 → ℚ))).mpr (Matrix.isSymm_diagonal _))
  exact coupled_not_evolution
    (h ℚ 4 3 mu nu
      (rank_one_evolution scalarA u hA) (rank_one_evolution scalarB v hB)
      (rank_one_hereditary scalarA u hA) (rank_one_hereditary scalarB v hB)
      coupled coupled_closed)

end D5.S3.QuadraticForms.EvolutionAlgebras.DirectSumHeredityRefutation
