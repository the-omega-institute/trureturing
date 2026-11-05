/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Semisimple evolution derivations force nonzero natural squares. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility none: structural existence and Lie equivalences; no finite certificate or algorithm.
escape_witness: Annihilator.semisimple_ann_or_perfect
  IsEvolutionAlgebra: proof_shape: bind-only; escape_witness: none;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.claim, D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result
  derivations: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.annModule, Annihilator.annSquareIdeal, Annihilator.annSquareIdeal_abelian, Annihilator.derivation_preserves_ann, Annihilator.derivation_preserves_square, Annihilator.rankOneDerivation, Annihilator.rankOne_mem_ideal, Annihilator.semisimple_ann_or_perfect, Annihilator.semisimple_natural_squares_ne_zero, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Blocks.nonzero_square_block_decomposition, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.assemble_mem_derivations, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.normalized_block_decomposition, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.productToDerivations, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.productToDerivations_injective, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.productToDerivations_surjective, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.restrictBlock_mem_stabilizer, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.mem_derivations_iff_basis, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.natural_derivation_iff_equations, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.off_diagonal_equation, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.square_equation, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized.derivation_bracket_diagonal_zero, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized.derivation_cross_zero, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized.derivation_off_diagonal_skew, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized.semisimple_diagonal_zero, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized.semisimple_normalized_derivation_iff, D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.claim, D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result
  Perfectness.semisimple_perfect: proof_shape: bind-only; escape_witness: none;
    consumers: Perfectness.semisimple_trace, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized.semisimple_diagonal_zero
  Perfectness.trace_eq_zero_of_perfect: proof_shape: bind-only; escape_witness: none;
    consumers: Perfectness.semisimple_trace
  Perfectness.semisimple_trace: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.semisimple_ann_or_perfect
  Annihilator.square: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.annSquareIdeal, Annihilator.annSquareIdeal_abelian, Annihilator.derivation_preserves_square, Annihilator.product_mem_square, Annihilator.rankOneDerivation, Annihilator.rankOne_mem_ideal, Annihilator.semisimple_ann_or_perfect, Annihilator.semisimple_natural_squares_ne_zero, Annihilator.square_le_squareMap_range, Annihilator.zero_square_square_ne_top
  Annihilator.product_mem_square: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.derivation_preserves_square, Annihilator.rankOneDerivation
  Annihilator.derivation_preserves_ann: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.annModule, Annihilator.annSquareIdeal
  Annihilator.derivation_preserves_square: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.annSquareIdeal
  Annihilator.annModule: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.semisimple_ann_or_perfect
  Annihilator.annSquareIdeal: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.annSquareIdeal_abelian, Annihilator.rankOne_mem_ideal, Annihilator.semisimple_ann_or_perfect
  Annihilator.rankOneDerivation: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.rankOne_mem_ideal, Annihilator.semisimple_ann_or_perfect
  Annihilator.rankOne_mem_ideal: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.semisimple_ann_or_perfect
  Annihilator.annSquareIdeal_abelian: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.semisimple_ann_or_perfect
  Annihilator.semisimple_ann_or_perfect: proof_shape: content; escape_witness: Annihilator.semisimple_ann_or_perfect;
    consumers: Annihilator.semisimple_natural_squares_ne_zero
  Annihilator.zero_square_mem_ann: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.semisimple_natural_squares_ne_zero
  Annihilator.square_le_squareMap_range: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.zero_square_square_ne_top
  Annihilator.zero_square_square_ne_top: proof_shape: bind-only; escape_witness: none;
    consumers: Annihilator.semisimple_natural_squares_ne_zero
  Annihilator.semisimple_natural_squares_ne_zero: proof_shape: content; escape_witness: Annihilator.semisimple_ann_or_perfect;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result
-/

import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Trace


attribute [local instance] Classical.propDecidable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction

open DirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Section 1.1: an evolution algebra is a commutative algebra `(V, μ)` with a natural basis
`{eᵢ}`, i.e. `eᵢ eⱼ = 0` whenever `i ≠ j`. -/
def IsEvolutionAlgebra (μ : V →ₗ[k] V →ₗ[k] V) : Prop :=
  (∀ x y, μ x y = μ y x) ∧
    ∃ (ι : Type) (b : Module.Basis ι k V), ∀ i j, i ≠ j → μ (b i) (b j) = 0

/-- `Der(A)`: the linear maps `D` with `D(xy) = D(x)y + xD(y)`, a Lie subalgebra of `End_k(A)`
under the commutator bracket. -/
def derivations (μ : V →ₗ[k] V →ₗ[k] V) : LieSubalgebra k (Module.End k V) where
  carrier := {D | ∀ x y, D (μ x y) = μ (D x) y + μ x (D y)}
  zero_mem' := by intro x y; simp
  add_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    simp only [Set.mem_ofPred_eq] at h₁ h₂
    simp only [LinearMap.add_apply, map_add, h₁, h₂]
    abel
  smul_mem' := by
    intro c D h x y
    simp only [Set.mem_ofPred_eq] at h
    simp only [LinearMap.smul_apply, map_smul, h, smul_add]
  lie_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    simp only [Set.mem_ofPred_eq] at h₁ h₂
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub,
      h₁, h₂, map_add]
    abel

end D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.Perfectness
variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
theorem semisimple_perfect [LieAlgebra.IsSemisimple k L] :
    ⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ = ⊤ := by
  apply le_antisymm le_top
  calc
    (⊤ : LieIdeal k L) = sSup {I : LieIdeal k L | IsAtom I} :=
      LieAlgebra.IsSemisimple.sSup_atoms_eq_top.symm
    _ ≤ ⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ := by
      apply sSup_le
      intro I hI
      rw [← lie_eq_self_of_isAtom_of_nonabelian I hI
        (LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI)]
      exact LieSubmodule.mono_lie le_top le_top

attribute [local instance 100] LieRing.ofAssociativeRing
variable {M : Type*} [AddCommGroup M] [Module k M]
private theorem trace_eq_zero_of_perfect
    (hp : ⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ = ⊤)
    (ρ : L →ₗ⁅k⁆ Module.End k M) (x : L) : LinearMap.trace k M (ρ x) = 0 := by
  have hx : x ∈ (⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ : LieIdeal k L).toSubmodule := by
    rw [hp]
    trivial
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, b, rfl⟩ := hy
      simp only [LieHom.map_lie, LinearMap.trace_lie]
  | zero => simp
  | add a b ha hb ia ib => simp [ia, ib]
  | smul c a ha ia => simp [ia]
private theorem semisimple_trace [LieAlgebra.IsSemisimple k L]
    (ρ : L →ₗ⁅k⁆ Module.End k M) (x : L) : LinearMap.trace k M (ρ x) = 0 := by
  exact trace_eq_zero_of_perfect semisimple_perfect ρ x

end D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.Perfectness

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.Annihilator
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (μ : V →ₗ[k] V →ₗ[k] V)
def square : Submodule k V := Submodule.span k {v | ∃ x y, μ x y = v}
private theorem product_mem_square (x y : V) : μ x y ∈ square μ := by
  exact Submodule.subset_span ⟨x, y, rfl⟩
private theorem derivation_preserves_ann (D : derivations μ) (x : V) (hx : x ∈ (LinearMap.ker μ)) :
    D.val x ∈ (LinearMap.ker μ) := by
  change μ (D.val x) = 0
  ext y
  have hz (v : V) : μ x v = 0 := LinearMap.congr_fun hx v
  have hh := D.property x y
  simp only [hz, map_zero, add_zero] at hh
  exact hh.symm
private theorem derivation_preserves_square (D : derivations μ) (x : V) (hx : x ∈ square μ) :
    D.val x ∈ square μ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, v, rfl⟩ := hx
      rw [D.property]
      exact (square μ).add_mem (product_mem_square μ _ _) (product_mem_square μ _ _)
  | zero => simpa using (square μ).zero_mem
  | add x y hx hy ihx ihy => simpa using (square μ).add_mem ihx ihy
  | smul c x hx ih => simpa using (square μ).smul_mem c ih
private def annModule : LieSubmodule k (derivations μ) V :=
  { (LinearMap.ker μ) with lie_mem := fun {D x} hx => derivation_preserves_ann μ D x hx }
private def annSquareIdeal : LieIdeal k (derivations μ) where
  carrier := {D | (∀ x, D.val x ∈ (LinearMap.ker μ)) ∧ ∀ x ∈ square μ, D.val x = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfP⟩ ⟨hg, hgP⟩
    exact ⟨fun x => ((LinearMap.ker μ)).add_mem (hf x) (hg x), by intro x hx; change f.val x + g.val x = 0; rw [hfP x hx, hgP x hx, add_zero]⟩
  smul_mem' := by
    rintro c f ⟨hf, hfP⟩
    exact ⟨fun x => ((LinearMap.ker μ)).smul_mem c (hf x), by intro x hx; change c • f.val x = 0; rw [hfP x hx, smul_zero]⟩
  lie_mem := by
    intro D f hf
    refine ⟨fun x => ((LinearMap.ker μ)).sub_mem (derivation_preserves_ann μ D (f.val x) (hf.1 x))
      (hf.1 (D.val x)), ?_⟩
    intro x hx
    change D.val (f.val x) - f.val (D.val x) = 0
    rw [hf.2 x hx, map_zero, hf.2 _ (derivation_preserves_square μ D x hx), sub_self]

variable (hc : ∀ x y, μ x y = μ y x)
private def rankOneDerivation (a : V) (ha : a ∈ (LinearMap.ker μ)) (φ : V →ₗ[k] k)
    (hφ : ∀ x ∈ square μ, φ x = 0) : derivations μ :=
  ⟨φ.smulRight a, by
    intro x y
    have hal : μ a y = 0 := LinearMap.congr_fun ha y
    have har : μ x a = 0 := (hc x a).trans (LinearMap.congr_fun ha x)
    simp only [LinearMap.smulRight_apply, LinearMap.map_smul₂, map_smul, LinearMap.smul_apply,
      hφ _ (product_mem_square μ x y), zero_smul, hal, har, smul_zero, add_zero]⟩
private theorem rankOne_mem_ideal (a : V) (ha : a ∈ (LinearMap.ker μ)) (φ : V →ₗ[k] k)
    (hφ : ∀ x ∈ square μ, φ x = 0) :
    rankOneDerivation μ hc a ha φ hφ ∈ annSquareIdeal μ := by
  exact ⟨fun x => ((LinearMap.ker μ)).smul_mem (φ x) ha, fun x hx => by
    change φ x • a = 0
    rw [hφ x hx, zero_smul]⟩
private theorem annSquareIdeal_abelian (hAP : (LinearMap.ker μ) ≤ square μ) :
    IsLieAbelian (annSquareIdeal μ) := by
  constructor
  intro f g
  apply Subtype.ext
  apply Subtype.ext
  ext x
  change f.val.val (g.val.val x) - g.val.val (f.val.val x) = 0
  rw [f.property.2 _ (hAP (g.property.1 x)), g.property.2 _ (hAP (f.property.1 x)), sub_self]

include hc in
theorem semisimple_ann_or_perfect [FiniteDimensional k V]
    [LieAlgebra.IsSemisimple k (derivations μ)] : (LinearMap.ker μ) = ⊥ ∨ square μ = ⊤ := by
  classical
  by_cases hp : square μ = ⊤
  · exact Or.inr hp
  left
  by_contra hK
  obtain ⟨a, ha, hane⟩ := ((LinearMap.ker μ)).ne_bot_iff.mp hK
  by_cases hAP : (LinearMap.ker μ) ≤ square μ
  · haveI : IsLieAbelian (annSquareIdeal μ) := annSquareIdeal_abelian μ hAP
    have hJ : annSquareIdeal μ = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _
    obtain ⟨φ, hφne, hφP⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hp) inferInstance
    have hφ (x : V) (hx : x ∈ square μ) : φ x = 0 := by
      have hh : φ x ∈ (square μ).map φ := ⟨x, hx, rfl⟩
      simpa only [hφP, Submodule.mem_bot] using hh
    let D := rankOneDerivation μ hc a ha φ hφ
    have hD : D = 0 := by
      have hh := rankOne_mem_ideal μ hc a ha φ hφ
      simpa only [hJ, LieSubmodule.mem_bot] using hh
    apply hφne
    ext x
    have hh : φ x • a = 0 := congrArg (fun f : derivations μ => f.val x) hD
    exact (smul_eq_zero.mp hh).resolve_right hane
  · obtain ⟨b, hbK, hbP⟩ : ∃ b, b ∈ (LinearMap.ker μ) ∧ b ∉ square μ := by
      have hh : ¬ ∀ b : V, b ∈ (LinearMap.ker μ) → b ∈ square μ := hAP
      obtain ⟨b, hb⟩ := not_forall.mp hh
      exact ⟨b, (not_imp.mp hb).1, (not_imp.mp hb).2⟩
    have hq : (square μ).mkQ b ≠ 0 := by
      intro hz
      exact hbP ((Submodule.Quotient.mk_eq_zero _).mp hz)
    obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hq
    let φ := ψ.comp (square μ).mkQ
    have hφb : φ b = 1 := hψ
    have hφ (x : V) (hx : x ∈ square μ) : φ x = 0 := by
      change ψ ((square μ).mkQ x) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx, map_zero]
    let D := rankOneDerivation μ hc b hbK φ hφ
    have hD := D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.Perfectness.semisimple_trace (LieModule.toEnd k (derivations μ) (annModule μ)) D
    have hrestrict : LieModule.toEnd k (derivations μ) (annModule μ) D =
        (φ.comp (annModule μ).toSubmodule.subtype).smulRight (⟨b, hbK⟩ : annModule μ) := by
      ext x
      rfl
    rw [hrestrict, LinearMap.trace_smulRight] at hD
    exact one_ne_zero (hφb.symm.trans hD)

variable {ι : Type*} (b : Module.Basis ι k V)
variable (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)

include hn in
private theorem zero_square_mem_ann (i : ι) (hi : μ (b i) (b i) = 0) : b i ∈ (LinearMap.ker μ) := by
  change μ (b i) = 0
  apply b.ext
  intro j
  by_cases hij : i = j
  · simpa only [← hij, LinearMap.zero_apply] using hi
  · exact hn i j hij

include hn in
private theorem square_le_squareMap_range [FiniteDimensional k V] :
    square μ ≤ LinearMap.range (b.constr k (fun i => μ (b i) (b i))) := by
  classical
  letI := FiniteDimensional.fintypeBasisIndex b
  apply Submodule.span_le.mpr
  rintro x ⟨u, v, rfl⟩
  rw [← b.sum_repr u, map_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i hi
  rw [LinearMap.map_smul₂]
  apply Submodule.smul_mem
  rw [← b.sum_repr v, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  apply Submodule.smul_mem
  by_cases hij : i = j
  · subst j
    exact ⟨b i, b.constr_basis k _ i⟩
  · rw [hn i j hij]
    exact Submodule.zero_mem _

include hn in
private theorem zero_square_square_ne_top [FiniteDimensional k V] (i : ι)
    (hi : μ (b i) (b i) = 0) : square μ ≠ ⊤ := by
  intro hp
  let T := b.constr k (fun i => μ (b i) (b i))
  have hT : LinearMap.range T = ⊤ := top_unique (hp ▸ square_le_squareMap_range μ b hn)
  have hinj : Function.Injective T := LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp hT)
  have hz : T (b i) = T 0 := by simp only [T, b.constr_basis k, hi, map_zero]
  exact b.ne_zero i (hinj hz)

include hc hn in
theorem semisimple_natural_squares_ne_zero [FiniteDimensional k V]
    [LieAlgebra.IsSemisimple k (derivations μ)] (i : ι) : μ (b i) (b i) ≠ 0 := by
  intro hi
  have hK : (LinearMap.ker μ) = ⊥ := (semisimple_ann_or_perfect μ hc).resolve_right
    (zero_square_square_ne_top μ b hn i hi)
  have hb : b i ∈ (⊥ : Submodule k V) := hK ▸ zero_square_mem_ann μ b hn i hi
  exact b.ne_zero i ((Submodule.mem_bot k).mp hb)

end D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.Annihilator
