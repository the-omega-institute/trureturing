/- GID: D5/S3/VertexAlgebra/Lattice/ActualC2
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualC2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A negative-norm charge collapses the literal full-state actual C2 space. -/

import D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra
import Batteries.Tactic.OpenPrivate

/-!
proof_shape: negative_norm_c2_eq_top: content; consumed private helpers are
  higher-mode induction, commutator span stability, ground-pair recovery and creation.
escape_witness: negative_norm_c2_eq_top; the negative-norm ground pair puts the
  vacuum in C2, and actual creation then witnesses every carrier state.
admission_basis: escape-witness
escape-audit: unfinished; no source-faithful enrolled Reg template;
  issue https://github.com/the-omega-institute/trureturing/issues/25088
Direct frozen dependencies:
  NormFourFixedPeirce (sha256:1e1478289a565d96c00677349de88d3082918b4a2104c9e71e77cf6025b7b499),
  NormFourVacuumC2Algebra (sha256:a46189d9f94c9e71d9ee224bf6f01b25aecd8b9105d8bd3654ad796c53376852)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualC2

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualStateFieldCalculus LatticeActualStateDerivative
open LatticeSugawaraConformal
open scoped BigOperators VertexOperator

open private ground ground_product
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private commutator_evaluated
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra
open private finite_sum_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

noncomputable section

def C2 (D : LatticeData) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {z | ∃ a b : Carrier D, z = mu D a (-2) b}

private theorem higher_product_mem (D : LatticeData) (r : ℕ)
    (a b : Carrier D) :
    mu D a (-((r : ℤ) + 2)) b ∈ C2 D := by
  induction r generalizing a b with
  | zero =>
      exact Submodule.subset_span ⟨a, b, rfl⟩
  | succ r ih =>
      have previous := ih (translation D a) b
      have derivative := congrArg (fun A : Module.End ℂ (Carrier D) => A b)
        (state_derivative_modes D a (-((r : ℤ) + 2)))
      change mu D (translation D a) (-((r : ℤ) + 2)) b =
        -((-((r : ℤ) + 2) : ℤ) : ℂ) •
          mu D a (-((r : ℤ) + 2) - 1) b at derivative
      have scalar : -((-((r : ℤ) + 2) : ℤ) : ℂ) = (r + 2 : ℂ) := by
        push_cast
        ring
      rw [scalar] at derivative
      rw [derivative] at previous
      have nonzero : (r + 2 : ℂ) ≠ 0 := by
        exact_mod_cast (show r + 2 ≠ 0 by omega)
      have recovered := (C2 D).smul_mem (r + 2 : ℂ)⁻¹ previous
      simpa only [smul_smul, inv_mul_cancel₀ nonzero, one_smul,
        Nat.cast_add, Nat.cast_one,
        show -((r : ℤ) + 2) - 1 = -(((r + 1 : ℕ) : ℤ) + 2) by omega]
        using recovered

private theorem left_minus_one_mem (D : LatticeData) (u z : Carrier D)
    (hz : z ∈ C2 D) : mu D u (-1) z ∈ C2 D := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      let terms (j : ℕ) : Carrier D :=
        commutatorTerm D u a (-1) (-2) j b
      have finite : Function.HasFiniteSupport terms :=
        (commutator_terms_finite D u a (-1) (-2)).fun_comp
          (map_zero (LinearMap.applyₗ b))
      have each (j : ℕ) : terms j ∈ C2 D := by
        change StateFieldResidueReconstruction.integerBinomial (-1) j •
          mu D (mu D u j a) (-1 + -2 - j) b ∈ C2 D
        apply (C2 D).smul_mem
        simpa only [show -1 + -2 - (j : ℤ) = -(((j + 1 : ℕ) : ℤ) + 2) by omega]
          using higher_product_mem D (j + 1) (mu D u j a) b
      have correction := finite_sum_mem (C2 D) terms finite each
      have base : mu D a (-2) (mu D u (-1) b) ∈ C2 D :=
        Submodule.subset_span ⟨a, mu D u (-1) b, rfl⟩
      have h := commutator_evaluated D u a b (-1) (-2)
      change _ = ∑ᶠ j, terms j at h
      simpa only [← h, sub_add_cancel] using (C2 D).add_mem correction base
  | zero => simp [mu]
  | add z w _ _ hz hw =>
      simpa only [mu, map_add] using (C2 D).add_mem hz hw
  | smul c z _ hz =>
      simpa only [mu, map_smul] using (C2 D).smul_mem c hz

private theorem ground_pair_mem (D : LatticeData) (α : Charge D)
    (hα : bilinear D α α < 0) : vacuum D ∈ C2 D := by
  let n : ℤ := bilinear D α α - 1
  have pair := ground_product D α (-α) n
  let r : ℕ := (-bilinear D α α - 1).toNat
  have hrnonneg : 0 ≤ -bilinear D α α - 1 := by omega
  have hr : (r : ℤ) = -bilinear D α α - 1 := by
    dsimp [r]
    exact Int.toNat_of_nonneg hrnonneg
  have pair_mem : mu D (ground D α) n (ground D (-α)) ∈ C2 D := by
    have h := higher_product_mem D r (ground D α) (ground D (-α))
    have index : -((r : ℤ) + 2) = n := by
      rw [hr]
      dsimp [n]
      ring
    rw [index] at h
    exact h
  have epsilon_ne_zero : epsilon D α (-α) ≠ 0 := by
    unfold epsilon paritySign
    split_ifs <;> norm_num
  have pair_value : mu D (ground D α) n (ground D (-α)) =
      epsilon D α (-α) • vacuum D := by
    rw [pair]
    simp [n, creationCoeff, exponential_constant, vacuum, bilinear]
  rw [pair_value] at pair_mem
  have recovered := (C2 D).smul_mem (epsilon D α (-α))⁻¹ pair_mem
  simpa only [smul_smul, inv_mul_cancel₀ epsilon_ne_zero, one_smul] using recovered

/-- For the literal span over all actual states, a negative-norm charge forces
the vacuum into C2 and creation then forces the span to be the whole carrier. -/
theorem negative_norm_c2_eq_top (D : LatticeData) (α : Charge D)
    (hα : bilinear D α α < 0) : C2 D = ⊤ := by
  apply le_antisymm le_top
  intro u _
  have vacuum_mem : vacuum D ∈ C2 D := ground_pair_mem D α hα
  have created := left_minus_one_mem D u (vacuum D) vacuum_mem
  change ((Y D u)[[-1]]) (vacuum D) ∈ C2 D at created
  rw [stateField_creation D u] at created
  exact created

end
end D5.S3.VertexAlgebra.Lattice.ActualC2
