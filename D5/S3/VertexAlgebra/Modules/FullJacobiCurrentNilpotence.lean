/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiCurrentNilpotence
   generality: I
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: []
   utility: Original stable locus and actual source/exponential module identities.
   status: UNCOMPILED source candidate.

This file keeps the original `FullJacobiLatticeModule` and the original source
field `Y`.  It contains the fully algebraic part of the local-nilpotence-locus
argument and proves the source identities consumed by the lattice-specific
rank descent in FullJacobiCurrentVacuum.  No grading, Fock decomposition, Zhu-top hypothesis, or altered
module record occurs here.

Canonical suppliers consumed by the imported adapter:
  D5/S3/VertexAlgebra/LatticeAllStateField.lean
  D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus.lean
  D5/S3/VertexAlgebra/LatticeActualMixedLocality.lean
  D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration.lean
  D5/S3/VertexAlgebra/LatticeSugawaraCurrents.lean
  D5/S3/VertexAlgebra/LatticeSugawaraConformal.lean
  D5/S3/VertexAlgebra/LatticeActualOrderedProducts.lean
The source ground-product calculation consumes public `raw_ground` from
D5/S3/VertexAlgebra/LatticeActualOrderedProducts.lean. This is the same
orientation as private `ground_product` in Lattice/NormFourFixedPeirce;
no private theorem or additional norm-four premise is imported here.
-/

import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport
import D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
import D5.S3.VertexAlgebra.LatticeActualMixedLocality
import D5.S3.VertexAlgebra.LatticeActualOrderedProducts
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Modules.FullJacobiCurrentNilpotence

open D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeAllStateField
open D5.S3.VertexAlgebra.LatticeAllStateReconstruction
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open StateFieldResidueReconstruction (integerBinomial epsilon)
open scoped BigOperators VertexOperator

-- Keep the authored finite-sum spelling while expanding to the native Finset sum.
local macro "∑ " x:ident " in " a:term ", " f:term : term =>
  `(Finset.sum $a (fun $x => $f))

noncomputable section
universe u

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The literal exponential state used below.  This is the original source
single, not an auxiliary Fock state. -/
def exponentialState (α : Charge D) : Carrier D :=
  Finsupp.single α (1 : Oscillator D)

/-- On the source carrier the all-state construction recovers the actual
charged field at the literal exponential state.  The module field is only
state-linear, so this statement is deliberately phrased for the source field
`Y`; its module transport is the application of `J.stateField`. -/
theorem source_exponential_stateField (α : Charge D) :
    Y D (exponentialState α) = actualField D α := by
  simpa [exponentialState] using (stateField_ground D α)

/-- A power which kills a vector continues to kill it at every larger power.
This is the only monotonicity used in the linearity of the stable locus. -/
theorem pow_map_zero_of_le (T : Module.End ℂ M) {v : M}
    {k l : ℕ} (hkl : k ≤ l) (hv : (T ^ k) v = 0) :
    (T ^ l) v = 0 := by
  exact Module.End.pow_map_zero_of_le hkl hv

/-- The pointwise local-nilpotence locus of an endomorphism, with the positive
exponent convention required by the original goal. -/
def powerNilpotenceSubmodule (T : Module.End ℂ M) : Submodule ℂ M where
  carrier := {v | ∃ k : ℕ, 0 < k ∧ (T ^ k) v = 0}
  zero_mem' := by
    exact ⟨1, Nat.zero_lt_one, by simp⟩
  add_mem' := by
    rintro v w ⟨k, hk, hv⟩ ⟨l, hl, hw⟩
    refine ⟨max k l, by omega, ?_⟩
    have hv' : (T ^ max k l) v = 0 :=
      pow_map_zero_of_le T (Nat.le_max_left _ _) hv
    have hw' : (T ^ max k l) w = 0 :=
      pow_map_zero_of_le T (Nat.le_max_right _ _) hw
    simpa [map_add, hv', hw']
  smul_mem' := by
    intro c v hv
    rcases hv with ⟨k, hk, hv⟩
    exact ⟨k, hk, by simp [hv]⟩

@[simp] theorem mem_powerNilpotenceSubmodule (T : Module.End ℂ M) (v : M) :
    v ∈ powerNilpotenceSubmodule T ↔ ∃ k : ℕ, 0 < k ∧ (T ^ k) v = 0 := Iff.rfl

/-- A central scalar commutator gives the finite power identity needed for
current stability.  The proof is by induction in the noncommutative ring of
endomorphisms; the scalar endomorphism commutes with every endomorphism. -/
theorem central_power_commutator (T H : Module.End ℂ M) (c : ℂ)
    (hcomm : T * H - H * T = c • (1 : Module.End ℂ M)) (k : ℕ) :
    T ^ (k + 1) * H = H * T ^ (k + 1) +
      ((k + 1 : ℕ) : ℂ) • (c • (T ^ k)) := by
  induction k with
  | zero =>
      simpa using (sub_eq_iff_eq_add'.mp hcomm)
  | succ k ih =>
      have base : T * H = H * T + c • (1 : Module.End ℂ M) :=
        sub_eq_iff_eq_add'.mp hcomm
      calc
        T ^ (k + 1 + 1) * H = T * (T ^ (k + 1) * H) := by
          rw [pow_succ', mul_assoc]
        _ = T * (H * T ^ (k + 1) +
            ((k + 1 : ℕ) : ℂ) • (c • T ^ k)) := by rw [ih]
        _ = H * T ^ (k + 1 + 1) +
            ((k + 1 + 1 : ℕ) : ℂ) • (c • T ^ (k + 1)) := by
          rw [mul_add, ← mul_assoc T H, base, add_mul]
          simp only [mul_smul_comm, one_mul, smul_mul_assoc,
            ← pow_succ', mul_assoc, ← pow_succ, Nat.cast_add, Nat.cast_one]
          module

/-- Current modes preserve the stable locus.  This is stated with the exact
central commutator supplied by `module_current_heisenberg`; no finite
-dimensionality of `M` is used. -/
theorem current_mode_stable
    (J : FullJacobiLatticeModule D M)
    (i h : Fin D.rank) (n t : ℤ)
    (v : M) (hv : v ∈ powerNilpotenceSubmodule (current J i n)) :
    current J h t v ∈ powerNilpotenceSubmodule (current J i n) := by
  rcases hv with ⟨k, hk, hv⟩
  let c : ℂ := if n + t = 0 then (n : ℂ) * (D.G i h : ℂ) else 0
  have hcomm : current J i n * current J h t - current J h t * current J i n =
      c • (1 : Module.End ℂ M) := by
    simpa [c] using module_current_heisenberg J i h n t
  refine ⟨k + 1, Nat.succ_pos _, ?_⟩
  have hp := congrArg (fun A : Module.End ℂ M => A v)
    (central_power_commutator (current J i n) (current J h t) c hcomm k)
  have hvnext : (current J i n ^ (k + 1)) v = 0 :=
    pow_map_zero_of_le (current J i n) (Nat.le_succ k) hv
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, hv, hvnext, map_zero, smul_zero, add_zero] at hp
  exact hp

/-- The preserved finite power proposition; its Pascal induction is supplied by
`FullJacobiCurrentLocus.current_exp_power_formula`. -/
def currentExpPowerFormulaStatement
    (J : FullJacobiLatticeModule D M)
    (i : Fin D.rank) (β : Charge D) (n m : ℤ) (N : ℕ) :
    Prop :=
    (current J i n ^ N) * mode J (exponentialState β) m =
      ∑ j in Finset.range (N + 1),
        ((Nat.choose N j : ℂ) *
          ((bilinear D (unitCharge D i) β : ℂ) ^ j)) •
          (mode J (exponentialState β) (m + (j : ℤ) * n)) *
            (current J i n ^ (N - j))

/-- The source negative-mode word span is the exact closure needed to extend
stability from the finite neutral/charged generating family to every original
source state. Its negative-word induction is supplied by
`FullJacobiCurrentLocus.all_source_modes_stable`. -/
def sourceModeStable (J : FullJacobiLatticeModule D M)
    (N : Submodule ℂ M) : Set (Carrier D) :=
  {a | ∀ s : ℤ, ∀ v : M, v ∈ N → mode J a s v ∈ N}


/-- The complete original charged ground coefficient, including its cocycle. -/
theorem source_exponential_product (α β : Charge D) (s : ℤ) :
    sourceProduct D (exponentialState α) s (exponentialState β) =
      LatticeGeneratingFieldLocality.epsilon D α β •
        Finsupp.single (α + β) (creationCoeff D α (-s - 1 - bilinear D α β)) := by
  rw [sourceProduct, source_exponential_stateField, actualField,
    VertexOperator.ncoeff_of_coeff]
  exact LatticeActualOrderedProducts.raw_ground D α (-s - 1) β

/-- Opposite-charge leading product. No positivity premise is needed for this identity. -/
theorem source_opposite_leading (α : Charge D) :
    sourceProduct D (exponentialState (-α)) (bilinear D α α - 1)
      (exponentialState α) =
      LatticeGeneratingFieldLocality.epsilon D (-α) α • vacuum D := by
  rw [source_exponential_product, bilinear_neg_left]
  simp [show -(bilinear D α α - 1) - 1 - -bilinear D α α = 0 by omega,
    creationCoeff, LatticeSugawaraConformal.exponential_constant, vacuum]

/-- Every strictly higher opposite-charge product is zero. -/
theorem source_opposite_higher (α : Charge D) (j : ℕ) (hj : 0 < j) :
    sourceProduct D (exponentialState (-α)) (bilinear D α α - 1 + j)
      (exponentialState α) = 0 := by
  rw [source_exponential_product, bilinear_neg_left]
  rw [show -(bilinear D α α - 1 + (j : ℤ)) - 1 - -bilinear D α α =
    -(j : ℤ) by omega]
  simp [creationCoeff, Nat.ne_of_gt hj]

/-- Source current/ground products, computed on the actual charged polynomial sector. -/
theorem source_current_exponential (i : Fin D.rank) (β : Charge D) (j : ℕ) :
    sourceProduct D (currentState D i) j (exponentialState β) =
      if j = 0 then (bilinear D (unitCharge D i) β : ℂ) •
        exponentialState β else 0 := by
  rw [sourceProduct, current_state_field, neutralField_ncoeff]
  by_cases hj : j = 0
  · subst j
    simp [exponentialState, neutralPolynomialMode, Finsupp.smul_single]
  · have hjpos : (0 : ℤ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
    simp [exponentialState, neutralPolynomialMode, not_lt.mpr hjpos.le,
      ne_of_gt hjpos, hj, LinearMap.smul_apply, LinearMap.sum_apply]

/-- Actual translation: the finite sum is over the original lattice coordinates. -/
theorem source_exponential_translation (α : Charge D) :
    LatticeSugawaraConformal.translation D (exponentialState α) =
      ∑ i : Fin D.rank, (α i : ℂ) •
        sourceProduct D (currentState D i) (-1) (exponentialState α) := by
  simp [sourceProduct, current_state_field, neutralField_ncoeff,
    exponentialState, neutralPolynomialMode, LatticeSugawaraConformal.chargePolynomial,
    Finsupp.smul_single, Finsupp.single_finsetSum]

/-- The basis-charge specialization needed in rank descent has one original current. -/
theorem source_unit_exponential_translation (i : Fin D.rank) :
    LatticeSugawaraConformal.translation D (exponentialState (unitCharge D i)) =
      sourceProduct D (currentState D i) (-1) (exponentialState (unitCharge D i)) := by
  rw [source_exponential_translation]
  simp [unitCharge]

/-- All integer mixed module modes, derived from the original module Jacobi equation. -/
theorem module_current_exponential (J : FullJacobiLatticeModule D M)
    (i : Fin D.rank) (β : Charge D) (m t : ℤ) :
    current J i m * mode J (exponentialState β) t -
      mode J (exponentialState β) t * current J i m =
      (bilinear D (unitCharge D i) β : ℂ) •
        mode J (exponentialState β) (m + t) := by
  classical
  rw [module_mode_commutator]
  rw [finsum_eq_single _ 0]
  · have hs := source_current_exponential (D := D) i β 0
    simp only [Nat.cast_zero, ite_true] at hs
    simp [commutatorTerm, hs, integerBinomial, mode]
  · intro j hj
    simp [commutatorTerm, source_current_exponential, hj, mode]

/-- Pointwise form, including m=0; this is used at the zero normal-product index. -/
theorem current_exponential_apply (J : FullJacobiLatticeModule D M)
    (i : Fin D.rank) (β : Charge D) (m t : ℤ) (v : M) :
    current J i m (mode J (exponentialState β) t v) =
      mode J (exponentialState β) t (current J i m v) +
        (bilinear D (unitCharge D i) β : ℂ) •
          mode J (exponentialState β) (m + t) v := by
  have h := LinearMap.congr_fun (module_current_exponential J i β m t) v
  exact sub_eq_iff_eq_add'.mp h

end
end D5.S3.VertexAlgebra.Modules.FullJacobiCurrentNilpotence
