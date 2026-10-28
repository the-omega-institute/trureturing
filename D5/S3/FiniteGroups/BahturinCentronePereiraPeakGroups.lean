/- GID: D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BahturinCentronePereiraPeakGroups
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.claim; result=D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.result; claim=D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.claim
   digest: A central direct factor refutes the peak-group dichotomy. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389

The public claim retains the quantified source conventions, with the cyclic-Sylow
condition written directly in ComplementCondition and no separate declaration for it.
Mathlib's IsZGroup states the corresponding property; it is not on this module's
dependency path because the refutation excludes every Frobenius complement.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).

admission_basis: open-problem-resolution (#19254; Refuted)
Direct frozen dependencies: none.
BCP31.factPrimeFive | proof_shape: bind-only | escape_witness: none | consumer: BCP31.FixedCertificate, BCP31.LowerCertificate, BCP31.SL2F5_card, BCP31.SL2F5_not_solvable, BCP31.UpperCertificate, BCP31.fixed_0, BCP31.fixed_1, BCP31.fixed_2, BCP31.fixed_3, BCP31.fixed_4, BCP31.lower_one_0, BCP31.lower_one_1, BCP31.lower_one_2, BCP31.lower_one_3, BCP31.lower_one_4, BCP31.matrixActionValue_mul, BCP31.matrixAction_no_eigenvalue_one, BCP31.matrixAction_transvection0, BCP31.matrixAction_transvection0_one, BCP31.matrixAction_transvection1, BCP31.matrixAction_transvection1_one, BCP31.upper_one_0, BCP31.upper_one_1, BCP31.upper_one_2, BCP31.upper_one_3, BCP31.upper_one_4
BCP31.factPrimeEleven | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_card, BCP31.B_degree_dvd, BCP31.B_peak, BCP31.FixedCertificate, BCP31.LowerCertificate, BCP31.UpperCertificate, BCP31.actionTable, BCP31.actionTable_det0, BCP31.actionTable_det1, BCP31.actionTable_det2, BCP31.actionTable_det3, BCP31.actionTable_det4, BCP31.degree120Representation, BCP31.degree120Representation_finrank, BCP31.degree120Representation_simple, BCP31.degree120_mem, BCP31.fixed_0, BCP31.fixed_1, BCP31.fixed_2, BCP31.fixed_3, BCP31.fixed_4, BCP31.instFiniteSemidirectProductMultiplicativeProdZModOfNatNatSpecialLinearGroupFinPairAction, BCP31.kernelCharacter, BCP31.kernelCharacter_free_orbit, BCP31.lower_one_0, BCP31.lower_one_1, BCP31.lower_one_2, BCP31.lower_one_3, BCP31.lower_one_4, BCP31.matrixAction_no_eigenvalue_one, BCP31.matrixAction_transvection0_one, BCP31.matrixAction_transvection1_one, BCP31.pairAction, BCP31.pairAction_apply, BCP31.pairAction_fixed, BCP31.pairLinearAction, BCP31.rawAction_det, BCP31.result, BCP31.upper_one_0, BCP31.upper_one_1, BCP31.upper_one_2, BCP31.upper_one_3, BCP31.upper_one_4, BCP31.vectorCharacter, BCP31.vectorCharacter_free_orbit, BCP31.vectorKernelEquiv, BCP31.vectorKernelEquivSymmApply, BCP31.vectorKernel_conj, BCP31.vectorKernel_fixedPointFree, BCP31.vectorKernel_index, BCP31.vectorKernel_isMulCommutative
BCP31.degreeSet | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_peak, BCP31.IsPeak, BCP31.result
BCP31.IsPeak | proof_shape: bind-only | escape_witness: none | consumer: BCP31.claim, BCP31.refutation_of_peak, BCP31.result
BCP31.IsFrobeniusWithComplement | proof_shape: bind-only | escape_witness: none | consumer: BCP31.AlternativeTwo, BCP31.refutation_of_peak
BCP31.fitting | proof_shape: bind-only | escape_witness: none | consumer: BCP31.ComplementCondition
BCP31.fitting_normal | proof_shape: bind-only | escape_witness: none | consumer: BCP31.ComplementCondition
BCP31.HasAllowedOrder | proof_shape: bind-only | escape_witness: none | consumer: BCP31.ComplementCondition
BCP31.ComplementCondition | proof_shape: bind-only | escape_witness: none | consumer: BCP31.AlternativeTwo, BCP31.refutation_of_peak
BCP31.AlternativeTwo | proof_shape: bind-only | escape_witness: none | consumer: BCP31.claim, BCP31.refutation_of_peak
BCP31.claim | proof_shape: bind-only | escape_witness: none | consumer: BCP31.refutation_of_peak
BCP31.actionTable | proof_shape: bind-only | escape_witness: none | consumer: BCP31.FixedCertificate, BCP31.LowerCertificate, BCP31.UpperCertificate, BCP31.actionTable_det0, BCP31.actionTable_det1, BCP31.actionTable_det2, BCP31.actionTable_det3, BCP31.actionTable_det4, BCP31.fixed_0, BCP31.fixed_1, BCP31.fixed_2, BCP31.fixed_3, BCP31.fixed_4, BCP31.lower_one_0, BCP31.lower_one_1, BCP31.lower_one_2, BCP31.lower_one_3, BCP31.lower_one_4, BCP31.matrixAction_transvection0_one, BCP31.matrixAction_transvection1_one, BCP31.rawAction, BCP31.rawAction_det, BCP31.upper_one_0, BCP31.upper_one_1, BCP31.upper_one_2, BCP31.upper_one_3, BCP31.upper_one_4
BCP31.rawAction | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixActionValue, BCP31.matrixAction_transvection0_one, BCP31.matrixAction_transvection1_one, BCP31.rawAction_det
BCP31.actionTable_det0 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.rawAction_det
BCP31.actionTable_det1 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.rawAction_det
BCP31.actionTable_det2 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.rawAction_det
BCP31.actionTable_det3 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.rawAction_det
BCP31.actionTable_det4 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.rawAction_det
BCP31.rawAction_det | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixActionValue
BCP31.UpperCertificate | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_upper_one
BCP31.LowerCertificate | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_lower_one
BCP31.upper_one_0 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_upper_one
BCP31.upper_one_1 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_upper_one
BCP31.upper_one_2 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_upper_one
BCP31.upper_one_3 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_upper_one
BCP31.upper_one_4 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_upper_one
BCP31.actionTable_upper_one | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction_transvection0_one
BCP31.lower_one_0 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_lower_one
BCP31.lower_one_1 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_lower_one
BCP31.lower_one_2 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_lower_one
BCP31.lower_one_3 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_lower_one
BCP31.lower_one_4 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_lower_one
BCP31.actionTable_lower_one | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction_transvection1_one
BCP31.matrixActionValue | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction, BCP31.matrixActionValue_mul, BCP31.matrixActionValue_one, BCP31.matrixActionValue_pow_mul, BCP31.matrixAction_transvection0, BCP31.matrixAction_transvection0_one, BCP31.matrixAction_transvection1, BCP31.matrixAction_transvection1_one
BCP31.matrixActionValue_one | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction, BCP31.matrixAction_transvection0, BCP31.matrixAction_transvection1
BCP31.matrixAction_transvection0_one | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction_transvection0
BCP31.matrixAction_transvection1_one | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction_transvection1
BCP31.matrixActionValue_pow_mul | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction_transvection0, BCP31.matrixAction_transvection1
BCP31.matrixAction_transvection0 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixActionValue_mul
BCP31.matrixAction_transvection1 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixActionValue_mul
BCP31.matrixActionValue_mul | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction
BCP31.matrixAction | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction_no_eigenvalue_one, BCP31.pairAction_apply, BCP31.pairAction_fixed, BCP31.pairLinearAction, BCP31.vectorCharacter_free_orbit
BCP31.FixedCertificate | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_fixed
BCP31.fixed_0 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_fixed
BCP31.fixed_1 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_fixed
BCP31.fixed_2 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_fixed
BCP31.fixed_3 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_fixed
BCP31.fixed_4 | proof_shape: bind-only | escape_witness: none | consumer: BCP31.actionTable_fixed
BCP31.actionTable_fixed | proof_shape: bind-only | escape_witness: none | consumer: BCP31.matrixAction_no_eigenvalue_one
BCP31.matrixAction_no_eigenvalue_one | proof_shape: bind-only | escape_witness: none | consumer: BCP31.pairAction_fixed, BCP31.vectorCharacter_free_orbit
BCP31.pairLinearAction | proof_shape: bind-only | escape_witness: none | consumer: BCP31.pairAction
BCP31.pairAction | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_card, BCP31.B_degree_dvd, BCP31.B_peak, BCP31.degree120Representation, BCP31.degree120Representation_finrank, BCP31.degree120Representation_simple, BCP31.degree120_mem, BCP31.instFiniteSemidirectProductMultiplicativeProdZModOfNatNatSpecialLinearGroupFinPairAction, BCP31.kernelCharacter, BCP31.kernelCharacter_free_orbit, BCP31.pairAction_apply, BCP31.pairAction_fixed, BCP31.result, BCP31.vectorCharacter_free_orbit, BCP31.vectorKernelEquiv, BCP31.vectorKernelEquivSymmApply, BCP31.vectorKernel_conj, BCP31.vectorKernel_fixedPointFree, BCP31.vectorKernel_index, BCP31.vectorKernel_isMulCommutative
BCP31.pairAction_apply | proof_shape: bind-only | escape_witness: none | consumer: BCP31.vectorCharacter_free_orbit
BCP31.instFiniteSemidirectProductMultiplicativeProdZModOfNatNatSpecialLinearGroupFinPairAction | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_degree_dvd, BCP31.degree120Representation_simple
BCP31.SL2F5_card | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_card, BCP31.vectorKernel_index
BCP31.B_card | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_degree_dvd
BCP31.pairAction_fixed | proof_shape: bind-only | escape_witness: none | consumer: BCP31.vectorKernel_fixedPointFree
BCP31.vectorCharacter | proof_shape: bind-only | escape_witness: none | consumer: BCP31.kernelCharacter, BCP31.kernelCharacter_free_orbit, BCP31.vectorCharacter_free_orbit
BCP31.vectorCharacter_free_orbit | proof_shape: bind-only | escape_witness: none | consumer: BCP31.kernelCharacter_free_orbit
BCP31.SL2F5_not_solvable | proof_shape: bind-only | escape_witness: none | consumer: BCP31.semidirect_C2_not_solvable
BCP31.semidirect_C2_not_solvable | proof_shape: bind-only | escape_witness: none | consumer: BCP31.refutation_of_peak
BCP31.refutation_of_peak | proof_shape: content | escape_witness: D5.S3.FiniteGroups.FrobeniusCentralObstruction.central_eq_one_of_frobenius | consumer: BCP31.result
BCP31.vectorKernelEquiv | proof_shape: bind-only | escape_witness: none | consumer: BCP31.kernelCharacter, BCP31.kernelCharacter_free_orbit, BCP31.vectorKernelEquivSymmApply, BCP31.vectorKernel_conj, BCP31.vectorKernel_fixedPointFree, BCP31.vectorKernel_isMulCommutative
BCP31.vectorKernelEquivSymmApply | proof_shape: bind-only | escape_witness: none | consumer: BCP31.vectorKernel_conj
BCP31.kernelCharacter | proof_shape: bind-only | escape_witness: none | consumer: BCP31.degree120Representation, BCP31.degree120Representation_finrank, BCP31.degree120Representation_simple, BCP31.kernelCharacter_free_orbit
BCP31.vectorKernel_conj | proof_shape: bind-only | escape_witness: none | consumer: BCP31.kernelCharacter_free_orbit, BCP31.vectorKernel_fixedPointFree
BCP31.kernelCharacter_free_orbit | proof_shape: bind-only | escape_witness: none | consumer: BCP31.degree120Representation_simple
BCP31.vectorKernel_index | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_degree_dvd, BCP31.degree120Representation_finrank
BCP31.degree120Representation | proof_shape: bind-only | escape_witness: none | consumer: BCP31.degree120Representation_finrank, BCP31.degree120_mem
BCP31.degree120Representation_simple | proof_shape: content | escape_witness: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_ofLinearCharacter_iff | consumer: BCP31.degree120_mem
BCP31.degree120Representation_finrank | proof_shape: bind-only | escape_witness: none | consumer: BCP31.degree120_mem
BCP31.degree120_mem | proof_shape: content | escape_witness: D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_ofLinearCharacter_iff | consumer: BCP31.B_peak
BCP31.vectorKernel_isMulCommutative | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_degree_dvd
BCP31.vectorKernel_fixedPointFree | proof_shape: bind-only | escape_witness: none | consumer: BCP31.B_degree_dvd
BCP31.B_degree_dvd | proof_shape: content | escape_witness: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree | consumer: BCP31.B_peak
BCP31.B_peak | proof_shape: content | escape_witness: D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree | consumer: BCP31.result
BCP31.result | proof_shape: content | escape_witness: D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.degreesProdAbelian | consumer: terminal settling result
-/

import D5.S3.FiniteGroups.FrobeniusCentralObstruction
import D5.S3.FiniteGroups.FrobeniusCharacterDegrees
import D5.S3.FiniteGroups.MackeyCharacterFormula
import D5.S3.FiniteGroups.ComplexCharacterAbelianProducts
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
import D5.S3.FiniteGroups.InducedCharacterFormula
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
open scoped MatrixGroups

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

private instance factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
private instance factPrimeEleven : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩

/-- Degrees of simple finite-dimensional complex representations. -/
def degreeSet (G : Type) [Group G] : Set ℕ :=
  {d | ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ Module.finrank ℂ V = d}

/-- A greatest character degree for the divisibility order. -/
def IsPeak (G : Type) [Group G] : Prop :=
  ∃ d ∈ degreeSet G, ∀ e ∈ degreeSet G, e ∣ d

/-- The literal complement condition in Definition 28. -/
def IsFrobeniusWithComplement (G : Type) [Group G] (H : Subgroup G) : Prop :=
  H ≠ ⊥ ∧ H ≠ ⊤ ∧ ∀ g : G, g ∉ H → H ⊓ H.map (MulAut.conj g) = ⊥

/-- The finite-group Fitting subgroup, defined as the supremum of normal nilpotent subgroups. -/
def fitting (H : Type) [Group H] [Finite H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Group.IsNilpotent N}

instance fitting_normal (H : Type) [Group H] [Finite H] : (fitting H).Normal :=
  Subgroup.sSup_normal _ (fun _ hN => hN.1)

/-- The three excluded prime divisors of the order of T. -/
def HasAllowedOrder (T : Type) : Prop :=
  (¬ 2 ∣ Nat.card T) ∧ (¬ 3 ∣ Nat.card T) ∧ (¬ 5 ∣ Nat.card T)

/-- The structural condition imposed on the Frobenius complement. -/
def ComplementCondition (H : Type) [Group H] [Finite H] : Prop :=
  ∃ H0 : Subgroup (H ⧸ fitting H), H0.Normal ∧
    ∃ (T : Type) (_ : Group T) (_ : Finite T),
      Nonempty (H0 ≃* (SL(2, ZMod 5) × T)) ∧
        (∀ (p : ℕ) [Fact p.Prime] (P : Sylow p T), IsCyclic P) ∧ HasAllowedOrder T

/-- Alternative (2), including its complement witness. -/
def AlternativeTwo (G : Type) [Group G] [Finite G] : Prop :=
  ∃ H : Subgroup G, IsFrobeniusWithComplement G H ∧ ComplementCondition H

/-- Conjecture 31: exactly one of (1) and (2), for every finite group. -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPeak G →
    ((Group.IsSolvable G ∨ AlternativeTwo G) ∧ ¬ (Group.IsSolvable G ∧ AlternativeTwo G))

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open Matrix

private def actionTable (a b c d : Fin 5) : Matrix (Fin 2) (Fin 2) (ZMod 11) :=
  match a.val, b.val, c.val, d.val with
  | 0, 1, 4, 0 => !![1, 7; 6, 10]
  | 0, 1, 4, 1 => !![4, 10; 2, 8]
  | 0, 1, 4, 2 => !![5, 8; 8, 2]
  | 0, 1, 4, 3 => !![9, 2; 10, 6]
  | 0, 1, 4, 4 => !![3, 6; 7, 7]
  | 0, 2, 2, 0 => !![8, 6; 2, 3]
  | 0, 2, 2, 1 => !![7, 10; 10, 5]
  | 0, 2, 2, 2 => !![2, 2; 6, 1]
  | 0, 2, 2, 3 => !![10, 7; 8, 9]
  | 0, 2, 2, 4 => !![6, 8; 7, 4]
  | 0, 3, 3, 0 => !![3, 5; 9, 8]
  | 0, 3, 3, 1 => !![5, 3; 4, 7]
  | 0, 3, 3, 2 => !![1, 4; 3, 2]
  | 0, 3, 3, 3 => !![9, 9; 5, 10]
  | 0, 3, 3, 4 => !![4, 1; 1, 6]
  | 0, 4, 1, 0 => !![10, 4; 5, 1]
  | 0, 4, 1, 1 => !![8, 5; 4, 4]
  | 0, 4, 1, 2 => !![2, 9; 1, 5]
  | 0, 4, 1, 3 => !![6, 3; 3, 9]
  | 0, 4, 1, 4 => !![7, 1; 9, 3]
  | 1, 0, 0, 1 => !![1, 0; 0, 1]
  | 1, 0, 1, 1 => !![2, 4; 5, 5]
  | 1, 0, 2, 1 => !![2, 6; 2, 1]
  | 1, 0, 3, 1 => !![1, 5; 9, 2]
  | 1, 0, 4, 1 => !![5, 7; 6, 2]
  | 1, 1, 0, 1 => !![3, 0; 0, 4]
  | 1, 1, 1, 2 => !![6, 5; 4, 9]
  | 1, 1, 2, 3 => !![6, 2; 6, 4]
  | 1, 1, 3, 4 => !![3, 9; 5, 8]
  | 1, 1, 4, 0 => !![4, 6; 7, 8]
  | 1, 2, 0, 1 => !![9, 0; 0, 5]
  | 1, 2, 1, 3 => !![7, 9; 1, 3]
  | 1, 2, 2, 0 => !![7, 8; 7, 5]
  | 1, 2, 3, 2 => !![9, 3; 4, 10]
  | 1, 2, 4, 4 => !![1, 2; 10, 10]
  | 1, 3, 0, 1 => !![5, 0; 0, 9]
  | 1, 3, 1, 4 => !![10, 3; 3, 1]
  | 1, 3, 2, 2 => !![10, 10; 10, 9]
  | 1, 3, 3, 0 => !![5, 1; 1, 7]
  | 1, 3, 4, 3 => !![3, 8; 8, 7]
  | 1, 4, 0, 1 => !![4, 0; 0, 3]
  | 1, 4, 1, 0 => !![8, 1; 9, 4]
  | 1, 4, 2, 4 => !![8, 7; 8, 3]
  | 1, 4, 3, 3 => !![4, 4; 3, 6]
  | 1, 4, 4, 2 => !![9, 10; 2, 6]
  | 2, 0, 0, 3 => !![0, 5; 2, 0]
  | 2, 0, 1, 3 => !![10, 5; 4, 1]
  | 2, 0, 2, 3 => !![8, 10; 10, 3]
  | 2, 0, 3, 3 => !![3, 3; 4, 8]
  | 2, 0, 4, 3 => !![1, 10; 2, 10]
  | 2, 1, 0, 3 => !![0, 1; 10, 0]
  | 2, 1, 1, 1 => !![6, 1; 9, 9]
  | 2, 1, 2, 4 => !![7, 2; 6, 5]
  | 2, 1, 3, 2 => !![4, 5; 9, 6]
  | 2, 1, 4, 0 => !![5, 2; 10, 2]
  | 2, 2, 0, 3 => !![0, 9; 6, 0]
  | 2, 2, 1, 4 => !![8, 9; 1, 4]
  | 2, 2, 2, 0 => !![2, 7; 8, 1]
  | 2, 2, 3, 1 => !![9, 1; 1, 10]
  | 2, 2, 4, 2 => !![3, 7; 6, 7]
  | 2, 3, 0, 3 => !![0, 4; 8, 0]
  | 2, 3, 1, 2 => !![7, 4; 5, 3]
  | 2, 3, 2, 1 => !![10, 8; 7, 9]
  | 2, 3, 3, 0 => !![1, 9; 5, 2]
  | 2, 3, 4, 4 => !![4, 8; 8, 8]
  | 2, 4, 0, 3 => !![0, 3; 7, 0]
  | 2, 4, 1, 0 => !![2, 3; 3, 5]
  | 2, 4, 2, 2 => !![6, 6; 2, 4]
  | 2, 4, 3, 4 => !![5, 4; 3, 7]
  | 2, 4, 4, 1 => !![9, 6; 7, 6]
  | 3, 0, 0, 2 => !![0, 6; 9, 0]
  | 3, 0, 1, 2 => !![10, 1; 9, 1]
  | 3, 0, 2, 2 => !![8, 8; 7, 3]
  | 3, 0, 3, 2 => !![3, 1; 1, 8]
  | 3, 0, 4, 2 => !![1, 6; 7, 10]
  | 3, 1, 0, 2 => !![0, 8; 4, 0]
  | 3, 1, 1, 4 => !![2, 5; 4, 5]
  | 3, 1, 2, 1 => !![6, 7; 8, 4]
  | 3, 1, 3, 3 => !![5, 5; 9, 7]
  | 3, 1, 4, 0 => !![9, 8; 8, 6]
  | 3, 2, 0, 2 => !![0, 7; 3, 0]
  | 3, 2, 1, 1 => !![7, 3; 3, 3]
  | 3, 2, 2, 0 => !![10, 2; 6, 9]
  | 3, 2, 3, 4 => !![1, 3; 4, 2]
  | 3, 2, 4, 3 => !![4, 7; 6, 8]
  | 3, 3, 0, 2 => !![0, 2; 5, 0]
  | 3, 3, 1, 3 => !![8, 4; 5, 4]
  | 3, 3, 2, 4 => !![2, 10; 10, 1]
  | 3, 3, 3, 0 => !![9, 4; 3, 10]
  | 3, 3, 4, 1 => !![3, 2; 10, 7]
  | 3, 4, 0, 2 => !![0, 10; 1, 0]
  | 3, 4, 1, 0 => !![6, 9; 1, 9]
  | 3, 4, 2, 3 => !![7, 6; 2, 5]
  | 3, 4, 3, 1 => !![4, 9; 5, 6]
  | 3, 4, 4, 4 => !![5, 10; 2, 2]
  | 4, 0, 0, 4 => !![10, 0; 0, 10]
  | 4, 0, 1, 4 => !![6, 4; 5, 9]
  | 4, 0, 2, 4 => !![10, 6; 2, 9]
  | 4, 0, 3, 4 => !![9, 5; 9, 10]
  | 4, 0, 4, 4 => !![9, 7; 6, 6]
  | 4, 1, 0, 4 => !![7, 0; 0, 8]
  | 4, 1, 1, 3 => !![2, 1; 9, 5]
  | 4, 1, 2, 2 => !![7, 7; 8, 5]
  | 4, 1, 3, 1 => !![3, 4; 3, 8]
  | 4, 1, 4, 0 => !![3, 10; 2, 7]
  | 4, 2, 0, 4 => !![6, 0; 0, 2]
  | 4, 2, 1, 2 => !![8, 3; 3, 4]
  | 4, 2, 2, 0 => !![6, 10; 10, 4]
  | 4, 2, 3, 3 => !![1, 1; 1, 2]
  | 4, 2, 4, 1 => !![1, 8; 8, 10]
  | 4, 3, 0, 4 => !![2, 0; 0, 6]
  | 4, 3, 1, 1 => !![10, 9; 1, 1]
  | 4, 3, 2, 3 => !![2, 8; 7, 1]
  | 4, 3, 3, 0 => !![4, 3; 4, 6]
  | 4, 3, 4, 2 => !![4, 2; 10, 8]
  | 4, 4, 0, 4 => !![8, 0; 0, 7]
  | 4, 4, 1, 0 => !![7, 5; 4, 3]
  | 4, 4, 2, 1 => !![8, 2; 6, 3]
  | 4, 4, 3, 2 => !![5, 9; 5, 7]
  | 4, 4, 4, 3 => !![5, 6; 7, 2]
  | _, _, _, _ => 1

private def rawAction (g : SL(2, ZMod 5)) : Matrix (Fin 2) (Fin 2) (ZMod 11) :=
  actionTable ((ZMod.finEquiv 5).symm (g 0 0)) ((ZMod.finEquiv 5).symm (g 0 1)) ((ZMod.finEquiv 5).symm (g 1 0)) ((ZMod.finEquiv 5).symm (g 1 1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem actionTable_det0 : ∀ b c d : Fin 5,
    Matrix.det (actionTable 0 b c d) = 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem actionTable_det1 : ∀ b c d : Fin 5,
    Matrix.det (actionTable 1 b c d) = 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem actionTable_det2 : ∀ b c d : Fin 5,
    Matrix.det (actionTable 2 b c d) = 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem actionTable_det3 : ∀ b c d : Fin 5,
    Matrix.det (actionTable 3 b c d) = 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem actionTable_det4 : ∀ b c d : Fin 5,
    Matrix.det (actionTable 4 b c d) = 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

private theorem rawAction_det (g : SL(2, ZMod 5)) : Matrix.det (rawAction g) = 1 := by
  unfold rawAction
  generalize (ZMod.finEquiv 5).symm (g 0 0) = a
  fin_cases a
  · exact actionTable_det0 _ _ _
  · exact actionTable_det1 _ _ _
  · exact actionTable_det2 _ _ _
  · exact actionTable_det3 _ _ _
  · exact actionTable_det4 _ _ _

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open Matrix

private def UpperCertificate (s a : Fin 5) : Prop := ∀ b c d : Fin 5,
  Matrix.det !![ZMod.finEquiv 5 a, ZMod.finEquiv 5 b; ZMod.finEquiv 5 c, ZMod.finEquiv 5 d] = 1 →
  actionTable ((ZMod.finEquiv 5).symm ((ZMod.finEquiv 5) a + (ZMod.finEquiv 5) s * (ZMod.finEquiv 5) c))
    ((ZMod.finEquiv 5).symm ((ZMod.finEquiv 5) b + (ZMod.finEquiv 5) s * (ZMod.finEquiv 5) d)) c d =
  actionTable 1 s 0 1 * actionTable a b c d

private def LowerCertificate (s a : Fin 5) : Prop := ∀ b c d : Fin 5,
  Matrix.det !![ZMod.finEquiv 5 a, ZMod.finEquiv 5 b; ZMod.finEquiv 5 c, ZMod.finEquiv 5 d] = 1 →
  actionTable a b ((ZMod.finEquiv 5).symm ((ZMod.finEquiv 5) s * (ZMod.finEquiv 5) a + (ZMod.finEquiv 5) c))
    ((ZMod.finEquiv 5).symm ((ZMod.finEquiv 5) s * (ZMod.finEquiv 5) b + (ZMod.finEquiv 5) d)) =
  actionTable 1 0 s 1 * actionTable a b c d

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem upper_one_0 : UpperCertificate 1 0 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem upper_one_1 : UpperCertificate 1 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem upper_one_2 : UpperCertificate 1 2 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem upper_one_3 : UpperCertificate 1 3 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem upper_one_4 : UpperCertificate 1 4 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem actionTable_upper_one (a : Fin 5) : UpperCertificate 1 a := by
  fin_cases a
  · exact upper_one_0
  · exact upper_one_1
  · exact upper_one_2
  · exact upper_one_3
  · exact upper_one_4

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem lower_one_0 : LowerCertificate 1 0 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem lower_one_1 : LowerCertificate 1 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem lower_one_2 : LowerCertificate 1 2 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem lower_one_3 : LowerCertificate 1 3 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem lower_one_4 : LowerCertificate 1 4 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)

private theorem actionTable_lower_one (a : Fin 5) : LowerCertificate 1 a := by
  fin_cases a
  · exact lower_one_0
  · exact lower_one_1
  · exact lower_one_2
  · exact lower_one_3
  · exact lower_one_4

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

open scoped MatrixGroups

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open Matrix
set_option maxHeartbeats 1500000

private def matrixActionValue (g : SL(2, ZMod 5)) : SL(2, ZMod 11) :=
  ⟨rawAction g, rawAction_det g⟩

private theorem matrixActionValue_one : matrixActionValue 1 = 1 := by
  decide

private theorem matrixAction_transvection0_one (g : SL(2, ZMod 5)) :
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) (1 : ZMod 5) * g) =
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) (1 : ZMod 5)) * matrixActionValue g := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  change rawAction (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) (1 : ZMod 5) * g) =
    rawAction (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) (1 : ZMod 5)) * rawAction g
  have hd : Matrix.det !![ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 0 0)), ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 0 1)); ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 1 0)), ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 1 1))] = 1 := by
    simpa only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, RingEquiv.apply_symm_apply] using g.property
  have h := actionTable_upper_one ((ZMod.finEquiv 5).symm (g 0 0)) ((ZMod.finEquiv 5).symm (g 0 1))
    ((ZMod.finEquiv 5).symm (g 1 0)) ((ZMod.finEquiv 5).symm (g 1 1)) hd
  simpa [rawAction, SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.single_apply, RingEquiv.apply_symm_apply, map_one, map_zero] using h

private theorem matrixAction_transvection1_one (g : SL(2, ZMod 5)) :
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) (1 : ZMod 5) * g) =
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) (1 : ZMod 5)) * matrixActionValue g := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul]
  change rawAction (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) (1 : ZMod 5) * g) =
    rawAction (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) (1 : ZMod 5)) * rawAction g
  have hd : Matrix.det !![ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 0 0)), ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 0 1)); ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 1 0)), ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 1 1))] = 1 := by
    simpa only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, RingEquiv.apply_symm_apply] using g.property
  have h := actionTable_lower_one ((ZMod.finEquiv 5).symm (g 0 0)) ((ZMod.finEquiv 5).symm (g 0 1))
    ((ZMod.finEquiv 5).symm (g 1 0)) ((ZMod.finEquiv 5).symm (g 1 1)) hd
  simpa [rawAction, SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.single_apply, RingEquiv.apply_symm_apply, map_one, map_zero] using h

private theorem matrixActionValue_pow_mul (t : SL(2, ZMod 5))
    (ht : ∀ g, matrixActionValue (t * g) = matrixActionValue t * matrixActionValue g)
    (n : ℕ) (g : SL(2, ZMod 5)) :
    matrixActionValue (t ^ n * g) = matrixActionValue t ^ n * matrixActionValue g := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      matrixActionValue (t ^ (n + 1) * g) = matrixActionValue (t * (t ^ n * g)) := by
        rw [pow_succ', mul_assoc]
      _ = matrixActionValue t * matrixActionValue (t ^ n * g) := ht _
      _ = matrixActionValue t * (matrixActionValue t ^ n * matrixActionValue g) := by rw [ih]
      _ = matrixActionValue t ^ (n + 1) * matrixActionValue g := by rw [pow_succ', mul_assoc]

private theorem matrixAction_transvection0 (c : ZMod 5) (g : SL(2, ZMod 5)) :
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) c * g) =
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) c) * matrixActionValue g := by
  let t : SL(2, ZMod 5) := Matrix.SpecialLinearGroup.transvection
    (i := (0 : Fin 2)) (j := 1) (by decide) 1
  have heq : Matrix.SpecialLinearGroup.transvection
      (i := (0 : Fin 2)) (j := 1) (by decide) c = t ^ c.val := by
    fin_cases c <;> decide +kernel
  rw [heq]
  have hpow : matrixActionValue (t ^ c.val) = matrixActionValue t ^ c.val := by
    simpa [matrixActionValue_one] using
      matrixActionValue_pow_mul t matrixAction_transvection0_one c.val 1
  rw [hpow]
  exact matrixActionValue_pow_mul t matrixAction_transvection0_one c.val g

private theorem matrixAction_transvection1 (c : ZMod 5) (g : SL(2, ZMod 5)) :
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) c * g) =
    matrixActionValue (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) c) * matrixActionValue g := by
  let t : SL(2, ZMod 5) := Matrix.SpecialLinearGroup.transvection
    (i := (1 : Fin 2)) (j := 0) (by decide) 1
  have heq : Matrix.SpecialLinearGroup.transvection
      (i := (1 : Fin 2)) (j := 0) (by decide) c = t ^ c.val := by
    fin_cases c <;> decide +kernel
  rw [heq]
  have hpow : matrixActionValue (t ^ c.val) = matrixActionValue t ^ c.val := by
    simpa [matrixActionValue_one] using
      matrixActionValue_pow_mul t matrixAction_transvection1_one c.val 1
  rw [hpow]
  exact matrixActionValue_pow_mul t matrixAction_transvection1_one c.val g

private theorem matrixActionValue_mul (a b : SL(2, ZMod 5)) :
    matrixActionValue (a * b) = matrixActionValue a * matrixActionValue b := by
  have hP : ∀ a : SL(2, ZMod 5), ∀ b : SL(2, ZMod 5),
      matrixActionValue (a * b) = matrixActionValue a * matrixActionValue b := by
    intro a
    refine Matrix.SL2.transvection_induction
      (fun a => ∀ b : SL(2, ZMod 5),
        matrixActionValue (a * b) = matrixActionValue a * matrixActionValue b) ?_ ?_ a
    · intro i j hij c
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact matrixAction_transvection0 c
      · exact matrixAction_transvection1 c
      · exact (hij rfl).elim
    · intro a b ha hb g
      calc
        matrixActionValue ((a * b) * g) = matrixActionValue (a * (b * g)) := by rw [mul_assoc]
        _ = matrixActionValue a * matrixActionValue (b * g) := ha _
        _ = matrixActionValue a * (matrixActionValue b * matrixActionValue g) := by rw [hb]
        _ = (matrixActionValue a * matrixActionValue b) * matrixActionValue g := (mul_assoc _ _ _).symm
        _ = matrixActionValue (a * b) * matrixActionValue g := by rw [ha b]
  exact hP a b

private def matrixAction : SL(2, ZMod 5) →* SL(2, ZMod 11) where
  toFun := matrixActionValue
  map_one' := matrixActionValue_one
  map_mul' := matrixActionValue_mul

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

open scoped MatrixGroups

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open Matrix

private def FixedCertificate (a : Fin 5) : Prop := ∀ b c d : Fin 5,
  Matrix.det !![ZMod.finEquiv 5 a, ZMod.finEquiv 5 b; ZMod.finEquiv 5 c, ZMod.finEquiv 5 d] = 1 → Matrix.det (actionTable a b c d - 1) = 0 →
  a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem fixed_0 : FixedCertificate 0 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; decide +kernel)

private theorem fixed_1 : FixedCertificate 1 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; decide +kernel)

private theorem fixed_2 : FixedCertificate 2 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; decide +kernel)

private theorem fixed_3 : FixedCertificate 3 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; decide +kernel)

private theorem fixed_4 : FixedCertificate 4 := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | (intro h; exact absurd h (by decide +kernel))
    | (intro _; decide +kernel)

private theorem actionTable_fixed (a : Fin 5) : FixedCertificate a := by
  fin_cases a
  · exact fixed_0
  · exact fixed_1
  · exact fixed_2
  · exact fixed_3
  · exact fixed_4

private theorem matrixAction_no_eigenvalue_one (g : SL(2, ZMod 5)) (hg : g ≠ 1) :
    Matrix.det ((matrixAction g).val - 1) ≠ 0 := by
  intro hz
  have hd : Matrix.det !![ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 0 0)), ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 0 1)); ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 1 0)), ZMod.finEquiv 5 ((ZMod.finEquiv 5).symm (g 1 1))] = 1 := by
    simpa only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, RingEquiv.apply_symm_apply] using g.property
  obtain ⟨ha, hb, hc, hd⟩ := actionTable_fixed ((ZMod.finEquiv 5).symm (g 0 0)) ((ZMod.finEquiv 5).symm (g 0 1))
    ((ZMod.finEquiv 5).symm (g 1 0)) ((ZMod.finEquiv 5).symm (g 1 1)) hd hz
  have ha' : g 0 0 = 1 := Eq.symm (ZMod.toAddCircle_inj.mp (congrArg (⇑ZMod.toAddCircle) ha.symm))
  have hb' : g 0 1 = 0 := Eq.symm (ZMod.toAddCircle_inj.mp (congrArg (⇑ZMod.toAddCircle) hb.symm))
  have hc' : g 1 0 = 0 := Eq.symm (ZMod.toAddCircle_inj.mp (congrArg (⇑ZMod.toAddCircle) hc.symm))
  have hd' : g 1 1 = 1 := Eq.symm (ZMod.toAddCircle_inj.mp (congrArg (⇑ZMod.toAddCircle) hd.symm))
  apply hg
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha', hb', hc', hd']

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

open scoped MatrixGroups

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open Matrix

private def pairLinearAction : SL(2, ZMod 5) →* ((ZMod 11 × ZMod 11) ≃ₗ[ZMod 11] (ZMod 11 × ZMod 11)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 11) (Fin 2 → ZMod 11)).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv
      (LinearEquiv.finTwoArrow (ZMod 11) (ZMod 11))).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 11) (ZMod 11 × ZMod 11)))).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.toLin'.comp matrixAction)

private def pairAction : SL(2, ZMod 5) →* MulAut (Multiplicative (ZMod 11 × ZMod 11)) :=
  ((MulAutMultiplicative (ZMod 11 × ZMod 11)).symm.toMonoidHom.comp
    (DistribMulAction.toAddAut
      ((ZMod 11 × ZMod 11) ≃ₗ[ZMod 11] (ZMod 11 × ZMod 11))
      (ZMod 11 × ZMod 11))).comp pairLinearAction

private theorem pairAction_apply (g : SL(2, ZMod 5)) (v : (ZMod 11 × ZMod 11)) :
    Multiplicative.toAdd (pairAction g (Multiplicative.ofAdd v)) =
      ((matrixAction g) 0 0 * v.1 + (matrixAction g) 0 1 * v.2,
       (matrixAction g) 1 0 * v.1 + (matrixAction g) 1 1 * v.2) := by
  change (LinearEquiv.finTwoArrow (ZMod 11) (ZMod 11)) ((matrixAction g).val *ᵥ (LinearEquiv.finTwoArrow (ZMod 11) (ZMod 11)).symm v) = _
  apply Prod.ext <;>
    simp [LinearEquiv.finTwoArrow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]


private instance : Finite ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) :=
  Finite.of_equiv ((Multiplicative (ZMod 11 × ZMod 11)) × SL(2, ZMod 5)) SemidirectProduct.equivProd.symm

private theorem SL2F5_card : Nat.card SL(2, ZMod 5) = 120 := by
  rw [Matrix.card_SL_field]
  norm_num [Fin.prod_univ_two]

private theorem B_card : Nat.card ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) = 14520 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, SL2F5_card]
  change Nat.card (ZMod 11 × ZMod 11) * 120 = 14520
  norm_num [Nat.card_prod, Nat.card_zmod]

private theorem pairAction_fixed (g : SL(2, ZMod 5)) (v : (Multiplicative (ZMod 11 × ZMod 11)))
    (hv : v ≠ 1) (hfix : pairAction g v = v) : g = 1 := by
  by_contra hg
  have hnonzero := matrixAction_no_eigenvalue_one g hg
  let w : Fin 2 → ZMod 11 := (LinearEquiv.finTwoArrow (ZMod 11) (ZMod 11)).symm (Multiplicative.toAdd v)
  have hw : w ≠ 0 := AddEquivClass.map_ne_zero_iff.mpr hv
  have hf : (matrixAction g).val *ᵥ w = w :=
    (LinearEquiv.eq_symm_apply (LinearEquiv.finTwoArrow (ZMod 11) (ZMod 11))).mpr hfix
  apply hw
  apply Matrix.eq_zero_of_mulVec_eq_zero hnonzero
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hf, sub_self]

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

open scoped MatrixGroups

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

private noncomputable def vectorCharacter : (Multiplicative (ZMod 11 × ZMod 11)) →* ℂˣ :=
  ((ZMod.stdAddChar (N := 11)).compAddMonoidHom
    (AddMonoidHom.fst (ZMod 11) (ZMod 11))).toMonoidHom.toHomUnits

/-- No nonidentity complement element stabilizes the coordinate character. -/
private theorem vectorCharacter_free_orbit (g : SL(2, ZMod 5)) (hg : g ≠ 1) :
    ∃ v : (Multiplicative (ZMod 11 × ZMod 11)), vectorCharacter (pairAction g v) ≠ vectorCharacter v := by
  by_contra h
  push_neg at h
  have h10 := h (Multiplicative.ofAdd ((1 : ZMod 11), (0 : ZMod 11)))
  have h01 := h (Multiplicative.ofAdd ((0 : ZMod 11), (1 : ZMod 11)))
  have h00 : (matrixAction g) 0 0 = 1 := by
    apply ZMod.injective_stdAddChar
    have hc := Units.val_inj.mpr h10
    simpa [vectorCharacter, pairAction_apply] using hc
  have h01' : (matrixAction g) 0 1 = 0 := by
    apply ZMod.injective_stdAddChar
    have hc := Units.val_inj.mpr h01
    simpa [vectorCharacter, pairAction_apply] using hc
  have hn := matrixAction_no_eigenvalue_one g hg
  apply hn
  simp [Matrix.det_fin_two, h00, h01']

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

open scoped MatrixGroups

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31


set_option maxHeartbeats 400000

/-- Reuse of the matrix-group perfection theorem; consumed below. -/
private theorem SL2F5_not_solvable : ¬ Group.IsSolvable SL(2, ZMod 5) := by
  intro hsol
  haveI := hsol
  let a : SL(2, ZMod 5) := -1
  have hne : a ≠ 1 := by
    intro h
    have h00 : (-1 : ZMod 5) = 1 := by
      simpa [a] using congrArg (fun g : SL(2, ZMod 5) => g 0 0) h
    exact (by decide : (-1 : ZMod 5) ≠ 1) h00
  haveI : Nontrivial SL(2, ZMod 5) := ⟨⟨a, 1, hne⟩⟩
  have hperfect : commutator SL(2, ZMod 5) = ⊤ :=
    Matrix.SL2.commutator_eq_top (a := (2 : ZMod 5)) (by decide) (by decide)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial SL(2, ZMod 5)).ne hperfect

/-- Every semidirect product with SL(2,5), and its product with C₂, is nonsolvable. -/
private theorem semidirect_C2_not_solvable {N : Type} [Group N]
    (φ : SL(2, ZMod 5) →* MulAut N) :
    ¬ Group.IsSolvable ((N ⋊[φ] SL(2, ZMod 5)) × Multiplicative (ZMod 2)) := by
  intro hsol
  haveI := hsol
  let f : ((N ⋊[φ] SL(2, ZMod 5)) × Multiplicative (ZMod 2)) →* SL(2, ZMod 5) :=
    SemidirectProduct.rightHom.comp (MonoidHom.fst _ _)
  have hf : Function.Surjective f := by
    intro h
    exact ⟨(SemidirectProduct.inr h, 1), rfl⟩
  exact SL2F5_not_solvable (Group.isSolvable_of_surjective hf)

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

private theorem refutation_of_peak {N : Type} [Group N] [Finite N]
    (φ : SL(2, ZMod 5) →* MulAut N)
    (hpeak : IsPeak ((N ⋊[φ] SL(2, ZMod 5)) × Multiplicative (ZMod 2))) : ¬ claim := by
  letI : Finite (N ⋊[φ] SL(2, ZMod 5)) :=
    Finite.of_equiv (N × SL(2, ZMod 5)) SemidirectProduct.equivProd.symm
  intro hc
  rcases (hc ((N ⋊[φ] SL(2, ZMod 5)) × Multiplicative (ZMod 2)) hpeak).1 with hsol | halt
  · exact semidirect_C2_not_solvable φ hsol
  · obtain ⟨H, hH, _⟩ := halt
    have hz := D5.S3.FiniteGroups.FrobeniusCentralObstruction.central_eq_one_of_frobenius
      hH.1 hH.2.1 hH.2.2 (z := (1, Multiplicative.ofAdd (1 : ZMod 2))) (by
        intro g
        apply Prod.ext
        · simp
        · exact mul_comm g.2 (Multiplicative.ofAdd (1 : ZMod 2)))
    exact one_ne_zero (congrArg (fun z => Multiplicative.toAdd z.2) hz)

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

open scoped MatrixGroups

namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open CategoryTheory


private noncomputable def vectorKernelEquiv : (Multiplicative (ZMod 11 × ZMod 11)) ≃* ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker) :=
  (MonoidHom.ofInjective (f := SemidirectProduct.inl)
    SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)

private theorem vectorKernelEquivSymmApply (v : ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker)) :
    vectorKernelEquiv.symm v = v.val.left := by
  have h := congrArg (fun x : ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker) => x.val.left) (vectorKernelEquiv.apply_symm_apply v)
  exact h

private noncomputable def kernelCharacter : ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker) →* ℂˣ :=
  vectorCharacter.comp vectorKernelEquiv.symm.toMonoidHom

private theorem vectorKernel_conj (s : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5))) (v : ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker)) :
    vectorKernelEquiv.symm (MulAut.conjNormal s v) =
      pairAction s.right (vectorKernelEquiv.symm v) := by
  rw [vectorKernelEquivSymmApply, vectorKernelEquivSymmApply]
  have hv : v.val.right = 1 := v.property
  change (s * v.val * s⁻¹).left = pairAction s.right v.val.left
  simp [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hv, map_mul, mul_comm, mul_left_comm, mul_assoc]

private theorem kernelCharacter_free_orbit :
    ∀ s : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)), s ∉ ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker) →
      ∃ v : ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker), kernelCharacter (MulAut.conjNormal s v) ≠ kernelCharacter v := by
  intro s hs
  have hsr : s.right ≠ 1 := hs
  obtain ⟨v, hv⟩ := vectorCharacter_free_orbit s.right hsr
  refine ⟨vectorKernelEquiv v, ?_⟩
  simpa [kernelCharacter, vectorKernel_conj] using hv

private theorem vectorKernel_index : ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker).index = 120 := by
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective,
    Subgroup.card_top, SL2F5_card]

private noncomputable def degree120Representation : FDRep ℂ ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) :=
  _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indFDRep (_root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.ofLinearCharacter kernelCharacter)

private instance degree120Representation_simple : Simple degree120Representation :=
  (_root_.D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_ofLinearCharacter_iff kernelCharacter).mpr kernelCharacter_free_orbit

private theorem degree120Representation_finrank : Module.finrank ℂ degree120Representation = 120 := by
  rw [degree120Representation, _root_.D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.finrank_indFDRep, _root_.D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.finrank_ofLinearCharacter,
    vectorKernel_index, mul_one]

private theorem degree120_mem : 120 ∈ degreeSet ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) :=
  ⟨degree120Representation, inferInstance, degree120Representation_finrank⟩

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31

open scoped MatrixGroups
namespace D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
open CategoryTheory D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti D5.S3.FiniteGroups.CliffordConstituents.TauCeti D5.S3.FiniteGroups.CliffordDecomposition.TauCeti D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti

private instance vectorKernel_isMulCommutative : IsMulCommutative ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker) where
  is_comm.comm a b := by
    apply vectorKernelEquiv.symm.injective
    simp only [map_mul]
    exact mul_comm _ _

private theorem vectorKernel_fixedPointFree (s : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5))) (hs : s ∉ ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker))
    (n : ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker)) (hn : MulAut.conjNormal s n = n) : n = 1 := by
  have hsr : s.right ≠ 1 := hs
  have hn' := congrArg vectorKernelEquiv.symm hn
  rw [vectorKernel_conj] at hn'
  have hz : vectorKernelEquiv.symm n = 1 := by
    by_contra hne
    exact hsr (pairAction_fixed s.right _ hne hn')
  exact vectorKernelEquiv.symm.injective (by simpa using hz)

private theorem B_degree_dvd (W : FDRep ℂ ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5))) [Simple W] : Module.finrank ℂ W ∣ 120 := by
  have hd := D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree ((SemidirectProduct.rightHom : ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) →* SL(2, ZMod 5)).ker)
    vectorKernel_fixedPointFree W
  rw [vectorKernel_index] at hd
  rcases hd with hd | hd
  · exact hd
  · have hp : 0 < Module.finrank ℂ W :=
      _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.finrank_pos (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple W)
    have hsq := D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_square_le_card ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) W
    rw [B_card] at hsq
    have hlo : 120 ≤ Module.finrank ℂ W := Nat.le_of_dvd hp hd
    have hhi : Module.finrank ℂ W < 240 := by nlinarith
    obtain ⟨m, hm⟩ := hd
    have hm1 : m = 1 := by omega
    simpa [hm, hm1]

private theorem B_peak : IsPeak ((Multiplicative (ZMod 11 × ZMod 11)) ⋊[pairAction] SL(2, ZMod 5)) := by
  refine ⟨120, degree120_mem, ?_⟩
  rintro d ⟨W, hW, rfl⟩
  letI := hW
  exact B_degree_dvd W

theorem result : ¬ BCP31.claim :=
  refutation_of_peak pairAction
    (by
      rcases B_peak with ⟨d, hd, hdiv⟩
      refine ⟨d, ?_, ?_⟩
      · simpa only [degreeSet, D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.degreesProdAbelian] using hd
      · simpa only [degreeSet, D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.degreesProdAbelian] using hdiv)

end D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31
