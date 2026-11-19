/- GID: D5/S3/FiniteGroups/GroupAlgebra/FiniteJetCoefficients
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/FiniteJetCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic]
   utility: none
   digest: Unique normalized linearized coordinates for actual finite-field linear maps. -/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
The single-variable linearized-polynomial basis proof below is adapted from
AxiomMath/CFSG, revision 69cb972f587a3ecc035e092253167ff2e303c962,
CFSG/LocalAnalysis/ComponentInitial/FieldFiniteLinearized.lean,
`eq_zero_of_forall_sum_mul_pow_eq_zero`, `linearIndependent_frobPowHom`, and the
single-variable part of `finite_field_linearized_linearMap_bases`.
Apache-2.0; the upstream license is in
docs/reports/licenses/cfsg-linearized-LICENSE.txt.
The adaptation uses the given algebra structure and native linear maps directly,
changes namespace and imports, and omits all bilinear constructions.
The normalized coordinate equivalence eliminates the coefficient of the identity
function by evaluation at one. Uniqueness is uniqueness of actual functions.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients
open Polynomial Finset Module
open scoped BigOperators
universe u
variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [Fintype K] [Algebra (ZMod p) K]

def frobLinear (j : ℕ) : K →ₗ[ZMod p] K :=
  (FiniteField.frobeniusAlgHom (ZMod p) K ^ j).toLinearMap

omit [Fintype K] in
theorem frobLinear_apply (j : ℕ) (x : K) :
    frobLinear (p := p) j x = x ^ p ^ j := by
  change (FiniteField.frobeniusAlgHom (ZMod p) K ^ j) x = _
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]

omit [Algebra (ZMod p) K] in
private theorem power_coefficients_zero {n : ℕ}
    (hn : p ^ (n - 1) < Fintype.card K) {a : Fin n → K}
    (ha : ∀ x : K, ∑ i, a i * x ^ p ^ (i : ℕ) = 0) : a = 0 := by
  classical
  have hp : p.Prime := Fact.out
  set P : K[X] := ∑ i : Fin n, C (a i) * X ^ p ^ (i : ℕ) with hPdef
  have hP : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := id) Function.injective_id
      (fun x => ?_) ?_
    · simp [P, eval_finsetSum, ha x]
    · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_) hn
      exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.pow_le_pow_right hp.pos (by omega))
  funext i
  have hc := congrArg (fun P : K[X] => P.coeff (p ^ (i : ℕ))) hP
  simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun j _ hji => ite_eq_right fun h =>
    hji (Fin.ext (Nat.pow_right_injective hp.two_le h).symm)) (by simp), ite_eq_left rfl] at hc
  exact hc

theorem linearized_coordinates {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) (q : K →ₗ[ZMod p] K) :
    ∃! a : Fin n → K, ∀ x, q x = ∑ i, a i * x ^ p ^ (i : ℕ) := by
  have hp : p.Prime := Fact.out
  have hlt : p ^ (n - 1) < Fintype.card K := by
    rw [hK]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hli : LinearIndependent K (fun i : Fin n => frobLinear (p := p) (K := K) i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    refine congrFun (power_coefficients_zero hlt fun x => ?_)
    simpa [frobLinear_apply] using DFunLike.congr_fun hg x
  have hrank : Module.finrank (ZMod p) K = n := by
    apply Nat.pow_right_injective hp.one_lt
    exact (FiniteField.pow_finrank_eq_card p K).trans hK
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin, Module.finrank_linearMap_self, hrank])
  have hB : ∀ i x, B i x = x ^ p ^ (i : ℕ) := fun i x => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank, frobLinear_apply]
  have hq : ∀ x, q x = ∑ i, B.repr q i * x ^ p ^ (i : ℕ) := fun x => by
    conv_lhs => rw [← B.sum_repr q]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hB]
  refine ⟨B.repr q, hq, fun a ha => ?_⟩
  have hz := power_coefficients_zero hlt (a := a - B.repr q) fun x => by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, ← ha x, ← hq x, sub_self]
  exact sub_eq_zero.mp hz

/-- Normalized prime-field-linear maps, with target-field scalar multiplication. -/
def Normalized : Submodule K (K →ₗ[ZMod p] K) where
  carrier := {q | q 1 = 0}
  zero_mem' := rfl
  add_mem' := by intro q r hq hr; simp_all
  smul_mem' := by intro c q hq; simp_all

/-- The full normalized linearized polynomial, including all zero coordinates. -/
def coefficientMap (n : ℕ) : (Fin (n - 1) → K) →ₗ[K] Normalized (p := p) (K := K) where
  toFun A := ⟨∑ i, A i • (frobLinear (p := p) (i.val + 1) - LinearMap.id), by
    simp [Normalized, frobLinear_apply]⟩
  map_add' A B := by apply Subtype.ext; simp [add_smul, Finset.sum_add_distrib]
  map_smul' c A := by apply Subtype.ext; simp [mul_smul, Finset.smul_sum]

@[simp] theorem coefficientMap_apply (n : ℕ) (A : Fin (n - 1) → K) (x : K) :
    (coefficientMap (p := p) n A).val x =
      ∑ i, A i * (x ^ p ^ (i.val + 1) - x) := by
  simp [coefficientMap, frobLinear_apply, smul_eq_mul]

private def extendCoefficients {m : ℕ} (A : Fin m → K) : Fin (m + 1) → K :=
  Fin.cons (-∑ i, A i) A

omit [Fact p.Prime] [Fintype K] [Algebra (ZMod p) K] in
private theorem extended_sum {m : ℕ} (A : Fin m → K) (x : K) :
    (∑ j, extendCoefficients A j * x ^ p ^ j.val) =
      ∑ i, A i * (x ^ p ^ (i.val + 1) - x) := by
  rw [Fin.sum_univ_succ]
  simp only [extendCoefficients, Fin.cons_zero, Fin.val_zero, pow_zero, pow_one,
    Fin.cons_succ, Fin.val_succ, neg_mul, Finset.sum_mul, mul_sub,
    Finset.sum_sub_distrib]
  ring

/-- Every normalized actual linear map has exactly one coefficient tuple. -/
theorem coefficientMap_bijective {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = p ^ n) :
    Function.Bijective (coefficientMap (p := p) (K := K) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  constructor
  · intro A B h
    have hA : ∀ x, (coefficientMap (p := p) (m + 1) A).val x =
        ∑ j, extendCoefficients A j * x ^ p ^ j.val := by
      intro x; rw [extended_sum, coefficientMap_apply]
    have hB : ∀ x, (coefficientMap (p := p) (m + 1) A).val x =
        ∑ j, extendCoefficients B j * x ^ p ^ j.val := by
      intro x; rw [h, extended_sum, coefficientMap_apply]
    have he := (linearized_coordinates (by omega : 1 ≤ m + 1) hK
      (coefficientMap (p := p) (m + 1) A).val).unique hA hB
    funext i
    exact congrFun he i.succ
  · intro q
    obtain ⟨a, ha, _⟩ := linearized_coordinates (by omega : 1 ≤ m + 1) hK q.val
    refine ⟨fun i => a i.succ, ?_⟩
    have ha0 : a 0 = -∑ i : Fin m, a i.succ := by
      have h := ha 1
      rw [q.property] at h
      simpa [Fin.sum_univ_succ, eq_neg_iff_add_eq_zero] using h.symm
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have hext : extendCoefficients (fun i : Fin m => a i.succ) = a := by
      funext j
      refine Fin.cases ?_ (fun i => rfl) j
      exact ha0.symm
    rw [coefficientMap_apply]
    calc
      _ = ∑ j : Fin (m + 1), extendCoefficients (fun i : Fin m => a i.succ) j * x ^ p ^ j.val :=
        (extended_sum (fun i : Fin m => a i.succ) x).symm
      _ = ∑ j : Fin (m + 1), a j * x ^ p ^ j.val := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun z : K => z * x ^ p ^ j.val) (congrFun hext j)
      _ = q.val x := (ha x).symm

/-- A linear equivalence on the given field, rather than a polynomial quotient. -/
def coefficientEquiv {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n) :
    (Fin (n - 1) → K) ≃ₗ[K] Normalized (p := p) (K := K) :=
  LinearEquiv.ofBijective (coefficientMap (p := p) n) (coefficientMap_bijective hn hK)

end D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients
