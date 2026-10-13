/- GID: D5/S3/Arith/ModularForms/FiniteHeckeArray
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/FiniteHeckeArray
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHecke_integralCuspLattice; premises=D5/S3/Arith/ModularForms/FiniteHeckeArray.millerDepthArrays_correct
   digest: Integer array elimination computes the actual prime Hecke matrix. -/

import D5.S3.Arith.ModularForms.IntegralMillerBasis
import D5.S3.Arith.ModularForms.ActualPrimeHecke

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups
open scoped BigOperators Matrix

namespace D5.S3.Arith.ModularForms

/-- A finite raw coefficient row, computed only by integer divisor sums and convolution. -/
def rawMillerCoefficientArray (m s j N : ℕ) : Array ℤ :=
  Array.ofFn (fun n : Fin N => rawMillerCoefficient m s j n.val)

/-- Bottom-up descending Miller elimination. Each step reads the already stored rows once
and appends one new finite row. No analytic coefficient or inverse equivalence is used. -/
def millerDepthArrays (m s N : ℕ) : ℕ → Array (Array ℤ)
  | 0 => #[]
  | d + 1 =>
    let previous := millerDepthArrays m s N d
    let raw := rawMillerCoefficientArray m s (m - 1 - d) N
    previous.push (Array.ofFn (fun n : Fin N =>
      raw.getD n.val 0 - ∑ ell : Fin d,
        raw.getD (m - ell.val) 0 * (previous.getD ell.val #[]).getD n.val 0))

/-- Finite coefficient array of zero-based Miller basis vector `j`. -/
def millerCoefficientArray (m s N j : ℕ) : Array ℤ :=
  (millerDepthArrays m s N m).getD (m - 1 - j) #[]

/-- Read a Hecke matrix using only the stored finite coefficient rows, in depth order. -/
def integerHeckeMatrixFromArrays (p m k : ℕ) (rows : Array (Array ℤ)) :
    Matrix (Fin m) (Fin m) ℤ :=
  fun i j =>
    let row := rows.getD (m - 1 - j.val) #[]
    row.getD (p * (i.val + 1)) 0 + (p : ℤ) ^ (k - 1) *
      (if p ∣ i.val + 1 then row.getD ((i.val + 1) / p) 0 else 0)

/-- Executable integer matrix: materialize the finite Miller rows at precision `p*m+1`,
then read the Hecke entries. -/
def integerMillerHeckeMatrix (p m s : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  integerHeckeMatrixFromArrays p m (12 * m + s)
    (millerDepthArrays m s (p * m + 1) m)

private lemma rawMillerCoefficientArray_getD (m s j N n : ℕ) (hn : n < N) :
    (rawMillerCoefficientArray m s j N).getD n 0 = rawMillerCoefficient m s j n := by
  simp [rawMillerCoefficientArray, Array.getD, hn]

private lemma millerDepthArrays_size (m s N d : ℕ) :
    (millerDepthArrays m s N d).size = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [millerDepthArrays, Array.size_push, ih]

/-- The bottom-up table agrees with the unbounded integer coefficient recursion on every
stored index. Its proof is an induction over the materialized table, not analytic evaluation. -/
theorem millerDepthArrays_correct (m s N d : ℕ) (hN : m < N) (hd : d ≤ m) :
    ∀ e : ℕ, e < d →
      ((millerDepthArrays m s N d).getD e #[]).size = N ∧
        ∀ n : ℕ, n < N →
          ((millerDepthArrays m s N d).getD e #[]).getD n 0 =
            millerCoefficientDepth m s e n := by
  induction d with
  | zero => omega
  | succ d ih =>
    have hdm : d < m := by omega
    have ih' := ih (by omega)
    intro e he
    by_cases hed : e = d
    · subst e
      simp only [millerDepthArrays, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        millerDepthArrays_size, if_true, Option.getD_some]
      constructor
      · exact Array.size_ofFn
      · intro n hn
        rw [millerCoefficientDepth, if_pos hdm]
        simp only [Array.getElem?_ofFn, hn, ↓reduceDIte,
          Option.getD_some]
        simp only [← Array.getD_eq_getD_getElem?]
        rw [rawMillerCoefficientArray_getD _ _ _ _ _ hn]
        congr 1
        apply Finset.sum_congr rfl
        intro ell _
        rw [rawMillerCoefficientArray_getD _ _ _ _ _ (by omega)]
        rw [(ih' ell.val ell.isLt).2 n hn]
    · have helt : e < d := by omega
      simpa only [millerDepthArrays, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        millerDepthArrays_size, if_neg hed] using ih' e helt

private lemma millerCoefficientArray_correct (m s N : ℕ) (hN : m < N)
    (j : Fin m) :
    (millerCoefficientArray m s N j.val).size = N ∧
      ∀ n : ℕ, n < N →
        (millerCoefficientArray m s N j.val).getD n 0 = millerCoefficient m s j.val n := by
  exact millerDepthArrays_correct m s N m hN le_rfl (m - 1 - j.val) (by omega)

private lemma hecke_array_indices (p m : ℕ) [Fact p.Prime] (i : Fin m) :
    m < p * m + 1 ∧ p * (i.val + 1) < p * m + 1 ∧
      (i.val + 1) / p < p * m + 1 := by
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  have hi : i.val + 1 ≤ m := by omega
  have hpm : m ≤ p * m := by simpa using Nat.mul_le_mul_right m hp
  have hmul := Nat.mul_le_mul_left p hi
  have hdiv := (Nat.div_le_self (i.val + 1) p).trans (hi.trans hpm)
  omega

private lemma integerMillerHeckeMatrix_entry (p m s : ℕ) [Fact p.Prime] (i j : Fin m) :
    integerMillerHeckeMatrix p m s i j =
      millerCoefficient m s j.val (p * (i.val + 1)) +
        (p : ℤ) ^ (12 * m + s - 1) *
          (if p ∣ i.val + 1 then millerCoefficient m s j.val ((i.val + 1) / p) else 0) := by
  rcases hecke_array_indices p m i with ⟨hN, hmul, hdiv⟩
  change (millerCoefficientArray m s (p * m + 1) j.val).getD _ 0 +
    (p : ℤ) ^ (12 * m + s - 1) *
      (if p ∣ i.val + 1 then
        (millerCoefficientArray m s (p * m + 1) j.val).getD _ 0 else 0) = _
  rw [(millerCoefficientArray_correct m s _ hN j).2 _ hmul]
  split_ifs <;> simp only [(millerCoefficientArray_correct m s _ hN j).2 _ hdiv]

noncomputable section

private lemma miller_weight_sub_one (m s : ℕ) (hm : 1 ≤ m) :
    ((12 * m + s : ℕ) : ℤ) - 1 = ((12 * m + s - 1 : ℕ) : ℤ) := by
  have hk : 1 ≤ 12 * m + s := by omega
  exact (Int.ofNat_sub hk).symm

/-- The finite integer algorithm is the matrix of the existing actual analytic operator. -/
theorem integerMillerHeckeMatrix_map (p m s : ℕ) [Fact p.Prime]
    (hm : 1 ≤ m) (hs : MillerResidualWeight s) :
    (integerMillerHeckeMatrix p m s).map (Int.castRingHom ℂ) =
      LinearMap.toMatrix (integralMillerBasis m s hm hs) (integralMillerBasis m s hm hs)
        (primeHecke p (12 * m + s : ℕ)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change _ = millerCoefficientEquiv m s hm hs
    (primeHecke p (12 * m + s : ℕ) (integralMillerBasis m s hm hs j)) i
  rw [millerCoefficientEquiv_apply, primeHecke_qExpansion_coeff,
    integralMillerBasis_apply]
  simp_rw [millerForm_coefficient]
  rw [miller_weight_sub_one m s hm, zpow_natCast]
  change ((integerMillerHeckeMatrix p m s i j : ℤ) : ℂ) = _
  rw [integerMillerHeckeMatrix_entry]
  split_ifs <;> push_cast <;> rfl

/-- First-m actual coefficients conjugate the analytic operator to the computed integer matrix. -/
theorem millerHecke_conjugacy (p m s : ℕ) [Fact p.Prime]
    (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (f : CuspForm 𝒮ℒ (12 * m + s : ℕ)) :
    millerCoefficientEquiv m s hm hs (primeHecke p (12 * m + s : ℕ) f) =
      (integerMillerHeckeMatrix p m s).map (Int.castRingHom ℂ) *ᵥ
        millerCoefficientEquiv m s hm hs f := by
  have h := LinearMap.toMatrix_mulVec_repr (integralMillerBasis m s hm hs)
    (integralMillerBasis m s hm hs) (primeHecke p (12 * m + s : ℕ)) f
  rw [← integerMillerHeckeMatrix_map p m s hm hs] at h
  exact h.symm

/-- The actual prime Hecke endomorphism preserves the entire integral coefficient lattice. -/
theorem primeHecke_integralCuspLattice (p m s : ℕ) [Fact p.Prime]
    (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (f : integralCuspLattice (12 * m + s : ℕ)) :
    primeHecke p (12 * m + s : ℕ) f.val ∈ integralCuspLattice (12 * m + s : ℕ) := by
  apply (miller_integrality_iff m s hm hs _).mpr
  let z := (millerIntegerLatticeEquiv m s hm hs).symm f
  have hz (j : Fin m) : millerCoefficientEquiv m s hm hs f.val j = (z j : ℂ) := by
    rw [millerCoefficientEquiv_apply]
    exact (millerIntegerLatticeEquiv_symm_coefficient m s hm hs f j).symm
  intro i
  refine ⟨∑ j : Fin m, integerMillerHeckeMatrix p m s i j * z j, ?_⟩
  have h := congrFun (millerHecke_conjugacy p m s hm hs f.val) i
  rw [millerCoefficientEquiv_apply] at h
  change (qExpansion 1 (primeHecke p (12 * m + s : ℕ) f.val)).coeff (i.val + 1) =
    ∑ j : Fin m, (integerMillerHeckeMatrix p m s i j : ℂ) *
      millerCoefficientEquiv m s hm hs f.val j at h
  rw [h]
  simp_rw [hz]
  push_cast
  rfl

def millerLatticeHecke (p m s : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (hs : MillerResidualWeight s) :
    integralCuspLattice (12 * m + s : ℕ) →ₗ[ℤ]
      integralCuspLattice (12 * m + s : ℕ) :=
  (((primeHecke p (12 * m + s : ℕ)).restrictScalars ℤ).domRestrict
    (integralCuspLattice (12 * m + s : ℕ))).codRestrict _
      (primeHecke_integralCuspLattice p m s hm hs)


end
end D5.S3.Arith.ModularForms

#print axioms D5.S3.Arith.ModularForms.millerDepthArrays
#print axioms D5.S3.Arith.ModularForms.millerDepthArrays_correct
#print axioms D5.S3.Arith.ModularForms.integerMillerHeckeMatrix
#print axioms D5.S3.Arith.ModularForms.integerMillerHeckeMatrix_map
#print axioms D5.S3.Arith.ModularForms.millerHecke_conjugacy
#print axioms D5.S3.Arith.ModularForms.primeHecke_integralCuspLattice

#eval D5.S3.Arith.ModularForms.millerCoefficientArray 1 0 3 0
#eval Array.ofFn (fun i : Fin 1 => Array.ofFn (fun j : Fin 1 =>
  D5.S3.Arith.ModularForms.integerMillerHeckeMatrix 2 1 0 i j))
#eval D5.S3.Arith.ModularForms.millerCoefficientArray 2 0 5 0
#eval D5.S3.Arith.ModularForms.millerCoefficientArray 2 0 5 1
#eval Array.ofFn (fun i : Fin 2 => Array.ofFn (fun j : Fin 2 =>
  D5.S3.Arith.ModularForms.integerMillerHeckeMatrix 2 2 0 i j))
#eval let A := D5.S3.Arith.ModularForms.integerMillerHeckeMatrix 2 1 0
  #[-A 0 0, 1]
#eval let A := D5.S3.Arith.ModularForms.integerMillerHeckeMatrix 2 2 0
  #[A 0 0 * A 1 1 - A 0 1 * A 1 0, -(A 0 0 + A 1 1), 1]
