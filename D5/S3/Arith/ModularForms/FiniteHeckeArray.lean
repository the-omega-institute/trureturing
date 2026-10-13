/- GID: D5/S3/Arith/ModularForms/FiniteHeckeArray
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/FiniteHeckeArray
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Finite q-expansion array transport for the actual prime Hecke action. -/

import D5.S3.Arith.ModularForms.ActualPrimeHecke
import D5.S3.Arith.ModularForms.IntegralMillerBasis

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups
open scoped BigOperators

namespace D5.S3.Arith.ModularForms

noncomputable section

/-!
The array below stores coefficients through `q^N`, including the constant term.
The `p * m + 1` instance is therefore exactly the precision needed to read the
first `m` nonconstant coefficients after applying `T_p`.
-/

def finiteCoefficientArray {k : ℤ} (f : CuspForm 𝒮ℒ k) (N : ℕ) : Fin (N + 1) → ℂ :=
  fun i => (qExpansion 1 f).coeff i.val

@[simp]
theorem finiteCoefficientArray_apply {k : ℤ} (f : CuspForm 𝒮ℒ k) (N : ℕ)
    (i : Fin (N + 1)) :
    finiteCoefficientArray f N i = (qExpansion 1 f).coeff i.val :=
  rfl

private lemma hecke_mul_index_lt (p m : ℕ) (hp : 0 < p) (i : Fin m) :
    p * (i.val + 1) < p * m + 1 := by
  have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
  have hmul : p * (i.val + 1) ≤ p * m := Nat.mul_le_mul_left p hi
  omega

private lemma hecke_div_index_lt (p m : ℕ) (hp : 0 < p) (i : Fin m) :
    (i.val + 1) / p < p * m + 1 := by
  have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
  have hpone : 1 ≤ p := hp
  have hpm : m ≤ p * m := by
    simpa using (Nat.mul_le_mul_right m hpone)
  have hq : (i.val + 1) / p ≤ i.val + 1 := Nat.div_le_self _ _
  have hle : (i.val + 1) / p ≤ p * m := hq.trans (hi.trans hpm)
  exact lt_of_le_of_lt hle (Nat.lt_succ_self _)

private def heckeMulIndex (p m : ℕ) [Fact p.Prime] (i : Fin m) : Fin (p * m + 1) :=
  ⟨p * (i.val + 1), hecke_mul_index_lt p m (show 0 < p from (show Nat.Prime p from Fact.out).pos) i⟩

private def heckeDivIndex (p m : ℕ) [Fact p.Prime] (i : Fin m) : Fin (p * m + 1) :=
  ⟨(i.val + 1) / p, hecke_div_index_lt p m (show 0 < p from (show Nat.Prime p from Fact.out).pos) i⟩

@[simp]
private lemma heckeMulIndex_val (p m : ℕ) [Fact p.Prime] (i : Fin m) :
    (heckeMulIndex p m i).val = p * (i.val + 1) :=
  rfl

@[simp]
private lemma heckeDivIndex_val (p m : ℕ) [Fact p.Prime] (i : Fin m) :
    (heckeDivIndex p m i).val = (i.val + 1) / p :=
  rfl

def primeHeckeFiniteCoordinate (p m : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) (i : Fin m) : ℂ :=
  finiteCoefficientArray f (p * m) (heckeMulIndex p m i) +
    (p : ℂ) ^ (k - 1) *
      (if p ∣ i.val + 1 then
        finiteCoefficientArray f (p * m) (heckeDivIndex p m i)
      else 0)

theorem primeHeckeFiniteCoordinate_eq (p m : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) (i : Fin m) :
    (qExpansion 1 (primeHecke p k f)).coeff (i.val + 1) =
      primeHeckeFiniteCoordinate p m k f i := by
  rw [primeHecke_qExpansion_coeff]
  rfl

/-!
The first `m` coefficients of `T_p f` are obtained from the finite source
array of length `p*m+1`.  This is the composable finite-precision statement;
the right side contains no coefficient beyond the declared array.
-/
theorem primeHecke_first_coefficients_from_array (p m : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) :
    ∀ i : Fin m,
      (qExpansion 1 (primeHecke p k f)).coeff (i.val + 1) =
        primeHeckeFiniteCoordinate p m k f i := by
  intro i
  exact primeHeckeFiniteCoordinate_eq p m k f i

def primeHeckeMillerMatrix (p m s : ℕ) [Fact p.Prime]
    (hm : 1 ≤ m) (hs : MillerResidualWeight s) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => primeHeckeFiniteCoordinate p m (12 * m + s : ℕ)
    (millerForm m s hs j) i

theorem primeHeckeMillerMatrix_apply_basis (p m s : ℕ) [Fact p.Prime]
    (hm : 1 ≤ m) (hs : MillerResidualWeight s) (i j : Fin m) :
    primeHeckeMillerMatrix p m s hm hs i j =
      millerCoefficientEquiv m s hm hs
        (primeHecke p (12 * m + s : ℕ) (millerForm m s hs j)) i := by
  rw [millerCoefficientEquiv_apply]
  exact (primeHeckeFiniteCoordinate_eq p m (12 * m + s : ℕ)
    (millerForm m s hs j) i).symm

end
end D5.S3.Arith.ModularForms

#print axioms D5.S3.Arith.ModularForms.finiteCoefficientArray
#print axioms D5.S3.Arith.ModularForms.primeHeckeFiniteCoordinate
#print axioms D5.S3.Arith.ModularForms.primeHeckeFiniteCoordinate_eq
#print axioms D5.S3.Arith.ModularForms.primeHecke_first_coefficients_from_array
#print axioms D5.S3.Arith.ModularForms.primeHeckeMillerMatrix
#print axioms D5.S3.Arith.ModularForms.primeHeckeMillerMatrix_apply_basis
