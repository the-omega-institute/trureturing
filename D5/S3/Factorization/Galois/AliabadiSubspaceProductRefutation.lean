/- GID: D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/AliabadiSubspaceProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.claim; result=D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.result; claim=D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.claim
   digest: A degree-seven rational extension refutes the uncapped subspace-product bound. -/

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic

/-! A prime-degree quotient field contradicts the uncapped universal product bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.AliabadiSubspaceProductRefutation

noncomputable section
open Polynomial Module
open scoped Pointwise

/-- Multiplicative translate of an actual intermediate field, as a base-field subspace. -/
def translate {K L : Type} [Field K] [Field L] [Algebra K L]
    (a : L) (M : IntermediateField K L) : Submodule K L :=
  M.toSubalgebra.toSubmodule.map (LinearMap.mulLeft K a)

/-- The premise quantifies over every scalar pair and every finite, nontrivial proper
intermediate field. In particular the ambient field itself is excluded. -/
def intersectionPremise {K L : Type} [Field K] [Field L] [Algebra K L]
    (A B : Submodule K L) : Prop :=
  ∀ (a b : L) (M : IntermediateField K L), ⊥ < M → M < ⊤ →
    FiniteDimensional K M →
      finrank K ↥(translate a M ⊓ A) + finrank K ↥(translate b M ⊓ B) ≤
        finrank K M + 1

/-- Aliabadi's whole Conjecture 5.1 (journal Conjecture 38).
The product is the span of the actual pointwise products in the extension field. -/
def claim : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (A B : Submodule K L), FiniteDimensional K A → FiniteDimensional K B →
    0 < finrank K A → 0 < finrank K B → intersectionPremise A B →
      ∀ (S T : Submodule K L), S ≤ A → T ≤ B →
        finrank K S + finrank K T - 1 ≤
          finrank K (Submodule.span K ((S : Set L) * (T : Set L)))

/-- The rational polynomial defining the extension. -/
abbrev polynomial : ℚ[X] := X ^ 7 - C 2

private theorem polynomial_irreducible : Irreducible polynomial := by
  let f : ℤ[X] := X ^ 7 - C 2
  have hm : f.Monic := monic_X_pow_sub_C 2 (by decide)
  have hp : (Ideal.span ({2} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2
      (by norm_num : Prime (2 : ℤ))
  have he : f.IsEisensteinAt (Ideal.span ({2} : Set ℤ)) := by
    apply hm.isEisensteinAt_of_mem_of_notMem hp.ne_top
    · intro i hi
      have hi7 : i < 7 := by simpa only [f, natDegree_X_pow_sub_C] using hi
      rw [Ideal.mem_span_singleton]
      interval_cases i <;> norm_num [f, coeff_sub, coeff_X_pow, coeff_C]
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      norm_num [f, coeff_sub, coeff_X_pow, coeff_C]
  have hf : Irreducible f := he.irreducible hp hm.isPrimitive (by simp only [f, natDegree_X_pow_sub_C]; decide)
  change Irreducible (X ^ 7 - C (2 : ℚ))
  simpa only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, map_ofNat, Polynomial.map_ofNat] using
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp hf

private instance polynomialFact : Fact (Irreducible polynomial) := ⟨polynomial_irreducible⟩

/-- The actual quotient field Q[X]/(X^7-2). -/
abbrev Extension := AdjoinRoot polynomial

/-- The residue class of X in the quotient field. -/
def alpha : Extension := AdjoinRoot.root polynomial

private def powerBasis : PowerBasis ℚ Extension :=
  AdjoinRoot.powerBasis' (monic_X_pow_sub_C 2 (by decide : 7 ≠ 0))

private theorem powerBasis_dim : powerBasis.dim = 7 := by
  simp [powerBasis, polynomial]

private theorem powerBasis_gen : powerBasis.gen = alpha := rfl

private instance extensionFinite : FiniteDimensional ℚ Extension := powerBasis.finite

private theorem extension_degree : finrank ℚ Extension = 7 :=
  powerBasis.finrank.trans powerBasis_dim

/-- The span of alpha through alpha to the n, without the constant basis vector. -/
def powerSpan (n : ℕ) : Submodule ℚ Extension :=
  Submodule.span ℚ (Set.range fun i : Fin n => alpha ^ (i.val + 1))

private def powerIndex {n : ℕ} (hn : n ≤ 6) (i : Fin n) : Fin powerBasis.dim :=
  ⟨i.val + 1, by rw [powerBasis_dim]; have := i.isLt; omega⟩

private theorem powerIndex_injective {n : ℕ} (hn : n ≤ 6) :
    Function.Injective (powerIndex hn) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  dsimp [powerIndex] at this
  omega

private theorem powerSpan_dim {n : ℕ} (hn : n ≤ 6) : finrank ℚ (powerSpan n) = n := by
  have h := powerBasis.basis.linearIndependent.comp (powerIndex hn) (powerIndex_injective hn)
  have hli : LinearIndependent ℚ (fun i : Fin n => alpha ^ (i.val + 1)) := by
    simpa only [Function.comp_def, powerBasis.basis_eq_pow, powerBasis_gen, powerIndex] using h
  rw [powerSpan, finrank_span_eq_card hli, Fintype.card_fin]

private theorem one_not_mem_powerSpan {n : ℕ} (hn : n ≤ 6) :
    (1 : Extension) ∉ powerSpan n := by
  have heq : Set.range (fun i : Fin n => alpha ^ (i.val + 1)) =
      powerBasis.basis '' Set.range (powerIndex hn) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp only [Function.comp_apply, powerBasis.basis_eq_pow, powerBasis_gen, powerIndex]
  intro h
  have hzero : powerBasis.basis ⟨0, by rw [powerBasis_dim]; decide⟩ ∈
      Submodule.span ℚ (powerBasis.basis '' Set.range (powerIndex hn)) := by
    simpa [powerSpan, heq, powerBasis.basis_eq_pow, powerBasis_gen] using h
  obtain ⟨i, hi⟩ := powerBasis.basis.self_mem_span_image.mp hzero
  have := congrArg Fin.val hi
  dsimp [powerIndex] at this
  omega

private theorem powerSpan_mono {n m : ℕ} (hnm : n ≤ m) : powerSpan n ≤ powerSpan m := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hnm⟩, rfl⟩

/-- The full realized certificate includes the proper subspaces and absence of 1.
It asserts only the sufficient ambient upper bound for the actual product span. -/
def countermodel : Prop :=
  finrank ℚ Extension = 7 ∧ alpha ^ 7 = (2 : Extension) ∧
  finrank ℚ (powerSpan 6) = 6 ∧ finrank ℚ (powerSpan 5) = 5 ∧
  powerSpan 5 < powerSpan 6 ∧ powerSpan 6 < ⊤ ∧
  (1 : Extension) ∉ powerSpan 6 ∧ (1 : Extension) ∉ powerSpan 5 ∧
  intersectionPremise (powerSpan 6) (powerSpan 6) ∧
  finrank ℚ (Submodule.span ℚ
    ((powerSpan 5 : Set Extension) * (powerSpan 5 : Set Extension))) ≤ 7

private theorem countermodel_verified : countermodel := by
  have hd6 := powerSpan_dim (by decide : 6 ≤ 6)
  have hd5 := powerSpan_dim (by decide : 5 ≤ 6)
  have hnot6 := one_not_mem_powerSpan (by decide : 6 ≤ 6)
  have hnot5 := one_not_mem_powerSpan (by decide : 5 ≤ 6)
  have hproper : powerSpan 6 < ⊤ :=
    Submodule.lt_top_of_finrank_lt_finrank (by rw [hd6, extension_degree]; decide)
  have hstrict : powerSpan 5 < powerSpan 6 :=
    Submodule.lt_of_le_of_finrank_lt_finrank (powerSpan_mono (by decide : 5 ≤ 6))
      (by rw [hd5, hd6]; decide)
  have hprem : intersectionPremise (powerSpan 6) (powerSpan 6) := by
    intro a b M hbot htop hfinite
    letI : IsSimpleOrder (IntermediateField ℚ Extension) :=
      IntermediateField.isSimpleOrder_of_finrank_prime ℚ Extension
        (by rw [extension_degree]; decide)
    rcases IsSimpleOrder.eq_bot_or_eq_top M with h | h
    · exact False.elim (hbot.ne h.symm)
    · exact False.elim (htop.ne h)
  have hroot : alpha ^ 7 = (2 : Extension) := by
    simpa only [alpha, polynomial, map_ofNat] using
      (root_X_pow_sub_C_pow (K := ℚ) 7 2)
  exact ⟨extension_degree, hroot, hd6, hd5, hstrict, hproper, hnot6, hnot5, hprem,
    (Submodule.finrank_le _).trans_eq extension_degree⟩

/-- The original universally quantified lower bound is false. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hdegree, hroot, hd6, hd5, hstrict, hproper, hnot6, hnot5, hprem, hproduct⟩ :=
    countermodel_verified
  have hlower := h ℚ Extension (powerSpan 6) (powerSpan 6)
    (inferInstance) (inferInstance) (by omega) (by omega) hprem
    (powerSpan 5) (powerSpan 5) hstrict.le hstrict.le
  rw [hd5] at hlower
  omega

#print axioms result

end
end D5.S3.Factorization.Galois.AliabadiSubspaceProductRefutation
