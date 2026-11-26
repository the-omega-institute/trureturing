import OmegaMath.NumberTheory.GRH.Lib.GLn.SchurModule.Bordering
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Leading exponent in a row interlaces; leading coefficient is again semi-invariant. -/
seal Finset.univ Finset.sum Finset.prod

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero
open MvPolynomial Finset Finsupp Algebra MonomialOrder

namespace PolyRep

variable {Φ m R} [CommRing R] {c : m → Φ} {x l f}
attribute [local simp] borelMul coeff_map mul_assoc algHom prod single_apply mul_pow ite_apply
attribute [local simp ←] map_pow map_prod C_pow Finsupp.sum.eq_1 pow_mul

/-- Interlacing: for f in ∇ of weight l, the leading exponent γ of f in the variables of row x
(order `PolyRep.columnOrder`; γ = 0 if f = 0) satisfies γ(i) ≤ l(c x, i) − l(c x, i+1), truncated at
0, for all i. -/
lemma degree_rowExpansion_mem_interlacing (hf : f ∈ nabla R c l) :
  columnOrder.degree (rowExpansion x f) ∈ interlacing (l.curry (c x)) := by
  set γ := columnOrder.degree (rowExpansion x f); simp [interlacing, le_def]; by_contra! ⟨i, _⟩
  let θ := aeval (R := R) fun y ↦ Polynomial.CC (X y : MatrixPoly {a // a ≠ x} R) +
    .X * .CC (single (c x, i) (X (y.1, i + 1)) (c y.1, y.2))
  have {p} : (θ p).coeff 0 = .C p := by apply p.induction_on <;> aesop
  let Ψ := (aevalTower ((mapAlgHom θ).comp (algHom ..)) fun j ↦ (C .X * X (i + 1)) ^
    single i 1 j * X i ^ single (i + 1) 1 j * X j).comp (rowExpansion x).toAlgHom
  let b : Φ × _ → type_of% (Ψ f) | (τ, j, k) => single j (C (.C .X ^ single (c x, i) 1 (τ, j) * .X ^
    single (c x, i + 1) 1 (τ, j))) k - single (c x, i) (single (j + 1) 1 k) (τ, j)
  apply absurd congr((($(mem_nabla.1 hf _ b (Ψ ∘ X)).coeff (single (i + 1) (γ i) + single i
    (γ (i + 1)) + γ)).coeff (l (c x, i + 1) + γ i)).coeff (l (c x, i)))
  rw [← aeval_unique, (algHom_ext fun ⟨y, _⟩ ↦ by
    simp +zetaDelta [rowExpansion, ite_and, mul_sub]
    split_ifs <;> subst_vars <;> simp_all <;> ring : aeval _ = (mapAlgHom (.restrictScalars _
    (Polynomial.aeval (.C .X * .X)))).comp (aeval (mapAlgHom (Polynomial.aeval 0) ∘ (borelMul c b
    (Ψ ∘ X) - Ψ ∘ X) + Ψ ∘ X)))]
  simp [Ψ, aevalTower, eval₂_eq, b, -pow_ite, -Prod.mk.injEq, prod_pow_eq_pow_sum, -map_aeval,
    ↓if_mem_support, coeff_sum, Polynomial.coeff_X_pow_mul', ← Polynomial.comp_eq_aeval]
  rw [sum_eq_ite γ] <;> simp_all [X_pow_eq_monomial, Polynomial.coeff_mul_X_pow',
    Finsupp.ext_iff, apply_ite Polynomial.coeff, DFunLike.ite_apply] <;> grind [coeff_eq_zero_of_lt,
    degree_zero, coeff_degree_eq_zero_iff, columnOrder_lt_of_eq_above]

lemma HasLeadingTerm.leadingCoeff_mem_nabla (hf :
  f ∈ nabla R c ((columnOrder.degree (rowExpansion x f)).mapDomain (c x, ·) + l)) :
  columnOrder.leadingCoeff (rowExpansion x f) ∈ nabla R (c ∘ (↑)) l := by
  have H := _root_.mem_nabla.1 hf _ (C ∘ C ∘ @X R _ _) ((mapAlgHom (aeval X)).comp (rowExpansion
    x).toAlgHom ∘ @X R _ _); rw [← aeval_unique, (algHom_ext (by simp [rowExpansion]; aesop) :
    aeval _ = (aevalTower ((algHom ..).comp (aeval (borelMul (c ∘ (↑)) (C ∘ @X R _ _) X)))
    (borelMul c (C ∘ C ∘ @X R _ _) (X ·.2) ⟨x, ·⟩)).comp (rowExpansion x).toAlgHom)] at H
  refine (IsRegular.right · ((sum (fun n ↦ mul of_monomial (prod fun j ↦ by
    simpa only [pow_eq_prod_const] using! prod fun _ ↦ sum (fun _ ↦ mul of_monomial of_monomial) j
      (by grind [columnOrder_lt_of_eq_above j]))) _ ?_ ?_).2.symm.trans
      ((congrArg (AddMonoidAlgebra.coeff · _) H).trans ?_)))
    (by simpa using .monomial (.prod (by simp))) <;> simp_all [leadingCoeff, ↓prod_add_index',
    pow_add, ↓prod_mapDomain_index, ← C_mul', lt_iff_le_and_ne] <;> grind [columnOrder.le_degree]
