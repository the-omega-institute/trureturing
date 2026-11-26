import OmegaMath.NumberTheory.GRH.Lib.PadicHodge.Crystalline.HodgeTateFrame
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: The Hodge-Tate cocharacter lies in the algebraic monodromy group. The result is
stated on coordinates in C_p, without algebraic groups or Tannakian categories. It says that a
polynomial that vanishes at the cyclotomically twisted Galois translates of a point, near the
identity, vanishes along the one-parameter torus. Source: Serre, Groupes algébriques associés aux
modules de Hodge-Tate, Astérisque 65 (1979), §1; Sen, Ann. of Math. 97 (1973).

This file: Hodge–Tate cocharacter lies in the Zariski closure of the image near the identity. -/

attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
open Finset Matrix LaurentPolynomial

seal Finset.univ Finset.sum Finset.prod in
/-- If a polynomial F over C_p vanishes at (χ(g)^(−κ_i)·g x_i)_i for all g in G_p near 1, then F
vanishes at (T^(κ_i)·x_i)_i in the ring of Laurent polynomials C_p[T, T⁻¹].

Known result: The Hodge-Tate cocharacter lies in the algebraic monodromy group. -/
lemma aeval_cocharacter_eq_zero {p} [ThePrime p] {n} [Fintype n] (κ : n → ℤ) (x : n → ℂ_[p])
    (F : MvPolynomial n ℂ_[p]) (h : ∀ᶠ g in nhds 1, F.aeval (fun i ↦
  (cyclotomicGp g ^ (-κ i)).1 • g • x i) = 0) : F.aeval (fun i ↦ T (κ i) * C (x i)) = 0 := by
  simp_rw [F.aeval_def, F.eval₂_eq', ← F.support.sum_coe_sort, ← Algebra.smul_def] at *
  let ⟨V, h⟩ := NonarchimedeanGroup.is_nonarchimedean _ h
  refine le_of_hodgeTate_stable le_rfl (∑ i, ·.1 i * κ i) (of _).vecMulLinear.ker
    (Fintype.linearCombination ..).ker (fun a u ↦ .mono V.mem_nhds_one fun k o ↦ funext fun g ↦ ?_)
    (fun v i a _ e _ _ ↦ .trans (sum_congr rfl fun l _ ↦ by cases e l <;> simp [*, T, C]; rfl)
    (sum_smul.symm.trans (congr($a 1 • T _).trans (by simp)))) (funext fun g : V ↦ h g.2)
  simpa [mul_pow, smul_smul, smul_prod', dotProduct, _root_.zpow_mul', vecMul, smul_sum,
    by simpa [-map_prod] using fun f ↦ map_prod (zpowersHom _ (cyclotomicGp k)) (.ofAdd ∘ f : n →
    _), mul_zpow, smul_pow, prod_smul, smul_comm k] using congr(k • $u (⟨k, o⟩⁻¹ * g))
