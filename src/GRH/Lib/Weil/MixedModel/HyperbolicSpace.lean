import GRH.Lib.Weil.Construction.ThetaFunctional
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Framed hyperbolic space; matrices unitary at infinity and integral at finite places. -/

open stdLattice MatMul Matrix

variable {E : Type _} [Field E] [CMType E] [WeilData E]
  {n : Type _} [Fintype n] {p : Type _} [Fintype p] {m q : Type _} [Fintype m]

/-- The sign function on two copies of p that is +1 on the first copy and −1 on the second. -/
abbrev hypSigns p : p ⊕ p → ℤˣ := 1 ⊕ᵥ -1

attribute [local simp ←] Complex.ofReal_mul Int.cast_mul ext_iff mul_assoc mul_inv

attribute [local simp] diagonal_apply Matrix.mul_apply mul_mem

variable (E p) in
/-- Hyperbolic space of rank 2p: Gram matrix with blocks (0, 1; 1, 0), signs +1 on the first p
and −1 on the last p coordinates, with an explicit adelic frame. -/
@[simps J] noncomputable def hypSpace :
  Space E _ (hypSigns p) := let c := Weil.normNegOne.1.1; let ϵ : 𝔸f E := traceOneAdele
    by refine ⟨fromBlocks 0 1 1 0, mkAdelicGL (fun _ ↦ ⟨(√2 : ℂ)⁻¹ • fromBlocks 1 (-1) 1 1,
      (√2 : ℂ)⁻¹ • fromBlocks 1 1 (-1) 1, ?_, ?_⟩, ⟨fromBlocks 1 (-c • 1) (ϵ • 1)
      ((c * star ϵ) • 1), fromBlocks (star ϵ • 1) 1 ((star c * ϵ) • 1) (-star c • 1), ?_, ?_⟩),
      gram_mkAdelicGL ?_ ?_⟩ <;> simp [signMatrix] <;> grind [star_normNegOne_mul_self]

lemma signs_comp_refl {m} {t : m → ℤˣ} : t ∘ Equiv.refl m = t := rfl

/-- The condition on an adelic matrix M that M_τ* M_τ = 1 at every infinite place τ and that all
entries have integral finite part. -/
@[local simp] def IsOrthoIntegral {E : Type _} [Field E] [NumberField E] {n m : Type _} [Fintype m]
    (M : Matrix m n _) := (∀ w,
  (M.map (evalInf w))ᴴ * M.map (evalInf w) = 1) ∧ ∀ i k, (M i k).2 ∈ Ô E

lemma isOrthoIntegral_hypSpace : IsOrthoIntegral (hypSpace E p).x.1 ∧ IsOrthoIntegral (hypSpace E
  p).x⁻¹.1 := by simp [hypSpace, ← map_inv, ite_mem, star_mem_Ô, traceOneAdele_mem]; grind

omit [WeilData E] in
lemma IsOrthoIntegral.of_stdForm s :
  IsOrthoIntegral (n := n) (stdForm E s) := by simp [stdForm, apply_ite]

omit [WeilData E] in
lemma IsOrthoIntegral.one : IsOrthoIntegral (1 : Matrix n n (𝔸 E)) := by aesop

variable {A : Matrix m n (𝔸 E)} (hA : IsOrthoIntegral A)

include hA

section

omit [WeilData E]

lemma IsOrthoIntegral.mul {B : Matrix n q (𝔸 E)} : IsOrthoIntegral B → IsOrthoIntegral (A * B) := by
  simp_all [-ext_iff, ← (A.map _)ᴴ.mul_assoc, Prod.snd_sum, sum_mem]

omit [Fintype n] in
lemma IsOrthoIntegral.block_diag {B : Matrix p q _} : IsOrthoIntegral B →
  IsOrthoIntegral (fromBlocks A 0 0 B) := by simp_all

omit [Fintype n] in
lemma IsOrthoIntegral.of_eq_submatrix_mul {C : Matrix p q (𝔸 E)} (e : p → n) (hC :
  IsOrthoIntegral C) {B} (h : B = A.submatrix id e * C)
  (he : e.Injective := by simp [Function.Injective]) : IsOrthoIntegral B := h ▸ mul (by aesop) hC

end
