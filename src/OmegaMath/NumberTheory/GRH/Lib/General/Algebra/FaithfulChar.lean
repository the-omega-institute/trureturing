import OmegaMath.NumberTheory.GRH.Lib.LocalGL.Green.GreenTau
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: A faithful complex character of the units of the algebraic closure of F_q exists. -/

open WittVector Algebra IsIntegral Function RingHom

instance faithfulChar_injective {k} [Field k] [Finite k] : IsFaithfulMulChar _ (faithfulChar k) :=
  ⟨by
  have := (charZero_iff (map_injective _
    (ZMod.castHom_injective (AlgebraicClosure k)))).1 (toPadicInt _).charZero
  refine @Classical.epsilon_spec (MulChar ..) (Injective ·) ⟨.ringHomComp ⟨(teichmuller (ringChar
    k)).codRestrict (integralClosure ℤ _) fun x ↦ ?_, by simp; rfl⟩ (IsAlgClosed.lift (R := ℤ)).1,
    fun _ _ h ↦ congrArg (·.1.coeff 0) ((injective_iff_ker_eq_bot IsAlgClosed.lift).2
    (Ideal.eq_bot_of_liesOver_bot ℤ (.comap ..)) h)⟩
  have := Module.finite_iff_finite.1 (finite_adjoin_simple_of_isIntegral (R := k) (isIntegral x))
  simpa using! (isIntegral (.single ⟨x, by simp⟩ 1)).map
    (MonoidAlgebra.lift ℤ _ _ ((teichmuller _).domRestrict k[x]))⟩
