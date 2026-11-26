import GRH.New.Exchange.BlockPartners
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: Locally constant partner data are matched pairs. -/

open SemilocalField

attribute [-simp] submatrix_id_mul

/-- For tame χ, partners Φ, Ψ (`IsPartner`) with Ψ locally constant form a pair in
`matchingPairs`. -/
lemma IsPartner.mem_matchingPairs {a b n} [Fintype a] [Fintype b] [Fintype n] {F} [SemilocalField F] {χ e Φ Ψ} (hχ : TameLocalChar χ)
    (h : @IsPartner F a b n _ _ O e χ Φ Ψ) (hΨ : IsLocallyConstant Ψ) : (Φ, Ψ) ∈ matchingPairs χ e := by
  refine' ⟨⟨.transpose_mem_schwartzBruhat (schwartzBruhat.of_support_primitive (fun s ↦ (Set.ext _).subst (((IsLocallyConstant.zero s).union
    (hχ.isClopen_primitive _ e).2).sdiff (((isCompact_intGL isCompact_O).diff ((hΨ.comp_continuous (f := firstCols e)
    (by fun_prop)).div (hχ.isLocallyConstant_invOnUnits.comp_continuous Units.continuous_val.matrix_det) s)).image_auto
    (Matrix.transpose ∘ invLastRows e)).isClosed)) ?l), schwartzBruhat.of_support_primitive hΨ ?r⟩, funext fun k ↦ match
    localSection_of_primitive _ _ (hasLeftInv_invLastRows_transpose ..), localSection_of_primitive _ _ ⟨_, invFirstRows_mul_firstCols ..⟩ with | ⟨g, a, A⟩, ⟨u, b, B⟩ => (
                                                                           congr($(A _ ?l) - _ * $(B _ ?r)).trans ((exists_firstCols_eq_mul e k ⊤ u _ (transposeGL g) ..).elim fun j p ↦
                                                                           (_ : ∃ i ∈ intGL n O, invLastRows e j = invLastRows e i).elim (b.mul_iff (x := invFirstRows e j * firstCols e ·) |>.elim _)))⟩
  repeat simp_all [← mul_assoc, ← map_mul, mem_intGL (O := ⊤)] <;> grind [invOnUnits,
    isPrimitiveMatrix_iff_isIntegralUnit_det, Matrix.transpose_submatrix, Matrix.transpose_mul,
    Matrix.transpose_transpose, right_mul, det_fromRows_invLastRows, χ.map_one,
    (exists_invLastRows_iff_transpose e).trans (valPair.exists_firstCols_iff _)]
