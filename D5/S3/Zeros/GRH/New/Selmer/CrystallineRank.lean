/- GID: D5/S3/Zeros/GRH/New/Selmer/CrystallineRank
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/CrystallineRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.CrystallineRank. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/CrystallineRank.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.ThickSpacing
import D5.S3.Zeros.GRH.Lib.ClassField.LocalDuality.CrystallineDuality
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

Part of: Bloch–Kato finite local condition: rank formula and size of its annihilator (known result;
see Lib.PadicHodge.BlochKato.BlochKato).

This file: the rank of the crystalline cocycles Z_f(L) is rk L plus the number of negative
Hodge–Tate weights; so a power of ℓ that maps Z_f(L) into a submodule bounds the quotient in
length. -/


export Lift (InClass)

open Lift crysCocycles Module Set Multiset Finset DFunLike Submodule Finite TensorProduct
variable {ℓ} [ThePrime ℓ] {O : CoeffRing ℓ} {Γ n} [Group Γ] [Fintype n] [𝒥 : OverGp Γ
  ℓ] {R} [CommRing R] [Algebra ℤ_[ℓ] R] {L : GalLattice O Γ}

/-- The Γ-lattice over R given by the module R^n with Γ acting through the matrix representation
ρ. -/
noncomputable abbrev matrixLattice (ρ : Γ →* Matrix n n R) : GalLattice R Γ :=
  ⟨n → R, actionRep R _ ρ⟩

/-- Let j identify Γ with the local Galois group of E at e, and L be potentially crystalline
with jumps J(ι⁻¹g⁻¹e) at each coefficient embedding g. Then rk Z_f(L) is rk L plus the
number of negative jumps, summed over the embeddings ι⁻¹g⁻¹e. -/
lemma finrank_crysCocycles_eq_add_neg_jumps [TopologicalSpace Γ] {E} [Field E] [UnramCMField E] {e :
  E →+* _} [PadicIso ℓ] (hj : IsCompletionGroup e 𝒥.toGp) (h : IsPotCrys L.ρ) {J : _ → _} (hJ : ∀ g,
  HasJumps L.ρ (coeffEmb O g) (J (complexEmbOf e g))) : finrank O (crysCocycles L.ρ) =
  finrank O L + ∑ σ with ∃ g, complexEmbOf e g = σ, (J σ).countP (· < 0) := have := fg h
  Nat.mul_left_cancel (card_pos_iff.2 ⟨coeffEmb O 1⟩) (by
    choose s _ using @coeffEmb_surjective _ _ O
    choose K _ hK using h.exists_hasJumps
    simpa [(finrank_eq h (J := univ.sum K) (by simp [h.sum_jump_eq_jump_overZp, count_sum',
      ← hK _ ·])).2, hj.index_eq_card_range, mul_add, finrank_mul_finrank, ← coe_countPAddMonoidHom,
      sum_set_coe, ← filter_mem_univ_eq_toFinset, (Multiset.ext' fun u ↦ hK .. ▸ hJ · u), fun g ↦
      (by simp [Function.Injective, Subtype.ext_iff, ← apply_rangeSplitting,
      hj.complexEmbOf_eq_iff] : ((⟨_, ·, rfl⟩) <| rangeSplitting (complexEmbOf e) · *
      g).Injective).bijective_of_finite.sum_comp (J ·)] using congrArg (countP _)
      (congr(∑ y, $((by intro; simp_all [coeffEmb, ext_iff]; grind : (coeffEmb O <| rangeSplitting
      (complexEmbOf e) y * s ·).Injective).bijective_of_finite.sum_comp K)).symm.trans sum_comm))

/-- Let L be potentially crystalline, ℓ^k Z_f(L) ⊆ S for a submodule S, and 2k·rank L ≤ y. Then
Z_f(L) modulo Z_f(L) ∩ S has normalised length at most y times the index of j(Γ) in the
absolute Galois group of ℚ_ℓ. -/
lemma normLength_defect_le {k : ℕ} (hT : IsPotCrys L.ρ) {S} {y : NNReal} (hk :
  finrank O L * (2 * k) ≤ y) (h : ∀ c ∈ crysCocycles L.ρ, (ℓ : ↑O) ^ k • c ∈ S) :
  O.normLength (relLength (crysCocycles L.ρ) S) ≤ 𝒥.toGp.range.index * y := by
  obtain ⟨_, K, r, H⟩ := fg hT, hT.exists_hasJumps (ρ := overZp _) _
  grw [relLength, length_le_of_surjective _ (factor_surjective ((span_smul_eq {(ℓ : ↑O) ^ k}
    ⊤).trans_le ?_)), ← (quotTensorEquivQuotSMul ..).length_eq, (equivFinsuppOfBasisRight (finBasis
    ..)).length_eq, ← hk] <;> simp_all [set_smul_le_iff, submoduleOf]
  exact_mod_cast le_of_mul_le_mul_left (by grw [← mul_assoc, finrank_mul_finrank, (finrank_eq hT
    H).2, countP_le_card, r, ← one_add_mul, Nat.one_le_of_lt (toGp.range.quotient_finite_of_isOpen
    𝒥.2.1).card_pos, ← finrank_mul_finrank _ O]; linarith!) (finrank_pos : _ < finrank ℤ_[ℓ] O)
