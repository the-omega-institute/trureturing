/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalExtension
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/LocalExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.LocalExtension. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/LocalExtension.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.LocalFrobenius
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Finite extension of a local field is local, with ef equal to the degree. -/


open Nat IsLocalRing Module Algebra.TensorProduct Ideal Subtype Rat IsIntegralClosure ResidueField
variable {Γ k Ω} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [G : IsLocalGalois Γ k A]

lemma valuation_residueCard_lt_one :
  A (residueCard k A) < 1 := by simpa [↓Valuation.mem_maximalIdeal_iff]
  using! (maximalIdeal (valRingBelow k A)).toAddSubgroup.nsmul_index_mem 1

/-- A finite extension k' of a local field k is local; there are e, f with ef = [k':k], q' = q^f
and ord_{k'} = e·ord_k; and #(𝒪'/n) = #(𝒪/n)^{[k':k]} for every natural number n. -/
lemma IsLocalGalois.of_finite (V : OpenSubgroup Γ) (k' := ↥(fixedFieldOf V.1)) [Field k'] [Algebra
  k' Ω] [IsProGalois V.1 k' Ω] [Algebra k k'] [IsScalarTower k k' Ω] [FiniteDimensional k k'] :
  IsLocalGalois V.1 k' A ∧ (∃ e f, (e * f = V.index ∧ residueCard k' A = residueCard k A ^ f ∧
  ordRat k' A = e • ordRat k A) ∧ (inertiaGroup Γ A ≤ V → e = 1)) ∧ ∀ n : ℕ, Nat.card
  (_ ⧸ span {(n : valRingBelow k' A)}) = .card (_ ⧸ span {(n : valRingBelow k A)}) ^ V.index := by
  obtain ⟨⟨H, d, hf⟩, ⟨π, hπ⟩, ⟨⟨σ, s⟩, D, F⟩, -, n⟩ := id G, G.exists_isUniformiser,
    G.frobenius_spec, eq_fixingSubgroup_of_isProGalois (V := V.1)
  let O := valRingBelow k A
  let P := valRingBelow k' A
  rcases (algebraMap k Ω).charZero, IsScalarTower.algebraMap_apply k k' Ω,
    (⟨(F ⟨_, ·.2⟩ |>.tower_bot_of_field.tower_bot val_injective)⟩ : Algebra.IsIntegral O P)
  rcases isNoetherian O k k' P, isNoetherianRing O k k' P, FaithfulSMul.tower_bot O P k'
  have L : IsLocalGalois V.1 k' A :=
    ⟨(H ·), ⟨ne_bot_of_liesOver_of_ne_bot d.3 _⟩, finite_of_finite hf⟩
  obtain ⟨⟨π', hπ'⟩, hc⟩ := L.exists_isUniformiser, fun x : O ↦ by
    simpa [← IsFractionRing.finrank_eq _ k P k', card_fun, ← n] using card_congr
      ((quotIdealMapEquivQuotTensor _ (span {x})).1.trans (basis _ (finBasis _ P)).equivFun.toEquiv)
  have ⟨e, he⟩ := hπ'.exists_val_eq_zpow L (algebraMap k k' π) (by simp)
  lift e to ℕ using by simpa [zero_lt_iff, hπ'.val_lt_one, valuationVia, *] using hπ.val_lt_one.le
  use L, ⟨e, .imp (fun f h ↦ ⟨h, fun I ↦ ?_⟩) ⟨_, Nat.pow_right_injective hf.one_lt_card (by
    simpa [O, pow_mul', ← natCard_eq_pow_finrank, hπ.card_quot G 1] using (hπ'.card_quot L _
      he).symm.trans (hc ⟨_, hπ.val_lt_one.le⟩)), natCard_eq_pow_finrank, ?_⟩⟩, (mod_cast hc ·)
  rcases I ((h.2.1 ▸ s.pow f).inv_mul L.frobenius_spec.1.choose_spec), n ▸ finrank_pos
  nlinarith [f.card_fin, h.1.trans_le (card_le_card_of_surjective (⟦σ ^ Fin.val ·⟧) (Quotient.ind
    (isClosed_property (D s) ⟨@isOpen_discrete (_ ⧸ V.1) _ _ (.range _)ᶜ⟩
    (⟨@.ofNat f ⟨by lia⟩ ·.1, by simp_all [mod_def, I _, pow_sub, mul_div_le, pow_mul,
    mul_mem_cancel_right, pow_mem]⟩))))]
  ext
  simpa [*, valuationVia, ← zpow_mul, hπ'.val_pow_eq_iff_mul_ordRat L _ _, -zpow_natCast,
    ← den_mul_eq_num,
    mul_left_comm e.cast] using (hπ.val_pow_eq_iff_mul_ordRat G ..).2 (den_mul_eq_num _)

/-- For a local field k, every x in Ω^× fixed by the inertia group has integral order, for the
order normalised on k. -/
lemma IsLocalGalois.exists_ordRat_eq_intCast {x} (h : ∀ g ∈ inertiaGroup Γ A, unitsRep g x = x) :
  ∃ n : ℤ, ordRat k A x = n := (G.of_finite (id ⟨_, G.1.6 _⟩)).elim fun L ⟨⟨_, _, o⟩, _⟩ ↦
  L.exists_isUniformiser.rec fun _ p ↦ (p.exists_val_eq_zpow L ⟨_, (·.2)⟩ (x.ne_zero ∘ mk.inj)).imp
  fun _ ↦ by simpa [o, o.2 (congr($(h · ·).1)), -id_eq] using! (p.val_pow_eq_iff_mul_ordRat L 1 _).1
