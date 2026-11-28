/- GID: D5/S3/Zeros/GRH/Lib/Weil/MixedModel/AdaptedSplitting
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/MixedModel/AdaptedSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.MixedModel.AdaptedSplitting. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/MixedModel/AdaptedSplitting.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Landherr.Landherr
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.HyperbolicSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

Part of: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa decomposition
(known result; see Lib.SiegelWeil.SingularForms.AdaptedHom).

This file: Zero term along an isotropic subspace taken in stages; independent of the frame. Witt
decomposition: every isotropic frame splits off hyperbolic planes plus a framed complement. Adapted
splittings; the standard splitting of a space plus hyperbolic planes. -/

open Classical ComplexOrder Fintype MatMul Matrix Sgn Space Splitting

attribute [local simp] Splitting.comp Splitting.zeroTerm_apply iAdelic kAdelic Space.ratMap
  funext_iff

variable {E n n₀ p n₁ q : Type*} [Field E] [CMType E] [Fintype n] {s : n → ℤˣ} [Fintype n₀]
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} [Fintype n₁]
  {s₁ : n₁ → ℤˣ} {V₁ : Space E n₁ s₁}

variable (V V₀)

@[simp] lemma Space.ratMap_mul_toAdele i (k : Matrix n₀ p E) :
    V.ratMap V₀ i * (V₀.x⁻¹.1 * k.map toAdele) = V.x⁻¹.1 * (i * k).map toAdele := by simp

lemma Space.ratMap_mul_ratMap i k : V.ratMap V₀ i * V₀.ratMap V₁ k = V.ratMap V₁ (i * k) := by simp

lemma Space.map_mulVec_mem_ratVectors [Fintype p] [WeilData E] c : ∀ b ∈ _root_.ratVectors E p,
  .map c toAdele *ᵥ b ∈ _root_.ratVectors E q | _, ⟨a, rfl⟩ => ⟨_, funext (toAdele.map_mulVec c a)⟩

variable [Fintype p] [Fintype q]

variable {V V₀} [WeilData E] (D : V.Splitting V₀ p) (D' : V₀.Splitting V₁ q)

omit [WeilData E] in
lemma Space.Splitting.comp_kAdelic : (D.comp D').kAdelic =
  D.kAdelic.fromCols (D.iAdelic * D'.kAdelic) := by simp

/-- Zero terms can be taken in stages: for splittings of V over V₀ and of V₀ over V₁, the zero
term of the composite splitting is the zero term of the second applied after that of the
first. -/
lemma Space.Splitting.zeroTerm_comp f : (D.comp D').zeroTerm f = D'.zeroTerm (D.zeroTerm f) := by
  ext; rw [zeroTerm_apply, ← quotMean_quotMean (_root_.ratVectors ..) _ (_root_.ratVectors ..)
    (.mk' ..) (Homeomorph.sumArrowHomeomorphProdArrow.3.comp continuous_swap) _ (⟨(_, _),
    Sum.elim_comp_inl_inr ·⟩)] <;> simp_all [↓isContPeriodic_along_k, mem_ratVectors]; ac_nf

/-- Two splittings of V over V₀, with isotropic frames k and k′ (of possibly different index
sets), have the same zero-term map 𝒮(V) → 𝒮(V₀) if k*Jk′ = 0 and their embeddings of V₀
coincide. -/
lemma Space.Splitting.zeroTerm_congr (D' : V.Splitting _ q) (hk : D.kᴴ * V.J * D'.k = 0) (hi :
  D'.i = D.i) : D'.zeroTerm = D.zeroTerm :=
  by have := V.gram_at_point_eq_map D.k D'.k; rcases congr($D.sum_frame_mul_coord_eq_one *
  D'.kAdelic), congr($D'.sum_frame_mul_coord_eq_one * D.kAdelic), D'.coord_mul_frame,
  D.coord_mul_frame, congr($thisᴴ); ext; rw [zeroTerm_apply, ← quotMean_comp _ (D'.kCoord *
  D.kAdelic).toLin' _ (V.gram_at_point_eq_map .. ▸ map_mulVec_mem_ratVectors _) (⟨D.kCoord *ᵥ
  D'.kAdelic *ᵥ ·, _⟩)] <;> simp_all [iCoord, lCoord, ↓conjTranspose_mul, ↓isContPeriodic_along_k]

variable {E : Type} [Field.{0} E] [CMType E] [WeilData E] {n : Type} (p : Type) [Fintype n]
  [Fintype.{0} p] {s : n → ℤˣ} (V : Space E n s)

/-- Every q×p matrix k over E with a left inverse and k*Jk = 0, J the Gram matrix of V, is the
isotropic frame k of a splitting of V over some space V₀. -/
lemma Space.exists_splitting {s p} [Fintype.{0} p] (V : Space E q s) {k} (hk : HasLeftInv k)
    (h : kᴴ * V.J * k = 0) : ∃ m s₀ V₀ D, (D : V.Splitting (V₀ : Space E (Fin m) s₀) p).k = k := by
  let X := (V.x⁻¹.1 * k.map toAdele).map (evalInf ofNonempty)
  have hc ε : p ↪ s ⁻¹' {ε} := (Function.Embedding.truncOfCardLE (by
    trans X.rank; simpa [X, ← Matrix.map_mul, hk.choose_spec] using
      ((hk.choose.map toAdele * V.x.1).map (evalInf ofNonempty)).rank_mul_le_right X
    grw [← rank_conjTranspose_mul_self, show Xᴴ * X = ε • Xᴴ * (signMatrix s + ↑ε) * X by
      fin_cases ε <;> simpa [-conjTranspose_map_toAdele, X, h, stdForm] using!
        congr($(V.gram_at_point_eq_map k k).map (evalInf _)), rank_mul_le_left, rank_mul_le_right]
    erw [diagonal_add, rank_diagonal]
    simp_all [↓card_subtype_mono, LE.le, not_imp_comm])).out
  let e := ((((hc 1).sumMap (hc (-1))).trans (.sumSet (.preimage s (by simp)))
    ).toEquivRange.sumCongr (equivFin _).symm).trans (.sumCompl _)
  have D := splittingOfGram _ ((Equiv.symm_apply_eq _).2 (V.landherr
    ((hypSum p (signedSpace E (s ∘ e ∘ .inr))).reindex e (by
    simp [↓e.comp_symm_eq, funext_iff, e]
    exact ⟨fun a ↦ (hc 1 a).2.symm, fun b ↦ (hc (-1) b).2.symm⟩))).choose_spec)
    (by simp +arith [← card_congr e])
  exact ⟨_, _, _, splittingOfGram _ ((U.gram_invariant ..).trans D.gram_eq_hypSum) D.card_eq,
    (V.witt ⟨_, D.gram_lk⟩ hk (h ▸ D.gram_kk)).choose_spec⟩

/-- The splitting is adapted: the adelic frame (l, k, ι) has orthonormal columns at every
infinite place and integral entries at every finite place. -/
class IsBaseAdapted {m p : Type} [Fintype n] [Fintype m] [Fintype p] {s t} {V' : Space E m t} {V :
  Space E n s} (D : V'.Splitting V p) where
  isOrthoIntegral : IsOrthoIntegral ((D.lAdelic.fromCols D.kAdelic).fromCols D.iAdelic)

/-- The tautological splitting over V of the sum of p hyperbolic planes and V. -/
noncomputable def removePlanes : (hypSum p V).Splitting V p := by
  use (fromRows 0 1).fromRows 0, (fromRows 1 0).fromRows 0, fromRows 0 1 <;> simp +arith [hypSum]

instance : IsBaseAdapted (removePlanes p V) := ⟨(isOrthoIntegral_hypSpace.2.block_diag
  .one).of_eq_submatrix_mul id .one (by simp [entrywise, lAdelic,
  kAdelic, iAdelic, Space.ratMap, removePlanes, hypSum, sum, blockGL])⟩
