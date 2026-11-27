/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MahlerForms
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Reduction/MahlerForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Reduction.MahlerForms. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Reduction/MahlerForms.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Reduction.MinkowskiSecond
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski
theorems (known result; see Lib.Adelic.Reduction.Defs).

This file: Field elements with bounded denominators and very small conjugates vanish. Compactness in
adelic GL_n from determinant bound; reduced bases in a compact set. Mahler-Godement criterion core:
dual reduced bases have finitely many Gram matrices, form varying. -/

open Matrix Set Units

variable {E : Type*} [Field E] [CMType E] {n} [Fintype n]

/-- For a compact set B of adeles there is an integer c such that, for every integer e < c, an
element a of E that lies in B after multiplication by 2^{−e} at the infinite places is zero. -/
lemma exists_eq_zero_of_zpow_mul_mem {B} (hB : IsCompact B) : ∃ c : ℤ, ∀ e < c,
    ∀ {a : E}, (twoAtInfinity E ^ (-e)).1 * a ∈ B → a = 0 :=
  have F := isCovolOneLattice_ratAdeles.finite_preimage (isCompact_closedBall_prod_integral.mul hB)
  ((F.div F).preimage_embedding Nat.castEmbedding).exists_notMem.imp' (-↑·) fun N h e k a l ↦ by
    refine by_contra (h ⟨_, ⟨N * ↑(twoAtInfinity E ^ e), ?_, _, l, by simp [mul_assoc]⟩, _,
      ⟨_, ?_, _, l, Units.inv_mul_cancel_left ..⟩, div_eq_of_eq_mul · rfl⟩) <;> simp [twoAtInfinity,
      ← map_zpow, Pi.mul_def]
    grw [N.lt_two_pow_self, k] <;> simp
    omega

/-- For a CM field E, a compact set M of n × n matrices over the adeles of E and a real c > 0,
the set of A in GL_n(𝔸) with matrix in M and idele module |det A| ≥ c is compact. -/
lemma isCompact_setOf_le_ideleAbs_det {M} (hM : IsCompact M) {c} (hc : 0 < c) :
    IsCompact {A : GL n (𝔸 E) | A.1 ∈ M ∧ c ≤ ideleAbs A.det} := by refine ((pow_unbounded_of_one_lt
      (_ / c) ?_).elim fun N hN ↦ (isClosedEmbedding_embedProduct.isCompact_preimage ((hM.prod
      (isCompact_closedBall_prod_integral.mul ((isCovolOneLattice_ratAdeles.finite_preimage
  ((hM.image_auto (det · * twoAtInfinity E ^ N)).mul isCompact_closedBall_prod_integral)).image
  (toAdele ·⁻¹)).isCompact)).image_auto fun (A, b) ↦ (A, .op ((twoAtInfinity E ^ N * b) •
  A.adjugate)))).of_isClosed_subset (.and hM.isClosed.preimage_of_continuous
  (.preimage_of_continuous isClosed_Ici)) fun (A : GL n _) ⟨a, d⟩ ↦ (exists_ne_zero_inv_mulVec_mem
  (.scalar (Fin 1) A.det * dyadicDiag N) (by simp [ideleAbs_det_dyadicDiag]; grw [← d,
  ← div_lt_iff₀' hc, hN])).elim fun ξ h ↦ have z := (h.1 0).imp_left (·.out.le); ⟨(_, _), ⟨a,
    mul_mem_mul z ⟨ξ 0, ⟨_, ⟨_, a, rfl⟩, _, z, ?_⟩, rfl⟩⟩, ?_⟩) <;> simp_all [dyadicDiag,
  funext_iff, inv_def, mul_assoc, ← map_mul, one_lt_pow₀, Ring.mul_inverse_cancel_left]

attribute [local simp ←] Matrix.map_mul map_inv map_zpow

lemma exists_compact_gram_entry {M K} (hM : IsCompact M) (hK : IsCompact K) : ∃ B, IsCompact B ∧
  ∀ {J : Matrix n n E} {y x Y}, y.1ᴴ * J.map toAdele * y.1 ∈ K → Y ∈ profileBases M x y → ∀ i j,
  (twoAtInfinity E ^ (-(x i + x j))).1 * (Y.1ᴴ * J * Y) i j ∈ B :=
  ⟨_, isCompact_iUnion fun p ↦ (hM.prod hK).image_auto fun (A, B) ↦ (A.1ᴴ * B * A) p.1 p.2,
  fun h u i j ↦ ⟨_, ⟨(i, j), rfl⟩, (_, _), ⟨u, h⟩, by ext <;> simp [↓gram_mul_of_gram_eq
  (gram_mul_of_gram_eq (gram_inv_of_gram_eq rfl) _), dyadicDiag, twoAtInfinity, field, zpow_add₀]⟩⟩

variable (E n) in
/-- There are a compact M ⊂ GL_n(𝔸) and c such that each y in GL_n(𝔸) has integers x_j, with
∑x_j ≤ c if |det y| ≥ 1, and Y ∈ GL_n(E) with y⁻¹Y·diag(t^{−x_j}) ∈ M; t is 2 at infinity, 1
elsewhere. -/
lemma exists_isCompact_profileBases : ∃ M c, IsCompact M ∧ ∀ y : GL n (𝔸 E), ∃ x, ∃ Y ∈ profileBases
  M x y, 1 ≤ ideleAbs y.det → ∑ i, x i ≤ c := by refine ⟨_, .log (2 ^ (2 * numInfPlaces E)) _,
  isCompact_setOf_le_ideleAbs_det isCompact_closedBall_prod_integral.matrix ?_,
  (minkowski_second · |>.elim fun Y ⟨x, k, H⟩ ↦ have := H.trans (le_max_left _ 1); ⟨x, .mk'' Yᵀ ?_,
    ⟨fun i j ↦ by simpa [pi_norm_le_iff_of_nonneg, dyadicDiag, twoAtInfinity, field] using!
    (k.2 j).symm.imp (ge_trans · <| PiLp.norm_apply_le _ ⟨·, i⟩) (· i), inv_le_of_inv_le₀ ?_
    (this.trans' ?_)⟩, fun _ ↦ (Int.zpow_le_iff_le_log ?_ ?_).1 (this.trans' ?_)⟩)⟩ <;> simp_all
  [field, ideleAbs_det_dyadicDiag]

/-- For compact K ⊂ GL_n(𝔸) there are finite F, compact C: if y*Jy ∈ K, some Y ∈ GL_n(E), d ∈
E^n have (Y*JY)_{ij} = 0 when d_i, d_j ≠ 1, ((W⁻¹y)_f, y⁻¹Z) ∈ C, (d, Z*JZ) ∈ F, for W =
(Y*J)⁻¹, Z = W·diag d. -/
lemma exists_finite_gram {K} (hK : IsCompact K) : ∃ F C, Set.Finite F ∧ IsCompact C ∧ ∀ J y,
  star y * J.map toAdele * y ∈ K → ∃ (Y : GL n E) (d : n → E), let W := (star Y * J)⁻¹
  let Z := W.1 * diagonal d
  (∀ i j : {i // d i ≠ 1}, (Y.1ᴴ * J * Y.1) i j = 0) ∧ ((W⁻¹.map toAdele * y).map (.snd ..),
  y⁻¹.1 * Z.map toAdele) ∈ C ∧ (d, Zᴴ * J * Z) ∈ F := by
  choose M _ hM x Y hY _ using exists_isCompact_profileBases E n
  choose _ hB t using exists_compact_gram_entry hM (hK.image_auto val)
  choose d hd using exists_eq_zero_of_zpow_mul_mem hB
  have : Continuous (.snd .. : 𝔸 E →+* _) := continuous_snd
  have hC := (((hM.image_auto star).mul hK).prod (isCompact_closedBall_prod_integral (E := E)
    (2⁻¹ ^ (d / 2))).matrix).image_auto fun (A, Δ) ↦ (A.map (.snd ..), A⁻¹.1 * Δ)
  refine ⟨_, _, .prod (finite_range (mulIndicator · 0)) (instLatMatrix𝔸RatM.finite_preimage
    ((hC.prod hK).image_auto fun ((_, A), S) ↦ Aᴴ * S * A)), hC, fun J y f ↦ ⟨_, (x y ⁻¹' Iio
    (d / 2)).mulIndicator 0, (hd _ (by grind [mulIndicator]) <| t ⟨_, f, rfl⟩ (hY y) · ·),
    (fun z ↦ ⟨z, ?_, (_, _), ⟨z, f⟩, ?_⟩) ⟨(_, _), ⟨mul_mem_mul ⟨_, hY y, rfl⟩ f, ?_⟩,
    Prod.ext ?_ (inv_mul_cancel_left ..)⟩⟩⟩ <;> simp [dyadicDiag, twoAtInfinity, mul_assoc,
    ← val_inj, mulIndicator, star_eq_conjTranspose, diagonal_mem_matrix_iff,
    ite_mem, zpow_nonneg, ← map_zpow, ← map_inv, field, ← Matrix.map_mul, conjTranspose_nonsing_inv]
