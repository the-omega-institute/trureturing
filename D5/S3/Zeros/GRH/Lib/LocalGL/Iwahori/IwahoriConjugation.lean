/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/IwahoriConjugation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Iwahori/IwahoriConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Iwahori.IwahoriConjugation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Iwahori/IwahoriConjugation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.CyclicSubrep
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Elements of I t I, t strictly dominant, are twisted-conjugate into the torus. -/

open Matrix WithZero Valued GeneralLinearGroup DoubleCoset Filter


attribute [local simp] zero_lt_iff mul_assoc zpow_ne_zero _root_.zpow_add mem_proIwahori
attribute [local simp ←] map_zpow
variable {F F' N} [Field F] [Valued F ℤᵐ⁰] [Field F'] [Valued F' ℤᵐ⁰]
  {g : GL (Fin N) F} {t : Fin N → Fˣ} (ht : StrictMono (v <| t · |>.1))

/-- The double coset I₁ diag(t) I₁ in GL_n(F), where I₁ = `proIwahori` is the pro-p Iwahori subgroup
and t a family of nonzero elements of F. -/
abbrev iwahoriDoubleCoset (t : Fin N → Fˣ) :=
  doubleCoset (diagGL t) (SetLike.coe proIwahori) (SetLike.coe proIwahori)

lemma diagGL_mem_proIwahori : diagGL t ∈ proIwahori ↔ ∀ i, v ((t i).1 - 1) < 1 := by
  simp [diagonal]; grind [v.map_eq_of_sub_lt, one_pos]

lemma map_mem_proIwahori_iff_of_isEquiv {ι : F →+* F'} (h : (v.comap ι).IsEquiv v) :
  g.map ι ∈ proIwahori ↔ g ∈ proIwahori := by simp [← h.le_one_iff_le_one, ← h.lt_one_iff_lt_one]

include ht

lemma eventually_v_mul_pow_le_one (a : _ → _ → F) : ∀ᶠ k in atTop, ∀ i j, i < j →
    v (t i ^ k / t j ^ k * a i j) ≤ 1 := by
  simp_rw [eventually_all, ← div_pow]
  exact fun i j h ↦ (tendsto_zero_pow_of_v_lt_one (by simp [ht h, field])).mul_const _
    ((isOpen_integer F).mem_nhds (by simp))

lemma eventually_pow_mul_mem_dominantTorus s : ∀ᶠ k in atTop, t ^ k * s ∈ dominantTorus :=
  (eventually_v_mul_pow_le_one ht
  (s · / s ·)).mono (by simp [dominantTorus, monotone_iff_forall_lt, field])

/-- Let σ be a continuous isometric endomorphism of the local field F, surjective on GL_n(F),
and t diagonal with strictly increasing absolute values. Every g in I₁tI₁ (I₁ the pro-p
Iwahori subgroup) satisfies k⁻¹gσ(k) = td with k, d in I₁, d diagonal. -/
lemma exists_twisted_conj_diag [CompactSpace 𝒪[F]]
    (σ : F →+* F) (hσ : ∀ x, v (σ x) = v x) (cont : Continuous σ) (sur :
  (⇑(map (n := Fin N) σ)).Surjective) (hg : g ∈ iwahoriDoubleCoset t) : ∃ k ∈ proIwahori, ∃ d,
  diagGL d ∈ proIwahori ∧ k⁻¹ * g * k.map σ = diagGL (t * d) := by
  let H (j : ℤ) := (MulAut.conj (diagGL t) ^ j).comapSubgroup proIwahori
  let X (k : proIwahori) := (diagGL t)⁻¹ * (k.1⁻¹ * g * .map σ k)
  have L {j g} : g.map σ ∈ H j ↔ g ∈ H j := by
    simp [H, ← map_inv, ← hσ (g _ _ - 1), mul_left_comm (_ ^ j), *]
  choose f h using (Nat.rec (Nat.rec (let ⟨k, p, _, q, e⟩ := mem_doubleCoset.1 hg
    ⟨⟨k, p⟩, by simp [X, (H 0).mul_mem q (L.2 p), *]⟩) fun y ⟨k, hc⟩ ↦
    (exists_unipotent_conj_mem_proIwahori ht.monotone (hc 0)).rec fun u ⟨hu,
    _⟩ ↦ let ⟨z, hp⟩ := sur (u⁻¹ * X k)
    have U (j : ℕ) : u ∈ H j := by simpa [H, ← map_pow] using
      conj_unitriangular_mem_proIwahori (pow_mem ht.monotone j) hu
    have B (j : ℕ) (h : j ≤ y.succ := by grind) : z ∈ H (j + -1) :=
      by cases j; rwa [← L, hp]; grind [mul_mem, inv_mem]
    ⟨k * ⟨_, B 1⟩⁻¹, fun j a ↦ by lift j to ℕ using a.1; simpa [X, H, *] using
      (proIwahori.mul_mem (B j) (U j))⟩) fun _ h y ↦ let ⟨k, hc⟩ := h y.succ
    ⟨k * ⟨_, hc 1⟩, fun j a ↦ by simpa [X] using (@L _ (⟨_, hc 1⟩ : proIwahori)).2 (by simpa [H]
      using (hc (j + 1)))⟩ : ∀ x y : ℕ, ∃ k, ∀ j (_ : j ∈ Set.Icc (-↑x) ↑y := by grind), X k ∈ H j)
  have ⟨k, K⟩ := exists_clusterPt_of_compactSpace (atTop.map (diag f))
  have K j : k ∈ X ⁻¹' H j := ((proIwahori.isClosed_of_isOpen isOpen_proIwahori).preimage
    (by simp; fun_prop)).mem_of_mapClusterPt K (.mono (mem_atTop j.natAbs) fun _ _ ↦ h ..)
  use k, k.2, (.mk0 _ <| v.pos_iff.1 <| v_diag_eq_one_of_mem_proIwahori (K 0) · ▸ one_pos),
    diagGL_mem_proIwahori.2 (K 0).2.2,
    map_mul diagGL t _ ▸ eq_mul_of_inv_mul_eq (Units.ext (IsDiag.diagonal_diag fun i j h ↦ by_contra
    fun e : X k i j ≠ 0 ↦ have A m := (by simpa [← map_inv, ← log_le_log, e] using
      (mem_proIwahori.1 (K (m - m * (v (X k i j)).log))).1 i j)
    by cases h.lt_or_gt <;> nlinarith [A 1, A (-1), by simpa [← log_lt_log] using ht ‹_›]).symm)
