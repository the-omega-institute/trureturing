/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/ExponentOfLabel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Iwahori/ExponentOfLabel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Iwahori.ExponentOfLabel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Iwahori/ExponentOfLabel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori.SortedExponents
import D5.S3.Zeros.GRH.Lib.LocalGL.Shintani.ShintaniLifting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Depth-zero type induced from determinant characters yields a sorted tame Iwahori
eigenvector. -/

open Matrix Valued IsLocalRing MulChar Fintype Fint Submodule Pi Function Polynomial
attribute [-simp] MulCharClass.map_nonunit

/-- Let ρ be smooth unitary, cyclic subrepresentations having finite-dimensional I₁-invariants;
χ_a distinct, ∑m_a = N, Y = ∏_a (χ_a∘det in dimension m_a), x fixed by 1+𝔭M_N(𝒪), ∑ conj
Y(g) g x ≠ 0. Then translates of x span a ξ-eigenvector, |ξ_i(ϖ)| non-increasing, ξ_i = χ_a
on units m_a times.

Known result: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t
I. -/
lemma exists_sorted_of_detChar {F} [Field F] [Valued F _] [CompactSpace 𝒪[F]] {N} {ρ : Rep ℂ (GL
  (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ B x} (hϖ : v ϖ.1 = .exp (-1)) [∀ x, Module.Finite ℂ ((cyclicSpan
  ρ.ρ x).submoduleOf (levelSpace ρ.ρ proIwahori 1))] (hB : IsUnitary ρ.ρ B) {n r χ} [Fintype n] (e :
  n ≃ _) (hχ : Injective χ) {m : Fin r → _} (hm : ∑ a, m a = N) (hx : ∀ k, intGL.map (residue 𝒪[F])
  k = 1 → ρ (reindexGL e k.1) x = x) {s : _ → _} (_ : ∀ g, intGL.map (residue _) (s g) = g) (h : ∑ᶠ
  g, star ((∏ a, (detChar (χ a)).rankPart (m a)).evalGL g) • ρ (reindexGL e (s g).1) x ≠ 0) : ∃ y ∈
  cyclicSpan ρ.ρ x, ∃ θ, IsIwahoriEigen ρ (torusChar θ) y ∧ (Antitone fun i ↦ ‖(θ i ϖ : ℂ)‖) ∧ ∀ t
  (h : v t.1 = 1), ∏ i, (X - C (θ i t).1) = ∏ a, (X - C (χ a (residue 𝒪[F] ⟨t, h.le⟩))) ^ m a := by
  let := e.linearOrder
  obtain ⟨b, hb, rfl⟩ : ∃ b, Monotone b ∧ (card {i // b i = ·}) = m := ⟨_, (Tuple.monotone_sort
    (_ ∘ equivOfCardEq (by simp_all))).comp (by tauto), funext fun a ↦ (card_congr
    ((e.trans (.trans ..)).subtypeEquivOfSubtype.trans (.sigmaSubtype a))).trans (card_fin _)⟩
  have H g z w := by simpa [inv_mul_eq_one] using hx ((s w)⁻¹ * (g * z))
  choose _ h using by simpa using (sum_evalGL_prod_eq_zero_iff b (fun _ ↦
    lift_detChar (faithfulChar 𝓀[F]) rfl) _ (by grind)).2.mt h
  set y : ρ := Finset.sum ..
  have hu g : (BlockTriangular _ e → _ = (∏ i, χ (b i) (intGL.map (residue _) g i i)) • y) ∧ (_ →
    ∃ c, ρ (reindexGL e g) y = c • y) := (fun E : ∀ h, _ = (∏ a, χ a (blockHom b a ⟨intGL.map
    (residue _) g, h⟩).1.det) • y ↦ ⟨fun h ↦ (E fun _ _ c ↦ h (hb.reflect_lt c)).trans (by
    rw [← prod_fiberwise b]; congr!; rw [det_of_isUpperTriangular h.submatrix, map_prod]; congr!
    omega), (⟨_, E ·⟩)⟩) fun h ↦ by simpa [y, Finset.smul_sum, smul_smul, *] using .symm (sum_equiv
    (.mulLeft ⟨_, h⟩⁻¹) _ _ (by simp [inv_apply', mul_assoc, star_apply', starRingEnd_apply]))
  replace hu g (h : g ∈ intGL ..) := by
    simpa [↓(reindexGL e).apply_symm_apply, reindex_equiv e.symm, reindexGL, parabolic,
      BlockTriangular] using (hu ⟨(reindexGL e).symm g, h.elim (⟨reindexGL e.symm ·, · ▸ rfl⟩)⟩)
  lift ⇑(residue 𝒪[F]) to F → 𝓀[F] using ⟨⟩ with R hR
  have k a m := congr($hR ⟨a, m⟩).trans ∘ residue_eq_one_iff_lt.2
  have ⟨_, _, _, σ, hs, z, hz, Z⟩ :=
    exists_sorted_of_type hϖ (by simp_all [mem_proIwahori_iff_blockParahoric, mem_blockParahoric,
    mem_intGL]) (fun _ o ↦ (hu _ o).1 (by simp_all [ne_of_gt])) (fun σ o ↦ (hu _
    (permGL_mem_intGL σ)).2 fun i j _ ↦ by simp [show σ.symm i ≠ j by grind [hχ (ext
    ((surjective_units_map_of_local_ringHom _ residue_surjective inferInstance).forall.2 fun a ↦ by
       simpa [mulSingle_apply, apply_ite, ← hR, *] using! o j (a.map _) ((Valuation.integer.integers
         _).valuation_unit _)))]]) hB h
  exact ⟨z, span_le.2 (by simp [y, sum_smul_mem, ← Module.End.mul_apply, ← map_mul,
    mem_span_of_mem]) hz, _, Z, hs, fun t h ↦ by simpa [mulSingle_apply, apply_ite, *] using
    (((σ.trans e.symm).prod_comp _).trans (prod_fiberwise' b fun a ↦ X - C (χ a _)).symm)⟩
