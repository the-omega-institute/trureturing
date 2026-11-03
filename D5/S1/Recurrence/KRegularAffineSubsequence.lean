/- GID: D5/S1/Recurrence/KRegularAffineSubsequence
   generality: I
   mirror-B: D5/B/S1/Recurrence/KRegularAffineSubsequence
   mirror-E: none(waiver:noncomputational-general-theorem)
   anchors: []
   utility: none
   digest: Every positive-step affine subsequence of an integer k-regular sequence is k-regular. -/

import D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

/-!
# Affine subsequences of integer k-regular sequences

The kernel and regularity predicate are the native ones in
`SobolewskiUlasParityPositions`. Both statements allow arbitrary bases k ≥ 2,
unbounded integer values, and infinite kernels.

Allouche and Shallit, *The Ring of k-Regular Sequences*, author-hosted preprint,
Theorem 2.6, PDF page 7; the Noetherian coefficient convention and Definition 2.1
are on PDF page 3. The coefficient ring here is the Noetherian ring of integers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.KRegularAffineSubsequence

open D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions (kKernel IsKRegular)

/-- Uniform transport of the entire affine-subsequence kernel into the span of
finitely many affine observations of any finite generating family. -/
theorem affine_kernel_span_le (k a b : ℕ) (s : ℕ → ℤ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (G : Finset (ℕ → ℤ))
    (hG : Submodule.span ℤ (G : Set (ℕ → ℤ)) = Submodule.span ℤ (kKernel k s)) :
    Submodule.span ℤ (kKernel k (fun n => s (a * n + b))) ≤
      Submodule.span ℤ {f | ∃ g ∈ G, ∃ c : ℕ, c < a + b ∧
        f = fun n => g (a * n + c)} := by
  apply Submodule.span_le.mpr
  rintro f ⟨e, r, hr, rfl⟩
  let q : ℕ := k ^ e
  have hq : 0 < q := pow_pos (by omega) _
  let c : ℕ := (a * r + b) / q
  let d : ℕ := (a * r + b) % q
  have hc : c < a + b := by
    apply (Nat.div_lt_iff_lt_mul hq).2
    have har : a * r < a * q := Nat.mul_lt_mul_of_pos_left hr (by omega)
    have hb : b ≤ b * q := by nlinarith [Nat.mul_le_mul_left b hq]
    nlinarith
  let v : ℕ → ℤ := fun n => s (q * n + d)
  have hv : v ∈ Submodule.span ℤ (G : Set (ℕ → ℤ)) := by
    rw [hG]
    exact Submodule.subset_span ⟨e, d, Nat.mod_lt _ hq, rfl⟩
  let L : (ℕ → ℤ) →ₗ[ℤ] (ℕ → ℤ) := LinearMap.funLeft ℤ ℤ (fun n => a * n + c)
  have hL := Submodule.apply_mem_span_image_of_mem_span L hv
  have hcontain : L '' (G : Set (ℕ → ℤ)) ⊆
      {f | ∃ g ∈ G, ∃ c : ℕ, c < a + b ∧ f = fun n => g (a * n + c)} := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, c, hc, rfl⟩
  have hindices (n : ℕ) : a * (q * n + r) + b = q * (a * n + c) + d := by
    have hdiv := Nat.mod_add_div (a * r + b) q
    dsimp [c, d]
    nlinarith
  have heq : (fun n => s (a * (k ^ e * n + r) + b)) = L v := by
    funext n
    exact congrArg s (hindices n)
  rw [heq]
  exact Submodule.span_mono hcontain hL

/-- Allouche--Shallit affine-subsequence closure for the native integer-valued
k-regularity predicate, with arbitrary base, positive step, and natural offset. -/
theorem is_k_regular_affine_subsequence (k a b : ℕ) (s : ℕ → ℤ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hs : IsKRegular k s) :
    IsKRegular k (fun n => s (a * n + b)) := by
  obtain ⟨G, _, hG⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (kKernel k s)).1 hs
  have hfinite : ({f | ∃ g ∈ G, ∃ c : ℕ, c < a + b ∧
      f = fun n => g (a * n + c)} : Set (ℕ → ℤ)).Finite := by
    have h := (G.finite_toSet.prod (Set.finite_Iio (a + b))).image
      (fun p : (ℕ → ℤ) × ℕ => fun n => p.1 (a * n + p.2))
    apply h.subset
    rintro _ ⟨g, hg, c, hc, rfl⟩
    exact ⟨(g, c), ⟨hg, hc⟩, rfl⟩
  exact (Submodule.fg_span hfinite).of_le (affine_kernel_span_le k a b s hk ha G hG.symm)

end D5.S1.Recurrence.KRegularAffineSubsequence
