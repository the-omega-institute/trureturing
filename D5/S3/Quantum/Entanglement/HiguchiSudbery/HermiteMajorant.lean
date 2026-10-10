/- GID: D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteMajorant
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HiguchiSudbery/HermiteMajorant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: HermiteMajorant for the sharp four-qubit marginal entropy bound. -/

/-
proof_shape: double_contact_nonnegative: content
escape_witness: double_contact_nonnegative (the general fourth-derivative comparison)
admission_basis: escape-witness
Direct frozen dependencies: none
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
namespace D5.S3.Quantum.Entanglement.HiguchiSudbery

set_option maxHeartbeats 0
open Set

private lemma rolle_positive /- proof_shape: bind-only; consumer: HermiteMajorant.no_four_roots -/ {f g : ℝ → ℝ} (h : ∀ x, 0 < x → HasDerivAt f (g x) x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (heq : f a = f b) :
    ∃ c ∈ Ioo a b, g c = 0 := by
  refine exists_hasDerivAt_eq_zero hab ?_ heq ?_
  · intro x hx
    exact (h x (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt
  · intro x hx
    exact h x (lt_trans ha hx.1)

private lemma no_four_roots /- proof_shape: bind-only; consumer: HermiteMajorant.no_double_contact_third_root -/ {f g h k : ℝ → ℝ}
    (hf : ∀ x, 0 < x → HasDerivAt f (g x) x)
    (hg : ∀ x, 0 < x → HasDerivAt g (h x) x)
    (hh : ∀ x, 0 < x → HasDerivAt h (k x) x)
    (hk : ∀ x, 0 < x → 0 < k x)
    {a b c d : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hfa : f a = 0) (hfb : f b = 0) (hfc : f c = 0) (hfd : f d = 0) : False := by
  obtain ⟨u, hu, hgu⟩ := rolle_positive hf ha hab (hfa.trans hfb.symm)
  obtain ⟨v, hv, hgv⟩ := rolle_positive hf (lt_trans ha hab) hbc (hfb.trans hfc.symm)
  obtain ⟨w, hw, hgw⟩ := rolle_positive hf (by linarith) hcd (hfc.trans hfd.symm)
  obtain ⟨s, hs, hhs⟩ := rolle_positive hg (by linarith [hu.1])
    (by linarith [hu.2, hv.1]) (hgu.trans hgv.symm)
  obtain ⟨t, ht, hht⟩ := rolle_positive hg (by linarith [hv.1])
    (by linarith [hv.2, hw.1]) (hgv.trans hgw.symm)
  obtain ⟨r, hr, hkr⟩ := rolle_positive hh (by linarith [hs.1, hu.1])
    (by linarith [hs.2, ht.1]) (hhs.trans hht.symm)
  have hp := hk r (by linarith [hr.1, hs.1, hu.1])
  linarith

private lemma no_double_contact_third_root /- proof_shape: bind-only; consumer: HermiteMajorant.double_contact_nonnegative -/ {f f1 f2 f3 f4 : ℝ → ℝ}
    (h0 : ∀ x, 0 < x → HasDerivAt f (f1 x) x)
    (h1 : ∀ x, 0 < x → HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x, 0 < x → HasDerivAt f2 (f3 x) x)
    (h3 : ∀ x, 0 < x → HasDerivAt f3 (f4 x) x)
    (h4 : ∀ x, 0 < x → 0 < f4 x)
    {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hx : 0 < x)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (hfa : f a = 0) (hfb : f b = 0) (hfx : f x = 0)
    (h1a : f1 a = 0) (h1b : f1 b = 0) : False := by
  rcases lt_or_gt_of_ne hxa with hxa | hax
  · obtain ⟨u, hu, hfu⟩ := rolle_positive h0 hx hxa (hfx.trans hfa.symm)
    obtain ⟨v, hv, hfv⟩ := rolle_positive h0 ha hab (hfa.trans hfb.symm)
    exact no_four_roots h1 h2 h3 h4 (by linarith [hu.1]) hu.2 hv.1 hv.2 hfu h1a hfv h1b
  · rcases lt_or_gt_of_ne hxb with hxb | hbx
    · obtain ⟨u, hu, hfu⟩ := rolle_positive h0 ha hax (hfa.trans hfx.symm)
      obtain ⟨v, hv, hfv⟩ := rolle_positive h0 hx hxb (hfx.trans hfb.symm)
      exact no_four_roots h1 h2 h3 h4 ha hu.1 (by linarith [hu.2, hv.1]) hv.2 h1a hfu hfv h1b
    · obtain ⟨u, hu, hfu⟩ := rolle_positive h0 ha hab (hfa.trans hfb.symm)
      obtain ⟨v, hv, hfv⟩ := rolle_positive h0 (lt_trans ha hab) hbx (hfb.trans hfx.symm)
      exact no_four_roots h1 h2 h3 h4 ha hu.1 hu.2 hv.1 h1a hfu h1b hfv



set_option maxHeartbeats 0
open Real Set

private def contactQ (a b x : ℝ) : ℝ := (x-a)^2 * (x-b)^2

private def contactQ1 (a b x : ℝ) : ℝ := 2*(x-a)*(x-b)^2 + 2*(x-b)*(x-a)^2

private def contactQ2 (a b x : ℝ) : ℝ := 2*(x-b)^2 + 8*(x-a)*(x-b) + 2*(x-a)^2

private def contactQ3 (a b x : ℝ) : ℝ := 12*(x-a) + 12*(x-b)

private lemma contactQ_derivatives /- proof_shape: bind-only; consumer: HermiteMajorant.double_contact_nonnegative -/ (a b x : ℝ) :
    HasDerivAt (contactQ a b) (contactQ1 a b x) x ∧
    HasDerivAt (contactQ1 a b) (contactQ2 a b x) x ∧
    HasDerivAt (contactQ2 a b) (contactQ3 a b x) x ∧
    HasDerivAt (contactQ3 a b) 24 x := by
  have ha := (hasDerivAt_id x).sub_const a
  have hb := (hasDerivAt_id x).sub_const b
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! (ha.pow 2).mul (hb.pow 2) using 1 <;>
      (try { with_unfolding_all rfl }) <;> (try funext y) <;> (try dsimp [contactQ, contactQ1]) <;> ring
  · convert! ((ha.mul (hb.pow 2)).const_mul 2).add
      ((hb.mul (ha.pow 2)).const_mul 2) using 1 <;>
      (try { with_unfolding_all rfl }) <;> (try funext y) <;> (try dsimp [contactQ1, contactQ2]) <;> ring
  · convert! (((hb.pow 2).const_mul 2).add
      ((ha.mul hb).const_mul 8)).add ((ha.pow 2).const_mul 2) using 1 <;>
      (try { with_unfolding_all rfl }) <;> (try funext y) <;> (try dsimp [contactQ2, contactQ3]) <;> ring
  · convert! (ha.const_mul 12).add (hb.const_mul 12) using 1 <;>
      (try { with_unfolding_all rfl }) <;> (try funext y) <;> (try dsimp [contactQ3]) <;> ring

lemma double_contact_nonnegative {f f1 f2 f3 f4 : ℝ → ℝ}
    (h0 : ∀ x, 0 < x → HasDerivAt f (f1 x) x)
    (h1 : ∀ x, 0 < x → HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x, 0 < x → HasDerivAt f2 (f3 x) x)
    (h3 : ∀ x, 0 < x → HasDerivAt f3 (f4 x) x)
    (h4 : ∀ x, 0 < x → 0 ≤ f4 x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hfa : f a = 0) (hfb : f b = 0) (h1a : f1 a = 0) (h1b : f1 b = 0) :
    ∀ x, 0 < x → 0 ≤ f x := by
  intro x hx
  by_cases hxa : x = a
  · simpa [hxa, hfa]
  by_cases hxb : x = b
  · simpa [hxb, hfb]
  by_contra hn
  have hneg : f x < 0 := lt_of_not_ge hn
  have hq : 0 < contactQ a b x := by
    exact mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxa))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hxb))
  let K := f x / contactQ a b x
  have hK : K < 0 := div_neg_of_neg_of_pos hneg hq
  let r := fun y => f y - K * contactQ a b y
  let r1 := fun y => f1 y - K * contactQ1 a b y
  let r2 := fun y => f2 y - K * contactQ2 a b y
  let r3 := fun y => f3 y - K * contactQ3 a b y
  let r4 := fun y => f4 y - K * 24
  refine no_double_contact_third_root
    (f := r) (f1 := r1) (f2 := r2) (f3 := r3) (f4 := r4)
    (a := a) (b := b) (x := x) ?_ ?_ ?_ ?_ ?_ ha hab hx hxa hxb ?_ ?_ ?_ ?_ ?_
  · intro y hy; exact (h0 y hy).sub ((contactQ_derivatives a b y).1.const_mul K)
  · intro y hy; exact (h1 y hy).sub ((contactQ_derivatives a b y).2.1.const_mul K)
  · intro y hy; exact (h2 y hy).sub ((contactQ_derivatives a b y).2.2.1.const_mul K)
  · intro y hy; exact (h3 y hy).sub ((contactQ_derivatives a b y).2.2.2.const_mul K)
  · intro y hy; dsimp [r4]; linarith [h4 y hy]
  · simp [r, contactQ, hfa]
  · simp [r, contactQ, hfb]
  · dsimp [r, K]; rw [div_mul_cancel₀ _ hq.ne']; ring
  · simp [r1, contactQ1, h1a]
  · simp [r1, contactQ1, h1b]

end D5.S3.Quantum.Entanglement.HiguchiSudbery
