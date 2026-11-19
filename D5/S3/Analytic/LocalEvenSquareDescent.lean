/- GID: D5/S3/Analytic/LocalEvenSquareDescent
   generality: I
   mirror-B: D5/B/S3/Analytic/LocalEvenSquareDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphic descent of even germs along the square and the negative square. -/

import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic

/-! Holomorphic descent of even germs along the square and the negative square. -/

namespace D5.S3.Analytic.LocalEvenSquareDescent

open Filter Set
open scoped Topology

private theorem sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

private noncomputable def evenPart (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z + f (-z)) / 2

private theorem evenPart_even (f : ℂ → ℂ) : Function.Even (evenPart f) := by
  intro z
  simp [evenPart, add_comm]

private theorem descent_pullback (f : ℂ → ℂ) (z : ℂ) :
    evenPart f (Complex.sqrt (z ^ 2)) = evenPart f z := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (sqrt_sq (z ^ 2)) with h | h
  · rw [h]
  · rw [h, evenPart_even]

private theorem evenPart_differentiableAt {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | z ^ 2 ∈ U}) {z : ℂ}
    (hz : z ^ 2 ∈ U) : DifferentiableAt ℂ (evenPart f) z := by
  have ho : IsOpen {w : ℂ | w ^ 2 ∈ U} := hU.preimage (continuous_id.pow 2)
  have hneg : (-z) ^ 2 ∈ U := by simpa using hz
  have h₁ := (hf z hz).differentiableAt (ho.mem_nhds hz)
  have h₂ := (hf (-z) hneg).differentiableAt (ho.mem_nhds hneg)
  exact (h₁.add (h₂.comp z differentiableAt_id.neg)).div_const 2

private theorem differentiable_off_zero {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | z ^ 2 ∈ U}) {z : ℂ}
    (hz : z ∈ U) (hn : z ≠ 0) :
    DifferentiableAt ℂ (fun w => evenPart f (Complex.sqrt w)) z := by
  let b := Complex.sqrt z
  have hb : b ^ 2 = z := sqrt_sq z
  have hb0 : b ≠ 0 := by
    intro h
    apply hn
    rw [← hb, h, zero_pow (by norm_num)]
  have hd : HasStrictDerivAt (fun w : ℂ => w ^ 2) (2 * b) b := by
    simpa using hasStrictDerivAt_pow 2 b
  have hder : (2 : ℂ) * b ≠ 0 := mul_ne_zero (by norm_num) hb0
  let g := hd.localInverse (fun w : ℂ => w ^ 2) (2 * b) b hder
  have hg : DifferentiableAt ℂ g (b ^ 2) :=
    (hd.to_localInverse hder).hasDerivAt.differentiableAt
  have hi : ∀ᶠ w in 𝓝 (b ^ 2), (g w) ^ 2 = w := hd.eventually_right_inverse hder
  have hgm : (g (b ^ 2)) ^ 2 ∈ U := by
    rw [hi.self_of_nhds, hb]
    exact hz
  have heq : (fun w => evenPart f (Complex.sqrt w)) =ᶠ[𝓝 (b ^ 2)]
      (fun w => evenPart f (g w)) := by
    filter_upwards [hi] with w hw
    simpa only [hw] using descent_pullback f (g w)
  rw [← hb]
  exact ((evenPart_differentiableAt hU hf hgm).comp (b ^ 2) hg).congr_of_eventuallyEq heq

/-- On an open set the even part on its square preimage descends
to a holomorphic function, with no branch choice in the descended value. -/
theorem even_square_descent_on {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | z ^ 2 ∈ U}) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧
      ∀ z : ℂ, F (z ^ 2) = (f z + f (-z)) / 2 := by
  refine ⟨fun w => evenPart f (Complex.sqrt w), fun z hz => ?_, descent_pullback f⟩
  by_cases hn : z = 0
  · subst z
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (f := fun w => evenPart f (Complex.sqrt w)) ?_ ?_).differentiableAt.differentiableWithinAt
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hU.mem_nhds hz)] with w hw hmem
      exact differentiable_off_zero hU hf hmem hw
    · have hzero : (0 : ℂ) ^ 2 ∈ U := by simpa using hz
      have hc := (evenPart_differentiableAt hU hf hzero).continuousAt
      have hs : ContinuousAt Complex.sqrt (0 : ℂ) :=
        Complex.continuousAt_sqrt (Or.inl (by simp))
      have hs₀ : Complex.sqrt (0 : ℂ) = 0 := by simp
      have hc' : ContinuousAt (evenPart f) (Complex.sqrt 0) := by simpa only [hs₀] using hc
      exact hc'.comp hs
  · exact (differentiable_off_zero hU hf hz hn).differentiableWithinAt

/-- The negative square used by the original four-point Laurent diagonal.
Any germ with the same pullback agrees at the cusp with the descended function. -/
theorem even_neg_square_descent_on {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | -(z ^ 2) ∈ U}) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧
      (∀ z : ℂ, F (-(z ^ 2)) = (f z + f (-z)) / 2) ∧
      ∀ G : ℂ → ℂ, (∀ᶠ z in 𝓝 (0 : ℂ), G (-(z ^ 2)) = (f z + f (-z)) / 2) →
        F =ᶠ[𝓝 (0 : ℂ)] G := by
  let V := (fun z : ℂ => -z) ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_neg
  obtain ⟨A, hA, hA_sq⟩ := even_square_descent_on hV hf
  refine ⟨fun z => A (-z), hA.comp differentiable_id.neg.differentiableOn ?_, ?_, ?_⟩
  · intro z hz
    change - -z ∈ U
    simpa using hz
  · intro z
    simpa only [neg_neg] using hA_sq z
  · intro G hG
    have hs : ContinuousAt (fun z : ℂ => Complex.sqrt (-z)) (0 : ℂ) := by
      have h : ContinuousAt Complex.sqrt (0 : ℂ) :=
        Complex.continuousAt_sqrt (Or.inl (by simp))
      have hn : ContinuousAt (fun z : ℂ => -z) (0 : ℂ) := continuous_neg.continuousAt
      have h' : ContinuousAt Complex.sqrt (-(0 : ℂ)) := by simpa only [neg_zero] using h
      exact h'.comp hn
    have ht : Tendsto (fun z : ℂ => Complex.sqrt (-z)) (𝓝 0) (𝓝 0) := by
      simpa using hs.tendsto
    filter_upwards [ht.eventually hG] with z hz
    have hsq := sqrt_sq (-z)
    have hA_at := hA_sq (Complex.sqrt (-z))
    simpa only [hsq, neg_neg] using hA_at.trans hz.symm

#print axioms even_square_descent_on
#print axioms even_neg_square_descent_on

end D5.S3.Analytic.LocalEvenSquareDescent
