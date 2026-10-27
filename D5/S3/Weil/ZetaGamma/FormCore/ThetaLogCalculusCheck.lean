import D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
noncomputable section

/- Uncompiled generic derivative identities for log(F0).
   Search found the existing first-log derivative but no complete generic
   fourth-log chain in D5 or the pinned Mathlib. All differentiations below
   directly reuse HasDerivAt.log/div/mul/pow; the rational identities are
   consumed helpers of the actual theta square-variable concavity proof.
   No actual Phi positivity, parity, jet identity or numerator sign is claimed.
-/

noncomputable section

namespace RhTransient.GenericLogFourthJets

def logJet1 (F0 F1 : ℝ → ℝ) (x : ℝ) : ℝ := F1 x / F0 x

def logJet2 (F0 F1 F2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  F2 x / F0 x - (F1 x) ^ 2 / (F0 x) ^ 2

def logJet3 (F0 F1 F2 F3 : ℝ → ℝ) (x : ℝ) : ℝ :=
  F3 x / F0 x - 3 * ((F1 x * F2 x) / (F0 x) ^ 2) +
    2 * ((F1 x) ^ 3 / (F0 x) ^ 3)

/-- Exactly the actual fourth-log numerator N divided by F0^4. -/
def logJet4 (F0 F1 F2 F3 F4 : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((F0 x) ^ 3 * F4 x - 4 * (F0 x) ^ 2 * F1 x * F3 x -
      3 * (F0 x) ^ 2 * (F2 x) ^ 2 + 12 * F0 x * (F1 x) ^ 2 * F2 x -
      6 * (F1 x) ^ 4) / (F0 x) ^ 4

/-- The complete local logarithmic jet chain. A positive actual kernel
    supplies hne, while its original smooth jets supply h0 through h3. -/
theorem hasDerivAt_log_four_jets (F0 F1 F2 F3 F4 : ℝ → ℝ) {x : ℝ}
    (h0 : HasDerivAt F0 (F1 x) x) (h1 : HasDerivAt F1 (F2 x) x)
    (h2 : HasDerivAt F2 (F3 x) x) (h3 : HasDerivAt F3 (F4 x) x)
    (hne : F0 x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (F0 t)) (logJet1 F0 F1 x) x ∧
      HasDerivAt (logJet1 F0 F1) (logJet2 F0 F1 F2 x) x ∧
      HasDerivAt (logJet2 F0 F1 F2) (logJet3 F0 F1 F2 F3 x) x ∧
      HasDerivAt (logJet3 F0 F1 F2 F3) (logJet4 F0 F1 F2 F3 F4 x) x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [logJet1] using! h0.log hne
  · convert! h1.div h0 hne using 1 <;>
      dsimp only [logJet1, logJet2] <;> field_simp [hne] <;> ring
  · convert! (h2.div h0 hne).sub
      ((h1.pow 2).div (h0.pow 2) (pow_ne_zero _ hne)) using 1 <;>
      simp only [logJet2, logJet3, Pi.pow_apply, Pi.mul_apply] <;>
      field_simp [hne] <;> ring
  · convert! ((h3.div h0 hne).sub
      (((h1.mul h2).div (h0.pow 2) (pow_ne_zero _ hne)).const_mul (3 : ℝ))).add
      (((h1.pow 3).div (h0.pow 3) (pow_ne_zero _ hne)).const_mul (2 : ℝ)) using 1 <;>
      simp only [logJet3, logJet4, Pi.pow_apply, Pi.mul_apply] <;>
      field_simp [hne] <;> ring

end RhTransient.GenericLogFourthJets

#print axioms RhTransient.GenericLogFourthJets.hasDerivAt_log_four_jets

/- Uncompiled generic calculus bridge. The five f_i are jets of ell, which
   will be log(Phi) in the actual consumer; they are not the jets of Phi.
   The two origin conditions are the odd-jet consequences of evenness.
   No statement about the sign of the actual Phi numerator is assumed here.

   Reuses the existing Mathlib monotonicity and strict-concavity theorems.
   No matching complete square-variable bridge was found in D5 or Mathlib.
   Classification/retention remains subject to the actual consumer's review.
-/

namespace RhTransient.EvenLogFourthSquareConcavity

open Set Real

/-- Negative fourth derivative and vanishing odd origin jets imply a
    positive radial curvature gap and strict concavity in the square variable.
    Explicit jet assumptions keep this reusable independently of the actual
    theta-kernel logarithmic-derivative computation. -/
theorem squareVariable_strictConcavity_of_fourthJet_neg
    (f0 f1 f2 f3 f4 : ℝ → ℝ)
    (h01 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f0 (f1 x) x)
    (h12 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f1 (f2 x) x)
    (h23 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f2 (f3 x) x)
    (h34 : ∀ x : ℝ, 0 ≤ x → HasDerivAt f3 (f4 x) x)
    (h10 : f1 0 = 0) (h30 : f3 0 = 0)
    (h4neg : ∀ x : ℝ, 0 < x → f4 x < 0) :
    (∀ x : ℝ, 0 < x → 0 < f1 x - x * f2 x) ∧
      StrictConcaveOn ℝ (Ioi (0 : ℝ)) (fun r : ℝ => f0 (Real.sqrt r)) := by
  have hanti3 : StrictAntiOn f3 (Ici (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
      (fun x hx => (h34 x hx).continuousAt.continuousWithinAt)
    intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [(h34 x hx0.le).deriv]
    exact h4neg x hx0
  have h3neg (x : ℝ) (hx : 0 < x) : f3 x < 0 := by
    simpa only [h30] using hanti3 (show (0 : ℝ) ∈ Ici 0 by simp) hx.le hx
  let K : ℝ → ℝ := fun x => f1 x - x * f2 x
  have hK (x : ℝ) (hx : 0 ≤ x) : HasDerivAt K (-x * f3 x) x := by
    convert! (h12 x hx).sub ((hasDerivAt_id x).mul (h23 x hx)) using 1 <;>
      simp only [K, id_eq, one_mul] <;> ring
  have hmonoK : StrictMonoOn K (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
      (fun x hx => (hK x hx).continuousAt.continuousWithinAt)
    intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [(hK x hx0.le).deriv]
    simpa only [neg_mul] using neg_pos.mpr (mul_neg_of_pos_of_neg hx0 (h3neg x hx0))
  have hgap (x : ℝ) (hx : 0 < x) : 0 < f1 x - x * f2 x := by
    simpa only [K, zero_mul, sub_zero, h10] using
      hmonoK (show (0 : ℝ) ∈ Ici 0 by simp) hx.le hx
  refine ⟨hgap, ?_⟩
  let G : ℝ → ℝ := fun r => f0 (Real.sqrt r)
  let H : ℝ → ℝ := fun r => f1 (Real.sqrt r) / (2 * Real.sqrt r)
  have hG (r : ℝ) (hr : 0 < r) : HasDerivAt G (H r) r := by
    convert! (h01 (Real.sqrt r) (Real.sqrt_nonneg r)).comp r
      (Real.hasDerivAt_sqrt hr.ne') using 1 <;> dsimp only [G, H] <;> ring
  have hH (r : ℝ) (hr : 0 < r) :
      HasDerivAt H
        ((Real.sqrt r * f2 (Real.sqrt r) - f1 (Real.sqrt r)) /
          (4 * (Real.sqrt r) ^ 3)) r := by
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hsder := Real.hasDerivAt_sqrt hr.ne'
    have hnum := (h12 (Real.sqrt r) hs.le).comp r hsder
    have hden := hsder.const_mul (2 : ℝ)
    convert! hnum.div hden (by positivity : (2 : ℝ) * Real.sqrt r ≠ 0) using 1 <;>
      (try dsimp only [H]) <;> field_simp [hs.ne'] <;> ring
  have hHneg (r : ℝ) (hr : 0 < r) : deriv H r < 0 := by
    rw [(hH r hr).deriv]
    apply div_neg_of_neg_of_pos
    · linarith [hgap (Real.sqrt r) (Real.sqrt_pos.mpr hr)]
    · positivity
  have hantiH : StrictAntiOn H (Ioi (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
      (fun r hr => (hH r hr).continuousAt.continuousWithinAt)
    intro r hr
    apply hHneg
    simpa only [interior_Ioi, mem_Ioi] using hr
  change StrictConcaveOn ℝ (Ioi (0 : ℝ)) G
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi (0 : ℝ))
    (fun r hr => (hG r hr).continuousAt.continuousWithinAt)
  intro a ha b hb hab
  have ha0 : 0 < a := by simpa only [interior_Ioi, mem_Ioi] using ha
  have hb0 : 0 < b := by simpa only [interior_Ioi, mem_Ioi] using hb
  rw [(hG b hb0).deriv, (hG a ha0).deriv]
  exact hantiH ha0 hb0 hab

end RhTransient.EvenLogFourthSquareConcavity

#print axioms RhTransient.EvenLogFourthSquareConcavity.squareVariable_strictConcavity_of_fourthJet_neg
/- Uncompiled source fragment. The raw theta series has no absolute value,
   so its zeroth-jet identity holds on the entire real axis. -/

namespace RhTransient.ThetaLogFourthCertificate

open Real
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private fullJet fullJet_deriv fullJet_eq_iterated from
  D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck

theorem actual_phi_has_full_mode_sum (x : ℝ) :
    Summable (fun j : ℕ => primalJet 0 (j+1) x) ∧
    romikPhi x = ∑' j : ℕ, primalJet 0 (j+1) x := by
  have ht : 0 < exp (2*x) := exp_pos _
  have hs := (((thetaSeries_summable 4 ht).mul_left
      (2*Real.pi^2*(exp (2*x))^2)).sub
      ((thetaSeries_summable 2 ht).mul_left (3*Real.pi*exp (2*x)))).mul_left
        (2*exp (x/2))
  have hterm (j : ℕ) :
      2*exp (x/2)*
        (2*Real.pi^2*(exp (2*x))^2*
            (((j:ℝ)+1)^4*exp (-Real.pi*((j:ℝ)+1)^2*exp (2*x)))-
          (3*Real.pi*exp (2*x))*
            (((j:ℝ)+1)^2*exp (-Real.pi*((j:ℝ)+1)^2*exp (2*x)))) =
      primalJet 0 (j+1) x := by
    dsimp [primalJet,jetPolynomial,modeScale]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X]
    push_cast
    ring
  have hsum : Summable (fun j : ℕ => primalJet 0 (j+1) x) := by
    convert hs using 1
    funext j
    exact (hterm j).symm
  refine ⟨hsum,?_⟩
  rw [romikPhi,omega,← tsum_mul_left]
  apply tsum_congr
  intro j
  dsimp [primalJet,jetPolynomial,modeScale]
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  push_cast
  ring

theorem actual_fullJet_zero_eq_phi_all (x : ℝ) : fullJet 0 x = romikPhi x := by
  obtain ⟨hs,hphi⟩ := actual_phi_has_full_mode_sum x
  have hsplit : (∑' j : ℕ, primalJet 0 (j+1) x) = fullJet 0 x := by
    calc
      _ = primalJet 0 (0+1) x+∑' j : ℕ, primalJet 0 ((j+1)+1) x :=
        hs.tsum_eq_zero_add
      _ = _ := by
        dsimp only [fullJet,tailJet]
        congr 1
        apply tsum_congr
        intro j
        congr 1
        omega
  exact (hphi.trans hsplit).symm

theorem actual_fullJet_eq_phi_iterated_all (k : ℕ) (x : ℝ) :
    fullJet k x = iteratedDeriv k romikPhi x := by
  have heq : fullJet 0 = romikPhi := funext actual_fullJet_zero_eq_phi_all
  rw [fullJet_eq_iterated,heq]

theorem actual_fullJet_one_odd (x : ℝ) : fullJet 1 (-x) = -fullJet 1 x := by
  have h0 : (fun t : ℝ => fullJet 0 (-t)) = fullJet 0 := by
    funext t
    rw [actual_fullJet_zero_eq_phi_all,actual_fullJet_zero_eq_phi_all,romikPhi_even]
  have hl := (fullJet_deriv 0 (-x)).comp x (hasDerivAt_neg x)
  change HasDerivAt (fun t : ℝ => fullJet 0 (-t)) _ x at hl
  rw [h0] at hl
  have heq := hl.unique (fullJet_deriv 0 x)
  norm_num at heq ⊢
  linarith

theorem actual_fullJet_two_even (x : ℝ) : fullJet 2 (-x) = fullJet 2 x := by
  have h1 : (fun t : ℝ => fullJet 1 (-t)) = fun t => -fullJet 1 t :=
    funext actual_fullJet_one_odd
  have hl := (fullJet_deriv 1 (-x)).comp x (hasDerivAt_neg x)
  change HasDerivAt (fun t : ℝ => fullJet 1 (-t)) _ x at hl
  rw [h1] at hl
  have heq := hl.unique (fullJet_deriv 1 x).neg
  norm_num at heq ⊢
  linarith

theorem actual_fullJet_three_odd (x : ℝ) : fullJet 3 (-x) = -fullJet 3 x := by
  have h2 : (fun t : ℝ => fullJet 2 (-t)) = fullJet 2 :=
    funext actual_fullJet_two_even
  have hl := (fullJet_deriv 2 (-x)).comp x (hasDerivAt_neg x)
  change HasDerivAt (fun t : ℝ => fullJet 2 (-t)) _ x at hl
  rw [h2] at hl
  have heq := hl.unique (fullJet_deriv 2 x)
  norm_num at heq ⊢
  linarith

theorem actual_fullJet_odd_origin : fullJet 1 0 = 0 ∧ fullJet 3 0 = 0 := by
  have h1 := actual_fullJet_one_odd 0
  have h3 := actual_fullJet_three_odd 0
  norm_num at h1 h3
  exact ⟨by linarith,by linarith⟩

end RhTransient.ThetaLogFourthCertificate
#print axioms RhTransient.ThetaLogFourthCertificate.actual_fullJet_odd_origin
