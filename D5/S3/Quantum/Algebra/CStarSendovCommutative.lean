/- GID: D5/S3/Quantum/Algebra/CStarSendovCommutative
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarSendovCommutative
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarSendovCommutative.claimSendovCommutative; result=D5/S3/Quantum/Algebra/CStarSendovCommutative.result; claim=D5/S3/Quantum/Algebra/CStarSendovCommutative.claimSendovCommutative
   digest: Dense invertibles give the commutative C*-algebraic Sendov refutation. -/

/-
proof_shape: HasCStarDeriv: bind-only (consumer: CStarSendovCommutative.claimSendovCommutative, CStarSendovCommutative.cstar_deriv_unique, CStarSendovCommutative.cubic_cstar_deriv_iff, CStarSendovCommutative.result)
proof_shape: claimSendovCommutative: bind-only (consumer: CStarSendovCommutative.result)
proof_shape: polynomial_pair_approximation: bind-only (consumer: CStarSendovCommutative.invertibles_dense)
proof_shape: invertibles_dense: bind-only (consumer: CStarSendovCommutative.cubic_cstar_deriv_iff, CStarSendovCommutative.result)
proof_shape: cstar_deriv_unique: bind-only (consumer: CStarSendovCommutative.cubic_cstar_deriv_iff)
proof_shape: cubic_increment_identity: bind-only (consumer: CStarSendovCommutative.cubic_quotient_identity)
proof_shape: cubic_quotient_identity: bind-only (consumer: CStarSendovCommutative.cubic_has_cstar_deriv)
proof_shape: cubic_has_cstar_deriv: bind-only (consumer: CStarSendovCommutative.cubic_cstar_deriv_iff)
proof_shape: cubic_cstar_deriv_iff: bind-only (consumer: CStarSendovCommutative.result)
proof_shape: result: bind-only (consumer: settling result)
escape_witness: none
admission_basis: open-problem-resolution (#15036; Refuted)
Direct frozen dependencies (constant owners):
  D5/S3/Quantum/Algebra/CStarDualMeanValue.orderedPoly statement_id: sha256:69cfe22356400d6ebac4f53ecc8c9dde80c30ff01e8fb8ed8fbd3ce29ff9e221
  D5/S3/Quantum/Algebra/CStarSchoenberg.orderedDeriv statement_id: sha256:ce1938b197e00c32d6073b1ab7f80e347fafc998daeebfbe011a7ba6ce98cba7
Same-delivery dependency: `CStarSendov`.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Positive means nonnegative; the constructed weights are also invertible.
Only degrees at least two and unital algebras in Type are encoded.
-/

import D5.S3.Quantum.Algebra.CStarSendov
import D5.S3.Quantum.Algebra.CStarDualMeanValue
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Ring.Basic
open scoped BigOperators ComplexOrder
namespace D5.S3.Quantum.Algebra.CStarSendovCommutative
open D5.S3.Quantum.Algebra.CStarSendov
noncomputable section

def HasCStarDeriv {A : Type} [NormedRing A] (f : A → A) (w L : A) : Prop :=
  ∀ e > 0, ∃ d > 0, ∀ z : A, ‖z - w‖ < d → IsUnit (z - w) →
    ‖Ring.inverse (z - w) * (f z - f w) - L‖ < e

def claimSendovCommutative : Prop :=
  ∀ (A : Type) [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
    Dense {x : A | IsUnit x} → ∀ n : ℕ, 2 ≤ n → ∀ a : Fin n → A,
    (∀ j, a j ∈ cstarDisc 0 1) → ∀ b : Fin (n - 1) → A,
    (∀ k, HasCStarDeriv (CStarDualMeanValue.orderedPoly a) (b k) 0) → (∀ k, b k ∈ cstarDisc 0 1) →
    (∀ k, IsConvexForm a (b k)) →
    ∀ j, ∃ z, HasCStarDeriv (CStarDualMeanValue.orderedPoly a) z 0 ∧ z ∈ cstarDisc (a j) 1

end
end D5.S3.Quantum.Algebra.CStarSendovCommutative


set_option backward.isDefEq.respectTransparency false
open Set Topology
open D5.S3.Quantum.Algebra.CStarSendov
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendovCommutative

private theorem polynomial_pair_approximation (f : Alg) (e : ℝ) (he : 0 < e) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 1 g ∧ ∀ t : Interval, ‖g t - f t‖ < e := by
  let fr : C(Interval, ℝ) := ⟨fun t => (f t).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(Interval, ℝ) := ⟨fun t => (f t).im, Complex.continuous_im.comp f.continuous⟩
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 6 fr (e/2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_continuousMap 0 6 fi (e/2) (by positivity)
  let g : ℝ → ℂ := fun t => ((p.eval (t:ℝ) : ℝ) : ℂ) + ((q.eval (t:ℝ) : ℝ) : ℂ) * Complex.I
  have hpD : ContDiff ℝ 1 (fun t : ℝ => p.eval (t:ℝ)) := by simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using p.contDiff_aeval (𝕜 := ℝ) 1
  have hqD : ContDiff ℝ 1 (fun t : ℝ => q.eval (t:ℝ)) := by simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using q.contDiff_aeval (𝕜 := ℝ) 1
  have hg : ContDiff ℝ 1 g :=
    (Complex.ofRealCLM.contDiff.comp hpD).add ((Complex.ofRealCLM.contDiff.comp hqD).mul (contDiff_const (c := Complex.I)))
  refine ⟨g, hg, ?_⟩
  intro t
  have hp' := ((p.toContinuousMapOn (Icc 0 6) - fr).norm_lt_iff (by positivity : 0 < e/2)).mp hp t
  have hq' := ((q.toContinuousMapOn (Icc 0 6) - fi).norm_lt_iff (by positivity : 0 < e/2)).mp hq t
  change ‖p.eval (t:ℝ) - (f t).re‖ < e/2 at hp'
  change ‖q.eval (t:ℝ) - (f t).im‖ < e/2 at hq'
  have hd : g t - f t = ((p.eval (t:ℝ) - (f t).re : ℝ) : ℂ) +
      ((q.eval (t:ℝ) - (f t).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [g, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hd]
  calc
    ‖((p.eval (t:ℝ) - (f t).re : ℝ) : ℂ) + ((q.eval (t:ℝ) - (f t).im : ℝ) : ℂ) * Complex.I‖ ≤
        ‖((p.eval (t:ℝ) - (f t).re : ℝ) : ℂ)‖ + ‖((q.eval (t:ℝ) - (f t).im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖p.eval (t:ℝ) - (f t).re‖ + ‖q.eval (t:ℝ) - (f t).im‖ := by rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one]
    _ < e := by linarith

private theorem invertibles_dense : Dense {x : Alg | IsUnit x} := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro e he
  obtain ⟨g, hg, happ⟩ := polynomial_pair_approximation f (e/2) (by positivity)
  have hd : Dense (range g)ᶜ := hg.dense_compl_range_of_finrank_lt_finrank (by
    norm_num [Complex.finrank_real_complex])
  obtain ⟨w, hw, hwball⟩ := hd.exists_mem_open (U := Metric.ball (0:ℂ) (e/2)) (Metric.isOpen_ball) (Metric.nonempty_ball.mpr (by positivity : 0 < e/2))
  let u : Alg := ⟨fun t => g t - w, (hg.continuous.comp continuous_subtype_val).sub continuous_const⟩
  refine ⟨u, (ContinuousMap.isUnit_iff_forall_ne_zero u).mpr ?_, ?_⟩
  · intro t ht
    apply hw
    exact ⟨(t:ℝ), sub_eq_zero.mp ht⟩
  · rw [dist_eq_norm]
    rw [norm_sub_rev]
    apply (u - f).norm_lt_iff he |>.mpr
    intro t
    have hn : ‖w‖ < e/2 := by simpa [Metric.mem_ball, dist_zero_right] using hwball
    have hu : (u-f) t = (g t - f t) - w := by dsimp [u]; ring
    rw [hu]
    exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith [happ t])

end D5.S3.Quantum.Algebra.CStarSendovCommutative


open Set Topology
open D5.S3.Quantum.Algebra.CStarSendovCommutative
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendovCommutative

 private theorem cstar_deriv_unique {A : Type} [NormedRing A]
    (hd : Dense {x : A | IsUnit x}) {f : A → A} {w L M : A}
    (hL : HasCStarDeriv f w L) (hM : HasCStarDeriv f w M) : L = M := by
  by_contra hneq
  have hn : 0 < ‖L-M‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  obtain ⟨d1, hd1, h1⟩ := hL (‖L-M‖/3) (by positivity)
  obtain ⟨d2, hd2, h2⟩ := hM (‖L-M‖/3) (by positivity)
  obtain ⟨h, hunit, hsmall⟩ := hd.exists_mem_open (U := Metric.ball 0 (min d1 d2))
    Metric.isOpen_ball (Metric.nonempty_ball.mpr (lt_min hd1 hd2))
  have hh : ‖h‖ < min d1 d2 := by simpa [Metric.mem_ball, dist_zero_right] using hsmall
  have h1' := h1 (w+h) (by simpa using lt_of_lt_of_le hh (min_le_left _ _)) (by simpa using hunit)
  have h2' := h2 (w+h) (by simpa using lt_of_lt_of_le hh (min_le_right _ _)) (by simpa using hunit)
  let Q := Ring.inverse ((w+h)-w) * (f (w+h) - f w)
  have ht := dist_triangle L Q M
  simp only [dist_eq_norm] at ht
  have hn1 : ‖L-Q‖ < ‖L-M‖/3 := by rw [norm_sub_rev]; exact h1'
  have hn2 : ‖Q-M‖ < ‖L-M‖/3 := h2'
  linarith

end D5.S3.Quantum.Algebra.CStarSendovCommutative


open scoped BigOperators
open D5.S3.Quantum.Algebra.CStarSendov D5.S3.Quantum.Algebra
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendovCommutative

 private theorem cubic_increment_identity (z h : Alg) :
    CStarDualMeanValue.orderedPoly a (z+h) - CStarDualMeanValue.orderedPoly a z = h *
      (CStarSchoenberg.orderedDeriv a z + h*(3*z-c) + h^2) := by
  ext t
  rw [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    ContinuousMap.add_apply, ordered_deriv_apply]
  have hn : (3:Alg) t = (3:ℂ) := rfl
  norm_num [CStarDualMeanValue.orderedPoly, a, List.ofFn_succ, hn]
  ring

 private theorem cubic_quotient_identity (z h : Alg) (hh : IsUnit h) :
    Ring.inverse h * (CStarDualMeanValue.orderedPoly a (z+h) - CStarDualMeanValue.orderedPoly a z) - CStarSchoenberg.orderedDeriv a z =
      h*(3*z-c) + h^2 := by
  rw [cubic_increment_identity, Ring.inverse_mul_cancel_left h _ hh]
  abel

 private theorem cubic_has_cstar_deriv (z : Alg) :
    HasCStarDeriv (CStarDualMeanValue.orderedPoly a) z (CStarSchoenberg.orderedDeriv a z) := by
  have hc : Continuous (fun h : Alg => h*(3*z-c) + h^2) := by fun_prop
  have hc0 := hc.continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc0
  intro e he
  obtain ⟨d, hd, hbound⟩ := hc0 e he
  refine ⟨d, hd, ?_⟩
  intro w hw hu
  have hb := hbound (by simpa [dist_eq_norm] using hw : dist (w-z) 0 < d)
  rw [dist_eq_norm] at hb
  have hquot := cubic_quotient_identity z (w-z) hu
  rw [add_sub_cancel] at hquot
  rw [hquot]
  simpa using hb

end D5.S3.Quantum.Algebra.CStarSendovCommutative


open D5.S3.Quantum.Algebra.CStarSendov D5.S3.Quantum.Algebra
noncomputable section
namespace D5.S3.Quantum.Algebra.CStarSendovCommutative

 private theorem cubic_cstar_deriv_iff (z L : Alg) :
    HasCStarDeriv (CStarDualMeanValue.orderedPoly a) z L ↔ L = CStarSchoenberg.orderedDeriv a z := by
  constructor
  · intro h
    exact cstar_deriv_unique invertibles_dense h (cubic_has_cstar_deriv z)
  · rintro rfl
    exact cubic_has_cstar_deriv z

end D5.S3.Quantum.Algebra.CStarSendovCommutative

namespace D5.S3.Quantum.Algebra.CStarSendovCommutative
open D5.S3.Quantum.Algebra.CStarSendov D5.S3.Quantum.Algebra
noncomputable section

theorem result : ¬ claimSendovCommutative := by
  intro h
  have hc : ∀ k, CStarSchoenberg.orderedDeriv a (bs k) = 0 := by
    intro k
    fin_cases k <;> simp only [bs, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact critical_both.1
    · exact critical_both.2
  have hderiv : ∀ k, HasCStarDeriv (CStarDualMeanValue.orderedPoly a) (bs k) 0 := by
    intro k
    apply (cubic_cstar_deriv_iff (bs k) 0).mpr
    exact (hc k).symm
  have hd : ∀ k, bs k ∈ cstarDisc 0 1 := by
    intro k
    fin_cases k <;> simp only [bs, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact critical_in_disc.1
    · exact critical_in_disc.2
  have hf : ∀ k, IsConvexForm a (bs k) := fun k => critical_convex_form (bs k) (hc k)
  obtain ⟨z, hz, hdisc⟩ := h Alg invertibles_dense 3 (by norm_num) a roots_in_disc bs hderiv hd hf 0
  have hz' : CStarSchoenberg.orderedDeriv a z = 0 := ((cubic_cstar_deriv_iff z 0).mp hz).symm
  exact no_critical_in_half_disc z hz' (by simpa [a] using hdisc)

#print axioms result
#check result
end
end D5.S3.Quantum.Algebra.CStarSendovCommutative
