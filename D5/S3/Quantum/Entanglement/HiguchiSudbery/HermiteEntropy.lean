/- GID: D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: HermiteEntropy for the sharp four-qubit marginal entropy bound. -/

/-
proof_shape: hermite_majorant: content
escape_witness: hermite_majorant (the general fourth-derivative comparison)
admission_basis: escape-witness
Direct frozen dependencies: none
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.HiguchiSudbery.HermiteMajorant

noncomputable section
namespace D5.S3.Quantum.Entanglement.HiguchiSudbery



set_option maxHeartbeats 0
open Real Set

private def c0 : ℝ := (4 - 3 * log 3) / 8

private def c1 : ℝ := (-11 + 2 * log 2 + 12 * log 3) / 2

private def c2 : ℝ := (36 - 39 * log 3) / 2

private def c3 : ℝ := 18 * (log 3 - 1)

def pNat (x : ℝ) : ℝ :=
  (4 - 3 * log 3) / 8 + ((-11 + 2 * log 2 + 12 * log 3) / 2)*x +
    ((36 - 39 * log 3) / 2)*x^2 + (18 * (log 3 - 1))*x^3

private def gap (x : ℝ) : ℝ := pNat x + x * log x

private def gap1 (x : ℝ) : ℝ := c1 + 2*c2*x + 3*c3*x^2 + log x + 1

private def gap2 (x : ℝ) : ℝ := 2*c2 + 6*c3*x + x⁻¹

private def gap3 (x : ℝ) : ℝ := 6*c3 - (x^2)⁻¹

private def gap4 (x : ℝ) : ℝ := 2 / x^3

private lemma gap_derivatives /- proof_shape: bind-only; consumer: HermiteEntropy.hermite_majorant_pos -/ (x : ℝ) (hx : 0 < x) :
    HasDerivAt gap (gap1 x) x ∧ HasDerivAt gap1 (gap2 x) x ∧
    HasDerivAt gap2 (gap3 x) x ∧ HasDerivAt gap3 (gap4 x) x := by
  have hi := hasDerivAt_id x
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! ((((hasDerivAt_const x c0).add (hi.const_mul c1)).add
      ((hi.pow 2).const_mul c2)).add ((hi.pow 3).const_mul c3)).add
      (hasDerivAt_mul_log hx.ne') using 1 <;>
      (try { with_unfolding_all rfl }) <;> (try funext y) <;> (try dsimp [gap, gap1, pNat]) <;> ring
  · convert! ((((hasDerivAt_const x c1).add (hi.const_mul (2*c2))).add
      ((hi.pow 2).const_mul (3*c3))).add (hasDerivAt_log hx.ne')).add_const 1 using 1 <;>
      (try { with_unfolding_all rfl }) <;> (try funext y) <;> (try dsimp [gap1, gap2]) <;> ring
  · convert! ((hasDerivAt_const x (2*c2)).add (hi.const_mul (6*c3))).add
      (hasDerivAt_inv hx.ne') using 1 <;>
      (try { with_unfolding_all rfl }) <;> (try funext y) <;> (try dsimp [gap2, gap3]) <;> ring
  · convert! (hasDerivAt_const x (6*c3)).sub ((hi.pow 2).inv (pow_ne_zero 2 hx.ne')) using 1
    dsimp [gap4]
    field_simp
    ring

private lemma log_sixth /- proof_shape: bind-only; consumer: HermiteEntropy.gap_contacts -/ : log (1/6 : ℝ) = -(log 2 + log 3) := by
  rw [log_div (by norm_num) (by norm_num), log_one]
  rw [show (6 : ℝ) = 2*3 by norm_num, log_mul (by norm_num) (by norm_num)]
  ring

private lemma log_half /- proof_shape: bind-only; consumer: HermiteEntropy.gap_contacts -/ : log (1/2 : ℝ) = -log 2 := by
  rw [log_div (by norm_num) (by norm_num), log_one]; ring

private lemma gap_contacts /- proof_shape: bind-only; consumer: HermiteEntropy.hermite_majorant_pos -/ : gap (1/6) = 0 ∧ gap (1/2) = 0 ∧
    gap1 (1/6) = 0 ∧ gap1 (1/2) = 0 := by
  simp only [gap, gap1, pNat, c0, c1, c2, c3, log_sixth, log_half]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private lemma hermite_majorant_pos /- proof_shape: content; escape_witness: HermiteMajorant.double_contact_nonnegative; consumer: HermiteEntropy.hermite_majorant -/ (x : ℝ) (hx : 0 < x) : negMulLog x ≤ pNat x := by
  have hc := gap_contacts
  have h := double_contact_nonnegative
    (fun y hy => (gap_derivatives y hy).1)
    (fun y hy => (gap_derivatives y hy).2.1)
    (fun y hy => (gap_derivatives y hy).2.2.1)
    (fun y hy => (gap_derivatives y hy).2.2.2)
    (fun y hy => by dsimp [gap4]; positivity)
    (a := (1/6 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 x hx
  dsimp [gap, negMulLog] at *
  linarith

lemma hermite_majorant (x : ℝ) (hx : 0 ≤ x) : negMulLog x ≤ pNat x := by
  refine le_on_closure (s := Ioi (0 : ℝ))
    (fun y hy => hermite_majorant_pos y hy)
    (continuous_negMulLog.continuousOn) ?_ ?_
  · have : Continuous pNat := by unfold pNat; fun_prop
    exact this.continuousOn
  · simpa only [closure_Ioi, mem_Ici] using hx

end D5.S3.Quantum.Entanglement.HiguchiSudbery
