/- GID: D5/S1/Phase/PythagoreanInputValidator
   generality: G
   mirror-B: D5/B/S1/Phase/PythagoreanInputValidator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A decidable pin gate accepts one genuine input and rejects its beta perturbation. -/

import D5.S1.Phase.SeatTowerArithmetic

namespace D5.S1.Phase.PythagoreanInputValidator

/-- The three integer coordinates consumed by the Pythagorean input gate. -/
structure PinInput where
  beta : ℤ
  gamma0 : ℤ
  m : ℤ

namespace PinInput

/-- The scaled Pythagorean equation required of a pin input. -/
def valid (x : PinInput) : Prop :=
  (x.gamma0 - 2 * x.beta) ^ 2 + 3 * x.gamma0 ^ 2 = 4 * x.m * (x.m + 1)

instance (x : PinInput) : Decidable x.valid := by
  unfold valid
  infer_instance

/-- The executable Boolean decision procedure for the input gate. -/
def accepts (x : PinInput) : Bool := decide x.valid

end PinInput

/-- Boolean acceptance is equivalent to the normalized Eisenstein equation. -/
theorem accepts_iff (x : PinInput) :
    x.accepts = true ↔
      x.beta ^ 2 - x.beta * x.gamma0 + x.gamma0 ^ 2 = x.m * (x.m + 1) :=
  (Bool.decide_iff x.valid).trans
    (SeatTowerArithmetic.pythagorean_gate_iff_eisenstein_norm x.beta x.gamma0 x.m)

/-- The attested input is accepted, while perturbing only beta by one is rejected. -/
theorem genuine_and_perturbed_input_certificate :
    PinInput.accepts { beta := -384, gamma0 := 138, m := 468 } = true ∧
      PinInput.accepts { beta := -383, gamma0 := 138, m := 468 } = false := by
  constructor
  · rw [accepts_iff]
    norm_num
  · rw [PinInput.accepts, Bool.decide_false_iff]
    norm_num [PinInput.valid]

end D5.S1.Phase.PythagoreanInputValidator
