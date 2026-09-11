/- GID: D5/S3/Observer/BlockStructure/HiddenFieldResponse
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/HiddenFieldResponse
   mirror-E: none(waiver:symbolic-algebra-no-numerical-evidence)
   anchors: []
   utility: none
   digest: Nonresonant hidden-field elimination and leading-order propagation coefficients. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The frequency-domain hidden Euler-Lagrange equation is an explicit hypothesis;
the exact response retains both frequency and squared-wave-number dependence.
No variational calculus or Fourier transform is formalized here. The source's
stability assumptions are not needed for this scalar elimination identity.

The physical model assumes positive gaps and a positive zero-momentum restoring
matrix. Its leading-order coefficients apply in the low-frequency window
`abs (ch ^ 2 * kSq - omega ^ 2) < Oh ^ 2`, with `kSq` interpreted as a squared norm.
The coefficient definitions below are total real expressions; their algebraic
identities at `Oh = 0` do not extend the physical low-frequency interpretation.
No remainder estimate or limiting PDE assertion is proved here.

The source does not treat the hidden resonance `hiddenDen = 0` in this elimination;
`hH` therefore remains explicit. No value assigned by totalized division is used
as a response at resonance.

Changing the model parameters can change the effective propagation coefficient;
no universal propagation constant follows. The leading-order characteristic speed
is not identified with the full model's signal-front speed. `lam` is only a field
coupling, with no identification with a resource price. This quadratic classical
field calculation supplies no Born rule, quantum state, or thermal distribution.

Preregistered companion uses (consumer -> prerequisite):
* effective_speed_parameter_comparison -> c_eff_sq_sub_bare, c_eff_sq_bounds;
* leading_order_characteristic_readout -> principal_symbol_eq_zero_iff.
These are named uses of the derived model, not additional proof-dependency claims.
All three results are bind-only companions; only the exact elimination is content
under the implementation brief's supplied classification.
-/

noncomputable section

namespace D5.S3.Observer.BlockStructure.HiddenFieldResponse

/-- The full frequency-dependent hidden coefficient. -/
def hiddenDen (Oh ch kSq omega : ℝ) : ℝ := Oh ^ 2 + ch ^ 2 * kSq - omega ^ 2

/-- Solve the second frequency-domain field equation away from hidden resonance. -/
theorem hidden_field_solve_eq
    {Oh ch kSq omega lam q r : ℝ}
    (hH : hiddenDen Oh ch kSq omega ≠ 0)
    (hr : lam * q + hiddenDen Oh ch kSq omega * r = 0) :
    r = -(lam / hiddenDen Oh ch kSq omega) * q := by
  calc
    r = -(lam * q) / hiddenDen Oh ch kSq omega :=
      (eq_div_iff hH).2 (by nlinarith only [hr])
    _ = -(lam / hiddenDen Oh ch kSq omega) * q := by ring

/-- Substitution of the solved hidden field identifies the exact inverse response
as the coefficient of the visible amplitude, without dividing by that amplitude. -/
theorem hidden_field_schur_response
    {O0 Oh c0 ch kSq omega lam q r : ℝ}
    (hH : hiddenDen Oh ch kSq omega ≠ 0)
    (hr : lam * q + hiddenDen Oh ch kSq omega * r = 0) :
    (O0 ^ 2 + c0 ^ 2 * kSq - omega ^ 2) * q + lam * r =
      (O0 ^ 2 + c0 ^ 2 * kSq - omega ^ 2 -
        lam ^ 2 / hiddenDen Oh ch kSq omega) * q := by
  rw [hidden_field_solve_eq hH hr]
  ring

/-- The dimensionless leading-order inertia correction. -/
def inertiaCorrection (lam Oh : ℝ) : ℝ := lam ^ 2 / Oh ^ 4

/-- The leading-order kinetic coefficient. -/
def kineticCoeff (lam Oh : ℝ) : ℝ := 1 + inertiaCorrection lam Oh

/-- The squared leading-order characteristic speed. -/
def cEffSq (c0 ch lam Oh : ℝ) : ℝ :=
  (c0 ^ 2 + inertiaCorrection lam Oh * ch ^ 2) / kineticCoeff lam Oh

/-- The normalized massless principal symbol of the leading-order model. -/
def principalSymbol (c0 ch lam Oh kSq omega : ℝ) : ℝ :=
  -omega ^ 2 + cEffSq c0 ch lam Oh * kSq

private lemma inertiaCorrection_nonneg (lam Oh : ℝ) : 0 ≤ inertiaCorrection lam Oh := by
  apply div_nonneg (sq_nonneg lam)
  have hpow : Oh ^ 4 = (Oh ^ 2) ^ 2 := by ring
  rw [hpow]
  exact sq_nonneg _

private lemma kineticCoeff_pos (lam Oh : ℝ) : 0 < kineticCoeff lam Oh :=
  add_pos_of_pos_of_nonneg zero_lt_one (inertiaCorrection_nonneg lam Oh)

/-- Bind-only companion for effective_speed_parameter_comparison: the shift is
a nonnegative mixing weight times the hidden-versus-visible squared-speed difference. -/
theorem c_eff_sq_sub_bare (c0 ch lam Oh : ℝ) :
    cEffSq c0 ch lam Oh - c0 ^ 2 =
      inertiaCorrection lam Oh / kineticCoeff lam Oh * (ch ^ 2 - c0 ^ 2) := by
  have hZ := ne_of_gt (kineticCoeff_pos lam Oh)
  unfold cEffSq
  field_simp [hZ]
  unfold kineticCoeff
  ring

/-- Bind-only companion for effective_speed_parameter_comparison: the coefficient
is between the two squared bare speeds. -/
theorem c_eff_sq_bounds (c0 ch lam Oh : ℝ) :
    min (c0 ^ 2) (ch ^ 2) ≤ cEffSq c0 ch lam Oh ∧
      cEffSq c0 ch lam Oh ≤ max (c0 ^ 2) (ch ^ 2) := by
  have hZ := kineticCoeff_pos lam Oh
  have ha := inertiaCorrection_nonneg lam Oh
  unfold cEffSq
  constructor
  · apply (le_div_iff₀ hZ).2
    have h := mul_le_mul_of_nonneg_left (min_le_right (c0 ^ 2) (ch ^ 2)) ha
    dsimp only [kineticCoeff]
    nlinarith only [h, min_le_left (c0 ^ 2) (ch ^ 2)]
  · apply (div_le_iff₀ hZ).2
    have h := mul_le_mul_of_nonneg_left (le_max_right (c0 ^ 2) (ch ^ 2)) ha
    dsimp only [kineticCoeff]
    nlinarith only [h, le_max_left (c0 ^ 2) (ch ^ 2)]

/-- Bind-only companion for leading_order_characteristic_readout: the zero set
of the normalized massless principal symbol is its dispersion relation. -/
theorem principal_symbol_eq_zero_iff (c0 ch lam Oh kSq omega : ℝ) :
    principalSymbol c0 ch lam Oh kSq omega = 0 ↔
      omega ^ 2 = cEffSq c0 ch lam Oh * kSq := by
  unfold principalSymbol
  constructor <;> intro h <;> linarith only [h]

#print axioms hidden_field_solve_eq
#print axioms hidden_field_schur_response
#print axioms c_eff_sq_sub_bare
#print axioms c_eff_sq_bounds
#print axioms principal_symbol_eq_zero_iff

end D5.S3.Observer.BlockStructure.HiddenFieldResponse
