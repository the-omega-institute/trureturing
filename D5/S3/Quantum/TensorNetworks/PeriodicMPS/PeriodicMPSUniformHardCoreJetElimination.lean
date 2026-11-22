/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreQuarticSign]
   utility: none
   digest: Eliminating the regular coefficients factors the coherence equation and gives the residual fourth-order difference at its second root. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreQuarticSign
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Elimination in the normalized hard-core observation jet

The raw entries in this calculation are divided by G before forming the
normalized observation. Thus f is F/G and the constant mass is f + 2.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreJetElimination

noncomputable section

/-- Taylor coefficients of the parity-preserving paths in the certificate.
The first imaginary coefficients are (t, (3-2f)t, 1, 0). -/
structure Path where
  t : ℝ
  a₂ : ℝ := 0
  b₂ : ℝ := 0
  c₂ : ℝ := 0
  d₂ : ℝ := 0
  b₃ : ℝ := 0
  c₃ : ℝ := 0
  d₃ : ℝ := 0
  a₄ : ℝ := 0
  b₄ : ℝ := 0
  c₄ : ℝ := 0
  d₄ : ℝ := 0

def original : Path := { t := 1 }

def mass₂ (n f : ℝ) (x : Path) : ℝ :=
  n * (1 + 2 * (f - 2) * x.t + (4*f^2 - 9*f + 4) * x.t^2 +
    2 * (f - 1) * x.a₂ + 2 * x.b₂)

def p₂ (n f : ℝ) (x : Path) : ℝ :=
  (-(f*n - 6*f - 3*n + 10) + 2*(4*f*n - 4*f - 7*n + 5)*x.t -
    (4*f^3*n - 4*f^3 - 24*f^2*n + 12*f^2 + 34*f*n + 12*f - 9*n - 35)*x.t^2 +
    2*(3*f*n - 3*f - 4*n + 5)*x.a₂ - 2*(f*n - f - 3*n)*x.b₂) / 5

def q₂ (n f : ℝ) (x : Path) : ℝ :=
  ((3*f*n + 12*f - 4*n - 20) + 2*(10*f^2 - 7*f*n + 12*f + 11*n - 45)*x.t +
    (12*f^3*n - 12*f^3 - 52*f^2*n + 56*f^2 + 57*f*n + 21*f - 7*n - 130)*x.t^2 -
    2*(4*f*n - 19*f - 7*n + 30)*x.a₂ + 2*(3*f*n - 3*f - 4*n + 5)*x.b₂) / 5 +
    (4 - 2*f)*(x.c₂ + x.d₂)

def h₂ (n f : ℝ) (x : Path) : ℝ :=
  (-(f*n - f - 3*n + 5) + (8*f*n - 23*f - 14*n + 40)*x.t -
    (4*f^3*n - 4*f^3 - 24*f^2*n + 12*f^2 + 34*f*n + 17*f - 9*n - 40)*x.t^2 +
    (6*f*n - 16*f - 8*n + 25)*x.a₂ - (2*f*n - 2*f - 6*n + 5)*x.b₂) / 5 +
    (f - 1)*(x.c₂ + x.d₂)

def w₂ (f : ℝ) (x : Path) : ℝ :=
  3 - 2*f + (-2*f^2 + 3*f + 1)*x.t + (3-f)*x.c₂ + (f-1)*x.d₂

def v₂ (f : ℝ) (x : Path) : ℝ :=
  (2-f)*(1+x.t) + x.c₂ + (f-1)*x.d₂

def w₃ (n f : ℝ) (x : Path) : ℝ :=
  -f*n + 2*n - 1 + 2*(3*f-5)*(n-4)*x.t +
    (-4*f^3*n + 8*f^3 + 20*f^2*n - 28*f^2 - 25*f*n + 3*f + 5*n + 34)*x.t^2 +
    2*(2*f*n - 7*f - 3*n + 11)*x.a₂ + (-2*f*n + 3*f + 4*n - 5)*x.b₂ +
    ((2*f^2 - 3*f - 1)*x.t + 4*f - 6)*x.c₂ +
    ((-2*f^2 + 2*f + 2)*x.t + 2*f - 2)*x.d₂ + (3-f)*x.c₃ + (f-1)*x.d₃

def j₄ (n f : ℝ) (x : Path) : ℝ :=
  -(f-2)*(n-2) + 2*(3*f-5)*(n-2)*x.t +
    (-4*f^3*n + 4*f^3 + 20*f^2*n - 16*f^2 - 25*f*n + 5*f + 5*n + 17)*x.t^2 +
    2*(2*f-3)*(n-2)*x.a₂ - 2*(f*n - f - 2*n + 1)*x.b₂ +
    (3-f)*x.c₂^2 + 2*(f-1)*x.c₂*x.d₂ + (f-1)*x.d₂^2 +
    ((10-6*f)*x.t + 8 - 4*f)*x.d₂ + 2*(3-f)*x.c₃ + 2*(f-1)*x.d₃

def foldA (f : ℝ) : ℝ := 4*f^2 - 5*f - 3
def foldB (f : ℝ) : ℝ := 8*f^2 - 15*f + 3
def deltaRatio (f : ℝ) : ℝ := f^2 - f - 1
def determinantFactor (n f : ℝ) : ℝ := 2*n*f*deltaRatio f + (f+2)*(5-2*f^2)
def quarticP (n f : ℝ) : ℝ :=
  5*((2*n+20)*f - (3*n+34)) + deltaRatio f*((12*n-32)*f - (21*n-10))

def quadraticFactor (f : ℝ) : ℝ := 2*f^2 - 4*f + 1

/-- The quotients have common denominator (f+2)^2 in the p, q and h rows,
and f+2 in the other two real regular rows. -/
def pDiff (n f : ℝ) (x : Path) : ℝ :=
  (f+2)*(p₂ n f x - p₂ n f original) - (mass₂ n f x - mass₂ n f original)

def qDiff (n f : ℝ) (x : Path) : ℝ :=
  (f+2)*(q₂ n f x - q₂ n f original) - (f-1)*(mass₂ n f x - mass₂ n f original)

def hDiff (n f : ℝ) (x : Path) : ℝ :=
  (f+2)*(h₂ n f x - h₂ n f original) - (mass₂ n f x - mass₂ n f original)

def wDiff₃ (n f : ℝ) (x : Path) : ℝ :=
  (f+2)*(w₃ n f x - w₃ n f original) - (3-f)*(mass₂ n f x - mass₂ n f original)

def jDiff₄ (n f : ℝ) (x : Path) : ℝ :=
  (f+2)*(j₄ n f x - j₄ n f original) - (3-f)*(mass₂ n f x - mass₂ n f original)

structure RealRegularEqual (n f : ℝ) (x : Path) : Prop where
  p : pDiff n f x = 0
  q : qDiff n f x = 0
  w : w₂ f x = w₂ f original
  v : v₂ f x = v₂ f original

private theorem fold_identity (n f : ℝ) (x : Path) :
    (f-1)*(2*hDiff n f x + pDiff n f x + qDiff n f x -
      (f+2)*(x.t-1)*(foldA f*x.t+foldB f)) =
    2*(f+2)*(2*(v₂ f x - v₂ f original) - (w₂ f x - w₂ f original)) := by
  unfold hDiff pDiff qDiff mass₂ p₂ q₂ h₂ w₂ v₂ foldA foldB original
  ring

/-- The real coherence difference after the four real regular outputs are matched. -/
theorem fold_difference {n f : ℝ} {x : Path} (hf : f ≠ 1)
    (h : RealRegularEqual n f x) :
    2 * hDiff n f x = (f+2)*(x.t-1)*(foldA f*x.t+foldB f) := by
  have hid := fold_identity n f x
  rw [h.p, h.q, h.w, h.v] at hid
  simp only [add_zero, sub_self, mul_zero] at hid
  exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left (sub_ne_zero.mpr hf))

theorem fold_slopes {n f : ℝ} {x : Path} (hf : f ≠ 1) (hz : f+2 ≠ 0)
    (ha : foldA f ≠ 0) (h : RealRegularEqual n f x) (hh : hDiff n f x = 0) :
    x.t = 1 ∨ x.t = -foldB f / foldA f := by
  have he := fold_difference hf h
  rw [hh, mul_zero, mul_assoc] at he
  obtain ht | hr := mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hz)
  · exact Or.inl (sub_eq_zero.mp ht)
  · right
    apply (eq_div_iff ha).mpr
    linear_combination hr

private theorem forbidden_real_coefficients {f : ℝ} {x : Path} (hf : f ≠ 2) (h₁ : f ≠ 1)
    (hw : w₂ f x = w₂ f original) (hv : v₂ f x = v₂ f original) :
    x.c₂ = -((x.t-1)/(f-2))*quadraticFactor f ∧
    x.d₂ = ((x.t-1)/(f-2))*(3*f-5) := by
  unfold w₂ original at hw
  unfold v₂ original at hv
  have hc : (f-2)*x.c₂ = -(x.t-1)*quadraticFactor f := by
    unfold quadraticFactor
    linear_combination hv - hw
  have hd : (f-1)*((f-2)*x.d₂ - (x.t-1)*(3*f-5)) = 0 := by
    linear_combination hw - (3-f)*hv
  constructor
  · field_simp [sub_ne_zero.mpr hf]
    linear_combination hc
  · field_simp [sub_ne_zero.mpr hf]
    have := sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr h₁))
    linear_combination this

private def pMultiplier (n f : ℝ) : ℝ :=
  2*f^3*n + 8*f^3 + f^2*n - 22*f^2 - 5*f*n - 36*f - 3*n + 80

private def qMultiplier (n f : ℝ) : ℝ :=
  4*f^3*n - 4*f^3 - 3*f^2*n - 14*f^2 - 5*f*n + 8*f - n + 40

private def residualLinear (n f : ℝ) : ℝ :=
  4*f^5*n + 16*f^5 - 7*f^4*n - 70*f^4 - 4*f^3*n - 16*f^3 +
    302*f^2 + 9*f*n - 198*f + 6*n - 100

private def residualConstant (n f : ℝ) : ℝ :=
  -4*f^5*n + 64*f^5 + 35*f^4*n - 258*f^4 - 74*f^3*n + 20*f^3 +
    26*f^2*n + 974*f^2 + 37*f*n - 1110*f - 10*n + 220

set_option maxHeartbeats 1500000 in
private theorem residual_identity (n f r : ℝ) (x : Path)
    (ht : x.t = 1 + (f-2)*r)
    (hc : x.c₂ = -r*quadraticFactor f) (hd : x.d₂ = r*(3*f-5)) :
    determinantFactor n f * (jDiff₄ n f x - 2*wDiff₃ n f x) -
        pMultiplier n f * pDiff n f x - qMultiplier n f * qDiff n f x =
      (f+2)*r*(residualLinear n f*x.t + residualConstant n f) := by
  unfold determinantFactor deltaRatio jDiff₄ wDiff₃ pMultiplier qMultiplier
    pDiff qDiff j₄ w₃ mass₂ p₂ q₂ original residualLinear residualConstant
  rw [ht, hc, hd]
  unfold quadraticFactor
  ring

private theorem residual_at_root (n f t : ℝ) (ht : foldA f*t + foldB f = 0) :
    foldA f*(residualLinear n f*t + residualConstant n f) =
      -2*deltaRatio f*quadraticFactor f*quarticP n f := by
  linear_combination (norm := skip) residualLinear n f * ht
  unfold foldA foldB residualLinear residualConstant quarticP deltaRatio quadraticFactor
  ring

def quarticRatio (n f : ℝ) : ℝ :=
  8*f*(3*f-5)*deltaRatio f*quadraticFactor f*quarticP n f /
    ((f-2)*(f+2)*(foldA f)^2*determinantFactor n f)

/-- Equation (27) after normalization. A cubic change of parameter of size
σ contributes σ * (3-f)/(f+2) in the imaginary w row and twice this
in the forbidden diagonal. The equation includes this freedom. -/
theorem quartic_difference {n f σ : ℝ} {x : Path}
    (h₁ : f ≠ 1) (hf : f ≠ 2) (hz : f+2 ≠ 0) (ha : foldA f ≠ 0)
    (hd : determinantFactor n f ≠ 0)
    (h : RealRegularEqual n f x) (ht : x.t = -foldB f / foldA f)
    (hw : wDiff₃ n f x = σ * (f+2) * (3-f)) :
    (jDiff₄ n f x - 2*σ*(f+2)*(3-f))/(f+2)^2 = quarticRatio n f := by
  have h₂ := sub_ne_zero.mpr hf
  obtain ⟨hc, hd₂⟩ := forbidden_real_coefficients hf h₁ h.w h.v
  have ht' : x.t = 1 + (f-2)*((x.t-1)/(f-2)) := by
    field_simp
    ring
  have hres := residual_identity n f _ x ht' hc hd₂
  rw [h.p, h.q, hw, mul_zero, mul_zero, sub_zero, sub_zero] at hres
  have hroot : foldA f*x.t + foldB f = 0 := by rw [ht]; field_simp; ring
  have hresRoot := residual_at_root n f x.t hroot
  have hprod : x.t-1 = -(4*f*(3*f-5))/foldA f := by
    rw [ht]
    field_simp
    unfold foldB foldA
    ring
  have hresDiv := (eq_div_iff ha).mpr (by
    simpa only [mul_comm] using hresRoot :
    (residualLinear n f*x.t + residualConstant n f) * foldA f =
      -2*deltaRatio f*quadraticFactor f*quarticP n f)
  rw [hprod, hresDiv] at hres
  unfold quarticRatio
  field_simp at hres ⊢
  linear_combination hres

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreJetElimination
