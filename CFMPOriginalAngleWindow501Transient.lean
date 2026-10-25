import CFMPOriginalAngleWindow491Transient
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open CFMPOriginalForward390 (angle angleD)
open private quotient_window cos_small cos_medium from CFMPOriginalAngleWindow491Transient

namespace CFMPOriginalAngleWindow501Transient

def adjacentSlot : Fin 4 → Fin 6 := ![1,2,4,5]

/-- Any one of the four original neighbours may be the medium angle. -/
theorem original_window (x : Fin 6 → ℝ)
    (hx : ∀ q, 1 < x q) (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1)
    (h0 : angle x 0 ≤ Real.pi/5) (j : Fin 4)
    (hsmall : ∀ i : Fin 4, i ≠ j → angle x (adjacentSlot i) ≤ Real.pi/5)
    (hmedium : angle x (adjacentSlot j) ≤ Real.pi/3) :
    x 0 < Real.sqrt ((237620:ℝ)/28431) ∧
      Real.sqrt ((237620:ℝ)/28431) < 3 := by
  let z := Real.cos (angle x 0)
  let p := Real.cos (angle x 1)
  let q := Real.cos (angle x 2)
  let r := Real.cos (angle x 5)
  let t := Real.cos (angle x 4)
  let k := Real.cos (angle x 3)
  have ha (i : Fin 6) : 0 ≤ angle x i := Real.arccos_nonneg _
  have hz : (4:ℝ)/5 < z ∧ z ≤ 1 := cos_small _ (ha 0) h0
  have hsc (i : Fin 4) (hi : i ≠ j) :
      (4:ℝ)/5 < Real.cos (angle x (adjacentSlot i)) ∧
        Real.cos (angle x (adjacentSlot i)) ≤ 1 :=
    cos_small _ (ha _) (hsmall i hi)
  have hmc : (1:ℝ)/2 ≤ Real.cos (angle x (adjacentSlot j)) ∧
      Real.cos (angle x (adjacentSlot j)) ≤ 1 := cos_medium _ (ha _) hmedium
  obtain ⟨_, _, _, _, _, _, hquot⟩ := CFMPOriginalForward390.forward x hx hc
  have hsin : Real.sin (angle x 0)^2 = 1-Real.cos (angle x 0)^2 := by
    nlinarith only [Real.sin_sq_add_cos_sq (angle x 0)]
  rw [hsin] at hquot
  change x 0 = ((1-z^2)*k+p*r+q*t+z*(p*t+q*r)) /
    Real.sqrt (angleD z p q * angleD z t r) at hquot
  have hk : k ≤ 1 := Real.cos_le_one _
  fin_cases j
  · have hP : (4:ℝ)/5 < t ∧ t ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 2 (by decide)
    have hQ : (4:ℝ)/5 < r ∧ r ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 3 (by decide)
    have hR : (4:ℝ)/5 < q ∧ q ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 1 (by decide)
    have hT : (1:ℝ)/2 ≤ p ∧ p ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hmc
    have hquot' : x 0 = ((1-z^2)*k+t*q+r*p+z*(t*p+r*q)) /
        Real.sqrt (angleD z t r * angleD z p q) := by
      rw [hquot]
      congr 1
      · ring
      · congr 1
        dsimp only [angleD]
        ring
    exact quotient_window (x 0) z t r q p k (hx 0) hz hP hQ hR hT hk hquot'
  · have hP : (4:ℝ)/5 < r ∧ r ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 3 (by decide)
    have hQ : (4:ℝ)/5 < t ∧ t ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 2 (by decide)
    have hR : (4:ℝ)/5 < p ∧ p ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 0 (by decide)
    have hT : (1:ℝ)/2 ≤ q ∧ q ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hmc
    have hquot' : x 0 = ((1-z^2)*k+r*p+t*q+z*(r*q+t*p)) /
        Real.sqrt (angleD z r t * angleD z q p) := by
      rw [hquot]
      congr 1
      · ring
      · congr 1
        dsimp only [angleD]
        ring
    exact quotient_window (x 0) z r t p q k (hx 0) hz hP hQ hR hT hk hquot'
  · have hP : (4:ℝ)/5 < p ∧ p ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 0 (by decide)
    have hQ : (4:ℝ)/5 < q ∧ q ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 1 (by decide)
    have hR : (4:ℝ)/5 < r ∧ r ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 3 (by decide)
    have hT : (1:ℝ)/2 ≤ t ∧ t ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hmc
    exact quotient_window (x 0) z p q r t k (hx 0) hz hP hQ hR hT hk hquot
  · have hP : (4:ℝ)/5 < q ∧ q ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 1 (by decide)
    have hQ : (4:ℝ)/5 < p ∧ p ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 0 (by decide)
    have hR : (4:ℝ)/5 < t ∧ t ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hsc 2 (by decide)
    have hT : (1:ℝ)/2 ≤ r ∧ r ≤ 1 := by simpa [adjacentSlot, p, q, r, t] using hmc
    have hquot' : x 0 = ((1-z^2)*k+q*t+p*r+z*(q*r+p*t)) /
        Real.sqrt (angleD z q p * angleD z r t) := by
      rw [hquot]
      congr 1
      · ring
      · congr 1
        dsimp only [angleD]
        ring
    exact quotient_window (x 0) z q p t r k (hx 0) hz hP hQ hR hT hk hquot'

end CFMPOriginalAngleWindow501Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPOriginalAngleWindow501Transient.original_window
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP501 missing declaration {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP501 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP501 CHECKED {name} axioms={axioms}"
