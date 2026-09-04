/- GID: D5/S3/PrimeGaps/PrimeGap186PhysicalSourceGeometry
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the exact rational source-row geometry underlying the numerical PrimeGaps186 certificate. -/

import Mathlib

/-!
Exact rational source geometry ported from `openai/PrimeGaps186`, source commit
`61340d0b74163003b32756bb16e91d9209a5e330`. This module deliberately stops
before the physical-measure integrals. It therefore carries no numerical-certificate
assumption and no custom axiom.
-/

namespace D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry

/-- Mesh width used by the source geometry. -/
def trialMesh : ℚ := 1 / 100000

/-- Exact rational geometry for one source row. -/
structure PhysicalSourceRowData where
  order : ℕ
  lowerBand : ℚ
  upperBand : ℚ
  activation : ℚ
  outerCore : ℚ
  innerCore : ℚ
  outerThreshold : ℚ
  innerThreshold : ℚ

/-- The fixed rational density parameter `262499 / 1000000`. -/
def physicalSourceRho : ℚ := 262499 / 1000000

/-- The outer radial cutoff, equal to `98304` mesh widths. -/
def physicalSourceOuterRadius : ℚ := 98304 * trialMesh

/-- The inner radial cutoff for the base (`ν = 0`) or enlarged (`ν = 1`) source family. -/
def physicalSourceInnerRadius (ν : Fin 2) : ℚ :=
  if ν = 0 then 2 - 3 / 1000 - physicalSourceOuterRadius else 2510000 / 2624989

/-- The positive radial advance `10⁻⁷ / physicalSourceRho`. -/
def physicalSourceAdvance : ℚ := (1 / 10000000) / physicalSourceRho

/-- Assign source rows to dense-divisibility orders one, two, and three. -/
def physicalSourceOrder (t : ℕ) : ℕ :=
  if t < 12 then 1 else if t < 24 then 2 else 3

/-- Rational intercept and slope of the source-row activation inequality. -/
def physicalSourceAffine (ν : Fin 2) (t : ℕ) : ℚ × ℚ :=
  let σ : ℚ :=
    if ν = 0 then 100001 / 1000000 else 1 / 2 - 40481 / 100000 + 1 / 10000000000
  if physicalSourceOrder t = 1 then ((1 - 5 * σ) / 15, 18 / 5)
  else if physicalSourceOrder t = 2 then ((1 - 4 * σ) / 16, 7 / 2)
  else if ν = 0 then (3 / 80, 3) else ((1 - 2 * σ) / 20, 16 / 5)

/-- Recursively advanced rational source parameter, capped at the family terminal value. -/
def physicalSourceOmegaPrefix (ν : Fin 2) : ℕ → ℚ :=
  Nat.rec 0 (fun t previous =>
    let Ω : ℚ := if ν = 0 then 12499 / 1000000 else 253 / 20000
    let ε : ℚ := if ν = 0 then 1 / 1000000 else 1 / 10000000
    let E : ℚ := physicalSourceRho *
      (physicalSourceOuterRadius + physicalSourceInnerRadius ν) - 1 / 2
    let cs := physicalSourceAffine ν t
    if previous = Ω then Ω else
      min Ω ((cs.1 - ε - E + 2 * previous - 1 / 10000000) / cs.2))

/-- Construct one exact source row from two successive source parameters. -/
def physicalSourceRow (ν : Fin 2) (t : ℕ) : PhysicalSourceRowData :=
  let cs := physicalSourceAffine ν t
  let ε : ℚ := if ν = 0 then 1 / 1000000 else 1 / 10000000
  let B : ℚ := (1 / 2 + 2 * physicalSourceOmegaPrefix ν t) / physicalSourceRho
  let Bplus : ℚ :=
    (1 / 2 + 2 * physicalSourceOmegaPrefix ν (t + 1)) / physicalSourceRho
  let ξ : ℚ :=
    (cs.1 - cs.2 * physicalSourceOmegaPrefix ν (t + 1) - ε) / physicalSourceRho
  let a : ℚ := B - physicalSourceInnerRadius ν
  let b : ℚ := B - physicalSourceOuterRadius
  let η : ℚ := if physicalSourceOrder t ≤ 2 then ξ else
    (ξ + physicalSourceOuterRadius + physicalSourceInnerRadius ν - B) / 2
  { order := physicalSourceOrder t
    lowerBand := B
    upperBand := Bplus
    activation := ξ
    outerCore := a
    innerCore := b
    outerThreshold := a + η
    innerThreshold := b + η }

/-- The first source-index band has dense-divisibility order one. -/
theorem physicalSourceOrder_eq_one {t : ℕ} (ht : t < 12) :
    physicalSourceOrder t = 1 := by
  simp [physicalSourceOrder, ht]

/-- The middle source-index band has dense-divisibility order two. -/
theorem physicalSourceOrder_eq_two {t : ℕ} (h12 : 12 ≤ t) (h24 : t < 24) :
    physicalSourceOrder t = 2 := by
  simp [physicalSourceOrder, Nat.not_lt.mpr h12, h24]

/-- Every source index from twenty-four onward has dense-divisibility order three. -/
theorem physicalSourceOrder_eq_three {t : ℕ} (h24 : 24 ≤ t) :
    physicalSourceOrder t = 3 := by
  have h12 : ¬ t < 12 := by omega
  have h24' : ¬ t < 24 := by omega
  simp [physicalSourceOrder, h12, h24']

/-- Every source row has one of the three declared dense-divisibility orders. -/
theorem physicalSourceOrder_mem (t : ℕ) :
    physicalSourceOrder t = 1 ∨ physicalSourceOrder t = 2 ∨ physicalSourceOrder t = 3 := by
  by_cases h12 : t < 12
  · exact Or.inl (physicalSourceOrder_eq_one h12)
  · by_cases h24 : t < 24
    · exact Or.inr (Or.inl (physicalSourceOrder_eq_two (Nat.le_of_not_gt h12) h24))
    · exact Or.inr (Or.inr (physicalSourceOrder_eq_three (Nat.le_of_not_gt h24)))

/-- The density parameter is strictly positive. -/
theorem physicalSourceRho_pos : 0 < physicalSourceRho := by
  norm_num [physicalSourceRho]

/-- The rational radial advance is strictly positive. -/
theorem physicalSourceAdvance_pos : 0 < physicalSourceAdvance := by
  norm_num [physicalSourceAdvance, physicalSourceRho]

#print axioms PhysicalSourceRowData
#print axioms physicalSourceRho
#print axioms physicalSourceOuterRadius
#print axioms physicalSourceInnerRadius
#print axioms physicalSourceAdvance
#print axioms physicalSourceOrder
#print axioms physicalSourceAffine
#print axioms physicalSourceOmegaPrefix
#print axioms physicalSourceRow
#print axioms physicalSourceOrder_mem
#print axioms physicalSourceAdvance_pos

end D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry
