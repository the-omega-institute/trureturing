/- GID: D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineData
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicNine/EnumerationNineData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Twenty-six exact primitive period-nine Tribonacci orbit certificates. -/

import D5.S0.Tower.TribonacciPeriodicEight.EnumerationEight

/- Library-search audit trail (2026-08-18):
   * Repository search found the period-eight certificates and the shared coded
     orbit machinery; no period-nine data exists.
   * The twenty-six words are the primitive rotation classes among the two
     hundred forty phase-marked solutions of the period-nine equations.
   * The enumerator was validated against the frozen period-eight data before
     use: it reproduces exactly one hundred thirty-one phase points and fifteen
     primitive classes, and the fifteen rotation classes it emits coincide with
     the committed ones as sets. -/

namespace D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineData

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration
open D5.S0.Tower.TribonacciPeriodicEight.EnumerationEightData

local notation "makeOrbit" => tribonacciMakeOrbit

abbrev CodedOrbit := TribonacciCodedOrbit

def tribonacciPeriodNineOrbitA : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeRight]

def tribonacciPeriodNineOrbitB : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight]

def tribonacciPeriodNineOrbitC : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight]

def tribonacciPeriodNineOrbitD : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight]

def tribonacciPeriodNineOrbitE : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight]

def tribonacciPeriodNineOrbitF : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight]

def tribonacciPeriodNineOrbitG : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeRight]

def tribonacciPeriodNineOrbitH : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight]

def tribonacciPeriodNineOrbitI : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight]

def tribonacciPeriodNineOrbitJ : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeRight]

def tribonacciPeriodNineOrbitK : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft]

def tribonacciPeriodNineOrbitL : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight]

def tribonacciPeriodNineOrbitM : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight]

def tribonacciPeriodNineOrbitN : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight]

def tribonacciPeriodNineOrbitO : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]

def tribonacciPeriodNineOrbitP : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodNineOrbitQ : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft]

def tribonacciPeriodNineOrbitR : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodNineOrbitS : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodNineOrbitT : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodNineOrbitU : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodNineOrbitV : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight]

def tribonacciPeriodNineOrbitW : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodNineOrbitX : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft]

def tribonacciPeriodNineOrbitY : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft]

def tribonacciPeriodNineOrbitZ : CodedOrbit :=
  makeOrbit .large
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]

/-- The twenty-six primitive period-nine representatives. -/
def tribonacciPeriodNineOrbitRepresentatives : List CodedOrbit :=
  [tribonacciPeriodNineOrbitA, tribonacciPeriodNineOrbitB, tribonacciPeriodNineOrbitC,
   tribonacciPeriodNineOrbitD, tribonacciPeriodNineOrbitE, tribonacciPeriodNineOrbitF,
   tribonacciPeriodNineOrbitG, tribonacciPeriodNineOrbitH, tribonacciPeriodNineOrbitI,
   tribonacciPeriodNineOrbitJ, tribonacciPeriodNineOrbitK, tribonacciPeriodNineOrbitL,
   tribonacciPeriodNineOrbitM, tribonacciPeriodNineOrbitN, tribonacciPeriodNineOrbitO,
   tribonacciPeriodNineOrbitP, tribonacciPeriodNineOrbitQ, tribonacciPeriodNineOrbitR,
   tribonacciPeriodNineOrbitS, tribonacciPeriodNineOrbitT, tribonacciPeriodNineOrbitU,
   tribonacciPeriodNineOrbitV, tribonacciPeriodNineOrbitW, tribonacciPeriodNineOrbitX,
   tribonacciPeriodNineOrbitY, tribonacciPeriodNineOrbitZ]

/-- The enumeration lists exactly twenty-six primitive representatives. -/
theorem tribonacci_period_nine_representative_count :
    tribonacciPeriodNineOrbitRepresentatives.length = 26 := by
  simp only [tribonacciPeriodNineOrbitRepresentatives]
  rfl

end D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineData
