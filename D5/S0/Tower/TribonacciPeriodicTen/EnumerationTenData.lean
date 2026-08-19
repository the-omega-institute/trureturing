/- GID: D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenData
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicTen/EnumerationTenData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Forty-two exact primitive period-ten Tribonacci orbit certificates. -/

import D5.S0.Tower.TribonacciPeriodicNine.EnumerationNineMaximinB

/- Library-search audit trail (2026-08-18):
   * The enumerator was calibrated against both committed levels before use, and
     against their rotation classes as sets rather than against their counts: it
     reproduces the fifteen period-eight classes and the twenty-six period-nine
     classes exactly.
   * Names are numeric here rather than alphabetic because forty-two exceeds the
     twenty-six letters the shorter levels used. -/

namespace D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration

local notation "makeOrbit" => tribonacciMakeOrbit

abbrev CodedOrbit := TribonacciCodedOrbit

def tribonacciPeriodTenOrbit01 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeRight]

def tribonacciPeriodTenOrbit02 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit03 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight]

def tribonacciPeriodTenOrbit04 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight]

def tribonacciPeriodTenOrbit05 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit06 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight]

def tribonacciPeriodTenOrbit07 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeLeft, .largeRight]

def tribonacciPeriodTenOrbit08 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit09 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight]

def tribonacciPeriodTenOrbit10 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeLeft, .largeRight]

def tribonacciPeriodTenOrbit11 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft]

def tribonacciPeriodTenOrbit12 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit13 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight]

def tribonacciPeriodTenOrbit14 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight]

def tribonacciPeriodTenOrbit15 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit16 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodTenOrbit17 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeLeft, .largeRight]

def tribonacciPeriodTenOrbit18 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit19 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft]

def tribonacciPeriodTenOrbit20 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight]

def tribonacciPeriodTenOrbit21 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight]

def tribonacciPeriodTenOrbit22 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit23 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodTenOrbit24 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedRight]

def tribonacciPeriodTenOrbit25 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight]

def tribonacciPeriodTenOrbit26 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodTenOrbit27 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodTenOrbit28 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodTenOrbit29 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodTenOrbit30 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft]

def tribonacciPeriodTenOrbit31 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodTenOrbit32 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodTenOrbit33 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight]

def tribonacciPeriodTenOrbit34 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodTenOrbit35 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft]

def tribonacciPeriodTenOrbit36 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]

def tribonacciPeriodTenOrbit37 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough,
      .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodTenOrbit38 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodTenOrbit39 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft]

def tribonacciPeriodTenOrbit40 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft]

def tribonacciPeriodTenOrbit41 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft]

def tribonacciPeriodTenOrbit42 : CodedOrbit :=
  makeOrbit .large
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft]

/-- The forty-two primitive period-ten representatives. -/
def tribonacciPeriodTenOrbitRepresentatives : List CodedOrbit :=
  [tribonacciPeriodTenOrbit01, tribonacciPeriodTenOrbit02, tribonacciPeriodTenOrbit03,
    tribonacciPeriodTenOrbit04, tribonacciPeriodTenOrbit05, tribonacciPeriodTenOrbit06,
    tribonacciPeriodTenOrbit07, tribonacciPeriodTenOrbit08, tribonacciPeriodTenOrbit09,
    tribonacciPeriodTenOrbit10, tribonacciPeriodTenOrbit11, tribonacciPeriodTenOrbit12,
    tribonacciPeriodTenOrbit13, tribonacciPeriodTenOrbit14, tribonacciPeriodTenOrbit15,
    tribonacciPeriodTenOrbit16, tribonacciPeriodTenOrbit17, tribonacciPeriodTenOrbit18,
    tribonacciPeriodTenOrbit19, tribonacciPeriodTenOrbit20, tribonacciPeriodTenOrbit21,
    tribonacciPeriodTenOrbit22, tribonacciPeriodTenOrbit23, tribonacciPeriodTenOrbit24,
    tribonacciPeriodTenOrbit25, tribonacciPeriodTenOrbit26, tribonacciPeriodTenOrbit27,
    tribonacciPeriodTenOrbit28, tribonacciPeriodTenOrbit29, tribonacciPeriodTenOrbit30,
    tribonacciPeriodTenOrbit31, tribonacciPeriodTenOrbit32, tribonacciPeriodTenOrbit33,
    tribonacciPeriodTenOrbit34, tribonacciPeriodTenOrbit35, tribonacciPeriodTenOrbit36,
    tribonacciPeriodTenOrbit37, tribonacciPeriodTenOrbit38, tribonacciPeriodTenOrbit39,
    tribonacciPeriodTenOrbit40, tribonacciPeriodTenOrbit41, tribonacciPeriodTenOrbit42]

/-- The enumeration lists exactly forty-two primitive representatives. -/
theorem tribonacci_period_ten_representative_count :
    tribonacciPeriodTenOrbitRepresentatives.length = 42 := by
  simp only [tribonacciPeriodTenOrbitRepresentatives]
  rfl

end D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenData