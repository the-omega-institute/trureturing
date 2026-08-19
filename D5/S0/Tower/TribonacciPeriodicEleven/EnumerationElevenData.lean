/- GID: D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenData
   generality: I
   mirror-B: D5/B/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Seventy-four exact primitive period-eleven Tribonacci certificates. -/

import D5.S0.Tower.TribonacciPeriodicTen.EnumerationTenMaximinC

/- Library-search audit trail (2026-08-18):
   * The enumerator was calibrated against all three committed levels before
     use, and against their rotation classes as sets rather than their counts:
     it reproduces the fifteen, twenty-six and forty-two classes exactly.
   * Names are numeric, as at period ten, because the count exceeds the
     twenty-six letters the shortest levels used. -/

namespace D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData

open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicEnumeration

local notation "makeOrbit" => tribonacciMakeOrbit

abbrev CodedOrbit := TribonacciCodedOrbit

def tribonacciPeriodElevenOrbit01 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit02 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit03 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit04 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit05 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit06 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight]

def tribonacciPeriodElevenOrbit07 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit08 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit09 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit10 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit11 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit12 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit13 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit14 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit15 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit16 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit17 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight]

def tribonacciPeriodElevenOrbit18 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit19 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit20 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit21 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit22 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft,
      .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit23 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit24 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit25 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight]

def tribonacciPeriodElevenOrbit26 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit27 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit28 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit29 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit30 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit31 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeLeft, .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit32 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeLeft, .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit33 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit34 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit35 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit36 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit37 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit38 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit39 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit40 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit41 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodElevenOrbit42 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodElevenOrbit43 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeLeft, .largeRight, .combinedRight]

def tribonacciPeriodElevenOrbit44 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit45 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeLeft, .largeRight]

def tribonacciPeriodElevenOrbit46 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit47 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit48 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit49 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit50 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit51 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit52 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft,
      .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft]

def tribonacciPeriodElevenOrbit53 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit54 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit55 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedRight, .smallThrough, .largeLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit56 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeLeft]

def tribonacciPeriodElevenOrbit57 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeLeft, .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit58 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit59 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit60 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodElevenOrbit61 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodElevenOrbit62 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit63 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft,
      .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeLeft]

def tribonacciPeriodElevenOrbit64 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeLeft]

def tribonacciPeriodElevenOrbit65 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedLeft, .largeRight, .combinedLeft, .largeRight]

def tribonacciPeriodElevenOrbit66 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit67 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit68 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough,
      .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft, .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit69 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeLeft]

def tribonacciPeriodElevenOrbit70 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeLeft]

def tribonacciPeriodElevenOrbit71 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft,
      .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedLeft]
    [.largeLeft]

def tribonacciPeriodElevenOrbit72 : CodedOrbit :=
  makeOrbit .large
    [.largeLeft, .largeRight, .combinedRight, .smallThrough, .largeRight, .combinedRight,
      .smallThrough, .largeRight, .combinedLeft, .largeRight, .combinedLeft]
    [.largeLeft]

def tribonacciPeriodElevenOrbit73 : CodedOrbit :=
  makeOrbit .large
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough]
    [.largeRight, .combinedLeft, .largeRight, .combinedLeft, .largeRight, .combinedLeft,
      .largeRight, .combinedLeft]

def tribonacciPeriodElevenOrbit74 : CodedOrbit :=
  makeOrbit .large
    [.largeRight, .combinedLeft, .largeRight, .combinedRight, .smallThrough, .largeRight,
      .combinedRight, .smallThrough, .largeRight, .combinedRight, .smallThrough]
    [.largeRight, .combinedLeft]

/-- The seventy-four primitive period-eleven representatives. -/
def tribonacciPeriodElevenOrbitRepresentatives : List CodedOrbit :=
  [tribonacciPeriodElevenOrbit01, tribonacciPeriodElevenOrbit02, tribonacciPeriodElevenOrbit03,
    tribonacciPeriodElevenOrbit04, tribonacciPeriodElevenOrbit05,
    tribonacciPeriodElevenOrbit06, tribonacciPeriodElevenOrbit07,
    tribonacciPeriodElevenOrbit08, tribonacciPeriodElevenOrbit09,
    tribonacciPeriodElevenOrbit10, tribonacciPeriodElevenOrbit11,
    tribonacciPeriodElevenOrbit12, tribonacciPeriodElevenOrbit13,
    tribonacciPeriodElevenOrbit14, tribonacciPeriodElevenOrbit15,
    tribonacciPeriodElevenOrbit16, tribonacciPeriodElevenOrbit17,
    tribonacciPeriodElevenOrbit18, tribonacciPeriodElevenOrbit19,
    tribonacciPeriodElevenOrbit20, tribonacciPeriodElevenOrbit21,
    tribonacciPeriodElevenOrbit22, tribonacciPeriodElevenOrbit23,
    tribonacciPeriodElevenOrbit24, tribonacciPeriodElevenOrbit25,
    tribonacciPeriodElevenOrbit26, tribonacciPeriodElevenOrbit27,
    tribonacciPeriodElevenOrbit28, tribonacciPeriodElevenOrbit29,
    tribonacciPeriodElevenOrbit30, tribonacciPeriodElevenOrbit31,
    tribonacciPeriodElevenOrbit32, tribonacciPeriodElevenOrbit33,
    tribonacciPeriodElevenOrbit34, tribonacciPeriodElevenOrbit35,
    tribonacciPeriodElevenOrbit36, tribonacciPeriodElevenOrbit37,
    tribonacciPeriodElevenOrbit38, tribonacciPeriodElevenOrbit39,
    tribonacciPeriodElevenOrbit40, tribonacciPeriodElevenOrbit41,
    tribonacciPeriodElevenOrbit42, tribonacciPeriodElevenOrbit43,
    tribonacciPeriodElevenOrbit44, tribonacciPeriodElevenOrbit45,
    tribonacciPeriodElevenOrbit46, tribonacciPeriodElevenOrbit47,
    tribonacciPeriodElevenOrbit48, tribonacciPeriodElevenOrbit49,
    tribonacciPeriodElevenOrbit50, tribonacciPeriodElevenOrbit51,
    tribonacciPeriodElevenOrbit52, tribonacciPeriodElevenOrbit53,
    tribonacciPeriodElevenOrbit54, tribonacciPeriodElevenOrbit55,
    tribonacciPeriodElevenOrbit56, tribonacciPeriodElevenOrbit57,
    tribonacciPeriodElevenOrbit58, tribonacciPeriodElevenOrbit59,
    tribonacciPeriodElevenOrbit60, tribonacciPeriodElevenOrbit61,
    tribonacciPeriodElevenOrbit62, tribonacciPeriodElevenOrbit63,
    tribonacciPeriodElevenOrbit64, tribonacciPeriodElevenOrbit65,
    tribonacciPeriodElevenOrbit66, tribonacciPeriodElevenOrbit67,
    tribonacciPeriodElevenOrbit68, tribonacciPeriodElevenOrbit69,
    tribonacciPeriodElevenOrbit70, tribonacciPeriodElevenOrbit71,
    tribonacciPeriodElevenOrbit72, tribonacciPeriodElevenOrbit73, tribonacciPeriodElevenOrbit74]

/-- The enumeration lists exactly seventy-four primitive representatives. -/
theorem tribonacci_period_eleven_representative_count :
    tribonacciPeriodElevenOrbitRepresentatives.length = 74 := by
  simp only [tribonacciPeriodElevenOrbitRepresentatives]
  rfl

end D5.S0.Tower.TribonacciPeriodicEleven.EnumerationElevenData