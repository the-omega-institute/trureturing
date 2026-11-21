/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Initial class census for width-six rows with at most two defects. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Starts

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open HardinA229635State

def startTable : List State := [
  51, 66, 65, 52, 66, 51, 65, 52, 55, 62, 83, 37, 106, 87, 102, 44, 49, 68, 67, 50,
  43, 101, 88, 103, 38, 86, 61, 56, 62, 55, 87, 44, 102, 83, 106, 37, 43, 88, 101, 61,
  56, 103, 86, 38, 68, 49, 67, 50, 57, 60, 79, 39, 110, 81, 108, 42, 71, 111, 126, 91,
  31, 98, 121, 116, 78, 73, 123, 114, 119, 76, 118, 93, 96, 34, 53, 64, 84, 35, 105, 89,
  100, 46, 47, 70, 69, 48, 45, 99, 90, 104, 36, 85, 63, 54, 33, 95, 94, 117, 75, 120,
  113, 124, 74, 77, 115, 122, 97, 32, 92, 125, 112, 72, 41, 107, 82, 109, 40, 80, 59, 58,
  60, 57, 81, 42, 108, 79, 110, 39, 73, 114, 123, 93, 34, 96, 119, 118, 76, 71, 126, 111,
  121, 78, 116, 91, 98, 31, 33, 94, 95, 113, 74, 124, 117, 120, 75, 41, 82, 107, 59, 58,
  109, 80, 40, 77, 122, 115, 125, 72, 112, 97, 92, 32, 64, 53, 89, 46, 100, 84, 105, 35,
  45, 90, 99, 63, 54, 104, 85, 36, 70, 47, 69, 48, 47, 70, 48, 69, 35, 84, 105, 53,
  64, 100, 89, 46, 36, 104, 85, 99, 45, 90, 54, 63, 31, 91, 98, 111, 71, 126, 116, 121,
  78, 39, 79, 110, 57, 60, 108, 81, 42, 76, 119, 118, 123, 73, 114, 96, 93, 34, 32, 97,
  92, 115, 77, 122, 112, 125, 72, 75, 117, 120, 95, 33, 94, 124, 113, 74, 40, 109, 80, 107,
  41, 82, 58, 59, 49, 68, 50, 67, 37, 83, 106, 55, 62, 102, 87, 44, 38, 103, 86, 101,
  43, 88, 56, 61, 51, 66, 52, 65, 65, 52, 66, 51, 61, 56, 88, 43, 101, 86, 103, 38,
  44, 87, 102, 62, 55, 106, 83, 37, 67, 50, 68, 49, 59, 58, 82, 41, 107, 80, 109, 40,
  74, 113, 124, 94, 33, 95, 120, 117, 75, 72, 125, 112, 122, 77, 115, 92, 97, 32, 34, 93,
  96, 114, 73, 123, 118, 119, 76, 42, 81, 108, 60, 57, 110, 79, 39, 78, 121, 116, 126, 71,
  111, 98, 91, 31, 63, 54, 90, 45, 99, 85, 104, 36, 46, 89, 100, 64, 53, 105, 84, 35,
  69, 48, 70, 47, 48, 69, 47, 70, 36, 85, 104, 54, 63, 99, 90, 45, 35, 105, 84, 100,
  46, 89, 53, 64, 32, 92, 97, 112, 72, 125, 115, 122, 77, 40, 80, 109, 58, 59, 107, 82,
  41, 75, 120, 117, 124, 74, 113, 95, 94, 33, 31, 98, 91, 116, 78, 121, 111, 126, 71, 76,
  118, 119, 96, 34, 93, 123, 114, 73, 39, 110, 79, 108, 42, 81, 57, 60, 58, 59, 80, 40,
  109, 82, 107, 41, 72, 112, 125, 92, 32, 97, 122, 115, 77, 74, 124, 113, 120, 75, 117, 94,
  95, 33, 54, 63, 85, 36, 104, 90, 99, 45, 48, 69, 70, 47, 46, 100, 89, 105, 35, 84,
  64, 53, 34, 96, 93, 118, 76, 119, 114, 123, 73, 78, 116, 121, 98, 31, 91, 126, 111, 71,
  42, 108, 81, 110, 39, 79, 60, 57, 50, 67, 49, 68, 38, 86, 103, 56, 61, 101, 88, 43,
  37, 106, 83, 102, 44, 87, 55, 62, 56, 61, 86, 38, 103, 88, 101, 43, 50, 67, 68, 49,
  44, 102, 87, 106, 37, 83, 62, 55, 52, 65, 51, 66, 52, 65, 66, 51]

theorem checked_starts : startClasses = startTable := by decide +kernel

theorem start_tallies :
    ∀ s : State, (startTable.count s : ℤ) = (if s.val < 31 then 0 else 6) := by decide +kernel

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Starts
