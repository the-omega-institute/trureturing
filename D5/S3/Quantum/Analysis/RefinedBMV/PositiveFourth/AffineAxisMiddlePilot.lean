import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisMiddleData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCertificateBounds
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCertificateEvaluation

open RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisMiddle

private theorem checkedRates : certificate.checkRates = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedBounds : certificate.staticCheck 12 448 1850 194 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows0 :
    (List.range' 0 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows8 :
    (List.range' 8 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows16 :
    (List.range' 16 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows24 :
    (List.range' 24 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows32 :
    (List.range' 32 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows40 :
    (List.range' 40 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows48 :
    (List.range' 48 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows56 :
    (List.range' 56 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows64 :
    (List.range' 64 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows72 :
    (List.range' 72 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows80 :
    (List.range' 80 8).all (certificate.checkRow 1850 194) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedRows88 :
    (List.range' 88 3).all (certificate.checkRow 1850 194) = true := by decide +kernel
private theorem checkedRows (k : ℕ) (hk : k < certificate.rootsU.length) :
    certificate.checkRow 1850 194 k = true := by
  have hk' : k < 91 := hk
  by_cases h8 : k < 8
  · exact List.all_eq_true.mp checkedRows0 k (List.mem_range'.mpr (by omega))
  by_cases h16 : k < 16
  · exact List.all_eq_true.mp checkedRows8 k (List.mem_range'.mpr (by omega))
  by_cases h24 : k < 24
  · exact List.all_eq_true.mp checkedRows16 k (List.mem_range'.mpr (by omega))
  by_cases h32 : k < 32
  · exact List.all_eq_true.mp checkedRows24 k (List.mem_range'.mpr (by omega))
  by_cases h40 : k < 40
  · exact List.all_eq_true.mp checkedRows32 k (List.mem_range'.mpr (by omega))
  by_cases h48 : k < 48
  · exact List.all_eq_true.mp checkedRows40 k (List.mem_range'.mpr (by omega))
  by_cases h56 : k < 56
  · exact List.all_eq_true.mp checkedRows48 k (List.mem_range'.mpr (by omega))
  by_cases h64 : k < 64
  · exact List.all_eq_true.mp checkedRows56 k (List.mem_range'.mpr (by omega))
  by_cases h72 : k < 72
  · exact List.all_eq_true.mp checkedRows64 k (List.mem_range'.mpr (by omega))
  by_cases h80 : k < 80
  · exact List.all_eq_true.mp checkedRows72 k (List.mem_range'.mpr (by omega))
  by_cases h88 : k < 88
  · exact List.all_eq_true.mp checkedRows80 k (List.mem_range'.mpr (by omega))
  exact List.all_eq_true.mp checkedRows88 k (List.mem_range'.mpr (by omega))

#print axioms checkedRows
#print axioms checkedBounds
