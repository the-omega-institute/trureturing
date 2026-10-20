/- GID: D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate
   generality: I
   mirror-B: D5/B/S3/Arith/RoldanCirculantEnergyP2Q3Certificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/RoldanCirculantEnergyP2Q3.result; premises=D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.certificate_blocks
   digest: A finite coefficient certificate bounds every competing mask. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19204.

admission_basis: escape-witness.
proof_shape: model_gap: content.
escape_witness: certificate_blocks, the exhaustive integer inequalities
  for all 2047 competing masks; consumer: model_gap.
Direct frozen dependencies: none.
The positive coefficient gap yields a uniform bound for all nonnegative real u and v.

Declaration classification:
  star_sign_coherence: content; consumers: star_attains.
  weights_nonneg: bind-only; consumers: modelEnergy_le.
  optimum_coefficients: bind-only; consumers: ucoeff_star.
  block_0: content; consumers: certificate_blocks.
  block_1: content; consumers: certificate_blocks.
  block_2: content; consumers: certificate_blocks.
  block_3: content; consumers: certificate_blocks.
  block_4: content; consumers: certificate_blocks.
  block_5: content; consumers: certificate_blocks.
  block_6: content; consumers: certificate_blocks.
  block_7: content; consumers: certificate_blocks.
  block_8: content; consumers: certificate_blocks.
  block_9: content; consumers: certificate_blocks.
  block_10: content; consumers: certificate_blocks.
  block_11: content; consumers: certificate_blocks.
  block_12: content; consumers: certificate_blocks.
  block_13: content; consumers: certificate_blocks.
  block_14: content; consumers: certificate_blocks.
  block_15: content; consumers: certificate_blocks.
  block_16: content; consumers: certificate_blocks.
  block_17: content; consumers: certificate_blocks.
  block_18: content; consumers: certificate_blocks.
  block_19: content; consumers: certificate_blocks.
  block_20: content; consumers: certificate_blocks.
  block_21: content; consumers: certificate_blocks.
  block_22: content; consumers: certificate_blocks.
  block_23: content; consumers: certificate_blocks.
  block_24: content; consumers: certificate_blocks.
  block_25: content; consumers: certificate_blocks.
  block_26: content; consumers: certificate_blocks.
  block_27: content; consumers: certificate_blocks.
  block_28: content; consumers: certificate_blocks.
  block_29: content; consumers: certificate_blocks.
  block_30: content; consumers: certificate_blocks.
  block_31: content; consumers: certificate_blocks.
  certificate_blocks: content; consumers: coefficient_bound.
  coefficient_bound: content; consumers: all_coeff_bound.
  lcoeff_eq_fast: bind-only; consumers: ucoeff_eq_upper, upper_evaluation.
  ucoeff_eq_upper: bind-only; consumers: ucoeff_star, all_coeff_bound.
  abs_eval_le: bind-only; consumers: modelEnergy_le.
  eval_nonneg: bind-only; consumers: abs_eval_eq_of_nonneg, abs_eval_eq_of_nonpos.
  eval_mono: bind-only; consumers: gap_assembly.
  abs_eval_eq_of_nonneg: bind-only; consumers: star_attains.
  abs_eval_eq_of_nonpos: bind-only; consumers: star_attains.
  eval_sub: bind-only; consumers: gap_assembly.
  eval_ge_constant: bind-only; consumers: gap_assembly.
  gap_assembly: bind-only; consumers: model_gap.
  upper_evaluation: bind-only; consumers: modelEnergy_le, star_attains.
  modelEnergy_le: bind-only; consumers: model_gap.
  star_attains: content; consumers: model_gap.
  ucoeff_star: bind-only; consumers: model_gap.
  all_coeff_bound: content; consumers: model_gap.
  delta_nonneg: bind-only; consumers: model_gap.
  model_gap: content; consumers: result.
-/

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Basic.Real.Basic

open scoped BigOperators
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def A : Fin 3 → Fin 3 → Fin 3 → ℤ := ![![![0, 0, 0], ![-1, 0, 0], ![1, 0, 0]], ![![-3, -1, 0], ![2, 1, 0], ![1, 0, 0]], ![![6, 5, 1], ![2, 1, 0], ![1, 0, 0]]]
def B : Fin 4 → Fin 4 → Fin 4 → ℤ := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![-3, -1, 0, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]], ![![-9, -6, -1, 0], ![6, 5, 1, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]], ![![18, 21, 8, 1], ![6, 5, 1, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]]]
def wA : Fin 3 → Fin 3 → ℤ := ![![6, 5, 1], ![2, 1, 0], ![1, 0, 0]]
def wB : Fin 4 → Fin 4 → ℤ := ![![18, 21, 8, 1], ![6, 5, 1, 0], ![2, 1, 0, 0], ![1, 0, 0, 0]]
def switch (mask : ℕ) (c : Fin 3) (f : Fin 4) : ℤ :=
  if c.val = 2 ∧ f.val = 3 then 0 else if mask.testBit (4 * c.val + f.val) then 1 else 0
def lcoeff (mask : ℕ) (a : Fin 3) (b : Fin 4) (i : Fin 3) (j : Fin 4) : ℤ :=
  ∑ c, ∑ f, A a c i * B b f j * switch mask c f
def star : ℕ := 1445
private theorem star_sign_coherence : ∀ a b,
    (∀ i j, 0 ≤ lcoeff star a b i j) ∨ (∀ i j, lcoeff star a b i j ≤ 0) := by
  decide +kernel
private theorem weights_nonneg : (∀ a i, 0 ≤ wA a i) ∧ (∀ b j, 0 ≤ wB b j) := by
  decide +kernel
end D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate

open scoped BigOperators
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def upper (mask : ℕ) : Fin 12 → ℤ :=
  let x0 : ℤ := if mask.testBit 0 then 1 else 0
  let x1 : ℤ := if mask.testBit 1 then 1 else 0
  let x2 : ℤ := if mask.testBit 2 then 1 else 0
  let x3 : ℤ := if mask.testBit 3 then 1 else 0
  let x4 : ℤ := if mask.testBit 4 then 1 else 0
  let x5 : ℤ := if mask.testBit 5 then 1 else 0
  let x6 : ℤ := if mask.testBit 6 then 1 else 0
  let x7 : ℤ := if mask.testBit 7 then 1 else 0
  let x8 : ℤ := if mask.testBit 8 then 1 else 0
  let x9 : ℤ := if mask.testBit 9 then 1 else 0
  let x10 : ℤ := if mask.testBit 10 then 1 else 0
  let y0000 : ℤ := |x6 + (-1) * x7 + (-1) * x10|
  let y0100 : ℤ := |(3) * x5 + (-2) * x6 + (-1) * x7 + (-3) * x9 + (2) * x10|
  let y0101 : ℤ := |x5 + (-1) * x6 + (-1) * x9 + x10|
  let y0200 : ℤ := |(9) * x4 + (-6) * x5 + (-2) * x6 + (-1) * x7 + (-9) * x8 + (6) * x9 + (2) * x10|
  let y0201 : ℤ := |(6) * x4 + (-5) * x5 + (-1) * x6 + (-6) * x8 + (5) * x9 + x10|
  let y0202 : ℤ := |x4 + (-1) * x5 + (-1) * x8 + x9|
  let y0300 : ℤ := |(-18) * x4 + (-6) * x5 + (-2) * x6 + (-1) * x7 + (18) * x8 + (6) * x9 + (2) * x10|
  let y0301 : ℤ := |(-21) * x4 + (-5) * x5 + (-1) * x6 + (21) * x8 + (5) * x9 + x10|
  let y0302 : ℤ := |(-8) * x4 + (-1) * x5 + (8) * x8 + x9|
  let y0303 : ℤ := |(-1) * x4 + x8|
  let y1000 : ℤ := |(3) * x2 + (-3) * x3 + (-2) * x6 + (2) * x7 + (-1) * x10|
  let y1010 : ℤ := |x2 + (-1) * x3 + (-1) * x6 + x7|
  let y1100 : ℤ := |(9) * x1 + (-6) * x2 + (-3) * x3 + (-6) * x5 + (4) * x6 + (2) * x7 + (-3) * x9 + (2) * x10|
  let y1101 : ℤ := |(3) * x1 + (-3) * x2 + (-2) * x5 + (2) * x6 + (-1) * x9 + x10|
  let y1110 : ℤ := |(3) * x1 + (-2) * x2 + (-1) * x3 + (-3) * x5 + (2) * x6 + x7|
  let y1111 : ℤ := |x1 + (-1) * x2 + (-1) * x5 + x6|
  let y1200 : ℤ := |(27) * x0 + (-18) * x1 + (-6) * x2 + (-3) * x3 + (-18) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (-9) * x8 + (6) * x9 + (2) * x10|
  let y1201 : ℤ := |(18) * x0 + (-15) * x1 + (-3) * x2 + (-12) * x4 + (10) * x5 + (2) * x6 + (-6) * x8 + (5) * x9 + x10|
  let y1202 : ℤ := |(3) * x0 + (-3) * x1 + (-2) * x4 + (2) * x5 + (-1) * x8 + x9|
  let y1210 : ℤ := |(9) * x0 + (-6) * x1 + (-2) * x2 + (-1) * x3 + (-9) * x4 + (6) * x5 + (2) * x6 + x7|
  let y1211 : ℤ := |(6) * x0 + (-5) * x1 + (-1) * x2 + (-6) * x4 + (5) * x5 + x6|
  let y1212 : ℤ := |x0 + (-1) * x1 + (-1) * x4 + x5|
  let y1300 : ℤ := |(-54) * x0 + (-18) * x1 + (-6) * x2 + (-3) * x3 + (36) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (18) * x8 + (6) * x9 + (2) * x10|
  let y1301 : ℤ := |(-63) * x0 + (-15) * x1 + (-3) * x2 + (42) * x4 + (10) * x5 + (2) * x6 + (21) * x8 + (5) * x9 + x10|
  let y1302 : ℤ := |(-24) * x0 + (-3) * x1 + (16) * x4 + (2) * x5 + (8) * x8 + x9|
  let y1303 : ℤ := |(-3) * x0 + (2) * x4 + x8|
  let y1310 : ℤ := |(-18) * x0 + (-6) * x1 + (-2) * x2 + (-1) * x3 + (18) * x4 + (6) * x5 + (2) * x6 + x7|
  let y1311 : ℤ := |(-21) * x0 + (-5) * x1 + (-1) * x2 + (21) * x4 + (5) * x5 + x6|
  let y1312 : ℤ := |(-8) * x0 + (-1) * x1 + (8) * x4 + x5|
  let y1313 : ℤ := |(-1) * x0 + x4|
  let y2000 : ℤ := |(-6) * x2 + (6) * x3 + (-2) * x6 + (2) * x7 + (-1) * x10|
  let y2010 : ℤ := |(-5) * x2 + (5) * x3 + (-1) * x6 + x7|
  let y2020 : ℤ := |(-1) * x2 + x3|
  let y2100 : ℤ := |(-18) * x1 + (12) * x2 + (6) * x3 + (-6) * x5 + (4) * x6 + (2) * x7 + (-3) * x9 + (2) * x10|
  let y2101 : ℤ := |(-6) * x1 + (6) * x2 + (-2) * x5 + (2) * x6 + (-1) * x9 + x10|
  let y2110 : ℤ := |(-15) * x1 + (10) * x2 + (5) * x3 + (-3) * x5 + (2) * x6 + x7|
  let y2111 : ℤ := |(-5) * x1 + (5) * x2 + (-1) * x5 + x6|
  let y2120 : ℤ := |(-3) * x1 + (2) * x2 + x3|
  let y2121 : ℤ := |(-1) * x1 + x2|
  let y2200 : ℤ := |(-54) * x0 + (36) * x1 + (12) * x2 + (6) * x3 + (-18) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (-9) * x8 + (6) * x9 + (2) * x10|
  let y2201 : ℤ := |(-36) * x0 + (30) * x1 + (6) * x2 + (-12) * x4 + (10) * x5 + (2) * x6 + (-6) * x8 + (5) * x9 + x10|
  let y2202 : ℤ := |(-6) * x0 + (6) * x1 + (-2) * x4 + (2) * x5 + (-1) * x8 + x9|
  let y2210 : ℤ := |(-45) * x0 + (30) * x1 + (10) * x2 + (5) * x3 + (-9) * x4 + (6) * x5 + (2) * x6 + x7|
  let y2211 : ℤ := |(-30) * x0 + (25) * x1 + (5) * x2 + (-6) * x4 + (5) * x5 + x6|
  let y2212 : ℤ := |(-5) * x0 + (5) * x1 + (-1) * x4 + x5|
  let y2220 : ℤ := |(-9) * x0 + (6) * x1 + (2) * x2 + x3|
  let y2221 : ℤ := |(-6) * x0 + (5) * x1 + x2|
  let y2222 : ℤ := |(-1) * x0 + x1|
  let y2300 : ℤ := |(108) * x0 + (36) * x1 + (12) * x2 + (6) * x3 + (36) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (18) * x8 + (6) * x9 + (2) * x10|
  let y2301 : ℤ := |(126) * x0 + (30) * x1 + (6) * x2 + (42) * x4 + (10) * x5 + (2) * x6 + (21) * x8 + (5) * x9 + x10|
  let y2302 : ℤ := |(48) * x0 + (6) * x1 + (16) * x4 + (2) * x5 + (8) * x8 + x9|
  let y2303 : ℤ := |(6) * x0 + (2) * x4 + x8|
  let y2310 : ℤ := |(90) * x0 + (30) * x1 + (10) * x2 + (5) * x3 + (18) * x4 + (6) * x5 + (2) * x6 + x7|
  let y2311 : ℤ := |(105) * x0 + (25) * x1 + (5) * x2 + (21) * x4 + (5) * x5 + x6|
  let y2312 : ℤ := |(40) * x0 + (5) * x1 + (8) * x4 + x5|
  let y2313 : ℤ := |(5) * x0 + x4|
  let y2320 : ℤ := |(18) * x0 + (6) * x1 + (2) * x2 + x3|
  let y2321 : ℤ := |(21) * x0 + (5) * x1 + x2|
  let y2322 : ℤ := |(8) * x0 + x1|
  let y2323 : ℤ := |x0|
  ![(108) * y0000 + (36) * y0100 + (12) * y0200 + (6) * y0300 + (36) * y1000 + (12) * y1100 + (4) * y1200 + (2) * y1300 + (18) * y2000 + (6) * y2100 + (2) * y2200 + y2300,
    (126) * y0000 + (30) * y0100 + (36) * y0101 + (6) * y0200 + (12) * y0201 + (6) * y0301 + (42) * y1000 + (10) * y1100 + (12) * y1101 + (2) * y1200 + (4) * y1201 + (2) * y1301 + (21) * y2000 + (5) * y2100 + (6) * y2101 + y2200 + (2) * y2201 + y2301,
    (48) * y0000 + (6) * y0100 + (30) * y0101 + (6) * y0201 + (12) * y0202 + (6) * y0302 + (16) * y1000 + (2) * y1100 + (10) * y1101 + (2) * y1201 + (4) * y1202 + (2) * y1302 + (8) * y2000 + y2100 + (5) * y2101 + y2201 + (2) * y2202 + y2302,
    (6) * y0000 + (6) * y0101 + (6) * y0202 + (6) * y0303 + (2) * y1000 + (2) * y1101 + (2) * y1202 + (2) * y1303 + y2000 + y2101 + y2202 + y2303,
    (90) * y0000 + (30) * y0100 + (10) * y0200 + (5) * y0300 + (18) * y1000 + (36) * y1010 + (6) * y1100 + (12) * y1110 + (2) * y1200 + (4) * y1210 + y1300 + (2) * y1310 + (18) * y2010 + (6) * y2110 + (2) * y2210 + y2310,
    (105) * y0000 + (25) * y0100 + (30) * y0101 + (5) * y0200 + (10) * y0201 + (5) * y0301 + (21) * y1000 + (42) * y1010 + (5) * y1100 + (6) * y1101 + (10) * y1110 + (12) * y1111 + y1200 + (2) * y1201 + (2) * y1210 + (4) * y1211 + y1301 + (2) * y1311 + (21) * y2010 + (5) * y2110 + (6) * y2111 + y2210 + (2) * y2211 + y2311,
    (40) * y0000 + (5) * y0100 + (25) * y0101 + (5) * y0201 + (10) * y0202 + (5) * y0302 + (8) * y1000 + (16) * y1010 + y1100 + (5) * y1101 + (2) * y1110 + (10) * y1111 + y1201 + (2) * y1202 + (2) * y1211 + (4) * y1212 + y1302 + (2) * y1312 + (8) * y2010 + y2110 + (5) * y2111 + y2211 + (2) * y2212 + y2312,
    (5) * y0000 + (5) * y0101 + (5) * y0202 + (5) * y0303 + y1000 + (2) * y1010 + y1101 + (2) * y1111 + y1202 + (2) * y1212 + y1303 + (2) * y1313 + y2010 + y2111 + y2212 + y2313,
    (18) * y0000 + (6) * y0100 + (2) * y0200 + y0300 + (18) * y1010 + (6) * y1110 + (2) * y1210 + y1310 + (18) * y2020 + (6) * y2120 + (2) * y2220 + y2320,
    (21) * y0000 + (5) * y0100 + (6) * y0101 + y0200 + (2) * y0201 + y0301 + (21) * y1010 + (5) * y1110 + (6) * y1111 + y1210 + (2) * y1211 + y1311 + (21) * y2020 + (5) * y2120 + (6) * y2121 + y2220 + (2) * y2221 + y2321,
    (8) * y0000 + y0100 + (5) * y0101 + y0201 + (2) * y0202 + y0302 + (8) * y1010 + y1110 + (5) * y1111 + y1211 + (2) * y1212 + y1312 + (8) * y2020 + y2120 + (5) * y2121 + y2221 + (2) * y2222 + y2322,
    y0000 + y0101 + y0202 + y0303 + y1010 + y1111 + y1212 + y1313 + y2020 + y2121 + y2222 + y2323]
private def optimum : Fin 12 → ℤ := ![1384, 1684, 678, 92, 1192, 1456, 588, 80, 266, 326, 132, 18]
private def gap : Fin 12 → ℤ := ![96, 136, 56, 8, 94, 128, 54, 8, 24, 32, 14, 2]
private def check (mask : ℕ) : Bool :=
  (List.finRange 12).all fun i => decide (upper mask i ≤ optimum i - gap i)
private def block (start count : ℕ) : Bool :=
  (List.range' start count).all fun mask => (mask == 1445) || check mask
private theorem optimum_coefficients : upper 1445 = optimum := by
  exact List.ofFn_inj.mp rfl
private theorem block_0 : block 0 64 = true := by decide +kernel
private theorem block_1 : block 64 64 = true := by decide +kernel
private theorem block_2 : block 128 64 = true := by decide +kernel
private theorem block_3 : block 192 64 = true := by decide +kernel
private theorem block_4 : block 256 64 = true := by decide +kernel
private theorem block_5 : block 320 64 = true := by decide +kernel
private theorem block_6 : block 384 64 = true := by decide +kernel
private theorem block_7 : block 448 64 = true := by decide +kernel
private theorem block_8 : block 512 64 = true := by decide +kernel
private theorem block_9 : block 576 64 = true := by decide +kernel
private theorem block_10 : block 640 64 = true := by decide +kernel
private theorem block_11 : block 704 64 = true := by decide +kernel
private theorem block_12 : block 768 64 = true := by decide +kernel
private theorem block_13 : block 832 64 = true := by decide +kernel
private theorem block_14 : block 896 64 = true := by decide +kernel
private theorem block_15 : block 960 64 = true := by decide +kernel
private theorem block_16 : block 1024 64 = true := by decide +kernel
private theorem block_17 : block 1088 64 = true := by decide +kernel
private theorem block_18 : block 1152 64 = true := by decide +kernel
private theorem block_19 : block 1216 64 = true := by decide +kernel
private theorem block_20 : block 1280 64 = true := by decide +kernel
private theorem block_21 : block 1344 64 = true := by decide +kernel
private theorem block_22 : block 1408 64 = true := by decide +kernel
private theorem block_23 : block 1472 64 = true := by decide +kernel
private theorem block_24 : block 1536 64 = true := by decide +kernel
private theorem block_25 : block 1600 64 = true := by decide +kernel
private theorem block_26 : block 1664 64 = true := by decide +kernel
private theorem block_27 : block 1728 64 = true := by decide +kernel
private theorem block_28 : block 1792 64 = true := by decide +kernel
private theorem block_29 : block 1856 64 = true := by decide +kernel
private theorem block_30 : block 1920 64 = true := by decide +kernel
private theorem block_31 : block 1984 64 = true := by decide +kernel
private theorem certificate_blocks (b : Fin 32) : block (64 * b.val) 64 = true := by
  fin_cases b
  · exact block_0
  · exact block_1
  · exact block_2
  · exact block_3
  · exact block_4
  · exact block_5
  · exact block_6
  · exact block_7
  · exact block_8
  · exact block_9
  · exact block_10
  · exact block_11
  · exact block_12
  · exact block_13
  · exact block_14
  · exact block_15
  · exact block_16
  · exact block_17
  · exact block_18
  · exact block_19
  · exact block_20
  · exact block_21
  · exact block_22
  · exact block_23
  · exact block_24
  · exact block_25
  · exact block_26
  · exact block_27
  · exact block_28
  · exact block_29
  · exact block_30
  · exact block_31
end D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate

namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
private theorem coefficient_bound (mask : Fin 2048) (hne : mask.val ≠ 1445) (i : Fin 12) :
    upper mask.val i ≤ optimum i - gap i := by
  have hb := certificate_blocks ⟨mask.val / 64, by omega⟩
  change (List.range' (64 * (mask.val / 64)) 64).all
    (fun m => (m == 1445) || check m) = true at hb
  have hm : mask.val ∈ List.range' (64 * (mask.val / 64)) 64 := by
    simp only [List.mem_range'_1]
    omega
  have hc := (List.all_eq_true.mp hb) mask.val hm
  have hcheck : check mask.val = true := by simpa [hne] using hc
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) i (List.mem_finRange i))
end D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate

namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
private theorem lcoeff_eq_fast (mask : ℕ) : lcoeff mask = (
let x0 : ℤ := if mask.testBit 0 then 1 else 0
  let x1 : ℤ := if mask.testBit 1 then 1 else 0
  let x2 : ℤ := if mask.testBit 2 then 1 else 0
  let x3 : ℤ := if mask.testBit 3 then 1 else 0
  let x4 : ℤ := if mask.testBit 4 then 1 else 0
  let x5 : ℤ := if mask.testBit 5 then 1 else 0
  let x6 : ℤ := if mask.testBit 6 then 1 else 0
  let x7 : ℤ := if mask.testBit 7 then 1 else 0
  let x8 : ℤ := if mask.testBit 8 then 1 else 0
  let x9 : ℤ := if mask.testBit 9 then 1 else 0
  let x10 : ℤ := if mask.testBit 10 then 1 else 0
  ![![![![x6 + (-1) * x7 + (-1) * x10, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![(3) * x5 + (-2) * x6 + (-1) * x7 + (-3) * x9 + (2) * x10, x5 + (-1) * x6 + (-1) * x9 + x10, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![(9) * x4 + (-6) * x5 + (-2) * x6 + (-1) * x7 + (-9) * x8 + (6) * x9 + (2) * x10, (6) * x4 + (-5) * x5 + (-1) * x6 + (-6) * x8 + (5) * x9 + x10, x4 + (-1) * x5 + (-1) * x8 + x9, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![(-18) * x4 + (-6) * x5 + (-2) * x6 + (-1) * x7 + (18) * x8 + (6) * x9 + (2) * x10, (-21) * x4 + (-5) * x5 + (-1) * x6 + (21) * x8 + (5) * x9 + x10, (-8) * x4 + (-1) * x5 + (8) * x8 + x9, (-1) * x4 + x8], ![0, 0, 0, 0], ![0, 0, 0, 0]]], ![![![(3) * x2 + (-3) * x3 + (-2) * x6 + (2) * x7 + (-1) * x10, 0, 0, 0], ![x2 + (-1) * x3 + (-1) * x6 + x7, 0, 0, 0], ![0, 0, 0, 0]], ![![(9) * x1 + (-6) * x2 + (-3) * x3 + (-6) * x5 + (4) * x6 + (2) * x7 + (-3) * x9 + (2) * x10, (3) * x1 + (-3) * x2 + (-2) * x5 + (2) * x6 + (-1) * x9 + x10, 0, 0], ![(3) * x1 + (-2) * x2 + (-1) * x3 + (-3) * x5 + (2) * x6 + x7, x1 + (-1) * x2 + (-1) * x5 + x6, 0, 0], ![0, 0, 0, 0]], ![![(27) * x0 + (-18) * x1 + (-6) * x2 + (-3) * x3 + (-18) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (-9) * x8 + (6) * x9 + (2) * x10, (18) * x0 + (-15) * x1 + (-3) * x2 + (-12) * x4 + (10) * x5 + (2) * x6 + (-6) * x8 + (5) * x9 + x10, (3) * x0 + (-3) * x1 + (-2) * x4 + (2) * x5 + (-1) * x8 + x9, 0], ![(9) * x0 + (-6) * x1 + (-2) * x2 + (-1) * x3 + (-9) * x4 + (6) * x5 + (2) * x6 + x7, (6) * x0 + (-5) * x1 + (-1) * x2 + (-6) * x4 + (5) * x5 + x6, x0 + (-1) * x1 + (-1) * x4 + x5, 0], ![0, 0, 0, 0]], ![![(-54) * x0 + (-18) * x1 + (-6) * x2 + (-3) * x3 + (36) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (18) * x8 + (6) * x9 + (2) * x10, (-63) * x0 + (-15) * x1 + (-3) * x2 + (42) * x4 + (10) * x5 + (2) * x6 + (21) * x8 + (5) * x9 + x10, (-24) * x0 + (-3) * x1 + (16) * x4 + (2) * x5 + (8) * x8 + x9, (-3) * x0 + (2) * x4 + x8], ![(-18) * x0 + (-6) * x1 + (-2) * x2 + (-1) * x3 + (18) * x4 + (6) * x5 + (2) * x6 + x7, (-21) * x0 + (-5) * x1 + (-1) * x2 + (21) * x4 + (5) * x5 + x6, (-8) * x0 + (-1) * x1 + (8) * x4 + x5, (-1) * x0 + x4], ![0, 0, 0, 0]]], ![![![(-6) * x2 + (6) * x3 + (-2) * x6 + (2) * x7 + (-1) * x10, 0, 0, 0], ![(-5) * x2 + (5) * x3 + (-1) * x6 + x7, 0, 0, 0], ![(-1) * x2 + x3, 0, 0, 0]], ![![(-18) * x1 + (12) * x2 + (6) * x3 + (-6) * x5 + (4) * x6 + (2) * x7 + (-3) * x9 + (2) * x10, (-6) * x1 + (6) * x2 + (-2) * x5 + (2) * x6 + (-1) * x9 + x10, 0, 0], ![(-15) * x1 + (10) * x2 + (5) * x3 + (-3) * x5 + (2) * x6 + x7, (-5) * x1 + (5) * x2 + (-1) * x5 + x6, 0, 0], ![(-3) * x1 + (2) * x2 + x3, (-1) * x1 + x2, 0, 0]], ![![(-54) * x0 + (36) * x1 + (12) * x2 + (6) * x3 + (-18) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (-9) * x8 + (6) * x9 + (2) * x10, (-36) * x0 + (30) * x1 + (6) * x2 + (-12) * x4 + (10) * x5 + (2) * x6 + (-6) * x8 + (5) * x9 + x10, (-6) * x0 + (6) * x1 + (-2) * x4 + (2) * x5 + (-1) * x8 + x9, 0], ![(-45) * x0 + (30) * x1 + (10) * x2 + (5) * x3 + (-9) * x4 + (6) * x5 + (2) * x6 + x7, (-30) * x0 + (25) * x1 + (5) * x2 + (-6) * x4 + (5) * x5 + x6, (-5) * x0 + (5) * x1 + (-1) * x4 + x5, 0], ![(-9) * x0 + (6) * x1 + (2) * x2 + x3, (-6) * x0 + (5) * x1 + x2, (-1) * x0 + x1, 0]], ![![(108) * x0 + (36) * x1 + (12) * x2 + (6) * x3 + (36) * x4 + (12) * x5 + (4) * x6 + (2) * x7 + (18) * x8 + (6) * x9 + (2) * x10, (126) * x0 + (30) * x1 + (6) * x2 + (42) * x4 + (10) * x5 + (2) * x6 + (21) * x8 + (5) * x9 + x10, (48) * x0 + (6) * x1 + (16) * x4 + (2) * x5 + (8) * x8 + x9, (6) * x0 + (2) * x4 + x8], ![(90) * x0 + (30) * x1 + (10) * x2 + (5) * x3 + (18) * x4 + (6) * x5 + (2) * x6 + x7, (105) * x0 + (25) * x1 + (5) * x2 + (21) * x4 + (5) * x5 + x6, (40) * x0 + (5) * x1 + (8) * x4 + x5, (5) * x0 + x4], ![(18) * x0 + (6) * x1 + (2) * x2 + x3, (21) * x0 + (5) * x1 + x2, (8) * x0 + x1, x0]]]]
  ) := by
  funext a b i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [lcoeff, A, B, switch, Fin.sum_univ_succ] <;> ring
private theorem ucoeff_eq_upper (mask : ℕ) (i : Fin 3) (j : Fin 4) :
    (fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff mask a b h k| * wA a (i - h) * wB b (j - k) else 0) i j = upper mask ⟨4 * i.val + j.val, by omega⟩ := by
  fin_cases i <;> fin_cases j <;>
    norm_num [ lcoeff_eq_fast, wA, wB,
      upper, Fin.sum_univ_succ] <;> ring
end D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate

open scoped BigOperators
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
noncomputable section
def eval {r s : ℕ} (C : Fin r → Fin s → ℤ) (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, (C i j : ℝ) * u ^ i.val * v ^ j.val
private theorem abs_eval_le {r s : ℕ} (C : Fin r → Fin s → ℤ)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |eval C u v| ≤ eval ((fun i j => |C i j|)) u v := by
  unfold eval
  calc
    _ ≤ ∑ i, |∑ j : Fin s, (C i j : ℝ) * u ^ i.val * v ^ j.val| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin r, ∑ j : Fin s, |(C i j : ℝ) * u ^ i.val * v ^ j.val| := by
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      simp only [abs_mul, abs_of_nonneg (pow_nonneg hu _),
        abs_of_nonneg (pow_nonneg hv _), Int.cast_abs]
private theorem eval_nonneg {r s : ℕ} (C : Fin r → Fin s → ℤ) (hC : ∀ i j, 0 ≤ C i j)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ eval C u v := by
  unfold eval
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (by exact_mod_cast hC i j) (pow_nonneg hu _))
    (pow_nonneg hv _)
private theorem eval_mono {r s : ℕ} (C T : Fin r → Fin s → ℤ) (hCT : ∀ i j, C i j ≤ T i j)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : eval C u v ≤ eval T u v := by
  unfold eval
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hv _)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu _)
  exact_mod_cast hCT i j
private theorem abs_eval_eq_of_nonneg {r s : ℕ} (C : Fin r → Fin s → ℤ)
    (hC : ∀ i j, 0 ≤ C i j) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |eval C u v| = eval ((fun i j => |C i j|)) u v := by
  rw [abs_of_nonneg (eval_nonneg C hC u v hu hv)]
  congr 1
  funext i j
  exact (abs_of_nonneg (hC i j)).symm
private theorem abs_eval_eq_of_nonpos {r s : ℕ} (C : Fin r → Fin s → ℤ)
    (hC : ∀ i j, C i j ≤ 0) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |eval C u v| = eval ((fun i j => |C i j|)) u v := by
  have hn : eval (fun i j => -C i j) u v = -eval C u v := by simp [eval]
  have hpos : 0 ≤ eval (fun i j => -C i j) u v :=
    eval_nonneg _ (fun i j => neg_nonneg.mpr (hC i j)) u v hu hv
  rw [hn] at hpos
  rw [abs_of_nonpos (neg_nonneg.mp hpos)]
  rw [← hn]
  congr 1
  funext i j
  exact (abs_of_nonpos (hC i j)).symm
private theorem eval_sub {r s : ℕ} (C T : Fin r → Fin s → ℤ) (u v : ℝ) :
    eval (fun i j => C i j - T i j) u v = eval C u v - eval T u v := by
  simp [eval, sub_mul, Finset.sum_sub_distrib]
private theorem eval_ge_constant (C : Fin 3 → Fin 4 → ℤ) (hC : ∀ i j, 0 ≤ C i j)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : (C 0 0 : ℝ) ≤ eval C u v := by
  unfold eval
  calc
    _ = (C 0 0 : ℝ) * u ^ (0 : Fin 3).val * v ^ (0 : Fin 4).val := by simp
    _ ≤ ∑ j : Fin 4, (C 0 j : ℝ) * u ^ (0 : Fin 3).val * v ^ j.val := by
      apply Finset.single_le_sum (s := Finset.univ) (a := (0 : Fin 4))
        (f := fun j : Fin 4 => (C 0 j : ℝ) * u ^ (0 : Fin 3).val * v ^ j.val)
      · intro j _
        exact mul_nonneg (mul_nonneg (by exact_mod_cast hC 0 j) (pow_nonneg hu _)) (pow_nonneg hv _)
      · exact Finset.mem_univ 0
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 4, (C i j : ℝ) * u ^ i.val * v ^ j.val := by
      apply Finset.single_le_sum (s := Finset.univ) (a := (0 : Fin 3))
        (f := fun i : Fin 3 => ∑ j : Fin 4, (C i j : ℝ) * u ^ i.val * v ^ j.val)
      · intro i _
        exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (mul_nonneg (by exact_mod_cast hC i j) (pow_nonneg hu _)) (pow_nonneg hv _)
      · exact Finset.mem_univ 0
private theorem gap_assembly (C S Δ : Fin 3 → Fin 4 → ℤ)
    (hCS : ∀ i j, C i j ≤ S i j - Δ i j) (hΔ : ∀ i j, 0 ≤ Δ i j)
    (h00 : 96 ≤ Δ 0 0) (u v E Estar : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hE : E ≤ eval C u v) (hEstar : Estar = eval S u v) :
    96 ≤ Estar - E := by
  have hmono := eval_mono C (fun i j => S i j - Δ i j) hCS u v hu hv
  rw [eval_sub] at hmono
  have hgap := eval_ge_constant Δ hΔ u v hu hv
  have hc : (96 : ℝ) ≤ (Δ 0 0 : ℝ) := by exact_mod_cast h00
  linarith
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
open scoped BigOperators
noncomputable section
def evalW {R : Type*} [Ring R] {r : ℕ} (C : Fin r → ℤ) (x : R) : R :=
  Polynomial.eval x ((Polynomial.ofFn r C).map (Int.castRingHom R))
def modelEnergy (mask : ℕ) (u v : ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 4,
    evalW (wA a) u * evalW (wB b) v * |eval (lcoeff mask a b) u v|
private theorem upper_evaluation (mask : ℕ) (u v : ℝ) :
    eval ((fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff mask a b h k| * wA a (i - h) * wB b (j - k) else 0)) u v =
      ∑ a : Fin 3, ∑ b : Fin 4,
        evalW (wA a) u * evalW (wB b) v * eval ((fun i j => |lcoeff mask a b i j|)) u v := by
  rw [show eval ((fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff mask a b h k| * wA a (i - h) * wB b (j - k) else 0)) u v =
    ∑ a : Fin 3, ∑ b : Fin 4, ∑ i : Fin 3, ∑ j : Fin 4,
      (∑ h : Fin 3, ∑ k : Fin 4,
        if h.val ≤ i.val ∧ k.val ≤ j.val then
          (|lcoeff mask a b h k| : ℝ) * wA a (i-h) * wB b (j-k) else 0) *
        u ^ i.val * v ^ j.val by
      simp only [eval, Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_zero, Int.cast_abs]
      simp_rw [Finset.sum_mul]
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
        arg 2
        ext a
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  fin_cases a <;> fin_cases b <;>
    norm_num [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
      Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, eval, lcoeff_eq_fast, wA, wB,
      Fin.sum_univ_succ] <;> ring
private theorem modelEnergy_le (mask : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    modelEnergy mask u v ≤ eval ((fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff mask a b h k| * wA a (i - h) * wB b (j - k) else 0)) u v := by
  rw [upper_evaluation]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left (abs_eval_le _ u v hu hv)
  apply mul_nonneg
  all_goals simp only [evalW, Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
    Polynomial.map_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Int.coe_castRingHom]
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast weights_nonneg.1 a i) (pow_nonneg hu _)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (by exact_mod_cast weights_nonneg.2 b j) (pow_nonneg hv _)
private theorem star_attains (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    modelEnergy star u v = eval ((fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff star a b h k| * wA a (i - h) * wB b (j - k) else 0)) u v := by
  rw [upper_evaluation]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rcases star_sign_coherence a b with h | h
  · rw [abs_eval_eq_of_nonneg _ h u v hu hv]
  · rw [abs_eval_eq_of_nonpos _ h u v hu hv]
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
noncomputable section
private theorem ucoeff_star : (fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff star a b h k| * wA a (i - h) * wB b (j - k) else 0) = (fun i j => optimum ⟨4*i.val+j.val, by omega⟩) := by
  funext i j
  exact (ucoeff_eq_upper star i j).trans
    (congrFun optimum_coefficients ⟨4*i.val+j.val, by omega⟩)
private theorem all_coeff_bound (mask : Fin 2048) (hne : mask.val ≠ star) (i : Fin 3) (j : Fin 4) :
    (fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff mask.val a b h k| * wA a (i - h) * wB b (j - k) else 0) i j ≤ optimum ⟨4*i.val+j.val, by omega⟩ - gap ⟨4*i.val+j.val, by omega⟩ := by
  rw [ucoeff_eq_upper]
  exact coefficient_bound mask hne ⟨4*i.val+j.val, by omega⟩
private theorem delta_nonneg : ∀ (i : Fin 3) (j : Fin 4), 0 ≤ gap ⟨4*i.val+j.val, by omega⟩ := by
  decide +kernel
theorem model_gap (mask : Fin 2048) (hne : mask.val ≠ star)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    96 ≤ modelEnergy star u v - modelEnergy mask.val u v := by
  apply gap_assembly ((fun i j => ∑ a : Fin 3, ∑ b : Fin 4, ∑ h : Fin 3, ∑ k : Fin 4,
    if h.val ≤ i.val ∧ k.val ≤ j.val then
      |lcoeff mask.val a b h k| * wA a (i - h) * wB b (j - k) else 0))
    (fun i j => optimum ⟨4*i.val+j.val, by omega⟩)
    (fun i j => gap ⟨4*i.val+j.val, by omega⟩)
    (all_coeff_bound mask hne) delta_nonneg (by decide) u v
    (modelEnergy mask.val u v) (modelEnergy star u v) hu hv
    (modelEnergy_le mask.val u v hu hv)
  rw [star_attains u v hu hv, ucoeff_star]
end
end D5.S3.Arith.RoldanCirculantEnergyP2Q3Certificate
