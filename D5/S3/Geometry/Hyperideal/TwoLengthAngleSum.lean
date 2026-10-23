/- GID: D5/S3/Geometry/Hyperideal/TwoLengthAngleSum
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/TwoLengthAngleSum
   mirror-E: none(waiver:unbounded-continuous-angle-estimate)
   anchors: []
   utility: none
   digest: Complete selected-edge angle sum on the unbounded two-length domain. -/

import D5.S3.Geometry.Hyperideal.FourCycleCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Classical
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
namespace D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

-- Actual edge order (12,13,14,34,24,23).
-- All 64 actual six-slot masks; bits are the original six edge positions.
-- The ten continuous gaps below cover the nine K4 isomorphism types.
private def selected : Fin 64 → Finset (Fin 6) :=
  ![{},{0},{1},{0,1},{2},{0,2},{1,2},{0,1,2},{3},{0,3},{1,3},{0,1,3},{2,3},{0,2,3},{1,2,3},{0,1,2,3},{4},{0,4},{1,4},{0,1,4},{2,4},{0,2,4},{1,2,4},{0,1,2,4},{3,4},{0,3,4},{1,3,4},{0,1,3,4},{2,3,4},{0,2,3,4},{1,2,3,4},{0,1,2,3,4},{5},{0,5},{1,5},{0,1,5},{2,5},{0,2,5},{1,2,5},{0,1,2,5},{3,5},{0,3,5},{1,3,5},{0,1,3,5},{2,3,5},{0,2,3,5},{1,2,3,5},{0,1,2,3,5},{4,5},{0,4,5},{1,4,5},{0,1,4,5},{2,4,5},{0,2,4,5},{1,2,4,5},{0,1,2,4,5},{3,4,5},{0,3,4,5},{1,3,4,5},{0,1,3,4,5},{2,3,4,5},{0,2,3,4,5},{1,2,3,4,5},{0,1,2,3,4,5}]

private def useful : Fin 64 → Finset (Fin 6) :=
  ![{},{},{},{0,1},{},{0,2},{1,2},{0,1,2},{},{0,3},{1,3},{0,3},{2,3},{0,3},{1,2,3},{0,3},{},{0,4},{1,4},{1,4},{2,4},{0,2,4},{1,4},{1,4},{3,4},{0,3},{1,4},{0,1,3,4},{2,3,4},{0,3},{1,4},{0,1,3,4},{},{0,5},{1,5},{0,1,5},{2,5},{2,5},{2,5},{2,5},{3,5},{0,3},{1,3,5},{0,3},{2,5},{0,2,3,5},{2,5},{0,2,3,5},{4,5},{0,4,5},{1,4},{1,4},{2,5},{2,5},{1,2,4,5},{1,2,4,5},{3,4,5},{0,3},{1,4},{0,1,3,4},{2,5},{0,2,3,5},{1,2,4,5},{0,1,2,3,4,5}]

private def threshold : Fin 64 → ℝ :=
  ![0,0,0,(1/2 : ℝ),0,(1/2 : ℝ),(1/2 : ℝ),(2/3 : ℝ),0,0,(1/2 : ℝ),0,(1/2 : ℝ),0,(1/2 : ℝ),0,0,(1/2 : ℝ),0,0,(1/2 : ℝ),(1/2 : ℝ),0,0,(1/2 : ℝ),0,0,(1/2 : ℝ),(2/3 : ℝ),0,0,(1/2 : ℝ),0,(1/2 : ℝ),(1/2 : ℝ),(1/2 : ℝ),0,0,0,0,(1/2 : ℝ),0,(2/3 : ℝ),0,0,(1/2 : ℝ),0,(1/2 : ℝ),(1/2 : ℝ),(2/3 : ℝ),0,0,0,0,(1/2 : ℝ),(1/2 : ℝ),(1/2 : ℝ),0,0,(1/2 : ℝ),0,(1/2 : ℝ),(1/2 : ℝ),(2/3 : ℝ)]
private def angleFloor : Fin 64 → ℝ :=
  ![Real.pi/2,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/3,Real.pi/3,Real.pi/4,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/3,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/4,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/3,Real.pi/3,Real.pi/3,Real.pi/2,Real.pi/2,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/4,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/3,Real.pi/3,Real.pi/4,Real.pi/2,Real.pi/2,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/3,Real.pi/3,Real.pi/2,Real.pi/2,Real.pi/3,Real.pi/2,Real.pi/3,Real.pi/3,Real.pi/4]

private def values (A B : ℝ) (k : Fin 64) (q : Fin 6) : ℝ :=
  if q ∈ selected k then B else A

def rawNum (x : Fin 6 → ℝ) (q : Fin 6) : ℝ :=
  numerator (x (frame q 0)) (x (frame q 1)) (x (frame q 2))
    (x (frame q 3)) (x (frame q 4)) (x (frame q 5))
def leftRad (x : Fin 6 → ℝ) (q : Fin 6) : ℝ :=
  rad (x (frame q 0)) (x (frame q 1)) (x (frame q 5))
def rightRad (x : Fin 6 → ℝ) (q : Fin 6) : ℝ :=
  rad (x (frame q 0)) (x (frame q 2)) (x (frame q 4))
def rawCos (x : Fin 6 → ℝ) (q : Fin 6) : ℝ :=
  cosine (x (frame q 0)) (x (frame q 1)) (x (frame q 2))
    (x (frame q 3)) (x (frame q 4)) (x (frame q 5))
def extendedAngle (x : Fin 6 → ℝ) (q : Fin 6) : ℝ :=
  Real.arccos (max (-1) (min (rawCos x q) 1))

private def gap (A B : ℝ) (k : Fin 64) (q : Fin 6) : ℝ :=
  if threshold k = 0 then -rawNum (values A B k) q else
    (threshold k)^2 * leftRad (values A B k) q * rightRad (values A B k) q -
      (rawNum (values A B k) q)^2

-- The positive polynomial certificate applies on the full unbounded domain.
-- It never samples A or B, and never assumes any desired cosine bound.
set_option maxHeartbeats 2000000 in
private theorem continuous_gaps (A B : ℝ) (hA : 1 < A) (hB : 4*A+5 < B) :
    ∀ k : Fin 64, ∀ q ∈ useful k, 0 < gap A B k q := by
  let a := A-1
  let b := B-4*A-5
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have h0 : 0 < ((-1 * (((A ^ 2) + (A * B) + (A * (B ^ 2)) + (B * (A ^ 2)) + (-1 * A * (-1 + (B ^ 2)))) ^ 2)) + ((1/4 : ℝ) * (-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))) * (-1 + (B ^ 2) + (2 * (A ^ 2)) + (2 * B * (A ^ 2))))) := by
    have he : ((-1 * (((A ^ 2) + (A * B) + (A * (B ^ 2)) + (B * (A ^ 2)) + (-1 * A * (-1 + (B ^ 2)))) ^ 2)) + ((1/4 : ℝ) * (-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))) * (-1 + (B ^ 2) + (2 * (A ^ 2)) + (2 * B * (A ^ 2))))) =
      (7700 + (b ^ 4) + (38 * (b ^ 3)) + (48 * (a ^ 6)) + (537 * (b ^ 2)) + (658 * (a ^ 5)) + (3340 * b) + (3793 * (a ^ 4)) + (11762 * (a ^ 3)) + (19500 * a) + (20673 * (a ^ 2)) + ((a ^ 3) * (b ^ 3)) + ((1/2 : ℝ) * a * (b ^ 4)) + (11 * (a ^ 4) * (b ^ 2)) + (12 * (a ^ 2) * (b ^ 3)) + (39 * a * (b ^ 3)) + (40 * b * (a ^ 5)) + (118 * (a ^ 3) * (b ^ 2)) + (827 * a * (b ^ 2)) + (2297 * b * (a ^ 3)) + (5583 * b * (a ^ 2)) + (6820 * a * b) + ((953/2 : ℝ) * b * (a ^ 4)) + ((1885/4 : ℝ) * (a ^ 2) * (b ^ 2))) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h1 : 0 < ((-1 * (((A ^ 2) + (B ^ 2) + (-1 * A * (-1 + (B ^ 2))) + (2 * A * (B ^ 2))) ^ 2)) + ((4/9 : ℝ) * ((-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))) ^ 2))) := by
    have he : ((-1 * (((A ^ 2) + (B ^ 2) + (-1 * A * (-1 + (B ^ 2))) + (2 * A * (B ^ 2))) ^ 2)) + ((4/9 : ℝ) * ((-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))) ^ 2))) =
      (19760 + (112 * (b ^ 3)) + (1504 * (b ^ 2)) + (8928 * b) + (55392 * a) + ((28/9 : ℝ) * (b ^ 4)) + ((1792/9 : ℝ) * (a ^ 6)) + ((23264/9 : ℝ) * (a ^ 5)) + ((41849/3 : ℝ) * (a ^ 4)) + ((360536/9 : ℝ) * (a ^ 3)) + ((581128/9 : ℝ) * (a ^ 2)) + (20944 * a * b) + ((7/9 : ℝ) * (a ^ 2) * (b ^ 4)) + ((28/9 : ℝ) * a * (b ^ 4)) + ((112/9 : ℝ) * (a ^ 3) * (b ^ 3)) + ((224/3 : ℝ) * (a ^ 4) * (b ^ 2)) + ((700/9 : ℝ) * (a ^ 2) * (b ^ 3)) + ((1456/9 : ℝ) * a * (b ^ 3)) + ((1792/9 : ℝ) * b * (a ^ 5)) + ((5710/9 : ℝ) * (a ^ 3) * (b ^ 2)) + ((6416/3 : ℝ) * b * (a ^ 4)) + ((18160/9 : ℝ) * (a ^ 2) * (b ^ 2)) + ((25624/9 : ℝ) * a * (b ^ 2)) + ((27508/3 : ℝ) * b * (a ^ 3)) + ((176552/9 : ℝ) * b * (a ^ 2))) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h2 : 0 < ((-2 * (A ^ 2)) + (B * (-1 + (B ^ 2))) + (-2 * B * (A ^ 2))) := by
    have he : ((-2 * (A ^ 2)) + (B * (-1 + (B ^ 2))) + (-2 * B * (A ^ 2))) =
      (700 + (b ^ 3) + (27 * (b ^ 2)) + (56 * (a ^ 3)) + (240 * b) + (396 * (a ^ 2)) + (920 * a) + (12 * a * (b ^ 2)) + (46 * b * (a ^ 2)) + (212 * a * b)) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h3 : 0 < ((-1 * (A ^ 2)) + (B * (-1 + (B ^ 2))) + (-1 * A * B) + (-1 * A * (B ^ 2)) + (-1 * B * (A ^ 2))) := by
    have he : ((-1 * (A ^ 2)) + (B * (-1 + (B ^ 2))) + (-1 * A * B) + (-1 * A * (B ^ 2)) + (-1 * B * (A ^ 2))) =
      (620 + (b ^ 3) + (26 * (b ^ 2)) + (44 * (a ^ 3)) + (222 * b) + (322 * (a ^ 2)) + (778 * a) + (11 * a * (b ^ 2)) + (39 * b * (a ^ 2)) + (187 * a * b)) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h4 : 0 < ((-1 * (((-1 * A * (-1 + (B ^ 2))) + (2 * A * B) + (2 * A * (B ^ 2))) ^ 2)) + ((1/4 : ℝ) * (-1 + (2 * (B ^ 3)) + (3 * (B ^ 2))) * (-1 + (B ^ 2) + (2 * (A ^ 2)) + (2 * B * (A ^ 2))))) := by
    have he : ((-1 * (((-1 * A * (-1 + (B ^ 2))) + (2 * A * B) + (2 * A * (B ^ 2))) ^ 2)) + ((1/4 : ℝ) * (-1 + (2 * (B ^ 3)) + (3 * (B ^ 2))) * (-1 + (B ^ 2) + (2 * (A ^ 2)) + (2 * B * (A ^ 2))))) =
      (32500 + ((1/2 : ℝ) * (b ^ 5)) + (416 * (a ^ 5)) + (430 * (b ^ 3)) + (3950 * (b ^ 2)) + (5040 * (a ^ 4)) + (18000 * b) + (24280 * (a ^ 3)) + (58100 * (a ^ 2)) + (69000 * a) + ((93/4 : ℝ) * (b ^ 4)) + (10 * a * (b ^ 4)) + (302 * (a ^ 3) * (b ^ 2)) + (369 * a * (b ^ 3)) + (568 * b * (a ^ 4)) + (2151 * (a ^ 2) * (b ^ 2)) + (5070 * a * (b ^ 2)) + (5448 * b * (a ^ 3)) + (19470 * b * (a ^ 2)) + (30700 * a * b) + ((157/2 : ℝ) * (a ^ 2) * (b ^ 3))) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h5 : 0 < ((-1 * (A ^ 2)) + (-1 * (B ^ 2)) + (B * (-1 + (B ^ 2))) + (-2 * A * (B ^ 2))) := by
    have he : ((-1 * (A ^ 2)) + (-1 * (B ^ 2)) + (B * (-1 + (B ^ 2))) + (-2 * A * (B ^ 2))) =
      (476 + (b ^ 3) + (24 * (b ^ 2)) + (32 * (a ^ 3)) + (188 * b) + (239 * (a ^ 2)) + (588 * a) + (10 * a * (b ^ 2)) + (32 * b * (a ^ 2)) + (156 * a * b)) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h6 : 0 < ((B * (-1 + (B ^ 2))) + (-2 * A * B) + (-2 * A * (B ^ 2))) := by
    have he : ((B * (-1 + (B ^ 2))) + (-2 * A * B) + (-2 * A * (B ^ 2))) =
      (540 + (b ^ 3) + (25 * (b ^ 2)) + (32 * (a ^ 3)) + (204 * b) + (248 * (a ^ 2)) + (636 * a) + (10 * a * (b ^ 2)) + (32 * b * (a ^ 2)) + (162 * a * b)) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h7 : 0 < ((-1 * (((B ^ 3) + (B * (A ^ 2)) + (-1 * B * (-1 + (B ^ 2))) + (2 * A * B)) ^ 2)) + ((1/4 : ℝ) * ((-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))) ^ 2))) := by
    have he : ((-1 * (((B ^ 3) + (B * (A ^ 2)) + (-1 * B * (-1 + (B ^ 2))) + (2 * A * B)) ^ 2)) + ((1/4 : ℝ) * ((-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))) ^ 2))) =
      (24948 + (4 * (b ^ 4)) + (144 * (b ^ 3)) + (240 * (a ^ 6)) + (1928 * (b ^ 2)) + (3144 * (a ^ 5)) + (11376 * b) + (49530 * (a ^ 3)) + (69480 * a) + (80430 * (a ^ 2)) + ((68445/4 : ℝ) * (a ^ 4)) + ((a ^ 2) * (b ^ 4)) + (4 * a * (b ^ 4)) + (16 * (a ^ 3) * (b ^ 3)) + (95 * (a ^ 4) * (b ^ 2)) + (100 * (a ^ 2) * (b ^ 3)) + (208 * a * (b ^ 3)) + (248 * b * (a ^ 5)) + (809 * (a ^ 3) * (b ^ 2)) + (2578 * (a ^ 2) * (b ^ 2)) + (2678 * b * (a ^ 4)) + (3644 * a * (b ^ 2)) + (11538 * b * (a ^ 3)) + (24796 * b * (a ^ 2)) + (26584 * a * b)) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h8 : 0 < ((-1 * (((B ^ 2) + (B ^ 3) + (A * B) + (A * (B ^ 2)) + (-1 * B * (-1 + (B ^ 2)))) ^ 2)) + ((1/4 : ℝ) * (-1 + (2 * (B ^ 3)) + (3 * (B ^ 2))) * (-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))))) := by
    have he : ((-1 * (((B ^ 2) + (B ^ 3) + (A * B) + (A * (B ^ 2)) + (-1 * B * (-1 + (B ^ 2)))) ^ 2)) + ((1/4 : ℝ) * (-1 + (2 * (B ^ 3)) + (3 * (B ^ 2))) * (-1 + (A ^ 2) + (2 * (B ^ 2)) + (2 * A * (B ^ 2))))) =
      (105300 + (2 * (b ^ 5)) + (89 * (b ^ 4)) + (768 * (a ^ 6)) + (1576 * (b ^ 3)) + (10528 * (a ^ 5)) + (13873 * (b ^ 2)) + (59988 * (a ^ 4)) + (60660 * b) + (181852 * (a ^ 3)) + (279940 * a) + (309333 * (a ^ 2)) + (a * (b ^ 5)) + (19 * (a ^ 2) * (b ^ 4)) + (144 * (a ^ 3) * (b ^ 3)) + (544 * (a ^ 4) * (b ^ 2)) + (1024 * b * (a ^ 5)) + (2137 * a * (b ^ 3)) + (4910 * (a ^ 3) * (b ^ 2)) + (11640 * b * (a ^ 4)) + (24795 * a * (b ^ 2)) + (52794 * b * (a ^ 3)) + (119427 * b * (a ^ 2)) + (134744 * a * b) + ((165/2 : ℝ) * a * (b ^ 4)) + ((1925/2 : ℝ) * (a ^ 2) * (b ^ 3)) + ((66293/4 : ℝ) * (a ^ 2) * (b ^ 2))) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  have h9 : 0 < ((-1 * (((2 * (B ^ 2)) + (2 * (B ^ 3)) + (-1 * B * (-1 + (B ^ 2)))) ^ 2)) + ((4/9 : ℝ) * ((-1 + (2 * (B ^ 3)) + (3 * (B ^ 2))) ^ 2))) := by
    have he : ((-1 * (((2 * (B ^ 2)) + (2 * (B ^ 3)) + (-1 * B * (-1 + (B ^ 2)))) ^ 2)) + ((4/9 : ℝ) * ((-1 + (2 * (B ^ 3)) + (3 * (B ^ 2))) ^ 2))) =
      ((4270000/9 : ℝ) + (1003 * (b ^ 4)) + (256768 * (a ^ 4)) + (312000 * b) + (1248000 * a) + ((7/9 : ℝ) * (b ^ 6)) + ((130/3 : ℝ) * (b ^ 5)) + ((28672/9 : ℝ) * (a ^ 6)) + ((111080/9 : ℝ) * (b ^ 3)) + ((133120/3 : ℝ) * (a ^ 5)) + ((255400/3 : ℝ) * (b ^ 2)) + ((4086400/3 : ℝ) * (a ^ 2)) + ((7109120/9 : ℝ) * (a ^ 3)) + (16048 * a * (b ^ 3)) + (96288 * (a ^ 2) * (b ^ 2)) + (256768 * b * (a ^ 3)) + ((56/3 : ℝ) * a * (b ^ 5)) + ((560/3 : ℝ) * (a ^ 2) * (b ^ 4)) + ((2600/3 : ℝ) * a * (b ^ 4)) + ((8960/3 : ℝ) * (a ^ 4) * (b ^ 2)) + ((8960/9 : ℝ) * (a ^ 3) * (b ^ 3)) + ((14336/3 : ℝ) * b * (a ^ 5)) + ((20800/3 : ℝ) * (a ^ 2) * (b ^ 3)) + ((83200/3 : ℝ) * (a ^ 3) * (b ^ 2)) + ((166400/3 : ℝ) * b * (a ^ 4)) + ((444320/3 : ℝ) * a * (b ^ 2)) + ((1777280/3 : ℝ) * b * (a ^ 2)) + ((2043200/3 : ℝ) * a * b)) := by
      dsimp [a,b]
      ring
    rw [he]
    positivity
  intro k
  fin_cases k
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h2 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h2 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h2 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h2 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h2 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h2 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h0 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h1 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h3 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h7 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h4 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h5 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h6 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h8 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
  · intro q hq
    fin_cases q <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hq
    · convert h9 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h9 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h9 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h9 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h9 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring
    · convert h9 using 1 <;>
        simp only [gap, threshold, rawNum, leftRad, rightRad, values, selected, frame, Matrix.cons_val,
          Fin.isValue, Fin.reduceFinMk, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, Fin.ext_iff, rad, numerator] <;> norm_num <;> ring

theorem rad_positive (x y z : ℝ) (hx : 1 < x) (hy : 1 < y)
    (hz : 1 < z) : 0 < rad x y z := by
  have hp : 0 < 2*x*y*z := by positivity
  unfold rad
  nlinarith [sq_nonneg (x-1),sq_nonneg (y-1),sq_nonneg (z-1)]

private theorem raw_cos_lt_of_square (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (q : Fin 6) (c : ℝ) (hc : 0 < c)
    (hgap : (rawNum x q)^2 < c^2 * leftRad x q * rightRad x q) :
    rawCos x q < c := by
  have hl : 0 < leftRad x q := rad_positive _ _ _ (hx _) (hx _) (hx _)
  have hr : 0 < rightRad x q := rad_positive _ _ _ (hx _) (hx _) (hx _)
  let D := Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q)
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr hl) (Real.sqrt_pos.mpr hr)
  have hD2 : D^2 = leftRad x q * rightRad x q := by
    dsimp [D]
    rw [mul_pow, Real.sq_sqrt hl.le, Real.sq_sqrt hr.le]
  have hn : rawNum x q < c*D := by
    by_contra h
    have hge : c*D ≤ rawNum x q := le_of_not_gt h
    have hcp : 0 < c*D := mul_pos hc hD
    have hm : 0 ≤ (rawNum x q-c*D)*(rawNum x q+c*D) :=
      mul_nonneg (sub_nonneg.mpr hge) (by linarith)
    have he : c^2 * leftRad x q * rightRad x q = (c*D)^2 := by
      rw [mul_pow,hD2]
      ring
    rw [he] at hgap
    nlinarith only [hgap,hm]
  change rawNum x q / Real.sqrt (leftRad x q) / Real.sqrt (rightRad x q) < c
  rw [div_div]
  exact (div_lt_iff₀ hD).mpr hn

private theorem raw_cos_lt_zero (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (q : Fin 6) (hn : rawNum x q < 0) : rawCos x q < 0 := by
  have hl : 0 < leftRad x q := rad_positive _ _ _ (hx _) (hx _) (hx _)
  have hr : 0 < rightRad x q := rad_positive _ _ _ (hx _) (hx _) (hx _)
  change rawNum x q / Real.sqrt (leftRad x q) / Real.sqrt (rightRad x q) < 0
  exact div_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos hn (Real.sqrt_pos.mpr hl)) (Real.sqrt_pos.mpr hr)

private theorem cosine_bounds (A B : ℝ) (hA : 1 < A) (hB : 4*A+5 < B) :
    ∀ k : Fin 64, ∀ q ∈ useful k, rawCos (values A B k) q < threshold k := by
  intro k q hq
  have hx : ∀ i, 1 < values A B k i := by
    intro i
    unfold values
    split_ifs <;> linarith
  have hg := continuous_gaps A B hA hB k q hq
  by_cases hc : threshold k = 0
  · simp only [gap,hc,if_pos] at hg
    rw [hc]
    exact raw_cos_lt_zero _ hx q (by linarith)
  · have hcpos : 0 < threshold k := by
      fin_cases k <;>
        norm_num [threshold, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk] at hc <;>
        norm_num [threshold, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk]
    rw [gap,if_neg hc] at hg
    exact raw_cos_lt_of_square _ hx q _ hcpos (by linarith)

private theorem clipped_arccos_lower (q t : ℝ) (ht0 : 0 ≤ t)
    (htpi : t ≤ Real.pi) (hc : -1 < Real.cos t) (hq : q < Real.cos t) :
    t < Real.arccos (max (-1) (min q 1)) := by
  have hclip : max (-1) (min q 1) < Real.cos t :=
    max_lt hc ((min_le_left q 1).trans_lt hq)
  have h := Real.arccos_lt_arccos (le_max_left (-1) (min q 1)) hclip
    (Real.cos_le_one t)
  rw [Real.arccos_cos ht0 htpi] at h
  exact h

private theorem angle_bounds (A B : ℝ) (hA : 1 < A) (hB : 4*A+5 < B) :
    ∀ k : Fin 64, ∀ q ∈ useful k,
      angleFloor k < extendedAngle (values A B k) q := by
  intro k q hq
  have hb := cosine_bounds A B hA hB k q hq
  have hpi := Real.pi_pos
  have hsqrt : (2/3:ℝ) < Real.sqrt 2 / 2 := by
    nlinarith [Real.sqrt_nonneg (2:ℝ),Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hc : threshold k ≤ Real.cos (angleFloor k) := by
    fin_cases k <;>
      norm_num [threshold,angleFloor,Matrix.cons_val,Fin.isValue,Fin.reduceFinMk,Real.cos_pi_div_three,
        Real.cos_pi_div_two,Real.cos_pi_div_four] <;> linarith
  have ht0 : 0 ≤ angleFloor k := by fin_cases k <;> simp [angleFloor,Matrix.cons_val,Fin.isValue,Fin.reduceFinMk] <;> positivity
  have htpi : angleFloor k ≤ Real.pi := by fin_cases k <;> simp [angleFloor,Matrix.cons_val,Fin.isValue,Fin.reduceFinMk] <;> linarith
  have hcos : -1 < Real.cos (angleFloor k) := by
    fin_cases k <;>
      norm_num [angleFloor,Matrix.cons_val,Fin.isValue,Fin.reduceFinMk,Real.cos_pi_div_three,Real.cos_pi_div_two,
        Real.cos_pi_div_four] <;> linarith [Real.sqrt_nonneg (2:ℝ)]
  exact clipped_arccos_lower _ _ ht0 htpi hcos (hb.trans_le hc)

-- Every selected B edge remains in the sum, including unused middle/other edges.
-- No nondegeneracy condition and no desired angle estimate is a hypothesis.
-- The finite sum budget checks all 64 actual masks within this declaration.
set_option maxHeartbeats 4000000 in
private theorem mask_two_length_angle_sum (A B : ℝ)
    (hA : 1 < A) (hB : 4*A+5 < B) (k : Fin 64)
    (hcount : 2 ≤ (selected k).card) :
    ((selected k).card : ℝ)*Real.pi/4 <
      ∑ q ∈ selected k, extendedAngle (values A B k) q := by
  have hnonempty : (useful k).Nonempty := by
    fin_cases k <;>
      norm_num [selected, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hcount <;>
      norm_num [useful, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff]
  have hsub : useful k ⊆ selected k := by fin_cases k <;> decide
  have hsum : ((useful k).card : ℝ)*angleFloor k <
      ∑ q ∈ useful k, extendedAngle (values A B k) q := by
    have h := Finset.sum_lt_sum_of_nonempty hnonempty
      (angle_bounds A B hA hB k)
    simpa only [Finset.sum_const, nsmul_eq_mul] using h
  have hrest : (∑ q ∈ useful k, extendedAngle (values A B k) q) ≤
      ∑ q ∈ selected k, extendedAngle (values A B k) q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun q _ _ => Real.arccos_nonneg _)
  have hbudget : ((selected k).card : ℝ)*Real.pi/4 ≤
      ((useful k).card : ℝ)*angleFloor k := by
    have hp := Real.pi_pos
    fin_cases k <;>
      norm_num [selected, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.ext_iff] at hcount <;>
      norm_num [selected, useful, angleFloor, Matrix.cons_val, Fin.isValue,
        Fin.reduceFinMk, Fin.ext_iff] <;> linarith
  exact hbudget.trans_lt (hsum.trans_le hrest)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem selected_surjective :
    ∀ s : Finset (Fin 6), ∃ k : Fin 64, selected k = s := by
  decide

-- The complete source estimate for any actual subset of the six original slots.
-- The cardinality and sum are computed from the same S, with no relabeling input.
theorem two_length_angle_sum (A B : ℝ) (hA : 1 < A) (hB : 4*A+5 < B)
    (S : Finset (Fin 6)) (hS : 2 ≤ S.card) :
    (S.card : ℝ)*Real.pi/4 <
      ∑ q ∈ S, extendedAngle (fun j => if j ∈ S then B else A) q := by
  obtain ⟨k,hk⟩ := selected_surjective S
  have hcount : 2 ≤ (selected k).card := by rw [hk]; exact hS
  have h := mask_two_length_angle_sum A B hA hB k hcount
  have hvalues : values A B k = (fun j => if j ∈ S then B else A) := by
    funext j
    simp only [values, hk]
  rw [hvalues, hk] at h
  exact h

end D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
