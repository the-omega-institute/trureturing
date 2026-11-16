/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531Strip.finite_certificate
   digest: Exact HDA defect transfer and Hardin's registered recurrence. -/

/-
admission_basis: open-problem-resolution (#31121; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229531Strip.result)
raw_successors: proof_shape=bind-only; consumers=HardinA229531StripClass0.transition_counts through HardinA229531StripClass11.transition_counts
Row: proof_shape=bind-only; consumers=HardinA229531Strip.result
horizontal: proof_shape=bind-only; consumers=HardinA229531Strip.result
between: proof_shape=bind-only; consumers=HardinA229531Strip.result
Valid: proof_shape=bind-only; consumers=HardinA229531Strip.result
decidableValid: proof_shape=bind-only; consumers=HardinA229531Strip.result
cl: proof_shape=bind-only; consumers=HardinA229531Strip.result
T: proof_shape=bind-only; consumers=HardinA229531Strip.result
initial: proof_shape=bind-only; consumers=HardinA229531Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229531Strip.result
W: proof_shape=bind-only; consumers=HardinA229531Strip.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Logic.Equiv.Fin.Basic
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData

/-! Exact-budget class data for the width-five HDA strip. -/
open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData
open DefectTransfer (bondDefects)
abbrev Row := Fin 5 → Fin 3
def horizontal : Finset (Fin 5 × Fin 5) := HardinA229583StripData.horizontal
def between : Finset (Fin 5 × Fin 5) :=
  HardinA229583StripData.antidiagonal ∪ HardinA229583StripData.antidiagonal.image Prod.swap
def Valid (p : Row) (d : ℕ) : Prop :=
  d ≤ 1 ∧ bondDefects horizontal p p ≤ 1 - d
instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Row) (d : ℕ) : Fin 20 :=
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 1 then 0 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 2 then 1 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 3 then 2 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 4 then 3 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 5 then 4 else
  if d = 1 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 6 then 5 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 1 then 6 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 2 then 7 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 3 then 8 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 4 then 9 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 5 then 10 else
  if d = 0 ∧ bondDefects horizontal p p = 0 ∧ HardinA233126SquareStrip.boundaryClass (true, true) p = 6 then 11 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 1 ≠ p 4 ∧ p 2 ≠ p 3 ∧ p 2 = p 4 ∧ p 3 ≠ p 4) ∨ (p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 1 = p 4 ∧ p 2 ≠ p 3 ∧ p 2 ≠ p 4 ∧ p 3 = p 4)) then 12 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 1 ≠ p 4 ∧ p 2 ≠ p 3 ∧ p 2 ≠ p 4 ∧ p 3 ≠ p 4) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 1 = p 4 ∧ p 2 ≠ p 3 ∧ p 2 ≠ p 4 ∧ p 3 = p 4)) then 13 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 0 = p 4 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 1 = p 4 ∧ p 2 ≠ p 3 ∧ p 2 ≠ p 4 ∧ p 3 ≠ p 4) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 0 = p 4 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 1 ≠ p 4 ∧ p 2 ≠ p 3 ∧ p 2 ≠ p 4 ∧ p 3 = p 4)) then 14 else
  if d = 0 ∧ ((p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 1 ≠ p 4 ∧ p 2 ≠ p 3 ∧ p 2 = p 4 ∧ p 3 ≠ p 4) ∨ (p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 1 ≠ p 4 ∧ p 2 ≠ p 3 ∧ p 2 ≠ p 4 ∧ p 3 = p 4)) then 15 else
  if d = 0 ∧ ((p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 1 = p 4 ∧ p 2 = p 3 ∧ p 2 ≠ p 4 ∧ p 3 ≠ p 4) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 0 ≠ p 4 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 1 = p 4 ∧ p 2 ≠ p 3 ∧ p 2 = p 4 ∧ p 3 ≠ p 4)) then 16 else
  if d = 0 ∧ ((p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 1 ≠ p 4 ∧ p 2 = p 3 ∧ p 2 ≠ p 4 ∧ p 3 ≠ p 4) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 0 ≠ p 4 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 1 = p 4 ∧ p 2 ≠ p 3 ∧ p 2 = p 4 ∧ p 3 ≠ p 4)) then 17 else
  if d = 0 ∧ ((p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 0 ≠ p 4 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 1 ≠ p 4 ∧ p 2 ≠ p 3 ∧ p 2 ≠ p 4 ∧ p 3 ≠ p 4) ∨ (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 0 ≠ p 4 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 1 = p 4 ∧ p 2 = p 3 ∧ p 2 ≠ p 4 ∧ p 3 ≠ p 4)) then 18 else
  19
def T : Matrix (Fin 20) (Fin 20) ℤ :=
  ![![(HardinA233171DiagonalStrip.transfer 1 1 / 32), (HardinA233171DiagonalStrip.transfer 1 2 / 32), (HardinA233171DiagonalStrip.transfer 1 3 / 32), (HardinA233171DiagonalStrip.transfer 1 4 / 32), (HardinA233171DiagonalStrip.transfer 1 5 / 32), (HardinA233171DiagonalStrip.transfer 1 6 / 32), 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2],
    ![(HardinA233171DiagonalStrip.transfer 2 1 / 32), (HardinA233171DiagonalStrip.transfer 2 2 / 32), (HardinA233171DiagonalStrip.transfer 2 3 / 32), (HardinA233171DiagonalStrip.transfer 2 4 / 32), (HardinA233171DiagonalStrip.transfer 2 5 / 32), (HardinA233171DiagonalStrip.transfer 2 6 / 32), 1, 0, 2, 3, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1],
    ![(HardinA233171DiagonalStrip.transfer 3 1 / 32), (HardinA233171DiagonalStrip.transfer 3 2 / 32), (HardinA233171DiagonalStrip.transfer 3 3 / 32), (HardinA233171DiagonalStrip.transfer 3 4 / 32), (HardinA233171DiagonalStrip.transfer 3 5 / 32), (HardinA233171DiagonalStrip.transfer 3 6 / 32), 0, 4, 0, 2, 0, 4, 2, 2, 0, 2, 0, 0, 0, 0],
    ![(HardinA233171DiagonalStrip.transfer 4 1 / 32), (HardinA233171DiagonalStrip.transfer 4 2 / 32), (HardinA233171DiagonalStrip.transfer 4 3 / 32), (HardinA233171DiagonalStrip.transfer 4 4 / 32), (HardinA233171DiagonalStrip.transfer 4 5 / 32), (HardinA233171DiagonalStrip.transfer 4 6 / 32), 1, 3, 1, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0],
    ![(HardinA233171DiagonalStrip.transfer 5 1 / 32), (HardinA233171DiagonalStrip.transfer 5 2 / 32), (HardinA233171DiagonalStrip.transfer 5 3 / 32), (HardinA233171DiagonalStrip.transfer 5 4 / 32), (HardinA233171DiagonalStrip.transfer 5 5 / 32), (HardinA233171DiagonalStrip.transfer 5 6 / 32), 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(HardinA233171DiagonalStrip.transfer 6 1 / 32), (HardinA233171DiagonalStrip.transfer 6 2 / 32), (HardinA233171DiagonalStrip.transfer 6 3 / 32), (HardinA233171DiagonalStrip.transfer 6 4 / 32), (HardinA233171DiagonalStrip.transfer 6 5 / 32), (HardinA233171DiagonalStrip.transfer 6 6 / 32), 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, (HardinA233171DiagonalStrip.transfer 1 1 / 32), (HardinA233171DiagonalStrip.transfer 1 2 / 32), (HardinA233171DiagonalStrip.transfer 1 3 / 32), (HardinA233171DiagonalStrip.transfer 1 4 / 32), (HardinA233171DiagonalStrip.transfer 1 5 / 32), (HardinA233171DiagonalStrip.transfer 1 6 / 32), 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, (HardinA233171DiagonalStrip.transfer 2 1 / 32), (HardinA233171DiagonalStrip.transfer 2 2 / 32), (HardinA233171DiagonalStrip.transfer 2 3 / 32), (HardinA233171DiagonalStrip.transfer 2 4 / 32), (HardinA233171DiagonalStrip.transfer 2 5 / 32), (HardinA233171DiagonalStrip.transfer 2 6 / 32), 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, (HardinA233171DiagonalStrip.transfer 3 1 / 32), (HardinA233171DiagonalStrip.transfer 3 2 / 32), (HardinA233171DiagonalStrip.transfer 3 3 / 32), (HardinA233171DiagonalStrip.transfer 3 4 / 32), (HardinA233171DiagonalStrip.transfer 3 5 / 32), (HardinA233171DiagonalStrip.transfer 3 6 / 32), 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, (HardinA233171DiagonalStrip.transfer 4 1 / 32), (HardinA233171DiagonalStrip.transfer 4 2 / 32), (HardinA233171DiagonalStrip.transfer 4 3 / 32), (HardinA233171DiagonalStrip.transfer 4 4 / 32), (HardinA233171DiagonalStrip.transfer 4 5 / 32), (HardinA233171DiagonalStrip.transfer 4 6 / 32), 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, (HardinA233171DiagonalStrip.transfer 5 1 / 32), (HardinA233171DiagonalStrip.transfer 5 2 / 32), (HardinA233171DiagonalStrip.transfer 5 3 / 32), (HardinA233171DiagonalStrip.transfer 5 4 / 32), (HardinA233171DiagonalStrip.transfer 5 5 / 32), (HardinA233171DiagonalStrip.transfer 5 6 / 32), 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, (HardinA233171DiagonalStrip.transfer 6 1 / 32), (HardinA233171DiagonalStrip.transfer 6 2 / 32), (HardinA233171DiagonalStrip.transfer 6 3 / 32), (HardinA233171DiagonalStrip.transfer 6 4 / 32), (HardinA233171DiagonalStrip.transfer 6 5 / 32), (HardinA233171DiagonalStrip.transfer 6 6 / 32), 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def initial : Fin 20 → ℤ := ![6, 12, 6, 12, 6, 6, 0, 0, 0, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12]
def terminal : Fin 20 → ℤ := ![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 14 → Fin 20 → ℤ :=
  ![![6, 12, 6, 12, 6, 6, 0, 0, 0, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12],
    ![78, 120, 54, 72, 24, 48, 96, 132, 96, 108, 24, 48, 36, 24, 24, 36, 0, 24, 0, 24],
    ![750, 1164, 480, 576, 150, 492, 1332, 2148, 1248, 1656, 504, 912, 336, 180, 276, 384, 0, 276, 0, 276],
    ![7098, 11160, 4350, 5076, 1206, 4812, 17856, 28380, 15240, 20064, 6072, 11856, 3036, 1536, 2664, 3624, 0, 2664, 0, 2664],
    ![67014, 106056, 40338, 46620, 10632, 46140, 217884, 343764, 175548, 227040, 66732, 143736, 27972, 13776, 25356, 34056, 0, 25356, 0, 25356],
    ![632730, 1004136, 378012, 435264, 97590, 438420, 2518824, 3966300, 1943496, 2477352, 709404, 1665360, 261324, 127296, 240084, 320760, 0, 240084, 0, 240084],
    ![5974590, 9492432, 3558474, 4091328, 910866, 4150572, 28121052, 44285772, 20984292, 26440644, 7399848, 18683544, 2456748, 1191288, 2269596, 3025620, 0, 2269596, 0, 2269596],
    ![56418054, 89678652, 33560754, 38562948, 8560668, 39235188, 306407664, 482883900, 222689088, 277971192, 76266396, 204597288, 23157456, 11208276, 21441612, 28558560, 0, 21441612, 0, 21441612],
    ![532766298, 847012032, 316759884, 363883500, 80684370, 370663788, 3278938524, 5171677476, 2333100288, 2889852636, 779441436, 2199146616, 218520564, 105684456, 202514760, 269636268, 0, 202514760, 0, 202514760],
    ![5031053802, 7999171740, 2990632266, 3435200136, 761327754, 3500884236, 34602482352, 54617875596, 24199453176, 29781291876, 7914938988, 23294331768, 2062935864, 997403268, 1912544628, 2546064396, 0, 1912544628, 0, 1912544628],
    ![47509738026, 75540903780, 28239071766, 32435599656, 7187160156, 33062219556, 361115721540, 570375547956, 248961461604, 304718971812, 79956963384, 243862308768, 19478572272, 9416464668, 18061279344, 24042543876, 0, 18061279344, 0, 18061279344],
    ![448649203938, 713365188636, 266661283176, 306284042988, 67861831578, 312225722724, 3734520551016, 5901939472380, 2543909715696, 3099146030724, 804197776632, 2528534642904, 183933219240, 88913743188, 170560379832, 227038523364, 0, 170560379832, 0, 170560379832],
    ![4236736043874, 6736567070532, 2518132037430, 2892277911996, 640807157742, 2948480230596, 38329501122612, 60604183122876, 25843946610108, 31357954013976, 8057917119564, 26009202551280, 1736905017216, 839606609340, 1610663596512, 2143986162864, 0, 1610663596512, 0, 1610663596512],
    ![40008844720734, 63615675366864, 23779388302878, 27312473372616, 6051217107168, 27843566690004, 390884463217968, 618297819662604, 261246780486720, 315872690778540, 80469856901928, 265742857567248, 16402014074604, 7928541986856, 15210039158280, 20246303233140, 0, 15210039158280, 0, 15210039158280]]

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA233255LiteralBridge (rowWeight rowFinish)

/-- The proper successor counts supplied by the frozen saturated scanner certificate. -/
theorem raw_successors (p : Fin 5 → Fin 3) (hp : HardinThinGraphTransport.proper p) (j : Fin 7) :
    32 * (∑ q : Fin 5 → Fin 3,
      if HardinThinGraphTransport.proper q ∧ HardinThinGraphTransport.compatible true p q ∧
        HardinA233126SquareStrip.boundaryClass (true, true) q = j then (1 : ℤ) else 0) =
      HardinA233171DiagonalStrip.transfer
        (HardinA233126SquareStrip.boundaryClass (true, true) p) j := by
  have ha : HardinA233254TriangleStrip.Valid (true, true) p := ⟨rfl, hp, by simp⟩
  have ht := HardinA233171DiagonalStrip.finite_certificate (true, true) p ha j
  have h := HardinA233171DiagonalStrip.class_fibres (true, true) p j
  have hs : ∀ q : Fin 5 → Fin 3,
      rowWeight (true, true) q = 32 ∧ rowFinish (true, true) q = (true, true) := by
    decide +kernel
  simp_rw [(hs _).1, (hs _).2] at h
  rw [← Finset.mul_sum] at h
  exact h.symm.trans ht


end D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData
