/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229589Strip.result)
Row: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
horizontal: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
between: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
Valid: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
cl: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
T: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
initial: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
W: proof_shape=bind-only; consumers=HardinA229589Strip.finite_certificate
-/

import Mathlib.Data.Matrix.Block
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.Tactic

/-! Finite class data consumed by the registered settlement. -/
open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
abbrev Row := Fin 4 → Fin 3
def horizontal : Finset (Fin 4 × Fin 4) := ∅
def between : Finset (Fin 4 × Fin 4) :=
  {(0, 0), (1, 1), (2, 2), (3, 3), (1, 0), (2, 1), (3, 2)}
def Valid (_ : Row) (d : ℕ) : Prop := d ≤ 1
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (d ≤ 1))
def cl (p : Row) (d : ℕ) : Fin 28 :=
  if d = 1 then (HardinA233177PairTransfer.cls (p 0, p 1, p 2, p 3)).castAdd 14
  else if d = 0 then (HardinA233177PairTransfer.cls (p 0, p 1, p 2, p 3)).natAdd 14
  else 27
def T : Matrix (Fin 28) (Fin 28) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 14 ⊕ Fin 14 ≃ Fin 28)
    (finSumFinEquiv : Fin 14 ⊕ Fin 14 ≃ Fin 28)
    (Matrix.fromBlocks (HardinA233259PairTransferCore.Q)
      (![![0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0],
      ![0, 3, 3, 2, 2, 0, 2, 1, 2, 0, 1, 1, 1, 2],
      ![0, 1, 3, 2, 1, 3, 2, 1, 0, 0, 1, 2, 1, 1],
      ![0, 1, 0, 2, 3, 2, 1, 1, 2, 2, 1, 2, 1, 2],
      ![0, 2, 2, 2, 1, 1, 0, 1, 2, 2, 2, 0, 2, 1],
      ![0, 1, 0, 0, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2],
      ![0, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 0, 0, 0],
      ![0, 2, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 2],
      ![0, 1, 2, 2, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2],
      ![1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 0, 2, 2],
      ![1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 2],
      ![0, 0, 1, 2, 1, 2, 0, 2, 2, 1, 1, 0, 1, 0],
      ![1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 2, 2, 1, 1],
      ![1, 1, 1, 3, 2, 1, 1, 0, 2, 2, 1, 1, 1, 1]])
      (0)
      (HardinA233259PairTransferCore.Q))
def initial : Fin 28 → ℤ := ![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def terminal : Fin 28 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 13 → Fin 28 → ℤ :=
  Fin.append (fun k : Fin 9 => Fin.append
    (if k = 1 then HardinA233259PairTransferCore.weights else fun i : Fin 14 =>
      (if i = 0 then 3 else 6) * HardinA233259PairTransferPowers.W k (![0, 9, 5, 3, 13, 2, 6, 12, 8, 1, 10, 11, 7, 4] i))
    ((![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![24, 120, 108, 120, 108, 108, 78, 78, 108, 120, 108, 78, 78, 108],
      ![918, 1458, 864, 1350, 1026, 828, 552, 636, 870, 1350, 1020, 534, 600, 954],
      ![9756, 13428, 8604, 12960, 8244, 8646, 5994, 5064, 7998, 13104, 8562, 4008, 4680, 7536],
      ![94314, 119838, 76362, 112416, 63270, 74778, 51804, 40074, 68112, 112506, 68118, 28812, 36192, 57588],
      ![831588, 1009788, 641940, 936912, 485412, 632940, 434550, 317478, 567084, 938472, 535548, 206706, 278040, 434454],
      ![7010946, 8253702, 5240520, 7611714, 3699918, 5179032, 3530232, 2478888, 4587048, 7595226, 4150926, 1489374, 2120994, 3261744],
      ![57312234, 65977182, 41858244, 60598062, 28005030, 41429916, 28088910, 19128078, 36400932, 60313734, 31877478, 10745028, 16094718, 24412014],
      ![458298864, 518711256, 328905972, 474978708, 210671424, 325920204, 220056066, 146210994, 284630940, 471916548, 242811432, 77480586, 121405212, 181963818]]) k))
    (![![276067116, 276067116, 174315240, 246878604, 72563364, 174315240, 113902848, 60412392, 145126728, 241992036, 96865308, 12150972, 43374852, 55525824, 3604507650, 4025701494, 2551529736, 3677491602, 1576344222, 2530713816, 1703069676, 1108940292, 2199541464, 3648822642, 1836399942, 558174258, 910677618, 1350878292],
      ![1924732044, 1924732044, 1215320112, 1721228292, 505908180, 1215320112, 794126268, 421193844, 1011816360, 1687153212, 675336852, 84714336, 302404428, 387118764, 27983643750, 30920192154, 19590697692, 28190758266, 11740112730, 19445570964, 13050899334, 8355856590, 16834926492, 27940236714, 13804279794, 4017095208, 6797386242, 9991982502],
      ![13419160488, 13419160488, 8473165704, 12000336624, 3527170920, 8473165704, 5536617300, 2936548404, 7054341840, 11762757792, 4708415952, 590622516, 2108347056, 2698969572, 214992582372, 235466084700, 149145632964, 214333304256, 87079997484, 148133816604, 99197452926, 62609667174, 127829237508, 212234286024, 103222148148, 28882447938, 50516232336, 73664261622],
      ![93557866428, 93557866428, 59074581096, 83665876860, 24591295764, 59074581096, 38601078768, 20473502328, 49182591528, 82009474164, 32826882636, 4117793436, 14699306196, 18817099632, 1637603470098, 1780343928054, 1127405471616, 1618343660538, 643570636446, 1120351129776, 748820220696, 466860643056, 964125058392, 1601253691722, 768320699022, 207471087990, 373986155322, 541477118160]])

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
