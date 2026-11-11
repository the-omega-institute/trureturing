/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.finite_certificate
   digest: The literal 7-column three-state strip satisfies Hardin's order-4 recurrence. -/

/-
admission_basis: open-problem-resolution (#29204; Proved)
escape_witness: none
Finite row tables normalize the row quotient; their helpers are bind-only.
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic

/-! A finite row quotient transports the recurrence to every strip height. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def T7 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n × Fin 7 → Fin 3 => Legal f)).card

private def codes : List (Fin 2187) := [0, 1, 3, 5, 9, 10, 16, 17, 27, 28, 30, 32, 48, 50, 52, 53, 81, 82, 84, 86, 90, 91, 97, 98, 144, 145, 151, 152, 156, 158, 160, 161, 243, 244, 246, 248, 252, 253, 259, 260, 270, 271, 273, 275, 291, 293, 295, 296, 432, 433, 435, 437, 453, 455, 457, 458, 468, 469, 475, 476, 480, 482, 484, 485, 729, 730, 732, 734, 738, 739, 745, 746, 756, 757, 759, 761, 777, 779, 781, 782, 810, 811, 813, 815, 819, 820, 826, 827, 873, 874, 880, 881, 885, 887, 889, 890, 1296, 1297, 1299, 1301, 1305, 1306, 1312, 1313, 1359, 1360, 1366, 1367, 1371, 1373, 1375, 1376, 1404, 1405, 1407, 1409, 1425, 1427, 1429, 1430, 1440, 1441, 1447, 1448, 1452, 1454, 1456, 1457, 1701, 1702, 1704, 1706, 1710, 1711, 1717, 1718, 1728, 1729, 1731, 1733, 1749, 1751, 1753, 1754, 1890, 1891, 1893, 1895, 1911, 1913, 1915, 1916, 1926, 1927, 1933, 1934, 1938, 1940, 1942, 1943, 2025, 2026, 2028, 2030, 2034, 2035, 2041, 2042, 2088, 2089, 2095, 2096, 2100, 2102, 2104, 2105, 2133, 2134, 2136, 2138, 2154, 2156, 2158, 2159, 2169, 2170, 2176, 2177, 2181, 2183, 2185, 2186]
private def classes : Array (Fin 16) := #[0, 0, 0, 10, 0, 10, 0, 0, 0, 5, 5, 0, 0, 0, 0, 0, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 15, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 12, 0, 12, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 11, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 14, 0, 14, 0, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 8, 0, 8, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 15, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 5, 0, 13, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 11, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14, 0, 0, 0, 0, 0, 7, 7, 0, 0, 0, 9, 0, 9, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 11, 0, 11, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 14, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 13, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 15, 0, 15, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 15, 0, 15, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 13, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 11, 0, 11, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 9, 0, 9, 0, 0, 0, 7, 7, 0, 0, 0, 0, 0, 14, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 12, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 13, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 15, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 8, 0, 8, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 0, 14, 0, 14, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 12, 0, 12, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 15, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 13, 0, 0, 0, 0, 0, 5, 5, 0, 0, 0, 10, 0, 10, 0, 0, 0]

def classify (r : Row 7) : Fin 16 := classes[(finFunctionFinEquiv r).val]!
def quotient : Matrix (Fin 16) (Fin 16) ℤ :=
  ![![5, 5, 3, 3, 4, 4, 2, 2, 3, 3, 3, 3, 1, 1, 0, 0], ![4, 4, 3, 3, 4, 4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1], ![3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 2, 2, 0, 0], ![1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2], ![4, 4, 2, 2, 4, 4, 2, 2, 3, 3, 1, 1, 1, 1, 0, 0], ![4, 4, 2, 2, 4, 4, 2, 2, 2, 2, 3, 3, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 1, 1], ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2, 2, 3, 3], ![3, 3, 3, 3, 3, 3, 1, 1, 3, 3, 3, 3, 1, 1, 0, 0], ![2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 1, 1], ![4, 4, 3, 3, 2, 2, 1, 1, 3, 3, 3, 3, 2, 2, 0, 0], ![2, 2, 3, 3, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2], ![2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 0, 0], ![2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2], ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 3, 3], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2]]
def weights : Fin 16 → ℤ := ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]

private theorem codes_table : legalCodes 7 = codes := by decide +kernel

private def classCount (r : Row 7) (s : Fin 16) : ℤ :=
  (codes.map (fun c => if compatible r (decode 7 c) ∧ classify (decode 7 c) = s
    then (1 : ℤ) else 0)).sum

private theorem row_counts_code : ∀ a : Fin 2187, rowLegal (decode 7 a) →
    ∀ s : Fin 16, classCount (decode 7 a) s = quotient (classify (decode 7 a)) s := by
  decide +kernel

private theorem row_counts : ∀ r : Row 7, rowLegal r → ∀ s : Fin 16,
    (∑ c : Row 7, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0) =
      quotient (classify r) s := by
  intro r hr s
  have hs := row_sum 7 (fun c => if compatible r c ∧ classify c = s then (1 : ℤ) else 0)
  simp only [← ite_and] at hs
  rw [hs, codes_table]
  have he : decode 7 (finFunctionFinEquiv r) = r :=
    Equiv.symm_apply_apply finFunctionFinEquiv r
  have hc := row_counts_code (finFunctionFinEquiv r) (by rw [he]; exact hr) s
  rw [he] at hc
  exact hc

private theorem initial_weights : ∀ s : Fin 16,
    (∑ c : Row 7, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) = weights s := by
  intro s
  have hs := row_sum 7 (fun c => if classify c = s then (1 : ℤ) else 0)
  simp only [← ite_and] at hs
  rw [hs, codes_table]
  revert s
  decide +kernel

private def W : Fin 6 → Fin 16 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], ![42, 36, 38, 28, 34, 38, 32, 22, 34, 26, 36, 30, 26, 28, 14, 22], ![1416, 1182, 1242, 816, 1140, 1248, 990, 588, 1134, 804, 1194, 924, 840, 858, 348, 630], ![45738, 37944, 39852, 25362, 36846, 40122, 31428, 17838, 36576, 25434, 38484, 29250, 27054, 27252, 10386, 19728], ![1463994, 1212948, 1273968, 805194, 1179630, 1283202, 1002780, 563382, 1170396, 810486, 1231416, 932526, 865890, 869832, 326862, 628020], ![46776042, 38745216, 40695048, 25686558, 37692054, 40993938, 32021892, 17954622, 37393164, 25873506, 39342996, 29773170, 27666846, 27778788, 10409634, 20046852]]
private theorem powers_table : ∀ j : Fin 6,
    (quotient ^ j.val).mulVec (1 : Fin 16 → ℤ) = W j := by
  apply TransferMatrix.tabulatedPowers
  · exact List.ofFn_inj.mp rfl
  · intro j
    fin_cases j <;> exact List.ofFn_inj.mp rfl

private theorem vector_relation :
    (quotient ^ (1+4)).mulVec (1 : Fin 16 → ℤ) =
      ∑ j : Fin 4, (![-810, 972, -351, 42] : Fin 4 → ℤ) j •
        (quotient ^ (1+j.val)).mulVec (1 : Fin 16 → ℤ) := by
  have hp : (quotient ^ (1+4)).mulVec (1 : Fin 16 → ℤ) = W 5 := powers_table 5
  rw [hp]
  have hc : (∑ j : Fin 4, (![-810, 972, -351, 42] : Fin 4 → ℤ) j •
      (quotient ^ (1+j.val)).mulVec (1 : Fin 16 → ℤ)) =
      ∑ j : Fin 4, (![-810, 972, -351, 42] : Fin 4 → ℤ) j • W ⟨1+j.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [powers_table ⟨1+j.val, by omega⟩]
  rw [hc]
  exact List.ofFn_inj.mp (by decide +kernel)

theorem finite_certificate :
    (∀ r : Row 7, rowLegal r → ∀ s : Fin 16,
      (∑ c : Row 7, if rowLegal c ∧ compatible r c ∧ classify c = s then (1 : ℤ) else 0) =
        quotient (classify r) s) ∧
    (∀ s : Fin 16, (∑ c : Row 7, if rowLegal c ∧ classify c = s then (1 : ℤ) else 0) =
      weights s) ∧
    (quotient ^ (1+4)).mulVec (1 : Fin 16 → ℤ) =
      ∑ j : Fin 4, (![-810, 972, -351, 42] : Fin 4 → ℤ) j •
        (quotient ^ (1+j.val)).mulVec (1 : Fin 16 → ℤ) :=
  ⟨row_counts, initial_weights, vector_relation⟩

private theorem counting_bridge (n : ℕ) :
    (T7 (n+2) : ℤ) = dotProduct weights
      ((quotient^(n+1)).mulVec (1 : Fin 16 → ℤ)) :=
  count_transfer 7 16 classify quotient weights
    finite_certificate.1 finite_certificate.2.1 n

private theorem first_count : T7 1 = 192 := by decide +kernel

private theorem initial_relation : (T7 5 : ℤ) =
    42 * (T7 (4) : ℤ) - 351 * (T7 (3) : ℤ) +
      972 * (T7 (2) : ℤ) - 810 * (T7 (1) : ℤ) := by
  have h1 : (T7 1 : ℤ) = 192 := by exact_mod_cast first_count
  have h2 := counting_bridge 0
  change (T7 2 : ℤ) = dotProduct weights
    ((quotient^1).mulVec (1 : Fin 16 → ℤ)) at h2
  have hp2 := powers_table (1 : Fin 6)
  change (quotient ^ 1).mulVec (1 : Fin 16 → ℤ) = W 1 at hp2
  rw [hp2] at h2
  have h3 := counting_bridge 1
  change (T7 3 : ℤ) = dotProduct weights
    ((quotient^2).mulVec (1 : Fin 16 → ℤ)) at h3
  have hp3 := powers_table (2 : Fin 6)
  change (quotient ^ 2).mulVec (1 : Fin 16 → ℤ) = W 2 at hp3
  rw [hp3] at h3
  have h4 := counting_bridge 2
  change (T7 4 : ℤ) = dotProduct weights
    ((quotient^3).mulVec (1 : Fin 16 → ℤ)) at h4
  have hp4 := powers_table (3 : Fin 6)
  change (quotient ^ 3).mulVec (1 : Fin 16 → ℤ) = W 3 at hp4
  rw [hp4] at h4
  have h5 := counting_bridge 3
  change (T7 5 : ℤ) = dotProduct weights
    ((quotient^4).mulVec (1 : Fin 16 → ℤ)) at h5
  have hp5 := powers_table (4 : Fin 6)
  change (quotient ^ 4).mulVec (1 : Fin 16 → ℤ) = W 4 at hp5
  rw [hp5] at h5
  norm_num [W, weights, dotProduct, Fin.sum_univ_succ] at *
  omega

theorem result (n : ℕ) : (T7 (n+5) : ℤ) =
    42 * (T7 (n+4) : ℤ) - 351 * (T7 (n+3) : ℤ) +
      972 * (T7 (n+2) : ℤ) - 810 * (T7 (n+1) : ℤ) := by
  cases n with
  | zero => exact initial_relation
  | succ n =>
    have h := TransferMatrix.scalarRelationShift quotient weights 4 1
      (![-810, 972, -351, 42] : Fin 4 → ℤ) finite_certificate.2.2 n
    have hb (j : ℕ) : dotProduct weights
        ((quotient ^ (n+1+j)).mulVec (1 : Fin 16 → ℤ)) = (T7 (n+j+2) : ℤ) := by
      rw [show n+1+j = n+j+1 by omega]
      exact (counting_bridge (n+j)).symm
    simp_rw [hb] at h
    norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.sum_empty,
      add_zero, Nat.add_assoc] at h
    simp only [Nat.succ_eq_add_one, Nat.add_assoc]
    linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233154Column
