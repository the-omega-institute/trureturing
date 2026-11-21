/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Large00
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Large00.strict_on_triples
   digest: Full-pair integer certificates for large exceptional lifts. -/

import D5.S3.Arith.Divisors.ErdosNicolas.FiniteChecker
import D5.S3.Arith.Divisors.ErdosNicolas.Classification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Arith.ErdosNicolas.Data.Large00

open D5.S3.Arith.ErdosNicolas

private def certificates : List NumberCertificate :=
  [
    ⟨228, [(2, 2), (3, 1), (19, 1)], [1, 2, 3, 4, 6, 12, 19, 38, 57, 76, 114, 228]⟩,
    ⟨4332, [(2, 2), (3, 1), (19, 2)], [1, 2, 3, 4, 6, 12, 19, 38, 57, 76, 114, 228, 361, 722,
      1083, 1444, 2166, 4332]⟩,
    ⟨456, [(2, 3), (3, 1), (19, 1)], [1, 2, 3, 4, 6, 8, 12, 19, 24, 38, 57, 76, 114, 152, 228,
      456]⟩,
    ⟨8664, [(2, 3), (3, 1), (19, 2)], [1, 2, 3, 4, 6, 8, 12, 19, 24, 38, 57, 76, 114, 152, 228,
      361, 456, 722, 1083, 1444, 2166, 2888, 4332, 8664]⟩,
    ⟨1140, [(2, 2), (3, 1), (5, 1), (19, 1)], [1, 2, 3, 4, 5, 6, 10, 12, 15, 19, 20, 30, 38, 57,
      60, 76, 95, 114, 190, 228, 285, 380, 570, 1140]⟩,
    ⟨21660, [(2, 2), (3, 1), (5, 1), (19, 2)], [1, 2, 3, 4, 5, 6, 10, 12, 15, 19, 20, 30, 38,
      57, 60, 76, 95, 114, 190, 228, 285, 361, 380, 570, 722, 1083, 1140, 1444, 1805, 2166,
      3610, 4332, 5415, 7220, 10830, 21660]⟩,
    ⟨2280, [(2, 3), (3, 1), (5, 1), (19, 1)], [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 19, 20, 24, 30,
      38, 40, 57, 60, 76, 95, 114, 120, 152, 190, 228, 285, 380, 456, 570, 760, 1140, 2280]⟩,
    ⟨43320, [(2, 3), (3, 1), (5, 1), (19, 2)], [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 19, 20, 24, 30,
      38, 40, 57, 60, 76, 95, 114, 120, 152, 190, 228, 285, 361, 380, 456, 570, 722, 760, 1083,
      1140, 1444, 1805, 2166, 2280, 2888, 3610, 4332, 5415, 7220, 8664, 10830, 14440, 21660,
      43320]⟩,
    ⟨3420, [(2, 2), (3, 2), (5, 1), (19, 1)], [1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 19, 20, 30,
      36, 38, 45, 57, 60, 76, 90, 95, 114, 171, 180, 190, 228, 285, 342, 380, 570, 684, 855,
      1140, 1710, 3420]⟩,
    ⟨64980, [(2, 2), (3, 2), (5, 1), (19, 2)], [1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 19, 20, 30,
      36, 38, 45, 57, 60, 76, 90, 95, 114, 171, 180, 190, 228, 285, 342, 361, 380, 570, 684,
      722, 855, 1083, 1140, 1444, 1710, 1805, 2166, 3249, 3420, 3610, 4332, 5415, 6498, 7220,
      10830, 12996, 16245, 21660, 32490, 64980]⟩,
    ⟨4560, [(2, 4), (3, 1), (5, 1), (19, 1)], [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 19, 20, 24,
      30, 38, 40, 48, 57, 60, 76, 80, 95, 114, 120, 152, 190, 228, 240, 285, 304, 380, 456, 570,
      760, 912, 1140, 1520, 2280, 4560]⟩,
    ⟨86640, [(2, 4), (3, 1), (5, 1), (19, 2)], [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 19, 20, 24,
      30, 38, 40, 48, 57, 60, 76, 80, 95, 114, 120, 152, 190, 228, 240, 285, 304, 361, 380, 456,
      570, 722, 760, 912, 1083, 1140, 1444, 1520, 1805, 2166, 2280, 2888, 3610, 4332, 4560,
      5415, 5776, 7220, 8664, 10830, 14440, 17328, 21660, 28880, 43320, 86640]⟩,
    ⟨6840, [(2, 3), (3, 2), (5, 1), (19, 1)], [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 19, 20,
      24, 30, 36, 38, 40, 45, 57, 60, 72, 76, 90, 95, 114, 120, 152, 171, 180, 190, 228, 285,
      342, 360, 380, 456, 570, 684, 760, 855, 1140, 1368, 1710, 2280, 3420, 6840]⟩,
    ⟨129960, [(2, 3), (3, 2), (5, 1), (19, 2)], [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 19, 20,
      24, 30, 36, 38, 40, 45, 57, 60, 72, 76, 90, 95, 114, 120, 152, 171, 180, 190, 228, 285,
      342, 360, 361, 380, 456, 570, 684, 722, 760, 855, 1083, 1140, 1368, 1444, 1710, 1805,
      2166, 2280, 2888, 3249, 3420, 3610, 4332, 5415, 6498, 6840, 7220, 8664, 10830, 12996,
      14440, 16245, 21660, 25992, 32490, 43320, 64980, 129960]⟩
  ]

def triples : List (ℕ × ℕ × ℕ) :=
  [(12, 19, 1), (12, 19, 2), (24, 19, 1), (24, 19, 2), (60, 19, 1), (60, 19, 2), (120, 19, 1),
  (120, 19, 2), (180, 19, 1), (180, 19, 2), (240, 19, 1), (240, 19, 2), (360, 19, 1), (360, 19,
  2)]

private theorem chunk_checked : certificates.all (checkGood 4294967296) = true := by decide +kernel

private theorem values_eq :
    certifiedValues certificates = (triples.map largeLiftValue).toFinset := by decide +kernel

private theorem outside : ∀ v ∈ triples,
    largeLiftValue v ∉ exceptions := by decide +kernel

theorem strict_on_triples : ∀ v ∈ triples,
    hHat (largeLiftValue v) < ((largeLiftValue v).divisors.card : ℚ) := by
  intro v hv
  have hg : Good (largeLiftValue v) := good_of_mem_certifiedValues chunk_checked
    (by rw [values_eq]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨v, hv, rfl⟩))
  simpa only [Good, outside v hv, if_false] using hg

#print axioms chunk_checked
#print axioms strict_on_triples

end D5.S3.Arith.ErdosNicolas.Data.Large00
