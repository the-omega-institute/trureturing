/- GID: D5/S3/Combinatorics/Games/DivisorNimBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every nonempty Divisor Nim board has Grundy value at most twice its smallest heap. -/

import D5.S3.Combinatorics.Games.DivisorNimBoundSmall
import D5.S3.Combinatorics.Games.DivisorNimBoundEight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

open D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic

theorem result : claim := by
  intro P hp hn m hm _hmin
  obtain ⟨k, hk⟩ := exists_depth hn
  obtain ⟨u, hu, hodd, hmu⟩ := valuation_decomposition (hp m hm)
  let v := valuation m
  have hmu' : m = 2 ^ v * u := hmu
  have hm' : 2 ^ v * u ∈ P := by rwa [hmu'] at hm
  have hkv : k ≤ v := hk.1 m hm
  have hodd' : u % 2 = 1 := Nat.odd_iff.mp hodd
  have hbound : grundy P ≤ 2 * (2 ^ v * u) := by
    by_cases hlu : v + 1 ≤ u
    · exact (coarse_bound hp hk hm' le_rfl).trans (coarseBound_le_reference hu hkv hlu)
    have huv : u ≤ v := by omega
    have hv : 0 < v := by omega
    by_cases hex : u = 1 ∧ v ≤ 3
    · rcases hex with ⟨rfl, hv3⟩
      have hv1 : 1 ≤ v := hv
      interval_cases v
      · have hm2 : 2 ∈ P := by simpa using hm'
        simpa using two_bound hp hm2
      · have hm4 : 4 ∈ P := by simpa using hm'
        simpa using four_bound hp hm4
      · have hm8 : 8 ∈ P := by simpa using hm'
        simpa using eight_bound hp hm8
    have hg := reference_bound hp hk hm' hv hu hodd' hkv
    have hd : recurrenceBound v u k ≤ bound v u := recurrenceBound_mono v u hkv
    have hb : bound v u ≤ 2 * 2 ^ v * u := by
      by_cases hvlarge : 16 ≤ v
      · exact large_bound v u hvlarge hu huv
      · exact finite_bound v u hv (by omega) hu huv hodd' hex
    have he : 2 * 2 ^ v * u = 2 * (2 ^ v * u) := by ring
    exact hg.trans (hd.trans (by rwa [he] at hb))
  rwa [← hmu'] at hbound

end D5.S3.Combinatorics.Games.DivisorNimGrundy
