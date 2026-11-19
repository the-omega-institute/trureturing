/- GID: D5/S1/Words/Complexity/LyndonFactorChristoffelScan
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/LyndonFactorChristoffelScan
   mirror-E: none(waiver:research-return-assignment-A)
   anchors: []
   utility: none
   digest: The Lyndon factor scan computes the finite-index occurrence image used in the Christoffel refutation. -/

import D5.S1.Words.Complexity.LyndonFactorTransport
import D5.S1.Words.Complexity.LyndonFactorChristoffelMinimumRefutation

/-! The scan enumerates the actual factor objects of the Christoffel certificate.
Each Lyndon infix yields a bounded start and length, and each indexed factor is an
infix. The count equality uses this correspondence after equal strings have
been identified. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.LyndonFactorTransport

open D5.S1.Words.Complexity.LyndonFactorChristoffelMinimumRefutation

/-- The scan computes precisely the occurrence image used by the original certificate. -/
theorem factorScan_eq_occurrence_image {σ n : ℕ} (w : Fin n → Fin σ) :
    factorScan ((List.finRange n).map w) =
      (lyndonOccurrences w).image (fun p => factor w p.1 p.2) := by
  classical
  ext u
  rw [mem_factorScan, Finset.mem_image]
  constructor
  · rintro ⟨hu, ⟨l, r, he⟩⟩
    have hlen := congrArg List.length he
    simp only [List.length_append, List.length_map, List.length_finRange] at hlen
    have hup := List.length_pos_of_ne_nil hu.1
    have hf : factor w l.length u.length = u := by
      unfold factor
      rw [← he]
      simp
    refine ⟨(l.length, u.length), ?_, hf⟩
    simp only [lyndonOccurrences, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega, by omega, by simpa [hf] using hu⟩
  · rintro ⟨⟨i, k⟩, hp, rfl⟩
    simp only [lyndonOccurrences, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hp
    refine ⟨hp.2.2.2, ?_⟩
    exact (List.take_prefix k _).isInfix.trans (List.drop_suffix i _).isInfix

/-- Counts identify equal strings; this is the original count, not an occurrence proxy. -/
theorem distinctLyndon_eq_scan {σ n : ℕ} (w : Fin n → Fin σ) :
    distinctLyndon w = (factorScan ((List.finRange n).map w)).card := by
  rw [factorScan_eq_occurrence_image]
  rfl

end D5.S1.Words.Complexity.LyndonFactorTransport
