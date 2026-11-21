/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine lines over F9 give the minimal mixed-unitary rank of the symmetric Werner–Holevo channel in every dimension 9^d with d at least two. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineBasisConcrete
import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineRank

open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel

namespace AffineNine

/-- The symmetric Werner–Holevo channel on a space of dimension \(9^d\)
attains its Choi rank as its mixed-unitary rank for every \(d \ge 2\). -/
theorem mixedUnitaryRank_power_nine (d : ℕ) (hd : 2 ≤ d) :
    let n := 9 ^ d
    ∃ channel : QuantumChannel (Fin n) (Fin n),
      (∀ X : Matrix (Fin n) (Fin n) ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        AffineNineRank.symmetricWernerHolevo (Fin n) X) ∧
      IsLeast {m : ℕ | AffineNineRank.HasMixedUnitaryDecomposition channel m} (n * (n + 1) / 2) := by
  classical
  let n := 9 ^ d
  let r := (n + 1).choose 2
  have hn : 0 < n := by positivity
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨basis, hunitary, horth⟩ := exists_f9Basis d hd
  let U (i : Fin r) : Matrix (Fin n) (Fin n) ℂ := basis i
  have hsym (i : Fin r) : (U i).IsSymm := (basis i).2
  have hcross (i j : Fin r) (hij : i ≠ j) : AffineNineRank.hsInner (U i) (U j) = 0 := by
    rw [AffineNineRank.hsInner_eq_sum]
    change hs (U i) (U j) = 0
    exact (horth i j).trans (if_neg hij)
  simpa only [Fintype.card_fin] using
    AffineNineRank.mixedUnitary_rank_exact U hunitary hsym hcross (by simp [r])

#print axioms mixedUnitaryRank_power_nine

end AffineNine
