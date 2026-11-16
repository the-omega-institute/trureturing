/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Constant fibres of the complementary-colour row map. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live paths of HardinA229750.result and HardinA229751.result)
sum_beta: proof_shape=bind-only;
consumers=Width3.ZeroTemperature.transition_counts,Width4.ZeroTemperature.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip

/-! Each complementary-pair row has two independent sign choices in every column. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.SignedFibres
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip (beta)

theorem sum_beta {k : ℕ} (w : (Fin k → Fin 4) → ℤ) :
    (∑ c : Fin k → Fin 8, w (beta ∘ c)) = (2 : ℤ)^k * ∑ r, w r := by
  classical
  have hc (r : Fin k → Fin 4) :
      (Finset.univ.filter (fun c : Fin k → Fin 8 => beta ∘ c = r)).card = 2^k := by
    have hb : ∀ a : Fin 4, (Finset.univ.filter (fun c : Fin 8 => beta c = a)).card = 2 := by
      decide +kernel
    have he : Finset.univ.filter (fun c : Fin k → Fin 8 => beta ∘ c = r) =
        Fintype.piFinset (fun j => Finset.univ.filter (fun c : Fin 8 => beta c = r j)) := by
      ext c
      simp [funext_iff, Function.comp_def]
    rw [he, Fintype.card_piFinset]
    simp [hb]
  rw [← Finset.sum_fiberwise' Finset.univ (fun c : Fin k → Fin 8 => beta ∘ c) w]
  simp only [Finset.sum_const, hc, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact (Finset.mul_sum _ _ _).symm

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.SignedFibres
