/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmLoading
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmLoading
   mirror-E: none(waiver:universal-loading-proof)
   anchors: []
   utility: none
   digest: Full physical loading domain and sharp active-set boundary. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Anonymous mechanism manuscript, loading regime; exact boundary and threshold
verification by Haobo Ma and Wenlin Zhang (4 November 2026, CC BY 4.0 for
that new note only). Hyunho Cha's symmetric score calculation is retained.
The mathematical content is the entire physical domain, sharp boundary and
global complement, not isolated numerical loading examples.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.EquiprobablePgmLoading
open D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore success)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

/-- Physical loading states; no implicit admissibility or limiting convention. -/
def states (κ K t : ℝ) := rho (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)

private theorem domain (κ K t : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 1 < K) (ht : 0 < t) (htκ : t ^ 2 < 1 - κ ^ 2) (htK : K * t ^ 2 < 1) :
    0 < 1 - t ^ 2 ∧ 1 - t ^ 2 < 1 ∧
      0 < 1 - K * t ^ 2 ∧ 1 - K * t ^ 2 < 1 ∧
      0 < (1 - t ^ 2) * (1 - (1 - t ^ 2)) - (κ * t) ^ 2 := by
  have hp : 0 < t ^ 2 := sq_pos_of_pos ht
  have hd := mul_pos hp (show 0 < 1 - κ ^ 2 - t ^ 2 by linarith)
  refine ⟨by nlinarith [sq_nonneg κ], by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- Equality at t=kappa/(K-1) belongs to the unique two-active optimum.
Above that boundary all three actual effects are active. -/
theorem loading_classification (κ K t : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 1 < K) (ht : 0 < t) (htκ : t ^ 2 < 1 - κ ^ 2) (htK : K * t ^ 2 < 1) :
    (∀ i, (states κ K t i).PosDef ∧ trace (states κ K t i) = 1) ∧
    finitePOVM (optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)) ∧
    (∀ E, finitePOVM E →
      ((∀ F, finitePOVM F → success (states κ K t) F ≤ success (states κ K t) E) ↔
        E = optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2))) ∧
    (Finset.univ.filter (fun i =>
      optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2) i ≠ 0)) =
        if t ≤ κ / (K - 1) then {0, 1} else Finset.univ := by
  obtain ⟨ha, ha1, hc, hc1, hd⟩ := domain κ K t hκ hκ1 hK ht htκ htK
  have hclass := complete_classification (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)
    (mul_pos hκ ht)
  refine ⟨states_posDef _ _ _ ha hc hc1 hd, hclass.1, hclass.2.1, ?_⟩
  rw [hclass.2.2]
  have habs : |(1 - K * t ^ 2) - (1 - t ^ 2)| = (K - 1) * t ^ 2 := by
    rw [abs_of_nonpos (by nlinarith : (1 - K * t ^ 2) - (1 - t ^ 2) ≤ 0)]
    ring
  have hiff : |(1 - K * t ^ 2) - (1 - t ^ 2)| ≤ κ * t ↔ t ≤ κ / (K - 1) := by
    rw [habs, le_div_iff₀ (by linarith : 0 < K - 1)]
    have hcancel := mul_le_mul_iff_left₀ ht (b := (K - 1) * t) (c := κ)
    convert hcancel using 1 <;> ring
  simp only [hiff]

/-- Exact full-domain identity for the spectral ratio controlling failure. -/
theorem spectral_ratio (κ K t : ℝ) (ht : 0 < t) (ht1 : t ^ 2 < 1) :
    ((2 * (1 - t ^ 2) + (1 - K * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - K * t ^ 2))) /
        ((1 - t ^ 2) * (1 - (1 - t ^ 2))) =
      3 * (K + 2) - (K + 2) * (K - 1) * t ^ 2 / (1 - t ^ 2) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hne : 1 - t ^ 2 ≠ 0 := by linarith
  field_simp
  ring

/-- The entire admissible loading domain is nonviolating when 1<K<=10/3,
including the sharp threshold. The three-active region gives equality. -/
theorem global_nonviolation (κ K t : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 1 < K) (hKhi : K ≤ 10 / 3) (ht : 0 < t)
    (htκ : t ^ 2 < 1 - κ ^ 2) (htK : K * t ^ 2 < 1) :
    let A := Finset.univ.filter (fun i =>
      optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2) i ≠ 0)
    ((A.card : ℝ) - 1) * (pgmScore (states κ K t) A - 1 / 3) ≤
      2 * (pgmScore (states κ K t) Finset.univ - 1 / 3) := by
  obtain ⟨ha, ha1, hc, hc1, hd⟩ := domain κ K t hκ hκ1 hK ht htκ htK
  have hf := (active_failure_iff (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)
    ha ha1 (mul_pos hκ ht) hc hc1 hd).2
  dsimp only at hf ⊢
  apply le_of_not_gt
  intro hv
  have hD := (hf.mp hv).2.1
  have hratio := spectral_ratio κ K t ht (by nlinarith [sq_nonneg κ])
  have hq : 0 < (1 - t ^ 2) * (1 - (1 - t ^ 2)) := mul_pos ha (sub_pos.mpr ha1)
  have hratiohi : 16 < ((2 * (1 - t ^ 2) + (1 - K * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - K * t ^ 2))) /
        ((1 - t ^ 2) * (1 - (1 - t ^ 2))) := (lt_div_iff₀ hq).mpr (by nlinarith)
  have hload : 0 ≤ (K + 2) * (K - 1) * t ^ 2 / (1 - t ^ 2) := by positivity
  linarith

end D5.S3.Quantum.Measurement.EquiprobablePgmLoading

/- Escape-audit delivery: four source-bound registrations are currently validated
for SupportIdentity.centered_identity/random_guessing_le and
Symmetric.states_posDef/pair_classification. The remaining theorem-specific
bindings are unfinished and disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
That issue is not proof, registration validation or independent approval. -/
