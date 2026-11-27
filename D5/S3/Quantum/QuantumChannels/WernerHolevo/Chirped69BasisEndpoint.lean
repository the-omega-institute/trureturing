/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.mixedUnitaryRank; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69ActualSeedBounds.existsUnique_zero_closedBall; result=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69BasisEndpoint.mixedUnitaryRank
   digest: Four chirped orbits yield a symmetric unitary basis and mixed-unitary rank 2415. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped69ActualSeedBounds
import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedBasisEndpoint
import D5.S3.Quantum.QuantumChannels.WernerHolevo.TransversalNineGluing

/-! The order-69 chirped system gives a full symmetric unitary basis.
The Gram factorization uses Ma's Theorem 5 (doi:10.5281/zenodo.24246318). -/

open scoped BigOperators ComplexConjugate
open ChirpedAnalyticDrift
open ChirpedAnalyticDrift.ReplayBridge (pullback ValidSeed replayRows)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open AffineNineRank (HasMixedUnitaryDecomposition)

namespace ChirpedBasisEndpoint

noncomputable section

namespace Order69

open Chirped69

local instance : NeZero n := ⟨by decide⟩

/-- Inverse of the actual multiplier 28 from the replay input. -/
private def inverseUnit : (ZMod n)ˣ :=
  ⟨(inverseMultiplier : ZMod n), (multiplier : ZMod n), by decide, by decide⟩

private def period : ℕ → ℕ
  | 0 => 22
  | 1 => 11
  | _ => 1

private def orbit (i : Fin 35) : ℕ × ℕ :=
  if i.val < 22 then (0, i.val)
  else if i.val < 33 then (1, i.val - 22)
  else if i.val = 33 then (2, 0)
  else (3, 0)

private theorem orbit_domain : ∀ i : Fin 35, (orbit i).1 < seeds.length := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem valid : ∀ a : Fin seeds.length, ValidSeed n m (seed a.val) := by
  exact fun a => Chirped69.valid_seed a.val a.isLt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem evenCoord : ∀ a : Fin seeds.length, ∀ l : ZMod n,
    (pullback (m := m) (seed a.val)).coord (-l) = (pullback (m := m) (seed a.val)).coord l := by
  intro a
  fin_cases a <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem stabilizers : ∀ a : Fin seeds.length,
    shiftedChirp inverseUnit (period a.val) (seed a.val) = (chirp (seed a.val) : ZMod n) ∧
    ∀ l : ZMod n,
      (pullback (m := m) (seed a.val)).coord ((inverseUnit ^ period a.val).mulLeft l) =
      (pullback (m := m) (seed a.val)).coord l := by
  intro a
  fin_cases a <;> decide +kernel

private abbrev signs (i : Fin m) : ℤ := signEntry i.val

private theorem periodic (x : Fin m → ℝ) (a : ℕ) (ha : a < seeds.length) :
    shift inverseUnit (period a) (baseSeed signs (seed a) x) = baseSeed signs (seed a) x :=
  let h := stabilizers ⟨a, ha⟩
  seed_period inverseUnit (period a) signs (seed a) x h.1 h.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
/-- The row lacking an imaginary projection is the orbit midpoint.
The check uses the replay's actual row indices and recorded constraints. -/
private theorem projections : ∀ k : Fin constraints.length,
    let c := constraint k.val
    HasRow pick imag c false ∧ (HasRow pick imag c true ∨
      c.includeImag = false ∧ c.left = c.right ∧
        (c.power + c.power) % period c.left = 0) := by
  intro k
  fin_cases k <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem coverage : ∀ i j : Fin 35, i < j →
    CoveredPair period (fun k : Fin constraints.length => constraint k.val)
      (orbit i) (orbit j) := by
  intro i
  fin_cases i <;> decide +kernel

private theorem residual_at_zero (x : Fin m → ℝ) (hx : F x = 0) :
    residual signs (replayRows inverseUnit pick imag seed) x = 0 := by
  have hDomain (i : Fin m) :=
    constraints_domain ⟨(equation i.val).1, equation_domain i⟩
  have h := ChirpedAnalyticDrift.ReplayBridge.residual_eq signs inverseUnit inverseMultiplier
    rfl pick imag seed
    (fun i => valid ⟨(pick i).left, (hDomain i).1⟩)
    (fun i => valid ⟨(pick i).right, (hDomain i).2⟩) x
  exact h.trans hx

private theorem recorded_rows_zero (x : Fin m → ℝ) (hx : F x = 0)
    (k : Fin constraints.length) :
    recordedGram inverseUnit (fun a => baseSeed signs (seed a) x) (constraint k.val) = 0 := by
  have h := projections k
  apply recorded_gram_zero inverseUnit signs seed pick imag x (constraint k.val)
    (residual_at_zero x hx) h.1
  rcases h.2 with hi | ⟨_, he, hp⟩
  · exact Or.inl hi
  · refine Or.inr ⟨he, ?_⟩
    rw [shift_mod inverseUnit _ _ (periodic x _ (constraints_domain k).1), hp, shift_zero]

private theorem seed_orthogonal (x : Fin m → ℝ) (hx : F x = 0) (i j : Fin 35) (hij : i ≠ j) :
    gram (shift inverseUnit (orbit i).2 (baseSeed signs (seed (orbit i).1) x))
      (shift inverseUnit (orbit j).2 (baseSeed signs (seed (orbit j).1) x)) = 0 := by
  refine gram_zero_of_coverage inverseUnit period (fun a => baseSeed signs (seed a) x)
    orbit constraint constraints.length (fun i => periodic x _ (orbit_domain i))
    (recorded_rows_zero x hx) ?_ hij
  intro a b hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact coverage a b hab
  · have h := coverage b a hba
    unfold CoveredPair at h ⊢
    obtain ⟨k, hk⟩ := h
    exact ⟨k, hk.symm⟩

private theorem family_card : Fintype.card (Fin 35 × ZMod n) = (n + 1).choose 2 := by
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card] <;> decide

/-- The 35 shifted seeds and their 69 modulations give all 2415 basis matrices. -/
def unitaryBasis (x : Fin m → ℝ) (hx : F x = 0) :
    TransversalNine.UnitaryBasis (Fin 35 × ZMod n) (ZMod n) :=
  assemble inverseUnit signs seed orbit x (by decide) (fun i => (signs_unit i).symm)
    (fun i => evenCoord ⟨(orbit i).1, orbit_domain i⟩)
    (seed_orthogonal x hx) family_card

theorem hasBasis_of_zero (x : Fin m → ℝ) (hx : F x = 0) : TransversalNine.HasBasis 69 :=
  hasBasis_of_family family_card (unitaryBasis x hx)

/-- An exact zero gives the exact minimum length of a mixed-unitary decomposition
of the symmetric Werner–Holevo channel in order 69. -/
theorem mixedUnitaryRank_of_zero (x : Fin m → ℝ) (hx : F x = 0) :
    ∃ channel : QuantumChannel (Fin 69) (Fin 69),
      (∀ X : Matrix (Fin 69) (Fin 69) ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        AffineNineRank.symmetricWernerHolevo (Fin 69) X) ∧
      IsLeast {k : ℕ | HasMixedUnitaryDecomposition channel k} 2415 := by
  exact TransversalNine.rank_exact (hasBasis_of_zero x hx)

/-- The order-69 symmetric Werner–Holevo channel has mixed-unitary rank 2415. -/
theorem mixedUnitaryRank :
    ∃ channel : QuantumChannel (Fin 69) (Fin 69),
      (∀ X : Matrix (Fin 69) (Fin 69) ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        AffineNineRank.symmetricWernerHolevo (Fin 69) X) ∧
      IsLeast {k : ℕ | HasMixedUnitaryDecomposition channel k} 2415 := by
  obtain ⟨x, hx, _⟩ := Chirped69.existsUnique_zero_closedBall
  exact mixedUnitaryRank_of_zero x hx.2

end Order69

#print axioms Order69.hasBasis_of_zero
#print axioms Order69.mixedUnitaryRank_of_zero
#print axioms Order69.mixedUnitaryRank

end
end ChirpedBasisEndpoint
