/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalModularPartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalModularPartners
   mirror-E: none(waiver:original-modular-partner-application)
   anchors: []
   utility: none
   digest: Original retained word solutions supply the modular partner nondegeneracy. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalCoefficients

/-! # Original observations for modular partner counting

The retained physical endpoint coordinates and the original reciprocal expression
are units. They supply the linear observation and anchor-product regularity without
assuming injectivity of a single linear value modulo the prime.
-/

open Polynomial

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem original_unit_observations {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (e : Endpoint)
    (hr : IsUnit (R.1 : ZMod c)) (ht : IsUnit (-(physical R V q).2 : ZMod c))
    (he : WordSolution c a₁ a₂ R V q e)
    (hx : IsUnit ((physical R V e.1).1 : ZMod c))
    (hy : IsUnit ((physical R V e.2).1 : ZMod c))
    (hk : IsUnit (1 - a₁ * a₂ * (ht.unit : ZMod c) *
      ((physical R V q).1 : ZMod c))) :
    let β := (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)
    let α := -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c)
    IsUnit α ∧
      IsUnit (α * (α + (q.1 : ZMod c) + β * q.2)) ∧
      IsUnit ((endpointL q e).eval₂ (Int.castRingHom (ZMod c)) β) := by
  dsimp only
  let gt := ha₁.unit * ha₂.unit * ht.unit
  let gtr := gt * hr.unit
  let β : ZMod c := (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)
  let α : ZMod c := -(↑gtr⁻¹ : ZMod c)
  let value (z : Coordinate) : ZMod c := (z.1 : ZMod c) + β * z.2
  have hphys (z : Coordinate) : ((physical R V z).1 : ZMod c) =
      (hr.unit : ZMod c) * value z := by
    have hinv : (↑hr.unit⁻¹ : ZMod c) * (hr.unit : ZMod c) = 1 := by simp
    calc
      _ = (z.1 : ZMod c) * (hr.unit : ZMod c) + (z.2 : ZMod c) * V.1 := by
        simp [physical, hr.unit_spec]
      _ = (hr.unit : ZMod c) * value z := by
        dsimp [value, β]
        calc
          _ = (hr.unit : ZMod c) *
              ((z.1 : ZMod c) + ((V.1 : ZMod c) * ↑hr.unit⁻¹) * z.2) := by
            linear_combination -(V.1 : ZMod c) * (z.2 : ZMod c) * hinv -
              (z.1 : ZMod c) * hr.unit_spec
          _ = _ := rfl
  have hxv : IsUnit (value e.1) := by
    rw [hphys] at hx
    exact (IsUnit.mul_iff.mp hx).2
  have hyv : IsUnit (value e.2) := by
    rw [hphys] at hy
    exact (IsUnit.mul_iff.mp hy).2
  have heval (n : ℤ) : (n : ℤ[X]).eval₂ (Int.castRingHom (ZMod c)) β =
      (n : ZMod c) := map_intCast
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod c)) β) n
  have hQ : (endpointQ e).eval₂ (Int.castRingHom (ZMod c)) β =
      value e.1 * value e.2 := by
    simp [endpointQ, PrimeCube.quadratic, coeffQ, coeffR, coeffS, heval, value]
    ring
  have hid : α * (endpointL q e).eval₂ (Int.castRingHom (ZMod c)) β +
      (endpointQ e).eval₂ (Int.castRingHom (ZMod c)) β = 0 := by
    simpa [α, gtr, gt, β] using
      original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q e hr ht he
  have hL : IsUnit ((endpointL q e).eval₂ (Int.castRingHom (ZMod c)) β) := by
    have hu : IsUnit (α * (endpointL q e).eval₂ (Int.castRingHom (ZMod c)) β) := by
      rw [show α * (endpointL q e).eval₂ (Int.castRingHom (ZMod c)) β =
        -(endpointQ e).eval₂ (Int.castRingHom (ZMod c)) β by linear_combination hid]
      rw [hQ]
      exact (hxv.mul hyv).neg
    exact (IsUnit.mul_iff.mp hu).2
  have hα : IsUnit α := (gtr⁻¹).isUnit.neg
  have hαgtr : α * (gtr : ZMod c) = -1 := by
    dsimp [α]
    rw [neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hminus : α * (gt : ZMod c) * ((physical R V q).1 : ZMod c) = -value q := by
    calc
      _ = (α * (gtr : ZMod c)) * value q := by
        rw [hphys]
        simp only [gtr, Units.val_mul]
        ring
      _ = -value q := by rw [hαgtr]; ring
  have hshift : α + value q =
      α * (1 - (gt : ZMod c) * ((physical R V q).1 : ZMod c)) := by
    linear_combination hminus
  have hku : IsUnit (1 - (gt : ZMod c) * ((physical R V q).1 : ZMod c)) := by
    simpa [gt, Units.val_mul, ha₁.unit_spec, ha₂.unit_spec, mul_assoc] using hk
  have hκ : IsUnit (α * (α + (q.1 : ZMod c) + β * q.2)) := by
    have hs : IsUnit (α + value q) := by
      rw [hshift]
      exact hα.mul hku
    convert hα.mul hs using 1 <;> dsimp [value] <;> ring
  exact ⟨hα, hκ, hL⟩

private theorem modular_observations_of_unit_source {c p : ℕ} [Fact p.Prime]
    (f : ZMod c →+* ZMod p) (α β : ZMod c) (q : Coordinate) (e : Endpoint)
    (hα : IsUnit α)
    (hκ : IsUnit (α * (α + (q.1 : ZMod c) + β * q.2)))
    (hL : IsUnit ((endpointL q e).eval₂ (Int.castRingHom (ZMod c)) β))
    (hid : α * (endpointL q e).eval₂ (Int.castRingHom (ZMod c)) β +
      (endpointQ e).eval₂ (Int.castRingHom (ZMod c)) β = 0) :
    f α ≠ 0 ∧
      f α * (f α + (q.1 : ZMod p) + f β * q.2) ≠ 0 ∧
      (endpointL q e).eval₂ (Int.castRingHom (ZMod p)) (f β) ≠ 0 ∧
      (f α + (e.1.1 : ZMod p) + f β * e.1.2) *
        (f α + (e.2.1 : ZMod p) + f β * e.2.2) =
        f α * (f α + (q.1 : ZMod p) + f β * q.2) := by
  have hcomp : f.comp (Int.castRingHom (ZMod c)) = Int.castRingHom (ZMod p) := by
    ext z
    simp
  have hEval (P : ℤ[X]) : f (P.eval₂ (Int.castRingHom (ZMod c)) β) =
      P.eval₂ (Int.castRingHom (ZMod p)) (f β) := by
    simpa [hcomp] using Polynomial.hom_eval₂ (Int.castRingHom (ZMod c)) f P β
  have hαp : f α ≠ 0 := (hα.map f).ne_zero
  have hκp : f α * (f α + (q.1 : ZMod p) + f β * q.2) ≠ 0 := by
    simpa only [map_mul, map_add, map_intCast] using (hκ.map f).ne_zero
  have hLp : (endpointL q e).eval₂ (Int.castRingHom (ZMod p)) (f β) ≠ 0 := by
    rw [← hEval]
    exact (hL.map f).ne_zero
  refine ⟨hαp, hκp, hLp, ?_⟩
  have hp := congrArg f hid
  simp only [map_add, map_mul, map_zero, hEval] at hp
  have heval (n : ℤ) : (n : ℤ[X]).eval₂ (Int.castRingHom (ZMod p)) (f β) =
      (n : ZMod p) := map_intCast
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) (f β)) n
  simp [endpointL, endpointQ, PrimeCube.linear, PrimeCube.quadratic,
    coeffL, coeffM, coeffQ, coeffR, coeffS, heval] at hp
  linear_combination hp

end
end D5.S3.Arith.CharacterSums.Original
