/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalModularPartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalModularPartners
   mirror-E: none(waiver:original-modular-partner-application)
   anchors: []
   utility: none
   digest: Original retained word solutions supply the modular partner nondegeneracy. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalCoefficients
import D5.S3.Arith.CharacterSums.PascadiModularZeroRegularity

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

/-- Every nonaligned actual base with a nonzero linear observation has a
uniform subpower bound for its full modular-zero partner set. The dividing
directions and the six-candidate nondividing branch are both included. -/
theorem actual_modular_zero_partner_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ : ℝ)
      (E : Finset Coordinate) (α β : ZMod p) (q a b : Coordinate),
      1 ≤ J₁ → 1 ≤ J₂ →
      ActualPair E α β q (a, b) → ¬ Aligned q (a, b) →
      (endpointL q (a, b)).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 →
      α ≠ 0 → α * (α + (q.1 : ZMod p) + β * q.2) ≠ 0 →
      CoordinateBound J₁ J₂ q →
      (∀ z ∈ E, CoordinateBound J₁ J₂ z) →
      8 * J₁ * J₂ < p →
      ((modularZeroPartners E α β q (a, b)).card : ℝ) ≤ C * (p : ℝ)^ε := by
  obtain ⟨C, hC, hdiv⟩ := actual_dividing_branches_modular_zero_partner_subpower ε hε
  refine ⟨C + 6, by linarith, ?_⟩
  intro p hp J₁ J₂ E α β q a b hJ₁ hJ₂ he hn hL hα hκ hq hE hsmall
  letI : Fact p.Prime := ⟨hp⟩
  have hpow0 : 0 ≤ (p : ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hle : C * (p : ℝ)^ε ≤ (C + 6) * (p : ℝ)^ε :=
    mul_le_mul_of_nonneg_right (by linarith) hpow0
  by_cases ha : (coordinateDet a (a + b - q) : ZMod p) = 0
  · exact (hdiv p hp J₁ J₂ E α β q a b he hn hL hα hκ hq hE hsmall
      (Or.inl ha)).trans hle
  by_cases hb : (coordinateDet (a + b - q) b : ZMod p) = 0
  · exact (hdiv p hp J₁ J₂ E α β q a b he hn hL hα hκ hq hE hsmall
      (Or.inr hb)).trans hle
  have hcard := nondividing_modular_zero_partner_count E α β q a b
    hJ₁ hJ₂ hE hsmall ha hb
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpow : 1 ≤ (p : ℝ)^ε := Real.one_le_rpow hpone hε.le
  calc
    _ ≤ 6 := by exact_mod_cast hcard
    _ ≤ C + 6 := by linarith
    _ ≤ (C + 6) * (p : ℝ)^ε := by
      simpa using mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ C + 6)

/-- A retained original word solution supplies the nondegeneracy needed for
the modular partner bound. Source modulus `c` may be any nonzero multiple of
the prime, including `p³`; the original fixed units and physical coordinates
are preserved. -/
theorem original_modular_zero_partner_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (c : ℕ)
      (hc : c ≠ 0) (hpc : p ∣ c) (J₁ J₂ : ℝ) (E : Finset Coordinate)
      (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (R V q a b : Coordinate)
      (hr : IsUnit (R.1 : ZMod c))
      (ht : IsUnit (-(physical R V q).2 : ZMod c)),
      1 ≤ J₁ → 1 ≤ J₂ → a ∈ E → b ∈ E →
      WordSolution c a₁ a₂ R V q (a, b) →
      IsUnit ((physical R V a).1 : ZMod c) →
      IsUnit ((physical R V b).1 : ZMod c) →
      IsUnit (1 - a₁ * a₂ * (ht.unit : ZMod c) *
        ((physical R V q).1 : ZMod c)) →
      ¬ Aligned q (a, b) → CoordinateBound J₁ J₂ q →
      (∀ z ∈ E, CoordinateBound J₁ J₂ z) → 8 * J₁ * J₂ < p →
      let f := ZMod.castHom hpc (ZMod p)
      let β := (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)
      let α := -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c)
      ((modularZeroPartners E (f α) (f β) q (a, b)).card : ℝ) ≤ C * (p : ℝ)^ε := by
  obtain ⟨C, hC, hcount⟩ := actual_modular_zero_partner_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp c hc hpc J₁ J₂ E a₁ a₂ ha₁ ha₂ R V q a b hr ht
    hJ₁ hJ₂ ha hb he hx hy hk hn hq hE hsmall
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero c := ⟨hc⟩
  let f := ZMod.castHom hpc (ZMod p)
  let β : ZMod c := (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)
  let α : ZMod c := -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c)
  change ((modularZeroPartners E (f α) (f β) q (a, b)).card : ℝ) ≤ C * (p : ℝ)^ε
  have hu : IsUnit α ∧
      IsUnit (α * (α + (q.1 : ZMod c) + β * q.2)) ∧
      IsUnit ((endpointL q (a, b)).eval₂ (Int.castRingHom (ZMod c)) β) := by
    simpa only [α, β] using
      original_unit_observations a₁ a₂ ha₁ ha₂ R V q (a, b) hr ht he hx hy hk
  have hid : α * (endpointL q (a, b)).eval₂ (Int.castRingHom (ZMod c)) β +
      (endpointQ (a, b)).eval₂ (Int.castRingHom (ZMod c)) β = 0 := by
    simpa only [α, β] using
      original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q (a, b) hr ht he
  obtain ⟨hα, hκ, hL, hprod⟩ := modular_observations_of_unit_source f α β q (a, b)
    hu.1 hu.2.1 hu.2.2 hid
  have hpair : ActualPair E (f α) (f β) q (a, b) := by
    refine ⟨ha, hb, ?_⟩
    simpa only [actualValue] using hprod
  exact hcount p hp J₁ J₂ E (f α) (f β) q a b hJ₁ hJ₂ hpair hn hL hα hκ
    hq hE hsmall

end
end D5.S3.Arith.CharacterSums.Original
