/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convergent actual half-Fock kernel traces with eta and even-rank S laws. -/

import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
import D5.S3.Combinatorics.Partitions.EtaOddOccupation

/-! The analytic character is a sum of traces of actual finite restrictions.
No trace on the infinite ambient tensor space is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open Complex

namespace D5.S3.VertexAlgebra.LatticeHalfFockCharacter

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockGradedTrace
open LatticeHalfFockChargedTensorCoefficients TwistedGround.OperatorAlgebra
open LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open HalfFockSpectralFiberSource
open D5.S3.Combinatorics.Partitions
open ColouredOddOccupation AnalyticOddOccupation EtaOddOccupation

/-- A coefficient is the trace of id tensor A restricted to the actual L0 kernel. -/
def actualTraceTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (q : ℂ) (N : ℕ) : ℂ :=
  LinearMap.trace ℂ (actualGrade D hu N) (actualGroundInsertRestrict D hu N A) * q ^ N

/-- The vacuum shift rank/48 multiplies the sum of actual restricted traces.
The oscillator parameter is exp(pi I tau), so grade N contributes N/2. -/
def actualInsertedCharacter (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (τ : ℂ) : ℂ :=
  exp (2 * Real.pi * I * τ * D.rank / 48) *
    ∑' N : ℕ, actualTraceTerm D hu A (exp (Real.pi * I * τ)) N

/-- Coefficient identification and absolute convergence precede evaluation.
The independent partition count is transported through its occupation equivalence;
no scalar trace is cancelled, and q=0 and the empty colour type are allowed. -/
theorem actual_trace_series (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (q : ℂ) (hq : ‖q‖ < 1) :
    (∀ N, actualTraceTerm D hu A q N =
      (ColouredOddMultiplicity.partitionCount D.rank N : ℂ) *
        LinearMap.trace ℂ (ActualGround D hu) A * q ^ N) ∧
    Summable (fun N : ℕ => ‖actualTraceTerm D hu A q N‖) ∧
    HasSum (actualTraceTerm D hu A q)
      (LinearMap.trace ℂ (ActualGround D hu) A * oddCoefficientSeries D.rank q) := by
  let c := LinearMap.trace ℂ (ActualGround D hu) A
  have hcoeff (N : ℕ) : actualTraceTerm D hu A q N =
      c * ((Nat.card (ColouredOddFiber (Fin D.rank) N) : ℂ) * q ^ N) := by
    rw [actualTraceTerm, actual_grade_insert_trace_bRank]
    rw [bRank, ← ColouredOddMultiplicity.card_colouredFiber]
    ring
  have hs := summable_norm_odd_coefficients (Fin D.rank) hq
  have habs : Summable (fun N : ℕ => ‖actualTraceTerm D hu A q N‖) := by
    simpa only [hcoeff, norm_mul] using hs.mul_left ‖c‖
  refine ⟨?_, habs, ?_⟩
  · intro N
    rw [actualTraceTerm, actual_grade_insert_trace_bRank, bRank]
  · have hsum := hs.of_norm.hasSum.mul_left c
    exact hsum.congr_fun hcoeff

private theorem q_norm_lt_one (τ : ℂ) (hτ : 0 < τ.im) :
    ‖exp (Real.pi * I * τ)‖ < 1 := by
  have he : Function.Periodic.qParam 2 τ = exp (Real.pi * I * τ) := by
    simp only [Function.Periodic.qParam, ofReal_ofNat]
    congr 1
    ring
  rw [← he]
  exact Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 2) hτ

/-- The trace-defined character has an absolutely convergent normalized series,
its eta value, and the branch-safe even-rank S transform. All endomorphisms and
complex phases are retained, including zero trace. -/
theorem actual_character_modular (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun N : ℕ => ‖exp (2 * Real.pi * I * τ * D.rank / 48) *
      actualTraceTerm D hu A (exp (Real.pi * I * τ)) N‖) ∧
    HasSum (fun N : ℕ => exp (2 * Real.pi * I * τ * D.rank / 48) *
      actualTraceTerm D hu A (exp (Real.pi * I * τ)) N)
      (LinearMap.trace ℂ (ActualGround D hu) A *
        (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank) ∧
    actualInsertedCharacter D hu A τ =
      LinearMap.trace ℂ (ActualGround D hu) A *
        (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank ∧
    (∀ m : ℕ, D.rank = 2 * m → actualInsertedCharacter D hu A (-1 / τ) =
      LinearMap.trace ℂ (ActualGround D hu) A * ((2 : ℂ) ^ m)⁻¹ *
        (ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ (2 * m)) ∧
    (∀ (x : Extension D ⧸ K D), quotientCharge D x ≠ 0 →
      A = groundRepresentation D hu x →
      (∀ N, actualTraceTerm D hu A (exp (Real.pi * I * τ)) N = 0) ∧
      HasSum (fun N : ℕ => exp (2 * Real.pi * I * τ * D.rank / 48) *
        actualTraceTerm D hu A (exp (Real.pi * I * τ)) N) 0 ∧
      actualInsertedCharacter D hu A τ = 0) := by
  let c := LinearMap.trace ℂ (ActualGround D hu) A
  let v := exp (2 * Real.pi * I * τ * D.rank / 48)
  have hs := actual_trace_series D hu A (exp (Real.pi * I * τ)) (q_norm_lt_one τ hτ)
  have he : v * (c * oddCoefficientSeries D.rank (exp (Real.pi * I * τ))) =
      c * (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank := by
    dsimp [v]
    rw [← mul_assoc, mul_comm _ c]
    exact normalized_odd_character_eq_eta D.rank c τ hτ
  have hsum := hs.2.2.mul_left v
  rw [he] at hsum
  have hchar : actualInsertedCharacter D hu A τ =
      c * (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank := by
    rw [actualInsertedCharacter, ← tsum_mul_left]
    exact hsum.tsum_eq
  refine ⟨?_, hsum, hchar, ?_, ?_⟩
  · simpa only [norm_mul] using hs.2.1.mul_left ‖v‖
  · intro m hr
    have hS : 0 < (-1 / τ).im := by
      simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨τ, hτ⟩ : UpperHalfPlane)
    have hSS := actual_trace_series D hu A (exp (Real.pi * I * (-1 / τ)))
      (q_norm_lt_one (-1 / τ) hS)
    rw [actualInsertedCharacter, hSS.2.2.tsum_eq]
    change exp (2 * Real.pi * I * (-1 / τ) * D.rank / 48) *
      (c * oddCoefficientSeries D.rank (exp (Real.pi * I * (-1 / τ)))) = _
    rw [hr]
    calc
      _ = c * exp (2 * Real.pi * I * (-1 / τ) * (2 * m : ℕ) / 48) *
          oddCoefficientSeries (2 * m) (exp (Real.pi * I * (-1 / τ))) := by ring
      _ = _ := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using normalized_odd_character_S m c τ hτ
  · intro x hx hA
    have hg : c = 0 := by
      dsimp [c]
      rw [hA, actual_quotient_charge_ground_trace_zero D hu x hx]
    refine ⟨?_, ?_, ?_⟩
    · intro N
      rw [hA, actualTraceTerm, actual_quotient_charge_grade_trace_zero D hu N x hx,
        zero_mul]
    · simpa only [hg, zero_mul] using hsum
    · simpa only [hg, zero_mul] using hchar

end D5.S3.VertexAlgebra.LatticeHalfFockCharacter

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_trace_series
#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_character_modular
