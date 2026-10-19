/- GID: D5/S3/Quantum/Matrix/CayleyResolvent
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CayleyResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse, mathlib/module/Mathlib.Analysis.Matrix.Order, mathlib/module/Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order]
   utility: none
   digest: Endpoint factorizations and uniform order bounds for positive matrix resolvents. -/

/-
admission_basis: escape-witness
proof_shape: endpoint_resolvent_factors: content
proof_shape: cayley_transport: bind-only
consumer: CzerwinskaFrancoMerinoCounterexample.radial_counterexample
proof_shape: cayley_resolvent: bind-only
consumer: CzerwinskaFrancoMerinoCounterexample.cayley_functional_calculus
escape_witness: endpoint_resolvent_factors
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-! Uniform endpoint factors and order-preserving transport on the positive definite cone. -/

noncomputable section
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Matrix.CayleyResolvent
open _root_.Matrix

variable {n : ℕ}

/-- Resolvent at a real scalar outside the spectrum. -/
def resolvent (s : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (s • 1 - X)⁻¹

theorem inverse_antitone {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (h : P ≤ Q) : Q⁻¹ ≤ P⁻¹ := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    CStarAlgebra.antitoneOn_ringInverse hP.isStrictlyPositive hQ.isStrictlyPositive h

private theorem resolvent_difference (s : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - U).PosDef)
    (hV : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - V).PosDef) :
    resolvent s V - resolvent s U = resolvent s U * (V-U) * resolvent s V := by
  have h := Matrix.inv_sub_inv
    (A := s • (1 : Matrix (Fin n) (Fin n) ℂ) - U) (B := s • 1 - V)
    ⟨fun _ => hV.isUnit, fun _ => hU.isUnit⟩
  have he : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - V) - (s • 1 - U) = -(V-U) := by
    abel
  rw [he, mul_neg, neg_mul] at h
  simpa only [resolvent, neg_sub, neg_neg] using congrArg Neg.neg h

private theorem square_le_two {H : Matrix (Fin n) (Fin n) ℂ} (hH : 0 ≤ H)
    (h2 : H ≤ (2 : ℝ) • 1) : H * H ≤ (2 : ℝ) • H := by
  have hp : 0 ≤ H * ((2 : ℝ) • 1 - H) := by
    apply Commute.mul_nonneg hH (sub_nonneg.mpr h2)
    change H * ((2 : ℝ) • 1 - H) = ((2 : ℝ) • 1 - H) * H
    simp [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  have he : H * ((2 : ℝ) • 1 - H) = (2 : ℝ) • H - H*H := by
    simp [mul_sub, mul_smul_comm]
  rw [he] at hp
  exact sub_nonneg.mp hp

/-- At the lower endpoint the increment factors through a matrix between `H` and `3H`.
The factorization does not require `H` to be invertible. -/
private theorem lower_endpoint_factor (s : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - U).PosDef)
    (hV : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - V).PosDef)
    (hUV : U ≤ V) (hH : V-U ≤ (2 : ℝ) • 1)
    (hR : resolvent s V ≤ 1) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, resolvent s V - resolvent s U = resolvent s U * Z * resolvent s U ∧
      V-U ≤ Z ∧ Z ≤ (3 : ℝ) • (V-U) := by
  let H := V-U
  have h0 : 0 ≤ H := sub_nonneg.mpr hUV
  have hr0 : 0 ≤ resolvent s V := hV.inv.posSemidef.nonneg
  have hpos : 0 ≤ H * resolvent s V * H :=
    (IsSelfAdjoint.of_nonneg h0).conjugate_nonneg hr0
  have hbound : H * resolvent s V * H ≤ (2 : ℝ) • H := by
    calc
      _ ≤ H * 1 * H := (IsSelfAdjoint.of_nonneg h0).conjugate_le_conjugate hR
      _ = H*H := by simp
      _ ≤ (2 : ℝ) • H := square_le_two h0 hH
  refine ⟨H + H*resolvent s V*H, ?_, le_add_of_nonneg_right hpos, ?_⟩
  · have hd := resolvent_difference s U V hU hV
    have hd' := resolvent_difference s V U hV hU
    have he : resolvent s V - resolvent s U = resolvent s V * H * resolvent s U := by
      dsimp [H]
      calc
        _ = -(resolvent s U - resolvent s V) := by abel
        _ = -(resolvent s V * (U-V) * resolvent s U) := by rw [hd']
        _ = _ := by noncomm_ring
    calc
      _ = resolvent s U * H * resolvent s V := hd
      _ = resolvent s U * H * resolvent s U +
          resolvent s U * H * (resolvent s V - resolvent s U) := by noncomm_ring
      _ = resolvent s U * H * resolvent s U +
          resolvent s U * H * (resolvent s V * H * resolvent s U) := by rw [he]
      _ = _ := by noncomm_ring
  · calc
      _ ≤ H + (2 : ℝ) • H := add_le_add_right hbound H
      _ = (3 : ℝ) • (V-U) := by dsimp [H]; module

/-- At the upper endpoint a square-root factorization gives a factor between `H/3` and `H`.
In particular the result includes singular positive semidefinite increments. -/
private theorem upper_endpoint_factor (s : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - U).PosDef)
    (hV : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - V).PosDef)
    (hUV : U ≤ V) (hH : V-U ≤ (2 : ℝ) • 1)
    (hR : resolvent s V ≤ 1) :
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, resolvent s V - resolvent s U = resolvent s V * Z * resolvent s V ∧
      (1/3 : ℝ) • (V-U) ≤ Z ∧ Z ≤ V-U := by
  let H := V-U
  let Q := CFC.sqrt H
  let M := 1 + Q * resolvent s V * Q
  have h0 : 0 ≤ H := sub_nonneg.mpr hUV
  have hQ : 0 ≤ Q := CFC.sqrt_nonneg H
  have hQQ : Q * Q = H := CFC.sqrt_mul_sqrt_self H h0
  have hr0 : 0 ≤ resolvent s V := hV.inv.posSemidef.nonneg
  have hm0 : 0 ≤ Q * resolvent s V * Q :=
    (IsSelfAdjoint.of_nonneg hQ).conjugate_nonneg hr0
  have hM : M.PosDef := Matrix.PosDef.one.add_posSemidef (Matrix.nonneg_iff_posSemidef.mp hm0)
  have h1M : (1 : Matrix (Fin n) (Fin n) ℂ) ≤ M := le_add_of_nonneg_right hm0
  have hM3 : M ≤ (3 : ℝ) • 1 := by
    have hb : Q * resolvent s V * Q ≤ H := by
      simpa only [mul_one, hQQ] using
        (IsSelfAdjoint.of_nonneg hQ).conjugate_le_conjugate hR
    calc
      M ≤ 1 + (2 : ℝ) • 1 := add_le_add_right (hb.trans hH) 1
      _ = (3 : ℝ) • 1 := by module
  have hi3 : ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = (1/3 : ℝ) • 1 := by
    apply Matrix.inv_eq_right_inv
    norm_num [smul_mul_smul, smul_smul]
  have hp0 : (1/3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ M⁻¹ := by
    rw [← hi3]
    exact inverse_antitone hM (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 3)) hM3
  have hp1 : M⁻¹ ≤ 1 := by
    simpa using inverse_antitone Matrix.PosDef.one hM h1M
  have hd := resolvent_difference s U V hU hV
  have hd' : resolvent s V - resolvent s U = resolvent s V * H * resolvent s U := by
    have he := resolvent_difference s V U hV hU
    dsimp [H]
    calc
      _ = -(resolvent s U - resolvent s V) := by abel
      _ = -(resolvent s V * (U-V) * resolvent s U) := by rw [he]
      _ = _ := by noncomm_ring
  have hinv : M⁻¹ = 1 - Q * resolvent s U * Q := by
    have hinner : (resolvent s V)⁻¹ + Q * (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ * Q =
        s • 1 - U := by
      rw [show (resolvent s V)⁻¹ = s • 1 - V from
        Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit)]
      simp only [inv_one, mul_one, hQQ]
      dsimp [H]
      abel
    have h := Matrix.add_mul_mul_inv_eq_sub (1 : Matrix (Fin n) (Fin n) ℂ)
      Q (resolvent s V) Q isUnit_one hV.inv.isUnit (by rw [hinner]; exact hU.isUnit)
    rw [hinner] at h
    simpa only [M, inv_one, one_mul, mul_one, resolvent] using h
  refine ⟨Q * M⁻¹ * Q, ?_, ?_, ?_⟩
  · rw [hinv]
    have he : Q * (1-Q*resolvent s U*Q) * Q = H-H*resolvent s U*H := by
      calc
        _ = Q*Q - (Q*Q)*resolvent s U*(Q*Q) := by noncomm_ring
        _ = _ := by rw [hQQ]
    rw [he]
    calc
      _ = resolvent s V * H * resolvent s U := hd'
      _ = resolvent s V * H * resolvent s V -
          resolvent s V * H * (resolvent s V - resolvent s U) := by noncomm_ring
      _ = resolvent s V * H * resolvent s V -
          resolvent s V * H * (resolvent s U * H * resolvent s V) := by rw [hd]
      _ = _ := by noncomm_ring
  · simpa only [mul_smul_comm, smul_mul_assoc, mul_one, hQQ] using
      (IsSelfAdjoint.of_nonneg hQ).conjugate_le_conjugate hp0
  · simpa only [mul_one, hQQ] using
      (IsSelfAdjoint.of_nonneg hQ).conjugate_le_conjugate hp1

/-- Both endpoint factors are uniformly controlled throughout the Cayley interval. -/
theorem endpoint_resolvent_factors (s : ℝ) (hs : 2 ≤ s)
    (U V : Matrix (Fin n) (Fin n) ℂ)
    (hUl : (1 + U).PosDef) (hUr : (1 - U).PosDef)
    (hVr : (1 - V).PosDef) (hUV : U ≤ V) :
    (∃ Z : Matrix (Fin n) (Fin n) ℂ,
      resolvent s V - resolvent s U = resolvent s U * Z * resolvent s U ∧
      V-U ≤ Z ∧ Z ≤ (3 : ℝ) • (V-U)) ∧
    (∃ Z : Matrix (Fin n) (Fin n) ℂ,
      resolvent s V - resolvent s U = resolvent s V * Z * resolvent s V ∧
      (1/3 : ℝ) • (V-U) ≤ Z ∧ Z ≤ V-U) := by
  have hshift : (0 : ℝ) ≤ s-2 := sub_nonneg.mpr hs
  have hUp : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - U).PosDef := by
    have ht := hUr.add_posSemidef (Matrix.PosSemidef.one.smul hshift)
    convert ht.add_posSemidef Matrix.PosSemidef.one using 1 <;> module
  have hVp : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - V).PosDef := by
    have ht := hVr.add_posSemidef (Matrix.PosSemidef.one.smul hshift)
    convert ht.add_posSemidef Matrix.PosSemidef.one using 1 <;> module
  have hU0 : -(1 : Matrix (Fin n) (Fin n) ℂ) ≤ U := by
    have h := hUl.posSemidef.nonneg
    exact neg_le_iff_add_nonneg.mpr (by simpa [add_comm] using h)
  have hV1 : V ≤ 1 := sub_nonneg.mp hVr.posSemidef.nonneg
  have hH : V-U ≤ (2 : ℝ) • 1 := by
    calc
      V-U ≤ 1-(-1) := sub_le_sub hV1 hU0
      _ = (2 : ℝ) • 1 := by module
  have hR : resolvent s V ≤ 1 := by
    have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ≤ s • 1 - V := by
      apply sub_nonneg.mp
      have hnon : 0 ≤ (s-2) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
        (Matrix.PosSemidef.one.smul hshift).nonneg
      convert add_nonneg hVr.posSemidef.nonneg hnon using 1 <;> module
    simpa [resolvent] using inverse_antitone Matrix.PosDef.one hVp h1
  exact ⟨lower_endpoint_factor s U V hUp hVp hUV hH hR,
    upper_endpoint_factor s U V hUp hVp hUV hH hR⟩

/-- The Cayley map from the positive cone to the open matrix interval. -/
def cayley (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - (2 : ℝ) • (A+1)⁻¹

/-- The Cayley map takes positive definite matrices into the open interval and preserves order.
Consumed bind-only auxiliary for `CzerwinskaFrancoMerinoCounterexample.radial_counterexample`. -/
theorem cayley_transport (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (1+cayley A).PosDef ∧ (1-cayley A).PosDef ∧
      ∀ B : Matrix (Fin n) (Fin n) ℂ, B.PosDef → A ≤ B → cayley A ≤ cayley B := by
  have hP : (A+1).PosDef := hA.add Matrix.PosDef.one
  have hR := hP.inv
  have hleft := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit)
  have hright := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit)
  have hc : Commute A (A+1)⁻¹ := by
    change A*(A+1)⁻¹ = (A+1)⁻¹*A
    calc
      _ = (A+1)*(A+1)⁻¹ - (A+1)⁻¹ := by noncomm_ring
      _ = 1-(A+1)⁻¹ := by rw [hright]
      _ = (A+1)⁻¹*(A+1) - (A+1)⁻¹ := by rw [hleft]
      _ = _ := by noncomm_ring
  have hp : (A*(A+1)⁻¹).PosDef :=
    Matrix.IsStrictlyPositive.posDef ((hA.isStrictlyPositive.commute_iff hR.isStrictlyPositive).mp hc)
  have he : A*(A+1)⁻¹ = 1-(A+1)⁻¹ := by
    calc
      _ = (A+1)*(A+1)⁻¹ - (A+1)⁻¹ := by noncomm_ring
      _ = _ := by rw [hright]
  refine ⟨?_, ?_, ?_⟩
  · convert hp.smul (by norm_num : (0 : ℝ) < 2) using 1
    rw [he]
    dsimp [cayley]
    module
  · convert hR.smul (by norm_num : (0 : ℝ) < 2) using 1
    dsimp [cayley]
    module
  · intro B hB hAB
    have hQ : (B+1).PosDef := hB.add Matrix.PosDef.one
    have hi := inverse_antitone hP hQ (add_le_add_left hAB 1)
    apply Matrix.le_iff.mpr
    have hn := (Matrix.le_iff.mp hi).smul (by norm_num : (0 : ℝ) ≤ 2)
    convert hn using 1 <;> dsimp [cayley] <;> module

/-- A resolvent of the Cayley image is the corresponding rational expression on the cone.
Consumed bind-only auxiliary for
`CzerwinskaFrancoMerinoCounterexample.cayley_functional_calculus`. -/
theorem cayley_resolvent (s : ℝ) (hs : 2 ≤ s)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    resolvent s (cayley A) =
      (A + 1) * ((s-1) • A + (s+1) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ := by
  have hP : (A+1).PosDef := hA.add Matrix.PosDef.one
  have hQ : ((s-1) • A + (s+1) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    (hA.smul (by linarith : (0 : ℝ) < s-1)).add_posSemidef
      (Matrix.PosSemidef.one.smul (by linarith : (0 : ℝ) ≤ s+1))
  have hi := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit)
  have hq := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ.isUnit)
  have he : (s • (1 : Matrix (Fin n) (Fin n) ℂ) - cayley A) * (A+1) =
      (s-1) • A + (s+1) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    dsimp [cayley]
    simp only [sub_mul, smul_mul_assoc, one_mul]
    rw [hi]
    module
  unfold resolvent
  apply Matrix.inv_eq_right_inv
  rw [← mul_assoc, he, hq]

end D5.S3.Quantum.Matrix.CayleyResolvent
