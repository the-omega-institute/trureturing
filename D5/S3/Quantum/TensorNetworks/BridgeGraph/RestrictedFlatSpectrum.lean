/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.claim; result=D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.result; claim=D5/S3/Quantum/TensorNetworks/BridgeGraph/RestrictedFlatSpectrum.claim
   digest: Coefficient-direction rigidity refutes the restricted native scalar-Gram cone. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Exact scalar-Gram rigidity in the finite native rectangular family. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum

open Matrix Module
open scoped ComplexConjugate

/-- The native eight-premise cone assertion, with a single positive scalar at equality. -/
def claim : Prop :=
  ∀ (a b c d : ℕ), 0 < a → a ≤ b → 0 < c → c ≤ d →
    a * a + b * b ≤ 3 * a * b → c * c + d * d ≤ 3 * c * d →
    2 * b ≤ 5 * a → 2 * d ≤ 5 * c →
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (lam : ℝ), 0 < lam ∧
      (b * c ≤ a * d →
        (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
          (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) ∧
      (a * d ≤ b * c →
        QuantumMaxFlowBound.flow M N * (QuantumMaxFlowBound.flow M N)ᴴ =
          (lam : ℂ) • (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ))

private theorem coefficient_direction {a b : ℕ}
    (M : Fin 3 → EuclideanSpace ℂ (Fin b) →ₗ[ℂ] EuclideanSpace ℂ (Fin a))
    (hM : ∀ x, (∀ r, M r x = 0) → x = 0) (hab : 2 * a < b)
    (z : Fin 3 → ℂ) (hz : z ≠ 0) :
    ∃ x u, u ≠ 0 ∧ ∀ r, M r x = z r • u := by
  classical
  let V := LinearMap.pi M
  let D : EuclideanSpace ℂ (Fin a) →ₗ[ℂ] (Fin 3 → EuclideanSpace ℂ (Fin a)) :=
    { toFun := fun u r => z r • u
      map_add' := by intros; ext r; simp [smul_add]
      map_smul' := by intros; ext r; simp [smul_smul, mul_comm] }
  have hV : Function.Injective V := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply hM x
    intro r
    exact congrFun hx r
  have hD : Function.Injective D := by
    obtain ⟨r, hr⟩ : ∃ r, z r ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hz
    intro u v huv
    have he := congrFun huv r
    exact (smul_right_injective _ hr) he
  by_contra! h
  have hd : Disjoint (LinearMap.range V) (LinearMap.range D) := by
    rw [Submodule.disjoint_def]
    intro v hv hw
    obtain ⟨x, rfl⟩ := hv
    obtain ⟨u, hu⟩ := hw
    have he : ∀ r, M r x = z r • u := fun r => (congrFun hu r).symm
    have hu0 : u = 0 := by
      by_contra hn
      obtain ⟨r, hr⟩ := h x u hn
      exact hr (he r)
    simp [hu0] at hu
    exact hu.symm
  have hdims := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [LinearMap.finrank_range_of_inj hV, LinearMap.finrank_range_of_inj hD] at hdims
  simp only [finrank_euclideanSpace, Fintype.card_fin, Module.finrank_pi_fintype] at hdims
  norm_num at hdims
  omega

private theorem gram_independent {a b : ℕ}
    (M : Fin 3 → EuclideanSpace ℂ (Fin b) →ₗ[ℂ] EuclideanSpace ℂ (Fin a))
    (hM : ∀ x, (∀ r, M r x = 0) → x = 0) (hab : 2 * a < b) :
    LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => (M p.1).adjoint.comp (M p.2)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro t ht
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s => t (r, s)
  have hq (z : EuclideanSpace ℂ (Fin 3)) :
      inner ℂ z (T.toEuclideanLin z) = 0 := by
    by_cases hz : z = 0
    · simp [hz]
    obtain ⟨x, u, hu, hx⟩ := coefficient_direction M hM hab (WithLp.ofLp z)
      (by intro h; exact hz (WithLp.ofLp_injective 2 h))
    have he := congrArg (fun A : EuclideanSpace ℂ (Fin b) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin b) => inner ℂ x (A x)) ht
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      inner_sum, inner_smul_right, LinearMap.adjoint_inner_right,
      LinearMap.zero_apply, inner_zero_right] at he
    simp_rw [hx, inner_smul_left, inner_smul_right] at he
    have he' : (∑ p : Fin 3 × Fin 3, t p * (star (z p.1) * z p.2)) *
        inner ℂ u u = 0 := by
      rw [Finset.sum_mul]
      convert he using 1
      apply Finset.sum_congr rfl
      intro p _
      simp only [starRingEnd_apply]
      ring
    have hs := (mul_eq_zero.mp he').resolve_right (inner_self_ne_zero.mpr hu)
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.mul_sum, T,
      mul_assoc, mul_left_comm, mul_comm] using hs
  have hT : T.toEuclideanLin = 0 := by
    apply (inner_map_self_eq_zero _).mp
    intro z
    rw [← inner_conj_symm, hq]
    simp
  have hT0 : T = 0 := Matrix.toEuclideanLin.injective (by simpa using hT)
  intro p
  exact congrFun (congrFun hT0 p.1) p.2

private theorem matrix_gram_independent {a b : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hM : ∀ x : EuclideanSpace ℂ (Fin b),
      (∀ r, (M r).toEuclideanLin x = 0) → x = 0) (hab : 2 * a < b) :
    LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => (M p.1)ᴴ * M p.2) := by
  have h := gram_independent (fun r => (M r).toEuclideanLin) hM hab
  have he : (fun p : Fin 3 × Fin 3 => (M p.1).toEuclideanLin.adjoint.comp
      (M p.2).toEuclideanLin) =
      fun p => Matrix.toEuclideanLin ((M p.1)ᴴ * M p.2) := by
    funext p
    simp [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [he] at h
  exact h.of_comp

/-- Above the threshold `b > 2a`, a native scalar column Gram forces `d ≥ 3c`. -/
theorem obstruction {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (hc : 0 < c)
    (hab : 2 * a < b) (lam : ℝ) (hlam : 0 < lam)
    (hF : (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
      (lam : ℂ) • 1) : 3 * c ≤ d := by
  classical
  have hlam' : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)
  have hLI := matrix_gram_independent M
    (FlatSpectrumObstruction.flow_common_kernel M N hc hlam' hF) hab
  let k : Fin c := ⟨0, hc⟩
  let H : Matrix (Fin 3) (Fin 3) ℂ := fun r s => ((N r)ᴴ * N s) k k
  have hN : ∀ r s, (N r)ᴴ * N s = H r s • 1 :=
    FlatSpectrumObstruction.scalar_cross_grams M N k hLI hF
  have hJ : (FlatSpectrumObstruction.stack M)ᴴ *
      Matrix.kronecker H (1 : Matrix (Fin a) (Fin a) ℂ) *
      FlatSpectrumObstruction.stack M = (lam : ℂ) • 1 :=
    FlatSpectrumObstruction.stack_gram M N k hF
  have hbr : b ≤ a * H.rank := by
    calc
      b = ((lam : ℂ) • (1 : Matrix (Fin b) (Fin b) ℂ)).rank := by
        rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
          (mem_nonZeroDivisors_of_ne_zero hlam'), Matrix.rank_one]
        simp
      _ = ((FlatSpectrumObstruction.stack M)ᴴ *
          Matrix.kronecker H (1 : Matrix (Fin a) (Fin a) ℂ) *
          FlatSpectrumObstruction.stack M).rank := congrArg Matrix.rank hJ.symm
      _ ≤ (Matrix.kronecker H (1 : Matrix (Fin a) (Fin a) ℂ)).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ = a * H.rank := FlatSpectrumObstruction.rank_kronecker_one H a
  have hr : H.rank = 3 := by
    have hle : H.rank ≤ 3 := by simpa using H.rank_le_card_width
    by_contra hne
    have htwo : H.rank ≤ 2 := by omega
    have hmul := Nat.mul_le_mul_left a htwo
    omega
  calc
    3 * c = (Matrix.kronecker H (1 : Matrix (Fin c) (Fin c) ℂ)).rank := by
      rw [FlatSpectrumObstruction.rank_kronecker_one, hr]
      omega
    _ = ((FlatSpectrumObstruction.concat N)ᴴ *
        FlatSpectrumObstruction.concat N).rank :=
      congrArg Matrix.rank (FlatSpectrumObstruction.concat_gram N H hN).symm
    _ ≤ (FlatSpectrumObstruction.concat N).rank := Matrix.rank_mul_le_right _ _
    _ ≤ d := by simpa using (FlatSpectrumObstruction.concat N).rank_le_card_height

/-- The permitted equality tuple `(2,5,2,5)` contradicts the live obstruction. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨M, N, lam, hlam, hcol, _⟩ :=
    h 2 5 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdim := obstruction M N (by norm_num) (by norm_num) lam hlam (hcol (by norm_num))
  norm_num at hdim

end D5.S3.Quantum.TensorNetworks.BridgeGraph.RestrictedFlatSpectrum
