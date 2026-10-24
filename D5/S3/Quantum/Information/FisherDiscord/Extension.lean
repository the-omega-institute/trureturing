/- GID: D5/S3/Quantum/Information/FisherDiscord/Extension
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FisherDiscord/Extension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Flagged extensions have the prescribed marginal and zero Fisher discord; the universal extension inequality forces zero marginal discord. -/

import D5.S3.Quantum.Information.FisherDiscord.Spectral
import D5.S3.Quantum.Decoherence.EnvironmentMarginalChannel

noncomputable section
open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Information.FisherDiscord.Extension
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Information.FisherDiscord.Defs
open D5.S3.Quantum.Information.FisherDiscord.Spectral

set_option maxHeartbeats 800000

variable {n : ℕ}

/-- The classical flag extension of a diagonal state. -/
def flagExtension (w : Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  diagonal (fun x => ((if x.2 = x.1 then w x.1 else 0 : ℝ) : ℂ))

/-- The flagged state has the original diagonal as its second-factor marginal. -/
theorem flag_partialTrace (w : Fin n → ℝ) :
    partialTrace₂ (flagExtension w) = diagonal (fun i => (w i : ℂ)) := by
  classical
  let record : Fin n → Fin n → ℂ := fun i b => if i = b then 1 else 0
  let V : Matrix (Fin n × Fin n) (Fin n) ℂ :=
    fun x j => if j = x.1 then record x.1 x.2 else 0
  have hV : V * diagonal (fun i => (w i : ℂ)) * V.conjTranspose = flagExtension w := by
    ext ⟨i, b⟩ ⟨j, c⟩
    rw [Matrix.mul_apply (M := V * diagonal (fun i => (w i : ℂ)))
      (N := V.conjTranspose)]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    simp [V, record, flagExtension, Matrix.diagonal_apply, Prod.ext_iff] <;>
      split_ifs <;> simp_all <;> aesop
  have hm := (D5.S3.Quantum.Decoherence.EnvironmentMarginalChannel.environment_marginal_channel
    record (diagonal (fun i => (w i : ℂ)))).1
  change partialTrace₂ (V * diagonal (fun i => (w i : ℂ)) * V.conjTranspose) =
    D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality.recordChannel record (diagonal (fun i => (w i : ℂ))) at hm
  rw [hV] at hm
  rw [hm]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality.recordChannel,
      D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality.recordGram, record]
  · simp [D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality.recordChannel,
      Matrix.diagonal_apply_ne _ hij, hij]

private theorem flag_term_zero (w : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n × Fin n) :
    pairKernel (if x.2 = x.1 then w x.1 else 0)
        (if y.2 = y.1 then w y.1 else 0) *
      Complex.normSq (liftLeft (d₂ := n) H x y) = 0 := by
  classical
  delta liftLeft pairKernel
  by_cases hxy : x.2 = y.2
  · by_cases hx : x.2 = x.1
    · by_cases hy : y.2 = y.1
      · have hxeq : x = y := by
          apply Prod.ext
          · exact hx.symm.trans (hxy.trans hy)
          · exact hxy
        subst y
        simp [Matrix.kroneckerMap_apply]
      · simp [Matrix.kroneckerMap_apply, hy]
    · simp [Matrix.kroneckerMap_apply, hx]
  · simp [Matrix.kroneckerMap_apply, hxy]

/- The product-indexed sum in the flag calculation is deliberately reduced by the diagonal
   support before invoking the spectral formula. -/
/- Every Hermitian SLD on a flagged extension has zero Fisher discord for a lifted observable. -/
theorem flag_discord_zero (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (H : Matrix (Fin n) (Fin n) ℂ)
    (L : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hH : H.IsHermitian)
    (hL : IsSLD (flagExtension w) (liftLeft (d₂ := n) H) L) :
    fisherSLD (flagExtension w) L - skewWY (flagExtension w) (liftLeft (d₂ := n) H) = 0 := by
  have hL' : IsSLD
      (diagonal (fun x : Fin n × Fin n =>
        ((if x.2 = x.1 then w x.1 else 0 : ℝ) : ℂ)))
      (liftLeft (d₂ := n) H) L := by
    simpa [flagExtension] using hL
  have hD := discord_diag
    (w := fun x : Fin n × Fin n => if x.2 = x.1 then w x.1 else 0)
    (hw := by intro x; split_ifs with hx; exact hw x.1; positivity)
    (H := liftLeft (d₂ := n) H) (L := L)
    (D5.S3.Quantum.Information.PartialTraceMutualInformation.isHermitian_kronecker
      hH (Matrix.isHermitian_one)) hL'
  change fisherSLD
      (diagonal (fun x : Fin n × Fin n =>
        ((if x.2 = x.1 then w x.1 else 0 : ℝ) : ℂ))) L -
      skewWY (diagonal (fun x : Fin n × Fin n =>
        ((if x.2 = x.1 then w x.1 else 0 : ℝ) : ℂ))) (liftLeft (d₂ := n) H) = 0
  rw [hD]
  have hsum : (∑ x, ∑ y,
      pairKernel (if x.2 = x.1 then w x.1 else 0)
        (if y.2 = y.1 then w y.1 else 0) *
          Complex.normSq (liftLeft (d₂ := n) H x y)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.sum_eq_zero
    intro y hy
    exact flag_term_zero w _ x y
  rw [hsum]
  norm_num

def extensionIneq (w : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (L : Matrix (Fin n) (Fin n) ℂ)
    (d₂ : ℕ) : Prop :=
  ∀ (σ : Matrix (Fin n × Fin d₂) (Fin n × Fin d₂) ℂ)
    (Lσ : Matrix (Fin n × Fin d₂) (Fin n × Fin d₂) ℂ),
    IsDensity σ → partialTrace₂ σ = diagonal (fun i => (w i : ℂ)) →
    IsSLD σ (liftLeft (d₂ := d₂) H) Lσ →
    fisherSLD (diagonal (fun i => (w i : ℂ))) L -
        skewWY (diagonal (fun i => (w i : ℂ))) H ≤
      fisherSLD σ Lσ - skewWY σ (liftLeft (d₂ := d₂) H)

/-- For a diagonal marginal, the inequality against every extension forces zero discord.
The flag gives the upper bound, and general spectral nonnegativity gives the lower bound. -/
theorem monotone_discord_zero (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (htrace : ∑ i, w i = 1)
    (H L : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L)
    (hFlag : ∃ LF, IsSLD (flagExtension w) (liftLeft (d₂ := n) H) LF) :
    (∀ d₂, extensionIneq w H L d₂) →
      fisherSLD (diagonal (fun i => (w i : ℂ))) L -
        skewWY (diagonal (fun i => (w i : ℂ))) H = 0 := by
  intro hAll
  dsimp [extensionIneq] at hAll
  obtain ⟨LF, hLF⟩ := hFlag
  have hσ : IsDensity (flagExtension w) := by
    constructor
    · exact Matrix.PosSemidef.diagonal (fun x => by
        split_ifs
        · exact Complex.zero_le_real.mpr (hw x.1)
        · exact le_rfl)
    · rw [flagExtension, Matrix.trace_diagonal, Fintype.sum_prod_type]
      norm_cast
      have hinner : ∀ i : Fin n, (∑ b, if b = i then w i else 0) = w i := by
        intro i
        simpa [eq_comm] using (Fintype.sum_ite_eq i (fun _ => w i))
      simp_rw [hinner]
      exact htrace
  have hMarg := flag_partialTrace w
  have hineq := hAll n (flagExtension w) LF hσ hMarg hLF
  have hzeroFlag := flag_discord_zero w hw H LF hH hLF
  have hineq' : fisherSLD (diagonal (fun i => (w i : ℂ))) L -
      skewWY (diagonal (fun i => (w i : ℂ))) H ≤ 0 := by
    calc
      _ ≤ fisherSLD (flagExtension w) LF -
          skewWY (flagExtension w) (liftLeft (d₂ := n) H) := hineq
      _ = 0 := hzeroFlag
  clear hineq hzeroFlag
  have hρ : (diagonal (fun i => (w i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hw i))
  have hnonneg := discord_nonneg _ H L hρ hH hL
  exact le_antisymm hineq' hnonneg

end D5.S3.Quantum.Information.FisherDiscord.Extension
