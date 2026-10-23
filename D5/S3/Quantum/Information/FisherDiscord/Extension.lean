/- GID: D5/S3/Quantum/Information/FisherDiscord/Extension
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FisherDiscord/Extension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Flagged extensions have the prescribed marginal and zero Fisher discord; the universal extension inequality is equivalent to zero marginal discord. -/

import D5.S3.Quantum.Information.FisherDiscord.Spectral

noncomputable section
open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Information.FisherDiscord.Extension
open D5.S3.Quantum.Information.FisherDiscord.Defs
open D5.S3.Quantum.Information.FisherDiscord.Spectral

set_option maxHeartbeats 800000

variable {n : ℕ}

private theorem liftLeft_isHermitian (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (d₂ : ℕ) :
    (liftLeft (d₂ := d₂) H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  by_cases hxy : x.2 = y.2
  · simp [liftLeft, Matrix.kroneckerMap_apply, Matrix.one_apply, hxy, hH.apply]
  · have hyx : y.2 ≠ x.2 := Ne.symm hxy
    simp [liftLeft, Matrix.kroneckerMap_apply, hxy, hyx]

/-- The classical flag extension of a diagonal state. -/
def flagExtension (w : Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  diagonal (fun x => ((if x.2 = x.1 then w x.1 else 0 : ℝ) : ℂ))

/-- The flagged state has the original diagonal as its second-factor marginal. -/
theorem flag_partialTrace (w : Fin n → ℝ) :
    partialTrace₂ (flagExtension w) = diagonal (fun i => (w i : ℂ)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTrace₂, flagExtension, Matrix.diagonal_apply_eq]
    norm_cast
    simp [Finset.sum_ite_eq']
  · simp [partialTrace₂, flagExtension, Matrix.diagonal_apply_ne, hij]

private theorem flag_term_zero (w : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n × Fin n) :
    pairKernel (if x.2 = x.1 then w x.1 else 0)
        (if y.2 = y.1 then w y.1 else 0) *
      Complex.normSq (liftLeft (d₂ := n) H x y) = 0 := by
  classical
  by_cases hxy : x.2 = y.2
  · by_cases hx : x.2 = x.1
    · by_cases hy : y.2 = y.1
      · have hxeq : x = y := by
          apply Prod.ext
          · exact hx.symm.trans (hxy.trans hy)
          · exact hxy
        subst y
        simp [liftLeft, Matrix.kroneckerMap_apply, pairKernel]
      · simp [liftLeft, Matrix.kroneckerMap_apply, hy, pairKernel]
    · simp [liftLeft, Matrix.kroneckerMap_apply, hx, pairKernel]
  · simp [liftLeft, Matrix.kroneckerMap_apply, hxy, pairKernel]

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
    (liftLeft_isHermitian H hH n) hL'
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

/-- For a diagonal marginal, the inequality against every extension is equivalent to zero discord.
The flag extension supplies the converse direction, while spectral nonnegativity supplies the forward direction. -/
theorem monotone_iff_discord_zero (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (htrace : ∑ i, w i = 1)
    (H L : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hL : IsSLD (diagonal (fun i => (w i : ℂ))) H L)
    (hFlag : ∃ LF, IsSLD (flagExtension w) (liftLeft (d₂ := n) H) LF) :
    (∀ d₂, extensionIneq w H L d₂) ↔
      fisherSLD (diagonal (fun i => (w i : ℂ))) L -
        skewWY (diagonal (fun i => (w i : ℂ))) H = 0 := by
  constructor
  · intro hAll
    dsimp [extensionIneq] at hAll
    obtain ⟨LF, hLF⟩ := hFlag
    have hσ : IsDensity (flagExtension w) := by
      constructor
      · exact Matrix.PosSemidef.diagonal (fun x => by
          split_ifs
          · exact Complex.zero_le_real.mpr (hw x.1)
          · exact le_rfl)
      · rw [Matrix.trace]
        simp only [flagExtension, Matrix.diag, Matrix.diagonal_apply_eq]
        rw [Fintype.sum_prod_type]
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
    have hnonneg := discord_nonneg_diag w hw H L hH hL
    linarith [hineq']
  · intro hzero d₂ σ Lσ hσ hMarg hLσ
    rw [hzero]
    have hHL := liftLeft_isHermitian H hH d₂
    exact discord_nonneg σ (liftLeft (d₂ := d₂) H) Lσ hσ.1 hHL hLσ

end D5.S3.Quantum.Information.FisherDiscord.Extension
