/- GID: D5/S3/Quantum/Lieb/FiniteOrder/SingularRatio
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/FiniteOrder/SingularRatio
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Two regularizations extend the finite-order ratio inequality to singular positive matrices without continuity at zero. -/
module

public import D5.S3.Quantum.Lieb.FiniteOrder.Ratio

/-! The quotient uses total division, so its value at zero is zero even when
both numerator and denominator vanish. Only finite spectral pointwise limits
are used when the positive constant added to the function tends to zero. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Lieb.FiniteOrder
open Matrix Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem finite_cfc_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} {l : Filter α} {F : α → ℝ → ℝ} {f : ℝ → ℝ}
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (h : ∀ t ∈ spectrum ℝ A, Tendsto (fun x => F x t) l (𝓝 (f t))) :
    Tendsto (fun x => cfc (F x) A) l (𝓝 (cfc f A)) := by
  have hd : Tendsto (fun x => Matrix.diagonal (fun i => (F x (hA.eigenvalues i) : ℂ))) l
      (𝓝 (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq, Function.comp_def] using
        (Complex.continuous_ofReal.tendsto _).comp (h _ (hA.eigenvalues_mem_spectrum_real i))
    · simpa only [Matrix.diagonal_apply_ne _ hij] using
        (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℂ)) l (𝓝 0))
  simpa only [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
    (tendsto_const_nhds.mul hd).mul_const (star (hA.eigenvectorUnitary : Matrix ι ι ℂ))

private theorem shift_cfc_tendsto {n : ℕ} (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici 0)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) :
    Tendsto (fun δ : ℝ => cfc g (A + δ • 1)) (𝓝[>] 0) (𝓝 (cfc g A)) := by
  let G : ℝ → ℝ := fun t => g (max t 0)
  have hG : Continuous G := hg.comp_continuous (continuous_id.max continuous_const)
    (fun t => le_max_right t 0)
  have hshift (δ : ℝ) (hδ : δ ∈ Set.Ici (0 : ℝ)) : 0 ≤ A + δ • 1 :=
    add_nonneg hA.nonneg (smul_nonneg hδ zero_le_one)
  have hcG : ContinuousOn (fun δ : ℝ => cfc G (A + δ • 1)) (Set.Ici 0) := by
    apply ContinuousOn.cfc_of_mem_nhdsSet G (s := Set.univ) (by simp)
      (by fun_prop) (fun δ hδ => IsSelfAdjoint.of_nonneg (hshift δ hδ)) hG.continuousOn
  have hc : ContinuousOn (fun δ : ℝ => cfc g (A + δ • 1)) (Set.Ici 0) := by
    refine hcG.congr ?_
    intro δ hδ
    apply cfc_congr
    intro t ht
    exact (congrArg g (max_eq_left (spectrum_nonneg_of_nonneg (hshift δ hδ) ht))).symm
  simpa using ((hc.continuousWithinAt (show (0 : ℝ) ∈ Set.Ici 0 by simp)).mono
    Set.Ioi_subset_Ici_self).tendsto

private theorem ratio_regularized_monotone (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0)) (hf0 : 0 ≤ f 0)
    (hfpos : ∀ t : ℝ, 0 < t → 0 < f t)
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (ε : ℝ) (hε : 0 < ε)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A ≤ B) :
    cfc (fun t => t / (f t + ε)) A ≤ cfc (fun t => t / (f t + ε)) B := by
  have hfnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
    rcases ht.eq_or_lt with rfl | ht
    · exact hf0
    · exact (hfpos t ht).le
  have hfε : ContinuousOn (fun t => f t + ε) (Set.Ici 0) := hf.add continuousOn_const
  have hfεpos (t : ℝ) (ht : 0 ≤ t) : 0 < f t + ε :=
    add_pos_of_nonneg_of_pos (hfnonneg t ht) hε
  have hg : ContinuousOn (fun t => t / (f t + ε)) (Set.Ici 0) :=
    continuousOn_id.div hfε (fun t ht => (hfεpos t ht).ne')
  have hmε : ∀ (X Y : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      X.PosSemidef → Y.PosSemidef → X ≤ Y →
        cfc (fun t => f t + ε) X ≤ cfc (fun t => f t + ε) Y := by
    intro X Y hX hY hXY
    have he (Z : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (hZ : Z.PosSemidef) :
        cfc (fun t => f t + ε) Z = cfc f Z + ε • 1 := by
      exact (cfc_add_const ε f Z (Z.finite_real_spectrum.continuousOn _) hZ.isHermitian).trans
        (congrArg (fun W => cfc f Z + W) (Algebra.algebraMap_eq_smul_one ε))
    rw [he X hX, he Y hY]
    exact add_le_add (hmono X Y hX hY hXY) le_rfl
  have hshift (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef)
      (δ : ℝ) (hδ : 0 < δ) : (X + δ • 1).PosDef :=
    (IsStrictlyPositive.nonneg_add hX.nonneg (isStrictlyPositive_one.smul hδ)).posDef
  apply le_of_tendsto_of_tendsto (shift_cfc_tendsto _ hg A hA)
    (shift_cfc_tendsto _ hg B hB)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact ratio_monotone_posDef n (fun t => f t + ε) hfε
    (fun t ht => hfεpos t ht.le) hmε (A + δ • 1) (B + δ • 1)
    (hshift A hA δ hδ) (hshift B hB δ hδ) (add_le_add hAB le_rfl)

/-- Finite doubled-order monotonicity makes the zero-extension `t / f(t)`
matrix monotone on all positive semidefinite `n` by `n` matrices, including
singular inputs and functions vanishing at zero. Continuity of the quotient
at zero is not a hypothesis. -/
theorem ratio_monotone_posSemidef (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    (hfpos : ∀ t : ℝ, 0 < t → 0 < f t)
    (hmono : ∀ (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A ≤ B) :
    cfc (fun t => t / f t) A ≤ cfc (fun t => t / f t) B := by
  have hf0 : 0 ≤ f 0 := by
    have ht := ((hf.continuousWithinAt (show (0 : ℝ) ∈ Set.Ici 0 by simp)).mono
      Set.Ioi_subset_Ici_self).tendsto
    exact ge_of_tendsto ht (Filter.mem_of_superset self_mem_nhdsWithin
      (fun t ht => (hfpos t ht).le))
  have ht (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) :
      Tendsto (fun ε : ℝ => cfc (fun t => t / (f t + ε)) X) (𝓝[>] 0)
        (𝓝 (cfc (fun t => t / f t) X)) := by
    apply finite_cfc_tendsto X hX.isHermitian
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
    · have hft : f t ≠ 0 := (hfpos t
        (lt_of_le_of_ne (spectrum_nonneg_of_nonneg hX.nonneg ht) (Ne.symm ht0))).ne'
      have hc : ContinuousAt (fun ε : ℝ => t / (f t + ε)) 0 :=
        continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simpa using hft)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto (ht A hA) (ht B hB)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ratio_regularized_monotone n f hf hf0 hfpos hmono ε hε A B hA hB hAB

#print axioms ratio_monotone_posSemidef
end D5.S3.Quantum.Lieb.FiniteOrder
