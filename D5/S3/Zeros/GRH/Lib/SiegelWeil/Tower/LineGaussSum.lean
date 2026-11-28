/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/LineGaussSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/Tower/LineGaussSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.Tower.LineGaussSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/Tower/LineGaussSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.EquivariantCoefficients
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Tower property: constant term of a theta lift along an isotropic line (known result;
see Lib.SiegelWeil.Tower.LargeSideConstantTerm).

This file: Finite part of isotropic-line term for standard ramified data is a Gauss sum. -/


open Matrix WeilData MeasureTheory SemilocalField Space Splitting Fintype MatMul
variable {E n n' r r' b s s' t t'} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n']
  [Fintype r] [Fintype r'] {W : Space E n s} {W' : Space E n' s'} {V : Space E r t}
  {V' : Space E r' t'} [Fintype b] (A : W'.Splitting W Unit) (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n)
attribute [local simp] stdColDatum stdForm adaptedFrame mulVec dotProduct iCoord sum_prod_type
  vecToMat matToVec mul_assoc Matrix.mul_apply

/-- For adapted A, X there are units κ_β such that, for tame χ, some γ with |γ|² = vol(ϖO) has:
the term `lineTerm` at x = αa, α = `scaleIdele` E, of the standard datum of s·I′ with
I′ = (`adaptedFrame` r A).I', is κ_β γ χ⁻¹(a)χ(ϖā) times that
of s, and 0 unless a is integral off S̄ and a, ϖā are units at S. -/
lemma exists_lineTerm_localDatum X [IsBaseAdapted A] [IsBaseAdapted X] : ∃ l : _ → ℂˣ,
  ∀ {F} [SemilocalField F] {S π} {χ : MulChar F _} (r : ReadsAt S π) (h : TameLocalChar χ),
  ∃ γ, ‖γ‖ ^ 2 = (Nat.card h.ResidueRing : ℝ)⁻¹ ∧ ∀ s β v x, let a := x * (scaleIdele
    E)⁻¹.1; lineTerm A X β x (localDatum _ V' v (stdRowDatum σ' χ (s * (adaptedFrame r A).I')) r) =
  (l β * γ * ite (idem S.conjClosureᶜ * a.2 ∈ Ô E) (invOnUnits χ (π a.2) / invOnUnits χ
    (π (star a.2) * ϖ.1)) 0) • localDatum W V (lineTermReal A X β a.1 v) (stdRowDatum σ χ s) r := by
  choose e d l using (tsum_lineTerm A X · |>.2.choose_spec.choose_spec)
  use (vacuumFactor <| d ·)
  introv
  let Q := adaptedFrame r X
  let H (K L : type_of% Q.K) I := ((fromRows 0 K).fromCols (((fromBlocks 1 0 0 I).submatrix id
    σ.symm).fromCols (fromRows 0 L))).submatrix σ'.symm id
  let G := H Q.K Q.L Q.I
  have j := (adaptedFrame r A).spec
  extract_lets P R at j
  obtain ⟨⟨j, j', p, q⟩, ⟨γ, _, Γ⟩, u, H', u', _⟩ := j, exists_local_gauss_sum h
    r.hasIntegralConductor_psi, (by use ?_, (H Q.K'ᵀ Q.L'ᵀ Q.I'ᵀ)ᵀ <;> simp [← ext_iff, G, H,
    eq_comm, ite_mem, IsIntMatrix, reindex_equiv σ, reindex_equiv σ', by simpa [← ext_iff,
    IsIntMatrix] using Q.blocks_spec] : IsPrimitiveMatrix O G)
  let ε := invOnUnits χ (R * G).det
  have K (T : type_of% (R * G)) : stdColDatum χ 1 (G * T * R) = ε * stdColDatum χ 1 T := by
    simpa [← det_comm' q p, ← Matrix.mul_assoc] using if_ctx_congr
      ⟨(by simpa [← H'.mul_assoc, *] using u'.mul <| ·.mul j),
      (u.mul · |>.mul j')⟩ (invOnUnits_mul (j'.mul u).det_mem ·.det_mem) (by simp)
  use ε * γ, by simpa [ε, invOnUnits, h.norm_eq_one, isPrimitiveMatrix_iff_isIntegralUnit_det.1
                  ((IsPrimitiveMatrix.mul_iff ⟨j', _, j, p⟩).2 ⟨u, by tauto⟩)]
  introv a
  rw [lineTermReal, e, (by simp [funext_iff, a, Units.smul_def, mul_comm x] : _ ⊕ᵥ _ =
    scaleIdele E • (a * ·.isRight.toNat)), mixedTerm_localDatum r (d β) (stdRowDatum_mem _ _) _ _
    (1 ⊕ᵥ fun _ ↦ ε • invOnUnits χ (π a.2) • invOnUnits χ) fun y
    z ↦ let Y := (s.fromRows y).submatrix σ.symm id; ((congrArg _ ?_).trans (K (fromBlocks (cond β
      (π a.2) (z (.inr 0)) • 1) (vecToMat (z ∘ .inl ∘ .inl)) 0 (Y.fromBlocks ((fromRows 0 (vecToMat
      (z ∘ .inl ∘ .inr))).submatrix σ.symm id) 0 (cond β (z (.inr 0)) (π a.2) • 1))))).trans ?_]
  simp [volume_O, Measure.real, Γ, mul_comm (r.ψ _)]; ring_nf; rfl
  simp +zetaDelta [↓l]
  cases β <;> congr with ⟨⟩ <;> simp [Finset.mul_sum, diagonal, mul_add] <;> ac_nf
  have q (h : IsIntMatrix O Y) := h.det_mem
  simp [Y, stdRowDatum, IsIntMatrix, reindex_equiv σ, Unique.forall_iff, prod_ite_zero,
    prod_prod_type, -ite_smul] at q ⊢
  grind [invOnUnits_mul, mul_mem, invOnUnits]
