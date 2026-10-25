import CFMPOriginalAdjacentConormal233Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open CFMPOriginalExteriorFaceChart435Transient
open CFMPOriginalSupportReadout232Transient
open CFMPOriginalExteriorNativeNormal435Transient
open CFMPOriginalBoundaryEdge229Transient
open CFMPPairedSupportConormal230Transient
open CFMPConormalIdentification231Transient (normalize normalize_positive_smul)

namespace CFMPOriginalTruncationOrthogonal236Transient

abbrev Space := Fin 4 → ℝ

theorem covector_cap (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 4) (hn : facet n = Sum.inr i) (j : Fin 4) :
    exteriorCovector l n j = supportScale l n * lengthGram l i j := by
  have hsum : ∑ k : Fin 4, (Pi.single j (1 : ℝ)) k = 1 := by simp
  have h := covector_support_readout l hl n (Pi.single j 1) hsum
  have hdot : (∑ d : Fin 4, lengthGram l i d *
      ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) d)) = lengthGram l i j :=
    dotProduct_single_one (lengthGram l i) j
  simpa [single_one_dotProduct, hn, support, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.sum_apply, hdot] using h

theorem covector_side (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (k : Fin 4) (hn : facet n = Sum.inl k) (j : Fin 4) :
    exteriorCovector l n j = -supportScale l n * ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) k) := by
  have hsum : ∑ a : Fin 4, (Pi.single j (1 : ℝ)) a = 1 := by simp
  have h := covector_support_readout l hl n (Pi.single j 1) hsum
  simpa [single_one_dotProduct, hn, support] using h

-- The actual cap normal is the corresponding row of the same realizing frame.
theorem cap_unit_eq_row (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (n : Fin 20) (i : Fin 4) (hn : facet n = Sum.inr i) :
    unit l M n = M i := by
  let reflected : Space := ![M i 0, M i 1, M i 2, -M i 3]
  have hcov : exteriorCovector l n = supportScale l n • (M *ᵥ reflected) := by
    ext j
    rw [covector_cap l hl n i hn j]
    change supportScale l n * lengthGram l i j =
      supportScale l n * (M *ᵥ reflected) j
    congr 1
    rw [← hG i j, lorentz_symm (M i) (M j)]
    simp [reflected, Matrix.mulVec, dotProduct, lorentz, Fin.sum_univ_four]
  have hinv : M⁻¹ *ᵥ exteriorCovector l n = supportScale l n • reflected := by
    rw [hcov, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  have hraw : raw l M n = supportScale l n • M i := by
    ext j
    fin_cases j <;> simp [raw, hinv, reflected, smul_eq_mul]
  have hdiag : lorentz (M i) (M i) = 1 := by
    rw [hG]
    fin_cases i <;> rfl
  change CFMPConormalIdentification231Transient.normalize (raw l M n) = M i
  rw [hraw, normalize_positive_smul _ _ (supportScale_pos l hl n)]
  simp [CFMPConormalIdentification231Transient.normalize, hdiag]

theorem cap_side_orthogonal (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (n m : Fin 20) (i k : Fin 4) (hik : i ≠ k)
    (hn : facet n = Sum.inr i) (hm : facet m = Sum.inl k) :
    lorentz (unit l M n) (unit l M m) = 0 := by
  rw [cap_unit_eq_row l hl M hM hG n i hn]
  have hrow : (Pi.single i (1 : ℝ)) ᵥ* M = M i := by
    simp [Matrix.single_vecMul, Matrix.row_apply']
  have hread := pair_raw l M hM m (Pi.single i 1)
  rw [hrow, single_one_dotProduct, covector_side l hl m k hm i] at hread
  have hzero : lorentz (M i) (raw l M m) = 0 := by
    simpa [Pi.single_apply, hik, Ne.symm hik] using hread
  have hsmul (X Y : Space) (r : ℝ) : lorentz X (r • Y) = r * lorentz X Y := by
    simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [unit, hsmul, hzero, mul_zero]

theorem original_truncation_unit_orthogonal (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (a : Fin 12) :
    lorentz (unit l M (pairs (truncation a)).1.1)
      (unit l M (pairs (truncation a)).2.1) = 0 := by
  rcases truncation_supports a with ⟨i,k,hik,hn,hm⟩ | ⟨i,k,hik,hm,hn⟩
  · exact cap_side_orthogonal l hl M hM hG _ _ i k hik hn hm
  · rw [lorentz_symm]
    exact cap_side_orthogonal l hl M hM hG _ _ i k hik hm hn

-- Orthogonal supporting planes retain zero angular boundary readout along a path.
theorem original_truncation_derivative_readout
    (l : ℝ → Fin 6 → ℝ) (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (dN : Fin 20 → Space) (t : ℝ)
    (hpos : ∀ᶠ s in 𝓝 t, ∀ k, 0 < l s k)
    (hinv : ∀ᶠ s in 𝓝 t, (M s).det ≠ 0)
    (hG : ∀ᶠ s in 𝓝 t, ∀ i j, lorentz (M s i) (M s j) = lengthGram (l s) i j)
    (hN : ∀ n i, HasDerivAt (fun s => unit (l s) (M s) n i) (dN n i) t)
    (a : Fin 12) :
    lorentz (dN (pairs (truncation a)).1.1)
        (conormal (unit (l t) (M t) (pairs (truncation a)).1.1)
          (unit (l t) (M t) (pairs (truncation a)).2.1)) +
      lorentz (dN (pairs (truncation a)).2.1)
        (conormal (unit (l t) (M t) (pairs (truncation a)).2.1)
          (unit (l t) (M t) (pairs (truncation a)).1.1)) = 0 := by
  have he : (fun s => lorentz (unit (l s) (M s) (pairs (truncation a)).1.1)
      (unit (l s) (M s) (pairs (truncation a)).2.1)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [hpos, hinv, hG] with s hs hi hg
    exact original_truncation_unit_orthogonal (l s) hs (M s) hi hg a
  have hd := lorentz_hasDerivAt
    (fun s => unit (l s) (M s) (pairs (truncation a)).1.1)
    (fun s => unit (l s) (M s) (pairs (truncation a)).2.1)
    (dN (pairs (truncation a)).1.1) (dN (pairs (truncation a)).2.1) t
    (hN _) (hN _)
  have hz := hd.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he)
  have horth := he.eq_of_nhds
  have horth' := (lorentz_symm
    (unit (l t) (M t) (pairs (truncation a)).2.1)
    (unit (l t) (M t) (pairs (truncation a)).1.1)).trans horth
  simp only [conormal, projected, horth, horth', zero_pow (by decide : 2 ≠ 0),
    sub_zero, Real.sqrt_one, inv_one, zero_smul, one_smul]
  rw [lorentz_symm (dN (pairs (truncation a)).2.1)]
  exact hz

end CFMPOriginalTruncationOrthogonal236Transient

run_cmd do
  let name := ``CFMPOriginalTruncationOrthogonal236Transient.original_truncation_derivative_readout
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP236 original truncation angular readout absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP236 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP236 CHECKED {name} axioms={axioms}"
