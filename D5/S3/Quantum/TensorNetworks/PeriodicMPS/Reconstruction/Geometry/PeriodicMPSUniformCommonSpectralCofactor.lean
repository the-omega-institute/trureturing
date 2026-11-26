/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralCofactor
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralCofactor
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The literal full-rank witness supplies a nonzero exact native cofactor. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralRotation

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport

open Function Matrix MvPolynomial TrivSqZeroExt
open scoped BigOperators Kronecker
open PeriodicMPSCommonSpectralJets
open PeriodicMPSUniformSpecialSpectralDomains (witnessK balancedWitnessCore)
open SevenSiteCriticalCertificate (sliceBlock observedRow)
open PeriodicMPSUniformNativeSliceReadout (rawSlicePolynomial)
open UniformNativeCriticalMatrix (criticalMatrix)
open UniformNativeRotation (rotationPolynomial)

open private frameTangent from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
open private pauliFrame from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private certificate_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteReadoutDerivative
open private physicalJet rotateInvariant from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralRotation
open private dual dualMap fst_dual snd_dual witnessDirection from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralRankTransport

noncomputable section

private def K (i : Fin 2) : Core ℂ := (balancedWitnessCore (ketIndex i)).map Complex.ofRealHom
private def B (i : Fin 2) : Core ℂ := (balancedWitnessCore (braIndex i)).map Complex.ofRealHom

private theorem coordinates_KB : coordinates K B = sliceCoordinates Complex.I nativeWitnessSlice := by
  rw [sliceCoordinates_nativeWitnessSlice]
  exact (map_coordinates Complex.ofRealHom (balancedWitnessCore ∘ ketIndex)
    (balancedWitnessCore ∘ braIndex)).symm

private def x := sliceCoordinates Complex.I nativeWitnessSlice
private def r (j : Fin 3) := rotateInvariant K B (frameTangent j)
private def s (j : Fin 5) := sliceDirection Complex.I (Pi.single j 1)
private def q (i : Fin 2) := blockScaling x (if i = 0 then 1 else 0) (if i = 1 then 1 else 0)

private def allDirections : Fin 10 → Coordinate → ℂ :=
  ![s 0, s 1, s 2, s 3, s 4, q 0, r 0, r 1, r 2, q 1]

private theorem K_tr (i : Fin 2) : (K i).trace = if i = 0 then 1 else 0 := by
  have h := congrFun coordinates_KB (0, i.castLE (by decide : 2 ≤ 5))
  fin_cases i <;> simpa [coordinates, invariants, sliceCoordinates, sliceBlock] using h

private theorem B_tr (i : Fin 2) : (B i).trace = if i = 0 then 1 else 0 := by
  have h := congrFun coordinates_KB (1, i.castLE (by decide : 2 ≤ 5))
  fin_cases i <;> simpa [coordinates, invariants, sliceCoordinates, sliceBlock] using h

private theorem frameTangent_eq :
    frameTangent = ![!![0, -Complex.I / 2; -Complex.I / 2, 0],
      !![0, -1 / 2; 1 / 2, 0], !![0, 0; 0, Complex.I]] := by
  funext j
  apply Matrix.ext
  intro a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [frameTangent, ← certificate_pauli, pauli, Matrix.one_apply, Complex.I_mul_I] <;>
    ring_nf <;> norm_num [Complex.I_sq]

private theorem rotate_trace (A : Fin 2 → Core ℂ) (hA : ∀ i, (A i).trace = if i = 0 then 1 else 0)
    (g : Core ℂ) (i : Fin 2) : (physicalJet A g i).trace.snd = g i 0 := by
  have ha : A 0 0 0 + A 0 1 1 = 1 := by simpa [Matrix.trace_fin_two] using hA 0
  have hb : A 1 0 0 + A 1 1 1 = 0 := by simpa [Matrix.trace_fin_two] using hA 1
  simp only [Matrix.trace_fin_two, snd_add, physicalJet, snd_dual, Fin.sum_univ_two]
  linear_combination g i 0 * ha + g i 1 * hb

private theorem rotate_mixed_z (A : Fin 2 → Core ℂ) (g : Core ℂ) (c : ℂ)
    (hg : g = !![0, 0; 0, c]) :
    (physicalJet A g 0 * physicalJet A g 1).trace.snd = c * (A 0 * A 1).trace := by
  subst g
  simp [Matrix.trace_fin_two, Matrix.mul_apply, physicalJet, Fin.sum_univ_two]
  ring

private theorem r_trace (j : Fin 3) (b : Fin 2) (i : Fin 2) :
    r j (b, i.castLE (by decide : 2 ≤ 5)) =
      if b = 0 then frameTangent j i 0 else -(frameTangent j 0 i) := by
  fin_cases b <;> fin_cases i <;> simp [r, rotateInvariant, coordinates, invariants,
    rotate_trace, K_tr, B_tr]

private theorem r_mixed_z (b : Fin 2) :
    r 2 (b, 4) = (if b = 0 then Complex.I else -Complex.I) * (witnessK : ℝ) := by
  have hk := congrFun coordinates_KB (0, 4)
  have hb := congrFun coordinates_KB (1, 4)
  change (K 0 * K 1).trace = (witnessK : ℝ) at hk
  change (B 0 * B 1).trace = (witnessK : ℝ) at hb
  have hg : -(frameTangent 2)ᵀ = (!![0, 0; 0, -Complex.I] : Core ℂ) := by
    rw [frameTangent_eq]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  fin_cases b
  · change (physicalJet K (frameTangent 2) 0 * physicalJet K (frameTangent 2) 1).trace.snd = _
    rw [rotate_mixed_z _ _ _ (by rw [frameTangent_eq]; rfl), hk]
    rfl
  · change (physicalJet B (-(frameTangent 2)ᵀ) 0 * physicalJet B (-(frameTangent 2)ᵀ) 1).trace.snd = _
    rw [rotate_mixed_z _ _ _ hg, hb]
    rfl

private def directionCombination := Fintype.linearCombination ℂ allDirections

private theorem directionCombination_injective : Function.Injective directionCombination := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have ev (i : Coordinate) := congrFun hv i
  have hr0 (j : Fin 3) (b : Fin 2) :
      r j (b, 0) = (if b = 0 then frameTangent j 0 0 else -frameTangent j 0 0) :=
    r_trace j b 0
  have hr1 (j : Fin 3) (b : Fin 2) :
      r j (b, 1) = (if b = 0 then frameTangent j 1 0 else -frameTangent j 0 1) :=
    r_trace j b 1
  have h5 : v 5 = 0 := by
    simpa [directionCombination, Fintype.linearCombination_apply, allDirections, Fin.sum_univ_succ,
      s, q, x, sliceCoordinates, sliceDirection, sliceBlock, blockScaling, nativeWitnessSlice,
      hr0, frameTangent_eq] using ev (0, 0)
  have h9 : v 9 = 0 := by
    simpa [directionCombination, Fintype.linearCombination_apply, allDirections, Fin.sum_univ_succ,
      s, q, x, sliceCoordinates, sliceDirection, sliceBlock, blockScaling, nativeWitnessSlice,
      hr0, frameTangent_eq, h5] using ev (1, 0)
  have e0 := ev (0, 1)
  have e1 := ev (1, 1)
  simp [directionCombination, Fintype.linearCombination_apply, allDirections, Fin.sum_univ_succ,
    s, sliceDirection, sliceBlock, hr1, frameTangent_eq, h5, h9] at e0 e1
  have h6 : v 6 = 0 := by
    have he : Complex.I * v 6 = 0 := by linear_combination -e0 + e1
    exact (mul_eq_zero.mp he).resolve_left Complex.I_ne_zero
  have h7 : v 7 = 0 := by
    linear_combination 2 * e0 + Complex.I * h6
  have e0 := ev (0, 4)
  have e1 := ev (1, 4)
  simp [directionCombination, Fintype.linearCombination_apply, allDirections, Fin.sum_univ_succ,
    s, sliceDirection, sliceBlock, r_mixed_z, h5, h6, h7, h9] at e0 e1
  have h8 : v 8 = 0 := by
    have he : (Complex.I * (witnessK : ℝ)) * v 8 = 0 := by
      linear_combination (e0 - e1) / 2
    exact (mul_eq_zero.mp he).resolve_left
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (Units.ne_zero witnessK)))
  have h1 : v 1 = 0 := by simpa [h8] using e0
  have ed0 := ev (0, 2)
  have ed1 := ev (1, 2)
  have ee0 := ev (0, 3)
  have ee1 := ev (1, 3)
  simp [directionCombination, Fintype.linearCombination_apply, allDirections, Fin.sum_univ_succ,
    s, sliceDirection, sliceBlock, h1, h5, h6, h7, h8, h9] at ed0 ed1 ee0 ee1
  have h0 : v 0 = 0 := by linear_combination (ed0 + ed1) / 2
  have h2 : v 2 = 0 := by linear_combination (ee0 + ee1) / 2
  have h3 : v 3 = 0 := (mul_eq_zero.mp (by simpa [h0] using ed0)).resolve_right Complex.I_ne_zero
  have h4 : v 4 = 0 := (mul_eq_zero.mp (by simpa [h2] using ee0)).resolve_right Complex.I_ne_zero
  funext i
  fin_cases i <;> assumption

private theorem directionCombination_surjective : Function.Surjective directionCombination :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by norm_num [Module.finrank_pi, Fintype.card_prod])).mp directionCombination_injective

private theorem complex_gramDifferential_cast (m : ℕ) (v : Coordinate → ℝ) (ab : Entry) :
    gramDifferential m x (Complex.ofReal ∘ v) ab =
      (gramDifferential m witnessCoordinates v ab : ℂ) := by
  have hx : x = Complex.ofReal ∘ witnessCoordinates := sliceCoordinates_nativeWitnessSlice
  rw [hx, gramDifferential_apply, gramDifferential_apply]
  have h := map_gramChart (dualMap Complex.ofRealHom) m (fun a => dual (witnessCoordinates a) (v a)) ab
  exact (congrArg TrivSqZeroExt.snd h).symm

private theorem complex_gramDifferential_rank_ge_nine {m : ℕ} (hm : 5 ≤ m) :
    9 ≤ Module.finrank ℂ (LinearMap.range (gramDifferential m x)) := by
  let D := gramDifferential m x
  let directions := Fintype.linearCombination ℂ
    (fun j : Fin 9 => Complex.ofReal ∘ witnessDirection (columns j))
  let extract : (Entry → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) := LinearMap.pi fun i => LinearMap.proj (rows i)
  let M := Complex.ofRealHom.mapMatrix (witnessGramMinor m)
  have hM : M.det ≠ 0 := by
    dsimp only [M]
    rw [← Complex.ofRealHom.map_det]
    exact Complex.ofReal_ne_zero.mpr (witnessGramMinor_det_ne_zero hm)
  have he : M.mulVecLin = extract.comp (D.comp directions) := by
    apply LinearMap.ext
    intro v
    funext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, D, M, directions, extract,
      LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      Fintype.linearCombination_apply, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [complex_gramDifferential_cast, mul_comm]
    rfl
  calc
    9 = M.rank := by rw [Matrix.rank_of_det_ne_zero hM, Fintype.card_fin]
    _ = Module.finrank ℂ (LinearMap.range (extract.comp (D.comp directions))) := by rw [Matrix.rank, he]
    _ ≤ Module.finrank ℂ (LinearMap.range D) := by
      rw [LinearMap.range_comp]
      exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _))

private def observed : (Entry → ℂ) →ₗ[ℂ] (Fin 10 → ℂ) where
  toFun G i := pauliGram Complex.I G (observedRow i)
  map_add' G H := by
    funext i
    simp [pauliGram, mul_add, Finset.sum_add_distrib]
  map_smul' z G := by
    funext i
    simp [pauliGram, Finset.mul_sum, mul_left_comm]

private theorem rank_observed (m : ℕ) :
    Module.finrank ℂ (LinearMap.range (observed.comp (gramDifferential m x))) =
      Module.finrank ℂ (LinearMap.range (gramDifferential m x)) := by
  let D := gramDifferential m x
  have hinj : Set.InjOn observed (LinearMap.range D) := by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩ h
    exact observedPauliGram_injective_on_differential m x v w (congrFun h)
  have h : Function.Injective (observed.comp (LinearMap.range D).subtype) :=
    fun u v huv => Subtype.ext (hinj u.property v.property huv)
  have hdim := LinearMap.finrank_range_of_inj h
  rw [LinearMap.range_comp _ observed, Submodule.range_subtype] at hdim
  rw [LinearMap.range_comp _ observed]
  exact hdim

private def nativeMatrix (m : ℕ) : Matrix (Fin 10) (Fin 9) ℂ :=
  (criticalMatrix m).map (eval nativeWitnessSlice)

private theorem radial_columns (m : ℕ) (j : Fin 2) :
    gramDifferential m x (q j) = ((2 + m : ℕ) : ℂ) • gramChart m x := by
  have h := gramDifferential_blockScaling m K B
    (if j = 0 then (1 : ℂ) else 0) (if j = 1 then 1 else 0)
  rw [coordinates_KB] at h
  fin_cases j <;> simpa [q, x] using h

private theorem augmented_column (m : ℕ) (j : Fin 10) (i : Fin 10) :
    ((observed.comp (gramDifferential m x)) (allDirections j)) i =
      if h : j.val < 9 then
        if j.val = 5 then ((2 + m : ℕ) : ℂ) * nativeMatrix m i ⟨j.val, h⟩
        else nativeMatrix m i ⟨j.val, h⟩
      else ((2 + m : ℕ) : ℂ) * nativeMatrix m i 5 := by
  have hs (k : Fin 5) := (eval_pderiv_rawSlicePolynomial m nativeWitnessSlice k (observedRow i)).symm
  have hr (k : Fin 3) := (eval_rotationPolynomial_eq_invariant m nativeWitnessSlice K B
    coordinates_KB k (observedRow i)).symm
  simp only [coordinates_KB] at hr
  have hvalue := (eval_rawSlicePolynomial_eq_pauliGram m nativeWitnessSlice (observedRow i)).symm
  have hrad (k : Fin 2) :
      observed (gramDifferential m x (q k)) i =
        ((2 + m : ℕ) : ℂ) * eval nativeWitnessSlice (rawSlicePolynomial m (observedRow i)) := by
    rw [radial_columns, map_smul]
    exact congrArg (((2 + m : ℕ) : ℂ) * ·) hvalue
  fin_cases j
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, s, x] using hs 0
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, s, x] using hs 1
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, s, x] using hs 2
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, s, x] using hs 3
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, s, x] using hs 4
  · simpa [allDirections, nativeMatrix, criticalMatrix] using hrad 0
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, r, x] using hr 0
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, r, x] using hr 1
  · simpa [allDirections, observed, nativeMatrix, criticalMatrix, r, x] using hr 2
  · simpa [allDirections, nativeMatrix, criticalMatrix] using hrad 1

private theorem nativeMatrix_full_rank {m : ℕ} (hm : 5 ≤ m) : (nativeMatrix m).rank = 9 := by
  let D := observed.comp (gramDifferential m x)
  have hc : LinearMap.range (D.comp directionCombination) = LinearMap.range D :=
    LinearMap.range_comp_of_range_eq_top D (LinearMap.range_eq_top.mpr directionCombination_surjective)
  have hsub : LinearMap.range (D.comp directionCombination) ≤ LinearMap.range (nativeMatrix m).mulVecLin := by
    have hcol (j : Fin 10) : D (allDirections j) ∈ LinearMap.range (nativeMatrix m).mulVecLin := by
      by_cases hj : j.val < 9
      · let k : Fin 9 := ⟨j.val, hj⟩
        let z : ℂ := if j.val = 5 then ((2 + m : ℕ) : ℂ) else 1
        refine ⟨z • Pi.single k 1, ?_⟩
        funext i
        rw [map_smul, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
        have h := augmented_column m j i
        by_cases h5 : j.val = 5 <;> simpa [D, k, z, hj, h5] using h.symm
      · refine ⟨((2 + m : ℕ) : ℂ) • Pi.single 5 1, ?_⟩
        funext i
        rw [map_smul, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
        simpa [D, hj] using (augmented_column m j i).symm
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply, directionCombination, Fintype.linearCombination_apply, map_sum, map_smul]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)
  apply le_antisymm (by simpa only [Fintype.card_fin] using (nativeMatrix m).rank_le_card_width)
  rw [hc] at hsub
  have hl := complex_gramDifferential_rank_ge_nine hm
  rw [← rank_observed] at hl
  exact hl.trans (Submodule.finrank_mono hsub)

private theorem exists_minor_of_rank_eq_nine (A : Matrix (Fin 10) (Fin 9) ℂ) :
  A.rank = 9 → ∃ d : Fin 10, (A.submatrix d.succAbove id).det ≠ 0 := by
  classical
  intro hRank
  have hSpan : Submodule.span ℂ (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hRank, Module.finrank_pi, Fintype.card_fin]
  obtain ⟨f, hf, hdet⟩ :=
    D5.S3.Combinatorics.Matroids.LinearRado.exists_nonsingular_rows A hSpan
  have hn : ¬ Surjective f := by
    intro h
    have hcard := Fintype.card_le_of_surjective f h
    norm_num [Fintype.card_fin] at hcard
  change ¬ ∀ i, ∃ j, f j = i at hn
  obtain ⟨d, hd⟩ := not_forall.mp hn
  let g : Fin 9 → Fin 9 := fun j =>
    (finSuccAboveEquiv d).symm ⟨f j, fun h => hd ⟨j, h⟩⟩
  have hg (j : Fin 9) : d.succAbove (g j) = f j := by
    have h := (finSuccAboveEquiv d).apply_symm_apply
      (⟨f j, fun h => hd ⟨j, h⟩⟩ : {i : Fin 10 // i ≠ d})
    exact congrArg Subtype.val h
  have hgi : Injective g := by
    intro a b h
    apply hf
    rw [← hg a, ← hg b, h]
  let e : Equiv.Perm (Fin 9) :=
    Equiv.ofBijective g ⟨hgi, Finite.injective_iff_surjective.mp hgi⟩
  refine ⟨d, fun hz => hdet ?_⟩
  have he : A.submatrix f id = (A.submatrix d.succAbove id).submatrix e id := by
    apply Matrix.ext
    intro i j
    change A (f i) j = A (d.succAbove (g i)) j
    rw [hg]
  rw [he, Matrix.det_permute, hz, mul_zero]

/-- At the common zero-root and repeated-root point, some actual native
maximal minor is nonzero at every suffix length at least five. -/
theorem nativeWitness_exists_cofactor_ne_zero {m : ℕ} (hm : 5 ≤ m) :
    ∃ i : Fin 10, eval nativeWitnessSlice ((criticalMatrix m).submatrix i.succAbove id).det ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_minor_of_rank_eq_nine (nativeMatrix m) (nativeMatrix_full_rank hm)
  refine ⟨i, ?_⟩
  let f := MvPolynomial.eval nativeWitnessSlice
  change f ((criticalMatrix m).submatrix i.succAbove id).det ≠ 0
  rw [f.map_det]
  exact hi

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport
