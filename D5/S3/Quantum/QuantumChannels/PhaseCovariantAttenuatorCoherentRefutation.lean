/- GID: D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.claim; result=D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.result; claim=D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.claim
   digest: PhaseCovariantAttenuatorCoherentRefutation on the full bosonic Hilbert space. -/
/-
result:
  proof_shape: content
  escape_witness: Conclusion witness: the exact entropy gap for the mixed environment, with the square-root pure-input channel bridge and unitary basis transport on the live path excluding all coherent amplitudes.
admission_basis: open-problem-resolution (#11681; Refuted)
Direct frozen dependencies: D5/S3/Entropy/MaxEntropy.shannonEntropy
  statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87
Chain prerequisite (first freeze in Stage B): Entropy.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
import D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
import D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
import D5.S3.Quantum.QuantumChannels.FockAttenuator.Entropy

open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.QuantumChannels.PhaseCovariantAttenuatorCoherentRefutation
open D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator D5.S3.Quantum.QuantumChannels.FockAttenuator.Entropy

private def vacuumNumerators : Fin 6 → ℝ := by
  exact ![113, 117, 10, 10, 5, 1]

private def onePhotonNumerators : Fin 7 → ℝ := by
  exact ![115, 8, 117, 0, 5, 8, 3]

private def entropyA : ℝ := by
  exact D5.S3.Entropy.MaxEntropy.shannonEntropy (fun i => vacuumNumerators i / 256)

private def entropyB : ℝ := by
  exact D5.S3.Entropy.MaxEntropy.shannonEntropy (fun i => onePhotonNumerators i / 256)

private def outputA : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
  exact finiteDiagonal (fun i => vacuumNumerators i / 256)

private def outputB : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
  exact finiteDiagonal (fun i => onePhotonNumerators i / 256)

private def environment : ProbabilityVector := by
  exact {
    weight := fun n => (if n = 1 then (7/8 : ℝ) else 0) + (if n = 5 then (1/8 : ℝ) else 0)
    nonneg := by intro n; split_ifs <;> norm_num
    normalized := by
      have h1 := hasSum_ite_eq (1 : ℕ) (7/8 : ℝ)
      have h5 := hasSum_ite_eq (5 : ℕ) (1/8 : ℝ)
      convert h1.add h5 using 1 <;> norm_num
  }

private def sectorVector (N : ℕ) (c : Fin (N+1) → ℂ) :
    lp (fun _ : ℕ => lp (fun _ : ℕ => ℂ) 2) 2 :=
  ∑ k : Fin (N+1), c k • fockPair k (N-k)


def claim : Prop := by
  exact ∀ (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (p : ProbabilityVector),
      ∃ α : ℂ, ∀ ρ : DensityOperator,
        vonNeumannEntropy (attenuator η hη p (coherentDensity α)).operator ≤
          vonNeumannEntropy (attenuator η hη p ρ).operator

theorem result : ¬ claim := by
  have exponential_vectors_total (v : (lp (fun _ : ℕ => ℂ) 2))
      (hv : ∀ α : ℂ, inner ℂ v (exponentialVector α) = 0) : v = 0 := by
    let h_FockAttCoherentBridge_scalarSeries (v : (lp (fun _ : ℕ => ℂ) 2)) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttCoherentBridge_scalarSeries_expansion (v : (lp (fun _ : ℕ => ℂ) 2)) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialVector z)) (h_FockAttCoherentBridge_scalarSeries v) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialVector z))
      intro n
      simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialVector, exponentialCoeff, RCLike.inner_apply]
      ring
    have hfun : (fun z : ℂ => inner ℂ v (exponentialVector z)) = 0 := funext hv
    have hs := h_FockAttCoherentBridge_scalarSeries_expansion v
    rw [hfun] at hs
    have hzero := hs.eq_zero
    apply lp.ext
    funext n
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hzero
    simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hvn : (starRingEnd ℂ) (v n) = 0 := (div_eq_zero_iff.mp hc).resolve_right hsqrt
    simpa using hvn

  have h_FockAttFockOutput_sector_partialTrace (N : ℕ) (c : Fin (N+1) → ℂ) :
      purePartialTrace (sectorVector N c) = finiteDiagonal (fun k => ‖c k‖ ^ 2) := by
    have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
    let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
    have h_FockAttFockOutput_fockPair_apply (m n l : ℕ) :
        fockPair m n l = if l = n then h_FockAttTwoMode_fock m else 0 := by
      simp only [fockPair, h_FockAttTwoMode_tensor_apply, h_FockAttTwoMode_fock, lp.single_apply, Pi.single_apply]
      split_ifs <;> simp_all
    have sectorVector_apply (N : ℕ) (c : Fin (N+1) → ℂ) (l : ℕ) :
        sectorVector N c l =
          if hl : l ≤ N then c ⟨N-l, by omega⟩ • h_FockAttTwoMode_fock (N-l) else 0 := by
      simp only [sectorVector, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
        h_FockAttFockOutput_fockPair_apply]
      split_ifs with hl
      · rw [Finset.sum_eq_single (⟨N-l, by omega⟩ : Fin (N+1))]
        · have hnat : l = N-(N-l) := by omega
          simp only [Fin.val_mk, if_pos hnat]
        · intro k _ hk
          have hne : l ≠ N-(k : ℕ) := by
            intro h
            apply hk
            apply Fin.ext
            change (k : ℕ) = N-l
            have hk_bound := k.isLt
            omega
          simp [hne]
        · simp
      · apply Finset.sum_eq_zero
        intro k _
        have hne : l ≠ N-(k : ℕ) := by omega
        simp [hne]
    have h_FockAttFockOutput_rankOne_smul_self (c : ℂ) (v : (lp (fun _ : ℕ => ℂ) 2)) :
        InnerProductSpace.rankOne ℂ (c • v) (c • v) =
          (‖c‖ ^ 2 : ℂ) • InnerProductSpace.rankOne ℂ v v := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul, smul_apply]
      congr 1
      calc
        (starRingEnd ℂ) c * inner ℂ v x * c = ((starRingEnd ℂ) c * c) * inner ℂ v x := by ring
        _ = _ := by rw [RCLike.conj_mul]; norm_cast
    unfold purePartialTrace mixture
    simp_rw [sectorVector_apply]
    rw [tsum_eq_sum (s := Finset.range (N+1)) (fun l hl => by
      have hnl : ¬ l ≤ N := by
        simp only [Finset.mem_range, not_lt] at hl
        omega
      simp [hnl])]
    have hterm (l : Fin (N+1)) :
        InnerProductSpace.rankOne ℂ
          (if hl : (l : ℕ) ≤ N then c ⟨N-l, by omega⟩ • h_FockAttTwoMode_fock (N-l) else 0)
          (if hl : (l : ℕ) ≤ N then c ⟨N-l, by omega⟩ • h_FockAttTwoMode_fock (N-l) else 0) =
        (‖c l.rev‖ ^ 2 : ℂ) • InnerProductSpace.rankOne ℂ (h_FockAttTwoMode_fock l.rev) (h_FockAttTwoMode_fock l.rev) := by
      simp only [show (l : ℕ) ≤ N by omega, ↓reduceDIte, h_FockAttFockOutput_rankOne_smul_self]
      have heq : (⟨N-l, by omega⟩ : Fin (N+1)) = l.rev := by
        apply Fin.ext
        simp [Fin.rev]
      rw [heq]
      simp only [Fin.val_rev, Nat.add_sub_add_right]
    rw [← Fin.sum_univ_eq_sum_range]
    simp_rw [hterm]
    unfold finiteDiagonal
    simpa only [Fin.revPerm_apply, Complex.ofReal_pow] using
      Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N+1)))
        (fun k : Fin (N+1) => (‖c k‖ ^ 2 : ℂ) • InnerProductSpace.rankOne ℂ (h_FockAttTwoMode_fock k) (h_FockAttTwoMode_fock k))

  have four_balanced_outputs (h : (1/2 : ℝ) ∈ Set.Icc 0 1) :
      (purePartialTrace (beamSplitter (1/2) h (fockPair 0 1)) =
        finiteDiagonal (![(1/2:ℝ),1/2])) ∧
      (purePartialTrace (beamSplitter (1/2) h (fockPair 1 1)) =
        finiteDiagonal (![(1/2:ℝ),0,1/2])) ∧
      (purePartialTrace (beamSplitter (1/2) h (fockPair 0 5)) =
        finiteDiagonal (![(1/32:ℝ),5/32,10/32,10/32,5/32,1/32])) ∧
      (purePartialTrace (beamSplitter (1/2) h (fockPair 1 5)) =
        finiteDiagonal (![(3/32:ℝ),8/32,5/32,0,5/32,8/32,3/32])) := by
    let h_FockAttFockOutput_q01 : Fin 2 → ℝ := ![1,-1]
    let h_FockAttFockOutput_q11 : Fin 3 → ℝ := ![1,0,-1]
    let h_FockAttFockOutput_q05 : Fin 6 → ℝ := ![1,-5,10,-10,5,-1]
    let h_FockAttFockOutput_q15 : Fin 7 → ℝ := ![1,-4,5,0,-5,4,-1]
    let h_FockAttFockOutput_balancedRoot : ℝ := Real.sqrt (1/2)
    let h_FockAttFockOutput_sectorCoefficient (m n : ℕ) (q : Fin (m+n+1) → ℝ) (k : Fin (m+n+1)) : ℂ := (q k * h_FockAttFockOutput_balancedRoot ^ (m+n) * Real.sqrt ((k : ℕ).factorial : ℝ) *
          Real.sqrt ((m+n-k : ℕ).factorial : ℝ) /
          (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) : ℝ)
    have h_FockAttFockOutput_sectorCoefficient_norm_sq (m n : ℕ) (q : Fin (m+n+1) → ℝ) (k : Fin (m+n+1)) :
        ‖h_FockAttFockOutput_sectorCoefficient m n q k‖ ^ 2 =
          q k ^ 2 * (1/2 : ℝ) ^ (m+n) * (k:ℕ).factorial * (m+n-k:ℕ).factorial /
            ((m.factorial : ℝ) * (n.factorial : ℝ)) := by
      simp only [h_FockAttFockOutput_sectorCoefficient, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        div_pow, mul_pow]
      rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _),
        Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [pow_right_comm]
      dsimp only [h_FockAttFockOutput_balancedRoot]
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2), div_pow]
    have h_FockAttFockOutput_four_sector_probabilities :
        (∀ k : Fin 2, ‖h_FockAttFockOutput_sectorCoefficient 0 1 h_FockAttFockOutput_q01 k‖ ^ 2 = ![(1/2:ℝ),1/2] k) ∧
        (∀ k : Fin 3, ‖h_FockAttFockOutput_sectorCoefficient 1 1 h_FockAttFockOutput_q11 k‖ ^ 2 = ![(1/2:ℝ),0,1/2] k) ∧
        (∀ k : Fin 6, ‖h_FockAttFockOutput_sectorCoefficient 0 5 h_FockAttFockOutput_q05 k‖ ^ 2 = ![(1/32:ℝ),5/32,10/32,10/32,5/32,1/32] k) ∧
        (∀ k : Fin 7, ‖h_FockAttFockOutput_sectorCoefficient 1 5 h_FockAttFockOutput_q15 k‖ ^ 2 = ![(3/32:ℝ),8/32,5/32,0,5/32,8/32,3/32] k) := by
      refine ⟨?_,?_,?_,?_⟩
      · intro k
        rw [h_FockAttFockOutput_sectorCoefficient_norm_sq 0 1 h_FockAttFockOutput_q01 k]
        fin_cases k <;> norm_num [h_FockAttFockOutput_q01, Nat.factorial]
      · intro k
        rw [h_FockAttFockOutput_sectorCoefficient_norm_sq 1 1 h_FockAttFockOutput_q11 k]
        fin_cases k <;> norm_num [h_FockAttFockOutput_q11, Nat.factorial]
      · intro k
        rw [h_FockAttFockOutput_sectorCoefficient_norm_sq 0 5 h_FockAttFockOutput_q05 k]
        fin_cases k <;> norm_num [h_FockAttFockOutput_q05, Nat.factorial]
      · intro k
        rw [h_FockAttFockOutput_sectorCoefficient_norm_sq 1 5 h_FockAttFockOutput_q15 k]
        fin_cases k <;> norm_num [h_FockAttFockOutput_q15, Nat.factorial]
    have h2sq : (Real.sqrt (2 : ℝ) : ℂ)^2 = 2 := by norm_cast; norm_num
    have h2ne : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by norm_cast; positivity
    have h120ne : (Real.sqrt (120 : ℝ) : ℂ) ≠ 0 := by norm_cast; positivity
    have h2inv : (Real.sqrt (2 : ℝ) : ℂ)⁻¹ = (Real.sqrt (2 : ℝ) : ℂ)/2 := by
      field_simp
      linear_combination -h2sq
    have hb01 : beamSplitter (1/2) h (fockPair 0 1) =
        sectorVector (0+1) (h_FockAttFockOutput_sectorCoefficient 0 1 h_FockAttFockOutput_q01) := by
      rw [beamSplitter, beamUnitary_fock]
      norm_num [fockExpansion, sectorVector, h_FockAttFockOutput_sectorCoefficient,
        h_FockAttFockOutput_balancedRoot, h_FockAttFockOutput_q01, Fin.sum_univ_succ,
        Nat.factorial, Nat.choose] <;>
        match_scalars <;> (try simp only [← inv_pow, h2inv]) <;>
        field_simp [h2ne, h120ne] <;> ring_nf <;> (try simp only [h2sq, pow_succ]) <;> ring
    have hb11 : beamSplitter (1/2) h (fockPair 1 1) =
        sectorVector (1+1) (h_FockAttFockOutput_sectorCoefficient 1 1 h_FockAttFockOutput_q11) := by
      rw [beamSplitter, beamUnitary_fock]
      norm_num [fockExpansion, sectorVector, h_FockAttFockOutput_sectorCoefficient,
        h_FockAttFockOutput_balancedRoot, h_FockAttFockOutput_q11, Fin.sum_univ_succ,
        Nat.factorial, Nat.choose] <;>
        match_scalars <;> (try simp only [← inv_pow, h2inv]) <;>
        field_simp [h2ne, h120ne] <;> ring_nf <;> (try simp only [h2sq, pow_succ]) <;> ring
    have hb05 : beamSplitter (1/2) h (fockPair 0 5) =
        sectorVector (0+5) (h_FockAttFockOutput_sectorCoefficient 0 5 h_FockAttFockOutput_q05) := by
      rw [beamSplitter, beamUnitary_fock]
      norm_num [fockExpansion, sectorVector, h_FockAttFockOutput_sectorCoefficient,
        h_FockAttFockOutput_balancedRoot, h_FockAttFockOutput_q05, Fin.sum_univ_succ,
        Nat.factorial, Nat.choose] <;>
        match_scalars <;> (try simp only [← inv_pow, h2inv]) <;>
        field_simp [h2ne, h120ne] <;> ring_nf <;> (try simp only [h2sq, pow_succ]) <;> ring
    have hb15 : beamSplitter (1/2) h (fockPair 1 5) =
        sectorVector (1+5) (h_FockAttFockOutput_sectorCoefficient 1 5 h_FockAttFockOutput_q15) := by
      rw [beamSplitter, beamUnitary_fock]
      norm_num [fockExpansion, sectorVector, h_FockAttFockOutput_sectorCoefficient,
        h_FockAttFockOutput_balancedRoot, h_FockAttFockOutput_q15, Fin.sum_univ_succ,
        Nat.factorial, Nat.choose] <;>
        match_scalars <;> (try simp only [← inv_pow, h2inv]) <;>
        field_simp [h2ne, h120ne] <;> ring_nf <;> (try simp only [h2sq, pow_succ]) <;> ring
    refine ⟨?_,?_,?_,?_⟩
    · rw [hb01, h_FockAttFockOutput_sector_partialTrace]
      congr 1
      funext k
      exact h_FockAttFockOutput_four_sector_probabilities.1 k
    · rw [hb11, h_FockAttFockOutput_sector_partialTrace]
      congr 1
      funext k
      exact h_FockAttFockOutput_four_sector_probabilities.2.1 k
    · rw [hb05, h_FockAttFockOutput_sector_partialTrace]
      congr 1
      funext k
      exact h_FockAttFockOutput_four_sector_probabilities.2.2.1 k
    · rw [hb15, h_FockAttFockOutput_sector_partialTrace]
      congr 1
      funext k
      exact h_FockAttFockOutput_four_sector_probabilities.2.2.2 k
  letI : Nontrivial (lp (fun _ : ℕ => ℂ) 2) := ⟨⟨lp.single 2 0 1, 0, by
    intro h
    have hc := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v 0) h
    simpa [lp.single_apply] using hc⟩⟩
  letI : IsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  have h_FockAttCoherentBridge_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
      inner ℂ (exponentialCoeff α n) (exponentialCoeff β n) =
        ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [exponentialCoeff, RCLike.inner_apply, map_div₀, map_pow, Complex.conj_ofReal]
    rw [mul_pow]
    field_simp
    rw [hsq]
    ring
  have h_FockAttCoherentBridge_exponential_inner (α β : ℂ) :
      inner ℂ (exponentialVector α) (exponentialVector β) =
        Complex.exp ((starRingEnd ℂ) α * β) := by
    rw [lp.inner_eq_tsum]
    simp only [exponentialVector, h_FockAttCoherentBridge_exponentialCoeff_inner]
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp ((starRingEnd ℂ) α * β)).tsum_eq
  have h_FockAttCoherentBridge_weyl_gram (α β γ : ℂ) :
      inner ℂ (weylVector α β) (weylVector α γ) =
        inner ℂ (exponentialVector β) (exponentialVector γ) := by
    have haa : (starRingEnd ℂ) α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    simp only [weylVector, inner_smul_left, inner_smul_right, h_FockAttCoherentBridge_exponential_inner,
      ← Complex.exp_conj, map_sub, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add]
    push_cast
    push_cast at haa
    linear_combination haa
  have h_FockAttCoherentBridge_weyl_dense (α : ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (weylVector α)) := by
    have hspan : (Submodule.span ℂ (Set.range (weylVector α))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun β => by
          have hmem : weylVector α (β - α) ∈ Submodule.span ℂ (Set.range (weylVector α)) :=
            Submodule.subset_span ⟨β - α, rfl⟩
          have hinner := Submodule.inner_left_of_mem_orthogonal hmem hv
          have heq : α + (β - α) = β := by ring
          simp only [weylVector, inner_smul_right, heq] at hinner
          exact (mul_eq_zero.mp hinner).resolve_left (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (weylVector α)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_exponential_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialVector) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialVector)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun α => by
          have hmem : exponentialVector α ∈ Submodule.span ℂ (Set.range exponentialVector) :=
            Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialVector))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  let h_FockAttFrameExtension_gramUnitary {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) : H ≃ₗᵢ[ℂ] H := (LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)])
  have h_FockAttFrameExtension_gramUnitary_apply {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) (i : ι) :
      h_FockAttFrameExtension_gramUnitary v w hgram hv hw (v i) = w i := by
    have hh := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (ι →₀ ℂ))
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw
      (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)]) (Finsupp.single i (1 : ℂ))
    simpa only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul, h_FockAttFrameExtension_gramUnitary] using hh
  have h_FockAttCoherentBridge_displacement_exponential (α β : ℂ) :
      displacement α (exponentialVector β) = weylVector α β := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCoherentBridge_weyl_gram α) h_FockAttCoherentBridge_exponential_dense (h_FockAttCoherentBridge_weyl_dense α) β
  have h_FockAttCovariance_exponential_zero : exponentialVector 0 = h_FockAttTwoMode_fock 0 := by
    apply lp.ext
    funext n
    by_cases hn : n = 0
    · subst n; simp [exponentialVector, exponentialCoeff, h_FockAttTwoMode_fock, lp.single_apply]
    · simp [exponentialVector, exponentialCoeff, h_FockAttTwoMode_fock, lp.single_apply, hn]
  have h_FockAttCovariance_displacement_vacuum_coeff (α : ℂ) (n : ℕ) :
      displacement α (h_FockAttTwoMode_fock 0) n =
        (Real.exp (-‖α‖ ^ 2 / 2) : ℂ) * α ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ) := by
    rw [← h_FockAttCovariance_exponential_zero, h_FockAttCoherentBridge_displacement_exponential]
    simp only [weylVector, mul_zero, sub_zero, add_zero, lp.coeFn_smul, Pi.smul_apply,
      exponentialVector, exponentialCoeff, smul_eq_mul]
    have hexp : Complex.exp (-((‖α‖ ^ 2 / 2 : ℝ) : ℂ)) = (Real.exp (-‖α‖ ^ 2 / 2) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
      congr 2
      ring
    rw [hexp]
    ring
  have h_FockAttProbe_coherent_displacement (α : ℂ) :
      coherent α = displacement α (h_FockAttTwoMode_fock 0) := by
    apply lp.ext
    funext n
    exact (h_FockAttCovariance_displacement_vacuum_coeff α n).symm
  have h_FockAttProbe_coherent_channel (α : ℂ) :
      (coherentDensity α) = pureDensity
        (displacement α (h_FockAttTwoMode_fock 0))
        (by rw [LinearIsometryEquiv.norm_map]; simp [h_FockAttTwoMode_fock, lp.norm_single]) := by
    have hext : ∀ ρ σ : DensityOperator, ρ.operator = σ.operator → ρ = σ := by
      rintro ⟨R,hR,tR⟩ ⟨S,hS,tS⟩ h
      dsimp at h
      cases h
      rfl
    apply hext
    change InnerProductSpace.rankOne ℂ (coherent α) (coherent α) = _
    rw [h_FockAttProbe_coherent_displacement]
    rfl
  have h_FockAttProbe_outputB_entropy : vonNeumannEntropy outputB = ENNReal.ofReal entropyB := by
    apply finiteDiagonal_entropy
    · intro j; fin_cases j <;> norm_num [onePhotonNumerators]
    · intro j; fin_cases j <;> norm_num [onePhotonNumerators]
  have h_FockAttProbe_outputA_entropy : vonNeumannEntropy outputA = ENNReal.ofReal entropyA := by
    apply finiteDiagonal_entropy
    · intro j; fin_cases j <;> norm_num [vacuumNumerators]
    · intro j; fin_cases j <;> norm_num [vacuumNumerators]
  have h_FockAttProbe_entropy_gap_formula :
      256 * (entropyA - entropyB) =
        115 * Real.log 115 - 113 * Real.log 113 + 16 * Real.log 8 +
          3 * Real.log 3 - 20 * Real.log 10 := by
    norm_num [entropyA, entropyB, D5.S3.Entropy.MaxEntropy.shannonEntropy, vacuumNumerators, onePhotonNumerators,
      Fin.sum_univ_succ, Real.negMulLog, Real.log_div, Real.log_one]
    have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [h128, h256, h32, h8, h10]
    ring
  have h_FockAttProbe_entropy_comparison : entropyB < entropyA := by
    have hprod : (10 : ℝ) ^ 20 < 115 ^ 2 * 8 ^ 16 * 3 ^ 3 := by norm_num
    have hlog := Real.log_lt_log (by positivity : 0 < (10 : ℝ) ^ 20) hprod
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at hlog
    simp only [Real.log_pow] at hlog
    norm_num at hlog
    have h115 : Real.log (113 : ℝ) < Real.log 115 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have hgap := h_FockAttProbe_entropy_gap_formula
    linarith
  have h_FockAttProbe_output_entropy_gap : vonNeumannEntropy outputB < vonNeumannEntropy outputA := by
    rw [h_FockAttProbe_outputA_entropy, h_FockAttProbe_outputB_entropy]
    apply (ENNReal.ofReal_lt_ofReal_iff ?_).mpr h_FockAttProbe_entropy_comparison
    have hb : 0 ≤ entropyB := by
      unfold entropyB D5.S3.Entropy.MaxEntropy.shannonEntropy
      apply Finset.sum_nonneg
      intro j _
      apply Real.negMulLog_nonneg
      · fin_cases j <;> norm_num [onePhotonNumerators]
      · fin_cases j <;> norm_num [onePhotonNumerators]
    exact lt_of_le_of_lt hb h_FockAttProbe_entropy_comparison
  have h_FockAttWitness_mix_A :
      (7/8 : ℝ) • finiteDiagonal (![(1/2:ℝ),1/2]) +
        (1/8 : ℝ) • finiteDiagonal
          (![(1/32:ℝ),5/32,10/32,10/32,5/32,1/32]) = outputA := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num [finiteDiagonal, outputA, finiteDiagonal,
      vacuumNumerators, Fin.sum_univ_succ, h_FockAttTwoMode_fock, h_FockAttTwoMode_fock]
    module
  have h_FockAttMixture_rankOne_summable {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2)) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
      Summable (fun i => InnerProductSpace.rankOne ℂ (v i) (v i)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hv
  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
  have h_FockAttTwoMode_tensor_norm_sq (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    rw [ht]
    simp only [h_FockAttTwoMode_tensor_apply, norm_smul, mul_pow]
    rw [hw.summable.tsum_mul_right, hw.tsum_eq, mul_comm]
  have h_FockAttChannel_pureOutputVector_hasSum (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) :
      HasSum (fun q : ℕ × ℕ => ‖pureOutputVector η hη p v q‖ ^ 2) 1 := by
    have hrow (n : ℕ) : HasSum (fun l => ‖pureOutputVector η hη p v (n,l)‖ ^ 2)
        (p.weight n) := by
      let w := beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))
      have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
      have hn : ‖w‖ ^ 2 = 1 := by
        change ‖beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))‖ ^ 2 = _
        rw [LinearIsometryEquiv.norm_map, h_FockAttTwoMode_tensor_norm_sq, hv]
        simp [h_FockAttTwoMode_fock, lp.norm_single]
      rw [hn] at hs
      have hsqrt : ‖(Real.sqrt (p.weight n) : ℂ)‖ ^ 2 = p.weight n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (p.nonneg n)]
      have hs' := HasSum.congr_fun (hs.mul_left (p.weight n)) (fun l => by
        change ‖pureOutputVector η hη p v (n,l)‖ ^ 2 = p.weight n * ‖w l‖ ^ 2
        simp only [pureOutputVector, norm_smul, mul_pow, hsqrt]
        rfl)
      simpa only [mul_one] using hs'
    have hall : Summable (fun q : ℕ × ℕ => ‖pureOutputVector η hη p v q‖ ^ 2) := by
      rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
      refine ⟨fun n => (hrow n).summable, ?_⟩
      simpa only [(hrow _).tsum_eq] using p.normalized.summable
    have ht : (∑' q : ℕ × ℕ, ‖pureOutputVector η hη p v q‖ ^ 2) = 1 := by
      rw [hall.tsum_prod]
      simpa only [(hrow _).tsum_eq] using p.normalized.tsum_eq
    exact ht ▸ hall.hasSum
  have h_FockAttChannel_rankOne_smul_self (c : ℂ) (v : (lp (fun _ : ℕ => ℂ) 2)) :
      InnerProductSpace.rankOne ℂ (c • v) (c • v) =
        (‖c‖ ^ 2 : ℝ) • InnerProductSpace.rankOne ℂ v v := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul, smul_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [smul_smul]
    change ((starRingEnd ℂ) c * inner ℂ v x * c) • v =
      (((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ v x) • v
    congr 1
    calc
      _ = ((starRingEnd ℂ) c * c) * inner ℂ v x := by ring
      _ = _ := by rw [RCLike.conj_mul]; norm_cast
  have h_FockAttChannel_pureAttenuator_environment (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) :
      pureAttenuatorOperator η hη p v =
        ∑' n, p.weight n • purePartialTrace (beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))) := by
    have hall := h_FockAttMixture_rankOne_summable _ (h_FockAttChannel_pureOutputVector_hasSum η hη p v hv).summable
    unfold pureAttenuatorOperator mixture
    rw [hall.tsum_prod]
    apply tsum_congr
    intro n
    let w := beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    have hrank := h_FockAttMixture_rankOne_summable (fun l => w l) hw.summable
    have hsqrt : ‖(Real.sqrt (p.weight n) : ℂ)‖ ^ 2 = p.weight n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (p.nonneg n)]
    change (∑' l, InnerProductSpace.rankOne ℂ
      ((Real.sqrt (p.weight n) : ℂ) • w l) ((Real.sqrt (p.weight n) : ℂ) • w l)) =
      p.weight n • mixture (fun l => w l)
    simp_rw [h_FockAttChannel_rankOne_smul_self, hsqrt]
    exact hrank.tsum_const_smul (p.weight n)
  have h_FockAttWitness_environment_sum (T : ℕ → (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) :
      (∑' n, environment.weight n • T n) = (7/8 : ℝ) • T 1 + (1/8 : ℝ) • T 5 := by
    rw [tsum_eq_sum (s := {1,5}) (fun n hn => by
      have hn1 : n ≠ 1 := by intro h; exact hn (by simp [h])
      have hn5 : n ≠ 5 := by intro h; exact hn (by simp [h])
      simp only [environment, hn1, hn5, if_false, zero_add, zero_smul])]
    norm_num [environment]
  have h_FockAttWitness_vacuum_output (h : (1/2 : ℝ) ∈ Set.Icc 0 1) :
      pureAttenuatorOperator (1/2) h environment (h_FockAttTwoMode_fock 0) = outputA := by
    rw [h_FockAttChannel_pureAttenuator_environment _ _ _ _ (by simp [h_FockAttTwoMode_fock, lp.norm_single]),
      h_FockAttWitness_environment_sum]
    have hfour := four_balanced_outputs h
    change (7/8 : ℝ) • purePartialTrace (beamSplitter (1/2) h (fockPair 0 1)) +
      (1/8 : ℝ) • purePartialTrace (beamSplitter (1/2) h (fockPair 0 5)) = _
    rw [hfour.1, hfour.2.2.1]
    exact h_FockAttWitness_mix_A
  have h_FockAttProbe_fock_channel (n : ℕ) :
      (fockDensity n) = pureDensity (h_FockAttTwoMode_fock n)
        (by simp [h_FockAttTwoMode_fock, lp.norm_single]) := by
    rfl
  have h_FockAttWitness_mix_B :
      (7/8 : ℝ) • finiteDiagonal (![(1/2:ℝ),0,1/2]) +
        (1/8 : ℝ) • finiteDiagonal
          (![(3/32:ℝ),8/32,5/32,0,5/32,8/32,3/32]) = outputB := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num [finiteDiagonal, outputB, finiteDiagonal,
      onePhotonNumerators, Fin.sum_univ_succ, h_FockAttTwoMode_fock, h_FockAttTwoMode_fock]
    module
  have h_FockAttWitness_onePhoton_output (h : (1/2 : ℝ) ∈ Set.Icc 0 1) :
      pureAttenuatorOperator (1/2) h environment (h_FockAttTwoMode_fock 1) = outputB := by
    rw [h_FockAttChannel_pureAttenuator_environment _ _ _ _ (by simp [h_FockAttTwoMode_fock, lp.norm_single]),
      h_FockAttWitness_environment_sum]
    have hfour := four_balanced_outputs h
    change (7/8 : ℝ) • purePartialTrace (beamSplitter (1/2) h (fockPair 1 1)) +
      (1/8 : ℝ) • purePartialTrace (beamSplitter (1/2) h (fockPair 1 5)) = _
    rw [hfour.2.1, hfour.2.2.2]
    exact h_FockAttWitness_mix_B
  have h_FockAttTwoMode_tensor_norm (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ = ‖v‖ * ‖w‖ := by
    have hs := h_FockAttTwoMode_tensor_norm_sq v w
    nlinarith [norm_nonneg (tensor v w), norm_nonneg v, norm_nonneg w,
      mul_nonneg (norm_nonneg v) (norm_nonneg w)]
  let h_FockAttTwoMode_tensorLeft (w : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun v => tensor v w
        map_add' := by intro v v'; apply lp.ext; funext n; exact smul_add (w n) v v'
        map_smul' := by
          intro c v; apply lp.ext; funext n
          exact smul_comm (w n) c v }
      ‖w‖ (fun v => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm, mul_comm])
  have h_FockAttTwoMode_tensor_smul_left (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor (c • v) w = c • tensor v w := (h_FockAttTwoMode_tensorLeft w).map_smul c v
  have h_FockAttChannel_densitySqrt_pure (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) :
      CFC.sqrt (pureDensity v hv).operator = InnerProductSpace.rankOne ℂ v v := by
    apply CFC.sqrt_unique
    · exact InnerProductSpace.isIdempotentElem_rankOne_self hv
    · exact (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
        (InnerProductSpace.isPositive_rankOne_self v)
  have h_FockAttChannel_outputVector_pure (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) (n m l : ℕ) :
      outputVector η hη p (pureDensity v hv) (n,m,l) =
        inner ℂ v (h_FockAttTwoMode_fock m) • pureOutputVector η hη p v (n,l) := by
    simp only [outputVector, h_FockAttChannel_densitySqrt_pure, InnerProductSpace.rankOne_apply,
      h_FockAttTwoMode_tensor_smul_left, map_smul, lp.coeFn_smul, Pi.smul_apply, pureOutputVector]
    exact smul_comm _ _ _
  have h_FockAttChannel_outputVector_slice_hasSum (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
        (p : ProbabilityVector) (ρ : DensityOperator) (n m : ℕ) :
      HasSum (fun l => ‖outputVector η hη p ρ (n,m,l)‖ ^ 2)
        (p.weight n * ‖CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)‖ ^ 2) := by
    let w := beamSplitter η hη (tensor (CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)) (h_FockAttTwoMode_fock n))
    have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    have hn : ‖w‖ ^ 2 = ‖CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)‖ ^ 2 := by
      change ‖beamSplitter η hη (tensor (CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)) (h_FockAttTwoMode_fock n))‖ ^ 2 = _
      rw [LinearIsometryEquiv.norm_map, h_FockAttTwoMode_tensor_norm_sq]
      simp [h_FockAttTwoMode_fock, lp.norm_single]
    rw [hn] at hs
    have hsqrt : ‖(Real.sqrt (p.weight n) : ℂ)‖ ^ 2 = p.weight n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (p.nonneg n)]
    apply HasSum.congr_fun (hs.mul_left (p.weight n))
    intro l
    simp only [outputVector, norm_smul, mul_pow, hsqrt]
    rfl
  have h_FockAttChannel_densitySqrt_squared (ρ : DensityOperator) : CFC.sqrt ρ.operator * CFC.sqrt ρ.operator = ρ.operator := CFC.sqrt_mul_sqrt_self ρ.operator
      ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr ρ.positive)
  have h_FockAttChannel_densitySqrt_selfAdjoint (ρ : DensityOperator) : IsSelfAdjoint (CFC.sqrt ρ.operator) := (CFC.sqrt_nonneg ρ.operator).isSelfAdjoint
  have h_FockAttChannel_densitySqrt_norm_sq (ρ : DensityOperator) (v : (lp (fun _ : ℕ => ℂ) 2)) :
      ‖CFC.sqrt ρ.operator v‖ ^ 2 = (inner ℂ v (ρ.operator v)).re := by
    have hs := (h_FockAttChannel_densitySqrt_selfAdjoint ρ).isSymmetric v (CFC.sqrt ρ.operator v)
    have hprod : CFC.sqrt ρ.operator (CFC.sqrt ρ.operator v) = ρ.operator v := by
      exact congrArg (fun T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) => T v) (h_FockAttChannel_densitySqrt_squared ρ)
    change inner ℂ (CFC.sqrt ρ.operator v) (CFC.sqrt ρ.operator v) =
      inner ℂ v (CFC.sqrt ρ.operator (CFC.sqrt ρ.operator v)) at hs
    rw [hprod, inner_self_eq_norm_sq_to_K] at hs
    have hr := congrArg Complex.re hs
    norm_cast at hr
  have h_FockAttChannel_densitySqrt_hasSum (ρ : DensityOperator) :
      HasSum (fun m : ℕ => ‖CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)‖ ^ 2) 1 := HasSum.congr_fun ρ.trace_one (fun m => h_FockAttChannel_densitySqrt_norm_sq ρ (h_FockAttTwoMode_fock m))
  have h_FockAttChannel_outputVector_hasSum (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (ρ : DensityOperator) :
      HasSum (fun q : ℕ × ℕ × ℕ => ‖outputVector η hη p ρ q‖ ^ 2) 1 := by
    have hs := h_FockAttChannel_outputVector_slice_hasSum η hη p ρ
    have hn (n : ℕ) : Summable (fun q : ℕ × ℕ => ‖outputVector η hη p ρ (n,q)‖ ^ 2) := by
      rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
      refine ⟨fun m => (hs n m).summable, ?_⟩
      simp_rw [(hs n _).tsum_eq]
      exact (h_FockAttChannel_densitySqrt_hasSum ρ).summable.mul_left (p.weight n)
    have hnt (n : ℕ) : (∑' q : ℕ × ℕ, ‖outputVector η hη p ρ (n,q)‖ ^ 2) = p.weight n := by
      rw [(hn n).tsum_prod]
      simp_rw [(hs n _).tsum_eq]
      rw [(h_FockAttChannel_densitySqrt_hasSum ρ).summable.tsum_mul_left, (h_FockAttChannel_densitySqrt_hasSum ρ).tsum_eq,
        mul_one]
    have hall : Summable (fun q : ℕ × ℕ × ℕ => ‖outputVector η hη p ρ q‖ ^ 2) := by
      rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
      refine ⟨hn, ?_⟩
      simpa only [hnt] using p.normalized.summable
    have ht : (∑' q : ℕ × ℕ × ℕ, ‖outputVector η hη p ρ q‖ ^ 2) = 1 := by
      rw [hall.tsum_prod]
      simp_rw [hnt]
      exact p.normalized.tsum_eq
    exact ht ▸ hall.hasSum
  have h_FockAttChannel_attenuator_pure (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) :
      attenuatorOperator η hη p (pureDensity v hv) = pureAttenuatorOperator η hη p v := by
    have hvsum : HasSum (fun m : ℕ => ‖inner ℂ v (h_FockAttTwoMode_fock m)‖ ^ 2) 1 := by
      have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) v
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, hv, one_pow] at hs
      apply HasSum.congr_fun hs
      intro m
      simp only [h_FockAttTwoMode_fock, lp.inner_single_right, RCLike.inner_apply, one_mul, RCLike.norm_conj]
    have hall := h_FockAttMixture_rankOne_summable _
      (h_FockAttChannel_outputVector_hasSum η hη p (pureDensity v hv)).summable
    have hbase := h_FockAttMixture_rankOne_summable _ (h_FockAttChannel_pureOutputVector_hasSum η hη p v hv).summable
    unfold attenuatorOperator pureAttenuatorOperator mixture
    rw [hall.tsum_prod]
    have hrow (n : ℕ) : Summable (fun q : ℕ × ℕ => InnerProductSpace.rankOne ℂ
        (outputVector η hη p (pureDensity v hv) (n,q))
        (outputVector η hη p (pureDensity v hv) (n,q))) := hall.prod_factor n
    have hroweq (n : ℕ) :
        (∑' q : ℕ × ℕ, InnerProductSpace.rankOne ℂ
          (outputVector η hη p (pureDensity v hv) (n,q))
          (outputVector η hη p (pureDensity v hv) (n,q))) =
        ∑' l, InnerProductSpace.rankOne ℂ (pureOutputVector η hη p v (n,l))
          (pureOutputVector η hη p v (n,l)) := by
      have hswap := (Equiv.prodComm ℕ ℕ).tsum_eq (fun q : ℕ × ℕ =>
        InnerProductSpace.rankOne ℂ (outputVector η hη p (pureDensity v hv) (n,q))
          (outputVector η hη p (pureDensity v hv) (n,q)))
      rw [← hswap]
      change (∑' q : ℕ × ℕ, InnerProductSpace.rankOne ℂ
        (outputVector η hη p (pureDensity v hv) (n,q.swap))
        (outputVector η hη p (pureDensity v hv) (n,q.swap))) = _
      rw [(hrow n).prod_symm.tsum_prod]
      apply tsum_congr
      intro l
      change (∑' m : ℕ, InnerProductSpace.rankOne ℂ
        (outputVector η hη p (pureDensity v hv) (n,m,l))
        (outputVector η hη p (pureDensity v hv) (n,m,l))) = _
      simp_rw [h_FockAttChannel_outputVector_pure, h_FockAttChannel_rankOne_smul_self]
      rw [hvsum.summable.tsum_smul_const, hvsum.tsum_eq, one_smul]
    simp_rw [hroweq]
    exact hbase.tsum_prod.symm
  intro hc
  have hη : (1/2 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
  obtain ⟨α,hα⟩ := hc (1/2) hη environment
  have hbad := hα (fockDensity 1)
  change vonNeumannEntropy (attenuatorOperator (1/2) hη
    (environment) ((coherentDensity α))) ≤
    vonNeumannEntropy (attenuatorOperator (1/2) hη
      (environment) ((fockDensity 1))) at hbad
  rw [h_FockAttProbe_coherent_channel, h_FockAttProbe_fock_channel, h_FockAttChannel_attenuator_pure,
    h_FockAttChannel_attenuator_pure] at hbad
  have hp : environment = environment := rfl
  rw [hp] at hbad
  change vonNeumannEntropy (pureAttenuatorOperator (1/2) hη
    environment (displacement α (h_FockAttTwoMode_fock 0))) ≤
    vonNeumannEntropy (pureAttenuatorOperator (1/2) hη
      environment (h_FockAttTwoMode_fock 1)) at hbad
  rw [coherent_output_covariance,
    h_FockAttWitness_vacuum_output, h_FockAttWitness_onePhoton_output] at hbad
  change vonNeumannEntropy (LinearIsometryEquiv.conjStarAlgEquiv
    (displacement ((Real.sqrt (1/2) : ℂ) * α)) outputA) ≤
      vonNeumannEntropy outputB at hbad
  have h_entropy_invariant (U : (lp (fun _ : ℕ => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => ℂ) 2))
      (T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) :
      vonNeumannEntropy (LinearIsometryEquiv.conjStarAlgEquiv U T) = vonNeumannEntropy T := by
    let transportedBasis (U : (lp (fun _ : ℕ => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => ℂ) 2))
        (b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
      HilbertBasis.ofRepr (U.symm.trans b.repr)
    have transportedBasis_apply (U : (lp (fun _ : ℕ => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => ℂ) 2))
        (b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : transportedBasis U b n = U (b n) := by
      rw [← (transportedBasis U b).repr_symm_single, ← b.repr_symm_single]
      change (U.symm.trans b.repr).symm (lp.single 2 n 1) = U (b.repr.symm (lp.single 2 n 1))
      rfl
    have basisEntropy_conjugate (U : (lp (fun _ : ℕ => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => ℂ) 2))
        (T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) (b : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)) :
        basisEntropy (LinearIsometryEquiv.conjStarAlgEquiv U T) (transportedBasis U b) = basisEntropy T b := by
      unfold basisEntropy
      apply tsum_congr
      intro n
      rw [transportedBasis_apply]
      change ENNReal.ofReal (Real.negMulLog ((inner ℂ (U (b n))
        (U (T (U.symm (U (b n)))))).re)) = _
      rw [U.symm_apply_apply, U.inner_map_map]
    have transportedBasis_surjective (U : (lp (fun _ : ℕ => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => ℂ) 2)) :
        Function.Surjective (transportedBasis U) := by
      intro b
      refine ⟨transportedBasis U.symm b, ?_⟩
      apply DFunLike.ext
      intro n
      simp only [transportedBasis_apply, U.apply_symm_apply]
    unfold vonNeumannEntropy
    rw [← (transportedBasis_surjective U).iInf_comp]
    simp only [basisEntropy_conjugate]
  rw [h_entropy_invariant] at hbad
  exact (not_le_of_gt h_FockAttProbe_output_entropy_gap) hbad

end D5.S3.Quantum.QuantumChannels.PhaseCovariantAttenuatorCoherentRefutation
