/- GID: D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.claim; result=D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result; claim=D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.claim
   digest: Generalized concentratable entanglement can drop when a qubit joins the subsystem. -/

/-
proof_shape: powerTrace, gce: definition (Tr(ρ_α^K) with Tr(ρ_∅^K) = 1, and Eq. (defeq))
proof_shape: claim: definition (published conjecture, arXiv:2406.18517, Conjecture 6.1, journal
  Conjecture 1(1), read for every normalized N-qubit state, s' ⊆ s and real K > 1)
proof_shape: coeff, psi: definition (the counterexample state)
proof_shape: tripleEquiv, out1Equiv: definition (coordinate equivalences of the qubit
  configurations)
proof_shape: result: bind-only (as local steps: reindexing of the frozen reduced states; explicit
  positive semidefinite square roots S with S * S equal to the reindexed reduced state, so that
  CFC.sqrt_eq_iff and CFC.rpow_sqrt_nnreal give ρ^(5/2) = S^5; entrywise rational computations
  of the reduced states, of S * S and of trace(Q * Q * S); the normalization of the state; and
  rational bounds for eight square roots)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #12852; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.Outside
    sha256:22a66bd1cf70aa0215d327bcab393d44fd715d36c5b7924a2279d5500f074f1a
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.join
    sha256:b4d70d024cb174f7d6ec1491438cded1a4c04640dacc0715b561e92baf6f0409
  D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.reducedState
    sha256:e65dc7b2f0f3b5addc7d668c466eff01c28a16d0b5d73337e0f7016866bfd137
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.pairEquiv
    sha256:c5adc83049f8b344ac6ce6d27bd51847a3231ab1f09a4cbf9f5e225710eece39
  D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.outEquiv
    sha256:bc9632fb5cc63684ca0f355f4e7a3ee069338608253158810dcea889967ff112
  D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.singleEquiv
    sha256:f25daa09935ebd8d3e08ed5ca7f356949bf174b06cc14f37d0e323a7b42129f6
  D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.out3Equiv
    sha256:a56eb57848427128f856479a6c61e39951b0d89797de5fadebfdc3e0c1481d29
  D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.fourEquiv
    sha256:9cfbf5dc04a4adc97f266c1754c95e9676ba5cda4e1ab4b88acf8f9353752c39
-/

import D5.S3.Quantum.Entanglement.FourQubitResidualSumMonotoneRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.ConcentratableEntanglementSubsystemRefutation

/-!
X. Liu, J. Knörzer, Z. J. Wang and J. Tura, *Generalized Concentratable Entanglement via
Parallelized Permutation Tests*, Phys. Rev. Research 7 (2025) L032022, arXiv:2406.18517, define
`C^{(K)}_ψ(s) = (1 - 2^{-|s|} ∑_{α ⊆ s} Tr(ρ_α^K)) / (K - 1)` for an `n`-qubit pure state, with
`Tr(ρ_∅^K) = 1`, and conjecture `C^{(K)}_ψ(s') ≤ C^{(K)}_ψ(s)` whenever `s' ⊆ s`, for every real
`K > 1`. For the four-qubit state proportional to
`-1100|0000⟩ - 100|0101⟩ - 100|1010⟩ + 75|1100⟩ - 9|1111⟩` and `K = 5/2`,
`C^{(5/2)}({0, 1}) - C^{(5/2)}({0, 1, 2}) ≈ 4.81 · 10^{-8} > 0`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum (Outside join reducedState)
open D5.S3.Quantum.Entanglement.FourQubitResidualSumMonotoneRefutation
  (pairEquiv outEquiv singleEquiv out3Equiv fourEquiv)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

/-- `Tr(ρ_α^K)` for the reduced state `ρ_α` of `ψ`, with `Tr(ρ_∅^K) = 1`. -/
noncomputable def powerTrace {N : ℕ} (K : ℝ) (ψ : (Fin N → Fin 2) → ℂ) (α : Finset (Fin N)) :
    ℝ :=
  if α = ∅ then 1 else (trace (reducedState α ψ ^ K)).re

/-- Eq. (defeq): `C^{(K)}_ψ(s) = (1 - 2^{-|s|} ∑_{α ⊆ s} Tr(ρ_α^K)) / (K - 1)`. -/
noncomputable def gce {N : ℕ} (K : ℝ) (ψ : (Fin N → Fin 2) → ℂ) (s : Finset (Fin N)) : ℝ :=
  1 / (K - 1) * (1 - 1 / 2 ^ s.card * ∑ α ∈ s.powerset, powerTrace K ψ α)

/-- Conjecture 1(1): for every normalized `N`-qubit state, `s' ⊆ s` and real `K > 1`,
`C^{(K)}_ψ(s') ≤ C^{(K)}_ψ(s)`. -/
def claim : Prop :=
  ∀ (N : ℕ) (ψ : (Fin N → Fin 2) → ℂ), ∑ w, ‖ψ w‖ ^ 2 = 1 →
    ∀ s' s : Finset (Fin N), s' ⊆ s → ∀ K : ℝ, 1 < K → gce K ψ s' ≤ gce K ψ s

/-- The amplitudes `-1100, -100, -100, 75, -9` on `|0000⟩, |0101⟩, |1010⟩, |1100⟩, |1111⟩`. -/
noncomputable def coeff (w : Fin 4 → Fin 2) : ℝ :=
  if (w 0, w 1, w 2, w 3) = (0, 0, 0, 0) then -1100
  else if (w 0, w 1, w 2, w 3) = (0, 1, 0, 1) then -100
  else if (w 0, w 1, w 2, w 3) = (1, 0, 1, 0) then -100
  else if (w 0, w 1, w 2, w 3) = (1, 1, 0, 0) then 75
  else if (w 0, w 1, w 2, w 3) = (1, 1, 1, 1) then -9 else 0

/-- The counterexample state `coeff / √1235706`. -/
noncomputable def psi : (Fin 4 → Fin 2) → ℂ := fun w =>
  (coeff w : ℂ) / (Real.sqrt 1235706 : ℂ)

/-- The configurations of the qubits `0, 1, 2` as `Fin 2 × Fin 2 × Fin 2`. -/
def tripleEquiv : (↥({0, 1, 2} : Finset (Fin 4)) → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun x := (x ⟨0, by decide⟩, x ⟨1, by decide⟩, x ⟨2, by decide⟩)
  invFun x i := if i.1 = 0 then x.1 else if i.1 = 1 then x.2.1 else x.2.2
  left_inv x := by
    funext ⟨i, hi⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  right_inv x := by simp

/-- The configurations of the qubit `3` outside `{0, 1, 2}` as `Fin 2`. -/
def out1Equiv : (Outside ({0, 1, 2} : Finset (Fin 4)) → Fin 2) ≃ Fin 2 where
  toFun z := z ⟨3, by decide⟩
  invFun d _ := d
  left_inv z := by
    funext ⟨i, hi⟩
    have : i = 3 := by fin_cases i <;> simp_all
    subst this
    rfl
  right_inv _ := rfl

set_option maxHeartbeats 8000000 in
-- Seven reduced states and their square roots are computed entrywise in this declaration.
theorem result : ¬ claim := by
  intro h
  have hkey : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (e : ι ≃ κ) (ρ : Matrix ι ι ℂ) (S' : Matrix κ κ ℂ), S'.PosSemidef →
      S' * S' = reindex e e ρ → trace (ρ ^ ((5 : ℝ) / 2)) = trace (S' ^ 5) := by
    intro ι κ _ _ _ _ e ρ S' hS hSS
    set S : Matrix ι ι ℂ := reindex e.symm e.symm S' with hSdef
    have hS0 : 0 ≤ S := by
      rw [Matrix.nonneg_iff_posSemidef, hSdef, reindex_apply]
      exact hS.submatrix _
    have hρS : S * S = ρ := by
      have : reindex e e (S * S) = reindex e e ρ := by
        rw [← hSS, hSdef]
        simp [reindex_apply, submatrix_mul_equiv]
      exact (reindex e e).injective this
    have hρ0 : 0 ≤ ρ := by
      rw [← hρS, Matrix.nonneg_iff_posSemidef]
      have h1 := Matrix.nonneg_iff_posSemidef.mp hS0
      have := Matrix.posSemidef_conjTranspose_mul_self S
      rwa [h1.1.eq] at this
    have hsqrt : CFC.sqrt ρ = S := (CFC.sqrt_eq_iff ρ S hρ0 hS0).2 hρS
    have h52 : ((5 : ℝ) / 2) = (((5 : NNReal) : ℝ) / 2) := by norm_num
    rw [h52, ← CFC.rpow_sqrt_nnreal hρ0, hsqrt]
    have : (S ^ (((5 : NNReal) : ℝ))) = S ^ (5 : ℕ) := by
      simpa using CFC.rpow_natCast S 5 hS0
    rw [this]
    have hpow : reindex e e (S ^ 5) = S' ^ 5 := by
      rw [hSdef]
      simp [reindex_apply, submatrix_mul_equiv, pow_succ]
    rw [← hpow]
    simp only [trace, diag, reindex_apply, submatrix_apply]
    exact (Equiv.sum_comp e.symm _).symm
  have hT : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (e : ι ≃ κ) (ρ : Matrix ι ι ℂ) (Q S : Matrix κ κ ℝ),
      (∀ x y, reindex e e ρ x y = ((Q x y / 1235706 : ℝ) : ℂ)) →
      (S.map ((↑) : ℝ → ℂ)).PosSemidef → S * S = Q →
      (trace (ρ ^ ((5 : ℝ) / 2))).re =
        (Q * Q * S).trace / (1235706 ^ 2 * Real.sqrt 1235706) := by
    intro ι κ _ _ _ _ e ρ Q S hρ hS hSS
    set r : ℝ := Real.sqrt 1235706 with hr
    have hr2 : r * r = 1235706 := Real.mul_self_sqrt (by norm_num)
    have hr0 : 0 < r := by positivity
    have hS' : ((r⁻¹ : ℝ) • S.map ((↑) : ℝ → ℂ)).PosSemidef := hS.smul (by positivity)
    have hmm : ∀ A B : Matrix κ κ ℝ,
        A.map ((↑) : ℝ → ℂ) * B.map ((↑) : ℝ → ℂ) = (A * B).map ((↑) : ℝ → ℂ) := by
      intro A B
      ext i j
      simp [Matrix.mul_apply]
    have hinv : r⁻¹ * r⁻¹ = (1235706 : ℝ)⁻¹ := by rw [← mul_inv, hr2]
    have hSS' : ((r⁻¹ : ℝ) • S.map ((↑) : ℝ → ℂ)) * ((r⁻¹ : ℝ) • S.map ((↑) : ℝ → ℂ)) =
        reindex e e ρ := by
      ext x y
      rw [hρ x y, smul_mul_smul_comm, hmm, hSS, hinv]
      simp only [Matrix.smul_apply, Matrix.map_apply, Complex.real_smul]
      push_cast
      ring
    have hpw : ∀ (A : Matrix κ κ ℝ) (n : ℕ),
        (A.map ((↑) : ℝ → ℂ)) ^ n = (A ^ n).map ((↑) : ℝ → ℂ) := by
      intro A n
      induction n with
      | zero =>
        ext i j
        simp [Matrix.one_apply]
        split_ifs <;> simp
      | succ n ih => rw [pow_succ, pow_succ, ih, hmm]
    have h5 : S ^ 5 = Q * Q * S := by
      rw [← hSS]
      simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
    rw [hkey e ρ _ hS' hSS', smul_pow, hpw, h5, Matrix.trace_smul]
    have htr : ((Q * Q * S).map ((↑) : ℝ → ℂ)).trace = (((Q * Q * S).trace : ℝ) : ℂ) := by
      simp [Matrix.trace]
    rw [htr, Complex.real_smul, Complex.re_ofReal_mul]
    have h5r : r⁻¹ ^ 5 = (1235706 ^ 2 * r)⁻¹ := by
      rw [show r⁻¹ ^ 5 = (r⁻¹ * r⁻¹) * (r⁻¹ * r⁻¹) * r⁻¹ by ring, hinv, mul_inv]
      ring
    rw [h5r, div_eq_inv_mul, Complex.ofReal_re]
  have hpp : ∀ x y : Fin 4 → Fin 2,
      psi x * star (psi y) = ((coeff x * coeff y / 1235706 : ℝ) : ℂ) := by
    intro x y
    have hs : Real.sqrt 1235706 * Real.sqrt 1235706 = 1235706 := Real.mul_self_sqrt (by norm_num)
    have hs0 : Real.sqrt 1235706 ≠ 0 := by positivity
    simp only [psi, star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, show ((Real.sqrt 1235706 : ℂ) * (Real.sqrt 1235706 : ℂ)) =
      (1235706 : ℂ) by rw [← Complex.ofReal_mul, hs]; norm_num]
    push_cast
    ring
  have hse : ∀ (k r s t : Fin 4) (hr : r ∉ ({k} : Finset (Fin 4)))
      (hs : s ∉ ({k} : Finset (Fin 4))) (ht : t ∉ ({k} : Finset (Fin 4))) (hrs : r ≠ s)
      (hrt : r ≠ t) (hst : s ≠ t)
      (hcov : ∀ i : Fin 4, i ∉ ({k} : Finset (Fin 4)) → i = r ∨ i = s ∨ i = t)
      (a a' : Fin 2),
      reindex (singleEquiv k) (singleEquiv k) (reducedState ({k} : Finset (Fin 4)) psi) a a' =
        ∑ b, ∑ c, ∑ d,
          psi (fun i => if i = k then a else if i = r then b else if i = s then c else d) *
            star (psi (fun i =>
              if i = k then a' else if i = r then b else if i = s then c else d)) := by
    intro k r s t hr hs ht hrs hrt hst hcov a a'
    simp only [reindex_apply, submatrix_apply, reducedState, partialTraceRight, Matrix.of_apply]
    rw [← Equiv.sum_comp (out3Equiv k r s t hr hs ht hrs hrt hst hcov).symm,
      Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    have hk : k ∈ ({k} : Finset (Fin 4)) := by simp
    have key : ∀ x b c d : Fin 2,
        join ({k} : Finset (Fin 4)) ((singleEquiv k).symm x)
            ((out3Equiv k r s t hr hs ht hrs hrt hst hcov).symm (b, c, d)) =
          fun i => if i = k then x else if i = r then b else if i = s then c else d := by
      intro x b c d
      funext i
      simp only [join, Equiv.piEquivPiSubtypeProd_symm_apply, singleEquiv, out3Equiv,
        Equiv.coe_fn_symm_mk]
      by_cases hi : i ∈ ({k} : Finset (Fin 4))
      · rw [dif_pos hi]
        simp only [Finset.mem_singleton] at hi
        subst hi
        simp
      · rw [dif_neg hi]
        have hik : i ≠ k := fun e => hi (e ▸ hk)
        rcases hcov i hi with rfl | rfl | rfl
        · simp [hik]
        · simp [hik, Ne.symm hrs]
        · simp [hik, Ne.symm hrt, Ne.symm hst]
    simp only [key]
  -- the single-qubit marginals
  have hsingle : ∀ (k r s t : Fin 4) (hr : r ∉ ({k} : Finset (Fin 4)))
      (hs : s ∉ ({k} : Finset (Fin 4))) (ht : t ∉ ({k} : Finset (Fin 4))) (hrs : r ≠ s)
      (hrt : r ≠ t) (hst : s ≠ t)
      (hcov : ∀ i : Fin 4, i ∉ ({k} : Finset (Fin 4)) → i = r ∨ i = s ∨ i = t) (p q : ℝ),
      0 ≤ p → 0 ≤ q →
      (∀ a a' : Fin 2, ∑ b, ∑ c, ∑ d,
          coeff (fun i => if i = k then a else if i = r then b else if i = s then c else d) *
            coeff (fun i => if i = k then a' else if i = r then b else if i = s then c else d) =
          diagonal ![p, q] a a') →
      (trace (reducedState ({k} : Finset (Fin 4)) psi ^ ((5 : ℝ) / 2))).re =
        (p ^ 2 * Real.sqrt p + q ^ 2 * Real.sqrt q) / (1235706 ^ 2 * Real.sqrt 1235706) := by
    intro k r s t hr hs ht hrs hrt hst hcov p q hp hq hval
    have hS : ((diagonal ![Real.sqrt p, Real.sqrt q]).map ((↑) : ℝ → ℂ)).PosSemidef := by
      rw [Matrix.diagonal_map (by simp)]
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> simp [Complex.zero_le_real, Real.sqrt_nonneg]
    have hSS : diagonal ![Real.sqrt p, Real.sqrt q] * diagonal ![Real.sqrt p, Real.sqrt q] =
        diagonal ![p, q] := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [Real.mul_self_sqrt hp, Real.mul_self_sqrt hq]
    rw [hT (singleEquiv k) _ (diagonal ![p, q]) _ ?_ hS hSS]
    · congr 1
      simp [Matrix.trace, Fin.sum_univ_two, diagonal_mul_diagonal]
      ring
    · intro a a'
      rw [hse k r s t hr hs ht hrs hrt hst hcov]
      simp only [hpp]
      rw [← hval a a']
      push_cast
      simp only [Finset.sum_div]
  have hpe : ∀ (p q r s : Fin 4) (h : p ≠ q) (hr : r ∉ ({p, q} : Finset (Fin 4)))
      (hs : s ∉ ({p, q} : Finset (Fin 4))) (hrs : r ≠ s)
      (hcov : ∀ i : Fin 4, i ∉ ({p, q} : Finset (Fin 4)) → i = r ∨ i = s) (a b a' b' : Fin 2),
      reindex (pairEquiv p q h) (pairEquiv p q h) (reducedState ({p, q} : Finset (Fin 4)) psi)
          (a, b) (a', b') =
        ∑ c, ∑ d, psi (fun i => if i = p then a else if i = q then b else if i = r then c else d) *
          star (psi (fun i =>
            if i = p then a' else if i = q then b' else if i = r then c else d)) := by
    intro p q r s h hr hs hrs hcov a b a' b'
    simp only [reindex_apply, submatrix_apply, reducedState, partialTraceRight, Matrix.of_apply]
    rw [← Equiv.sum_comp (outEquiv p q r s hr hs hrs hcov).symm, Fintype.sum_prod_type]
    have hp : p ∈ ({p, q} : Finset (Fin 4)) := by simp
    have hq : q ∈ ({p, q} : Finset (Fin 4)) := by simp
    have key : ∀ x y c d : Fin 2,
        join ({p, q} : Finset (Fin 4)) ((pairEquiv p q h).symm (x, y))
            ((outEquiv p q r s hr hs hrs hcov).symm (c, d)) =
          fun i => if i = p then x else if i = q then y else if i = r then c else d := by
      intro x y c d
      funext i
      simp only [join, Equiv.piEquivPiSubtypeProd_symm_apply, pairEquiv, outEquiv,
        Equiv.coe_fn_symm_mk]
      by_cases hi : i ∈ ({p, q} : Finset (Fin 4))
      · rw [dif_pos hi]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simp
        · simp [Ne.symm h]
      · rw [dif_neg hi]
        have hip : i ≠ p := fun e => hi (e ▸ hp)
        have hiq : i ≠ q := fun e => hi (e ▸ hq)
        rcases hcov i hi with rfl | rfl
        · simp [hip, hiq]
        · simp [hip, hiq, Ne.symm hrs]
    simp only [key]
  have hpair : ∀ (p q r s : Fin 4) (h : p ≠ q) (hr : r ∉ ({p, q} : Finset (Fin 4)))
      (hs : s ∉ ({p, q} : Finset (Fin 4))) (hrs : r ≠ s)
      (hcov : ∀ i : Fin 4, i ∉ ({p, q} : Finset (Fin 4)) → i = r ∨ i = s)
      (Q S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ),
      (∀ a b a' b' : Fin 2, ∑ c, ∑ d,
          coeff (fun i => if i = p then a else if i = q then b else if i = r then c else d) *
            coeff (fun i => if i = p then a' else if i = q then b' else if i = r then c else d) =
          Q (a, b) (a', b')) →
      (S.map ((↑) : ℝ → ℂ)).PosSemidef → S * S = Q →
      (trace (reducedState ({p, q} : Finset (Fin 4)) psi ^ ((5 : ℝ) / 2))).re =
        (Q * Q * S).trace / (1235706 ^ 2 * Real.sqrt 1235706) := by
    intro p q r s h hr hs hrs hcov Q S hval hS hSS
    refine hT (pairEquiv p q h) _ Q S ?_ hS hSS
    rintro ⟨a, b⟩ ⟨a', b'⟩
    rw [hpe p q r s h hr hs hrs hcov]
    simp only [hpp]
    rw [← hval a b a' b']
    push_cast
    simp only [Finset.sum_div]
  -- the marginal on the qubits 0, 1
  set c01 : ℝ := Real.sqrt 1235506 with hc01
  have hc01s : c01 * c01 = 1235506 := Real.mul_self_sqrt (by norm_num)
  have hc01p : 0 < c01 := by positivity
  obtain ⟨Q01, hQ01⟩ : ∃ Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, Q = Matrix.of fun x y =>
      if (x, y) = ((0, 0), (0, 0)) then 1210000 else if (x, y) = ((0, 0), (1, 1)) then -82500
      else if (x, y) = ((1, 1), (0, 0)) then -82500 else if (x, y) = ((1, 1), (1, 1)) then 5706
      else if (x, y) = ((0, 1), (0, 1)) then 10000 else if (x, y) = ((1, 0), (1, 0)) then 10000
      else 0 := ⟨_, rfl⟩
  obtain ⟨S01, hS01⟩ : ∃ S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, S = Matrix.of fun x y =>
      if (x, y) = ((0, 0), (0, 0)) then 1219900 / c01
      else if (x, y) = ((0, 0), (1, 1)) then -82500 / c01
      else if (x, y) = ((1, 1), (0, 0)) then -82500 / c01
      else if (x, y) = ((1, 1), (1, 1)) then 15606 / c01
      else if (x, y) = ((0, 1), (0, 1)) then 100 else if (x, y) = ((1, 0), (1, 0)) then 100
      else 0 := ⟨_, rfl⟩
  have hT01 : (trace (reducedState ({0, 1} : Finset (Fin 4)) psi ^ ((5 : ℝ) / 2))).re =
      (2 * 10000 ^ 2 * 100 + ((1210000 ^ 2 + 82500 ^ 2) * 1219900 +
        2 * (1215706 * 82500) * 82500 + (82500 ^ 2 + 5706 ^ 2) * 15606) / c01) /
        (1235706 ^ 2 * Real.sqrt 1235706) := by
    rw [hpair 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) Q01 S01]
    · congr 1
      rw [hQ01, hS01]
      simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
      field_simp
      ring
    · intro a b a' b'
      rw [hQ01]
      fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
        simp [coeff, Fin.sum_univ_two] <;> norm_num
    · have hE : S01.map ((↑) : ℝ → ℂ) =
          diagonal (fun x => if x = (0, 1) ∨ x = (1, 0) then (100 : ℂ) else 0) +
          ((c01⁻¹ : ℝ) • (vecMulVec (fun x => if x = (0, 0) then (-1100 : ℂ)
              else if x = (1, 1) then 75 else 0)
              (star fun x => if x = (0, 0) then (-1100 : ℂ) else if x = (1, 1) then 75 else 0) +
            vecMulVec (fun x => if x = (1, 1) then (-9 : ℂ) else 0)
              (star fun x => if x = (1, 1) then (-9 : ℂ) else 0) +
            ((9900 : ℝ) • diagonal (fun x =>
              if x = (0, 0) ∨ x = (1, 1) then (1 : ℂ) else 0)))) := by
        rw [hS01]
        ext ⟨a, b⟩ ⟨a', b'⟩
        fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
          simp [vecMulVec, diagonal, map_ofNat] <;> field_simp <;> norm_num
      rw [hE]
      refine Matrix.PosSemidef.add ?_ (Matrix.PosSemidef.smul ?_ (by positivity))
      · rw [Matrix.posSemidef_diagonal_iff]
        intro x
        split_ifs <;> simp
      · refine Matrix.PosSemidef.add (Matrix.PosSemidef.add (posSemidef_vecMulVec_self_star _)
          (posSemidef_vecMulVec_self_star _)) (Matrix.PosSemidef.smul ?_ (by norm_num))
        rw [Matrix.posSemidef_diagonal_iff]
        intro x
        split_ifs <;> simp
    · rw [hQ01, hS01]
      ext ⟨a, b⟩ ⟨a', b'⟩
      fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
        simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
        field_simp <;> nlinarith [hc01s]
  -- the marginal on the qubits 0, 2
  set c02 : ℝ := Real.sqrt 1230281 with hc02
  have hc02s : c02 * c02 = 1230281 := Real.mul_self_sqrt (by norm_num)
  have hc02p : 0 < c02 := by positivity
  obtain ⟨Q02, hQ02⟩ : ∃ Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, Q = Matrix.of fun x y =>
      if (x, y) = ((0, 0), (0, 0)) then 1220000 else if (x, y) = ((0, 0), (1, 1)) then 110900
      else if (x, y) = ((1, 1), (0, 0)) then 110900 else if (x, y) = ((1, 1), (1, 1)) then 10081
      else if (x, y) = ((1, 0), (1, 0)) then 5625 else 0 := ⟨_, rfl⟩
  obtain ⟨S02, hS02⟩ : ∃ S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, S = Matrix.of fun x y =>
      if (x, y) = ((0, 0), (0, 0)) then 1220100 / c02
      else if (x, y) = ((0, 0), (1, 1)) then 110900 / c02
      else if (x, y) = ((1, 1), (0, 0)) then 110900 / c02
      else if (x, y) = ((1, 1), (1, 1)) then 10181 / c02
      else if (x, y) = ((1, 0), (1, 0)) then 75 else 0 := ⟨_, rfl⟩
  have hT02 : (trace (reducedState ({0, 2} : Finset (Fin 4)) psi ^ ((5 : ℝ) / 2))).re =
      (5625 ^ 2 * 75 + ((1220000 ^ 2 + 110900 ^ 2) * 1220100 +
        2 * (110900 * 1230081) * 110900 + (110900 ^ 2 + 10081 ^ 2) * 10181) / c02) /
        (1235706 ^ 2 * Real.sqrt 1235706) := by
    rw [hpair 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) Q02 S02]
    · congr 1
      rw [hQ02, hS02]
      simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
      field_simp
      ring
    · intro a b a' b'
      rw [hQ02]
      fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
        simp [coeff, Fin.sum_univ_two] <;> norm_num
    · have hE : S02.map ((↑) : ℝ → ℂ) =
          diagonal (fun x => if x = (1, 0) then (75 : ℂ) else 0) +
          ((c02⁻¹ : ℝ) • (vecMulVec (fun x => if x = (0, 0) then (-1100 : ℂ)
              else if x = (1, 1) then -100 else 0)
              (star fun x => if x = (0, 0) then (-1100 : ℂ) else if x = (1, 1) then -100 else 0) +
            vecMulVec (fun x => if x = (0, 0) then (-100 : ℂ) else if x = (1, 1) then -9 else 0)
              (star fun x => if x = (0, 0) then (-100 : ℂ) else if x = (1, 1) then -9 else 0) +
            ((100 : ℝ) • diagonal (fun x => if x = (0, 0) ∨ x = (1, 1) then (1 : ℂ) else 0)))) := by
        rw [hS02]
        ext ⟨a, b⟩ ⟨a', b'⟩
        fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
          simp [vecMulVec, diagonal, map_ofNat] <;> field_simp <;> norm_num
      rw [hE]
      refine Matrix.PosSemidef.add ?_ (Matrix.PosSemidef.smul ?_ (by positivity))
      · rw [Matrix.posSemidef_diagonal_iff]
        intro x
        split_ifs <;> simp
      · refine Matrix.PosSemidef.add (Matrix.PosSemidef.add (posSemidef_vecMulVec_self_star _)
          (posSemidef_vecMulVec_self_star _)) (Matrix.PosSemidef.smul ?_ (by norm_num))
        rw [Matrix.posSemidef_diagonal_iff]
        intro x
        split_ifs <;> simp
    · rw [hQ02, hS02]
      ext ⟨a, b⟩ ⟨a', b'⟩
      fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
        simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
        field_simp <;> nlinarith [hc02s]
  -- the marginal on the qubits 1, 2
  set c12 : ℝ := Real.sqrt 45625 with hc12
  have hc12s : c12 * c12 = 45625 := Real.mul_self_sqrt (by norm_num)
  have hc12p : 0 < c12 := by positivity
  obtain ⟨Q12, hQ12⟩ : ∃ Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, Q = Matrix.of fun x y =>
      if (x, y) = ((0, 1), (0, 1)) then 10000 else if (x, y) = ((0, 1), (1, 0)) then -7500
      else if (x, y) = ((1, 0), (0, 1)) then -7500 else if (x, y) = ((1, 0), (1, 0)) then 15625
      else if (x, y) = ((0, 0), (0, 0)) then 1210000 else if (x, y) = ((1, 1), (1, 1)) then 81
      else 0 := ⟨_, rfl⟩
  obtain ⟨S12, hS12⟩ : ∃ S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, S = Matrix.of fun x y =>
      if (x, y) = ((0, 1), (0, 1)) then 20000 / c12
      else if (x, y) = ((0, 1), (1, 0)) then -7500 / c12
      else if (x, y) = ((1, 0), (0, 1)) then -7500 / c12
      else if (x, y) = ((1, 0), (1, 0)) then 25625 / c12
      else if (x, y) = ((0, 0), (0, 0)) then 1100 else if (x, y) = ((1, 1), (1, 1)) then 9
      else 0 := ⟨_, rfl⟩
  have hT12 : (trace (reducedState ({1, 2} : Finset (Fin 4)) psi ^ ((5 : ℝ) / 2))).re =
      (1210000 ^ 2 * 1100 + 81 ^ 2 * 9 + ((10000 ^ 2 + 7500 ^ 2) * 20000 +
        2 * (7500 * 25625) * 7500 + (7500 ^ 2 + 15625 ^ 2) * 25625) / c12) /
        (1235706 ^ 2 * Real.sqrt 1235706) := by
    rw [hpair 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) Q12 S12]
    · congr 1
      rw [hQ12, hS12]
      simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
      field_simp
      ring
    · intro a b a' b'
      rw [hQ12]
      fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
        simp [coeff, Fin.sum_univ_two] <;> norm_num
    · have hE : S12.map ((↑) : ℝ → ℂ) =
          diagonal (fun x => if x = (0, 0) then (1100 : ℂ) else if x = (1, 1) then 9 else 0) +
          ((c12⁻¹ : ℝ) • (vecMulVec (fun x => if x = (0, 1) then (-100 : ℂ)
              else if x = (1, 0) then 75 else 0)
              (star fun x => if x = (0, 1) then (-100 : ℂ) else if x = (1, 0) then 75 else 0) +
            vecMulVec (fun x => if x = (1, 0) then (-100 : ℂ) else 0)
              (star fun x => if x = (1, 0) then (-100 : ℂ) else 0) +
            ((10000 : ℝ) • diagonal (fun x =>
              if x = (0, 1) ∨ x = (1, 0) then (1 : ℂ) else 0)))) := by
        rw [hS12]
        ext ⟨a, b⟩ ⟨a', b'⟩
        fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
          simp [vecMulVec, diagonal, map_ofNat] <;> field_simp <;> norm_num
      rw [hE]
      refine Matrix.PosSemidef.add ?_ (Matrix.PosSemidef.smul ?_ (by positivity))
      · rw [Matrix.posSemidef_diagonal_iff]
        intro x
        split_ifs <;> simp
      · refine Matrix.PosSemidef.add (Matrix.PosSemidef.add (posSemidef_vecMulVec_self_star _)
          (posSemidef_vecMulVec_self_star _)) (Matrix.PosSemidef.smul ?_ (by norm_num))
        rw [Matrix.posSemidef_diagonal_iff]
        intro x
        split_ifs <;> simp
    · rw [hQ12, hS12]
      ext ⟨a, b⟩ ⟨a', b'⟩
      fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
        simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
        field_simp <;> nlinarith [hc12s]
  -- the marginal on the qubits 0, 1, 2
  have hte : ∀ a b c a' b' c' : Fin 2,
      reindex tripleEquiv tripleEquiv (reducedState ({0, 1, 2} : Finset (Fin 4)) psi) (a, b, c)
          (a', b', c') =
        ∑ d, psi (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d) *
          star (psi (fun i =>
            if i = 0 then a' else if i = 1 then b' else if i = 2 then c' else d)) := by
    intro a b c a' b' c'
    simp only [reindex_apply, submatrix_apply, reducedState, partialTraceRight, Matrix.of_apply]
    rw [← Equiv.sum_comp out1Equiv.symm]
    have key : ∀ x y z d : Fin 2,
        join ({0, 1, 2} : Finset (Fin 4)) (tripleEquiv.symm (x, y, z)) (out1Equiv.symm d) =
          fun i => if i = 0 then x else if i = 1 then y else if i = 2 then z else d := by
      intro x y z d
      funext i
      fin_cases i <;> simp [join, Equiv.piEquivPiSubtypeProd_symm_apply, tripleEquiv, out1Equiv]
    simp only [key]
  set su : ℝ := Real.sqrt 1225625 with hsu
  set sw : ℝ := Real.sqrt 10081 with hsw
  have hsus : su * su = 1225625 := Real.mul_self_sqrt (by norm_num)
  have hsws : sw * sw = 10081 := Real.mul_self_sqrt (by norm_num)
  have hsup : 0 < su := by positivity
  have hswp : 0 < sw := by positivity
  obtain ⟨uv, huv⟩ : ∃ u : Fin 2 × Fin 2 × Fin 2 → ℝ, u = fun x =>
      if x = (0, 0, 0) then -1100 else if x = (1, 0, 1) then -100 else if x = (1, 1, 0) then 75
      else 0 := ⟨_, rfl⟩
  obtain ⟨wv, hwv⟩ : ∃ w : Fin 2 × Fin 2 × Fin 2 → ℝ, w = fun x =>
      if x = (0, 1, 0) then -100 else if x = (1, 1, 1) then -9 else 0 := ⟨_, rfl⟩
  have huu : ∑ z, uv z * uv z = 1225625 := by
    rw [huv]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
  have hww : ∑ z, wv z * wv z = 10081 := by
    rw [hwv]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
  have huw : ∑ z, uv z * wv z = 0 := by
    rw [huv, hwv]
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
  set Q012 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℝ :=
    Matrix.of fun x y => uv x * uv y + wv x * wv y with hQ012
  set S012 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℝ :=
    Matrix.of fun x y => uv x * uv y / su + wv x * wv y / sw with hS012
  have hT012 : (trace (reducedState ({0, 1, 2} : Finset (Fin 4)) psi ^ ((5 : ℝ) / 2))).re =
      (1225625 ^ 3 / su + 10081 ^ 3 / sw) / (1235706 ^ 2 * Real.sqrt 1235706) := by
    have hSS : S012 * S012 = Q012 := by
      ext x y
      simp only [hS012, hQ012, Matrix.mul_apply, Matrix.of_apply]
      have hexp : ∀ z, (uv x * uv z / su + wv x * wv z / sw) *
          (uv z * uv y / su + wv z * wv y / sw) =
          uv x * uv y / (su * su) * (uv z * uv z) +
            (uv x * wv y + wv x * uv y) / (su * sw) * (uv z * wv z) +
            wv x * wv y / (sw * sw) * (wv z * wv z) := by
        intro z
        field_simp
        ring
      simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, huu, hww, huw, hsus, hsws]
      field_simp
      ring
    rw [hT tripleEquiv _ Q012 S012 ?_ ?_ hSS]
    · congr 1
      have hQQ : Q012 * Q012 = Matrix.of fun x y =>
          1225625 * (uv x * uv y) + 10081 * (wv x * wv y) := by
        ext x y
        simp only [hQ012, Matrix.mul_apply, Matrix.of_apply]
        have hexp : ∀ z, (uv x * uv z + wv x * wv z) * (uv z * uv y + wv z * wv y) =
            uv x * uv y * (uv z * uv z) + (uv x * wv y + wv x * uv y) * (uv z * wv z) +
              wv x * wv y * (wv z * wv z) := by
          intro z
          ring
        simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, huu, hww, huw]
        ring
      rw [hQQ]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, hS012]
      have hexp : ∀ x y, (1225625 * (uv x * uv y) + 10081 * (wv x * wv y)) *
          (uv y * uv x / su + wv y * wv x / sw) =
          1225625 / su * (uv x * uv x) * (uv y * uv y) +
            (1225625 / sw + 10081 / su) * (uv x * wv x) * (uv y * wv y) +
            10081 / sw * (wv x * wv x) * (wv y * wv y) := by
        intro x y
        field_simp
        ring
      simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, huu, hww, huw]
      ring
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
      rw [hte]
      simp only [hpp]
      rw [← Complex.ofReal_sum]
      congr 1
      rw [← Finset.sum_div]
      congr 1
      simp only [hQ012, Matrix.of_apply, huv, hwv]
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases a' <;> fin_cases b' <;>
        fin_cases c' <;> simp [coeff]
    · have hE : S012.map ((↑) : ℝ → ℂ) =
          (su⁻¹ : ℝ) • vecMulVec (fun x => (uv x : ℂ)) (star fun x => (uv x : ℂ)) +
            (sw⁻¹ : ℝ) • vecMulVec (fun x => (wv x : ℂ)) (star fun x => (wv x : ℂ)) := by
        ext x y
        simp [hS012, vecMulVec]
        ring
      rw [hE]
      exact Matrix.PosSemidef.add ((posSemidef_vecMulVec_self_star _).smul (by positivity))
        ((posSemidef_vecMulVec_self_star _).smul (by positivity))
  -- the single-qubit marginals
  have hT0 := hsingle 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) 1220000 15706 (by norm_num) (by norm_num)
    (by intro a a'; fin_cases a <;> fin_cases a' <;> simp [coeff, Fin.sum_univ_two] <;> norm_num)
  have hT1 := hsingle 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) 1220000 15706 (by norm_num) (by norm_num)
    (by intro a a'; fin_cases a <;> fin_cases a' <;> simp [coeff, Fin.sum_univ_two] <;> norm_num)
  have hT2 := hsingle 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) 1225625 10081 (by norm_num) (by norm_num)
    (by intro a a'; fin_cases a <;> fin_cases a' <;> simp [coeff, Fin.sum_univ_two] <;> norm_num)
  rw [← hsu, ← hsw] at hT2
  -- the state is normalized
  have hnorm : ∑ w, ‖psi w‖ ^ 2 = 1 := by
    have hsum : ∀ f : (Fin 4 → Fin 2) → ℝ, ∑ w, f w = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
      intro f
      rw [← Equiv.sum_comp fourEquiv.symm]
      simp only [Fintype.sum_prod_type]
      rfl
    have hn : ∀ w, ‖psi w‖ ^ 2 = coeff w ^ 2 / 1235706 := by
      intro w
      simp only [psi, norm_div, Complex.norm_real, Real.norm_eq_abs]
      rw [div_pow, sq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num)), Real.sq_sqrt (by norm_num)]
    simp only [hn]
    rw [hsum]
    simp [coeff, Fin.sum_univ_two]
    norm_num
  -- the two concentratable entanglements
  have hle := h 4 psi hnorm {0, 1} {0, 1, 2} (by decide) ((5 : ℝ) / 2) (by norm_num)
  have hP2 : ({0, 1} : Finset (Fin 4)).powerset = {∅, {0}, {1}, {0, 1}} := by decide
  have hP3 : ({0, 1, 2} : Finset (Fin 4)).powerset =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have hpt : ∀ α : Finset (Fin 4), α ≠ ∅ →
      powerTrace ((5 : ℝ) / 2) psi α = (trace (reducedState α psi ^ ((5 : ℝ) / 2))).re := by
    intro α hα
    simp [powerTrace, hα]
  have hpt0 : powerTrace ((5 : ℝ) / 2) psi ∅ = 1 := by simp [powerTrace]
  have hs2 : ∑ α ∈ ({0, 1} : Finset (Fin 4)).powerset, powerTrace ((5 : ℝ) / 2) psi α =
      1 + powerTrace ((5 : ℝ) / 2) psi {0} + powerTrace ((5 : ℝ) / 2) psi {1} +
        powerTrace ((5 : ℝ) / 2) psi {0, 1} := by
    rw [hP2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton, hpt0]
    ring
  have hs3 : ∑ α ∈ ({0, 1, 2} : Finset (Fin 4)).powerset, powerTrace ((5 : ℝ) / 2) psi α =
      1 + powerTrace ((5 : ℝ) / 2) psi {0} + powerTrace ((5 : ℝ) / 2) psi {1} +
        powerTrace ((5 : ℝ) / 2) psi {2} + powerTrace ((5 : ℝ) / 2) psi {0, 1} +
        powerTrace ((5 : ℝ) / 2) psi {0, 2} + powerTrace ((5 : ℝ) / 2) psi {1, 2} +
        powerTrace ((5 : ℝ) / 2) psi {0, 1, 2} := by
    rw [hP3, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, hpt0]
    ring
  simp only [gce, hs2, hs3] at hle
  rw [hpt _ (by decide), hpt _ (by decide), hpt _ (by decide), hpt _ (by decide), hpt _ (by decide),
    hpt _ (by decide), hpt _ (by decide), hT0, hT1, hT2, hT01, hT02, hT12, hT012] at hle
  rw [show ({0, 1} : Finset (Fin 4)).card = 2 by decide,
    show ({0, 1, 2} : Finset (Fin 4)).card = 3 by decide] at hle
  -- clear the common denominator
  set D : ℝ := 1235706 ^ 2 * Real.sqrt 1235706 with hD
  have hDp : 0 < D := by positivity
  set X0 : ℝ := 1220000 ^ 2 * Real.sqrt 1220000 + 15706 ^ 2 * Real.sqrt 15706 with hX0
  set X2 : ℝ := 1225625 ^ 2 * su + 10081 ^ 2 * sw with hX2
  set X01 : ℝ := 2 * 10000 ^ 2 * 100 + ((1210000 ^ 2 + 82500 ^ 2) * 1219900 +
    2 * (1215706 * 82500) * 82500 + (82500 ^ 2 + 5706 ^ 2) * 15606) / c01 with hX01
  set X02 : ℝ := 5625 ^ 2 * 75 + ((1220000 ^ 2 + 110900 ^ 2) * 1220100 +
    2 * (110900 * 1230081) * 110900 + (110900 ^ 2 + 10081 ^ 2) * 10181) / c02 with hX02
  set X12 : ℝ := 1210000 ^ 2 * 1100 + 81 ^ 2 * 9 + ((10000 ^ 2 + 7500 ^ 2) * 20000 +
    2 * (7500 * 25625) * 7500 + (7500 ^ 2 + 15625 ^ 2) * 25625) / c12 with hX12
  set X012 : ℝ := 1225625 ^ 3 / su + 10081 ^ 3 / sw with hX012
  have hE : X2 + X02 + X12 + X012 - D - 2 * X0 - X01 ≤ 0 := by
    have key : X2 / D + X02 / D + X12 / D + X012 / D - 1 - 2 * (X0 / D) - X01 / D ≤ 0 := by
      norm_num at hle
      linarith
    have : (X2 + X02 + X12 + X012 - D - 2 * X0 - X01) / D =
        X2 / D + X02 / D + X12 / D + X012 / D - 1 - 2 * (X0 / D) - X01 / D := by
      field_simp
    rw [← this] at key
    exact (div_le_iff₀ hDp).1 key |>.trans (by simp)
  have hbr0a : (552268050859363/500000000000 : ℝ) ≤ Real.sqrt 1220000 ∧
      Real.sqrt 1220000 ≤ (1104536101718727/1000000000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbr0b : (125323581180877/1000000000000 : ℝ) ≤ Real.sqrt 15706 ∧
      Real.sqrt 15706 ≤ (62661790590439/500000000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbrN : (1111623137578559/1000000000000 : ℝ) ≤ Real.sqrt 1235706 ∧
      Real.sqrt 1235706 ≤ (3473822304933/3125000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbhsu : (553539745637113/500000000000 : ℝ) ≤ su ∧
      su ≤ (1107079491274227/1000000000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbhsw : (20080836635957/200000000000 : ℝ) ≤ sw ∧ sw ≤ (50202091589893/500000000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbh01 : (1111533175393339/1000000000000 : ℝ) ≤ c01 ∧
      c01 ≤ (55576658769667/50000000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbh02 : (554590163994999/500000000000 : ℝ) ≤ c02 ∧
      c02 ≤ (1109180327989999/1000000000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbh12 : (106800046816469/500000000000 : ℝ) ≤ c12 ∧
      c12 ≤ (213600093632939/1000000000000 : ℝ) := by
    constructor
    · exact (Real.le_sqrt' (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have d01 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (1210000 ^ 2 + 82500 ^ 2) * 1219900 +
    2 * (1215706 * 82500) * 82500 + (82500 ^ 2 + 5706 ^ 2) * 15606 by norm_num)
    (by norm_num : (0 : ℝ) < 1111533175393339/1000000000000) hbh01.1
  have d02 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (1220000 ^ 2 + 110900 ^ 2) * 1220100 +
    2 * (110900 * 1230081) * 110900 + (110900 ^ 2 + 10081 ^ 2) * 10181 by norm_num) hc02p hbh02.2
  have d12 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (10000 ^ 2 + 7500 ^ 2) * 20000 +
    2 * (7500 * 25625) * 7500 + (7500 ^ 2 + 15625 ^ 2) * 25625 by norm_num) hc12p hbh12.2
  have dsu := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1225625 ^ 3 by norm_num) hsup hbhsu.2
  have dsw := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 10081 ^ 3 by norm_num) hswp hbhsw.2
  linarith [hbr0a.2, hbr0b.2, hbrN.2, hbhsu.1, hbhsw.1, d01, d02, d12, dsu, dsw, hX0, hX2, hX01,
    hX02,
    hX12, hX012, hD]


end D5.S3.Quantum.Entanglement.ConcentratableEntanglementSubsystemRefutation
