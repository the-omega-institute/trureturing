/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/MatrixAverages
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual noisy-GHZ MatrixAverages in the original finite-ensemble semantics. -/


import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.Foundations
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.TwoMeanBound
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.ObservableOptimum
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.CutStates


open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

/-- An explicit finite computational-basis/GHZ ensemble for the noisy state.
This also proves density and roof nonvacuity before any optimizing ensemble
is used. -/
def noisyWeights (n d : ℕ) (p : ℝ) : Unit ⊕ Word (Fin d) n → ℝ
  | .inl _ => 1 - p
  | .inr _ => p / (wordCount n d : ℝ)

def noisyStates (n d : ℕ) : Unit ⊕ Word (Fin d) n → Word (Fin d) n → ℂ
  | .inl _ => ghz n d
  | .inr x => Pi.single x 1

private lemma noisy_ensemble_data {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ i, 0 ≤ noisyWeights n d p i) ∧
      (∑ i, noisyWeights n d p i) = 1 ∧
      (∀ i, IsUnitState (noisyStates n d i)) ∧
      noisyGhz n d p = ∑ i, noisyWeights n d p i • rankOneDensity (noisyStates n d i) := by
  classical
  have hM : (0 : ℝ) < wordCount n d := by
    unfold wordCount
    exact_mod_cast (pow_pos hd n)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    cases i <;> simp only [noisyWeights]
    · exact sub_nonneg.mpr hp1
    · exact div_nonneg hp hM.le
  · simp only [Fintype.sum_sum_type, noisyWeights, Finset.sum_const, Finset.card_univ,
      Fintype.card_unit, Fintype.card_fun, Fintype.card_fin, one_nsmul, nsmul_eq_mul]
    simp only [Nat.cast_one, one_mul]
    change 1 - p + (wordCount n d : ℝ) * (p / wordCount n d) = 1
    field_simp
    <;> ring
  · intro i
    cases i with
    | inl _ => exact ghz_unit hn hd
    | inr x => exact basis_unit x
  · simp only [Fintype.sum_sum_type, noisyWeights, noisyStates, Fintype.sum_unique,
      ← Finset.smul_sum, basis_projector_sum]
    unfold noisyGhz wordCount
    push_cast
    exact add_comm _ _

def noisyDensity {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n) :=
  ensembleDensity (noisyWeights n d p) (noisyStates n d)
    (noisy_ensemble_data hn hd hp hp1).1
    (noisy_ensemble_data hn hd hp hp1).2.1
    (noisy_ensemble_data hn hd hp hp1).2.2.1

lemma noisyDensity_matrix {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    CStarMatrix.ofMatrix.symm (noisyDensity hn hd p hp hp1).1 = noisyGhz n d p := by
  exact (noisy_ensemble_data hn hd hp hp1).2.2.2.symm

private def pushMatrix {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) : Matrix κ κ ℂ := by
  classical
  exact fun x y => if hx : ∃ i, e i = x then
    if hy : ∃ j, e j = y then m hx.choose hy.choose else 0 else 0

private lemma pushMatrix_apply {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) (i j : ι) :
    pushMatrix e m (e i) (e j) = m i j := by
  classical
  have hi : ∃ k, e k = e i := ⟨i,rfl⟩
  have hj : ∃ k, e k = e j := ⟨j,rfl⟩
  have hi' : hi.choose = i := e.injective hi.choose_spec
  have hj' : hj.choose = j := e.injective hj.choose_spec
  simp only [pushMatrix, dif_pos hi, dif_pos hj, hi', hj']

private lemma pushMatrix_off_left {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) (x y : κ)
    (hx : ¬ ∃ i, e i = x) : pushMatrix e m x y = 0 := by
  classical
  simp [pushMatrix,hx]

private lemma pushMatrix_off_right {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) (x y : κ)
    (hy : ¬ ∃ j, e j = y) : pushMatrix e m x y = 0 := by
  classical
  simp [pushMatrix,hy]

private lemma pushMatrix_add {ι κ : Type*} (e : ι ↪ κ) (a b : Matrix ι ι ℂ) :
    pushMatrix e (a+b) = pushMatrix e a + pushMatrix e b := by
  classical
  ext x y
  simp only [pushMatrix, Matrix.add_apply]
  split_ifs <;> simp_all [pushMatrix]

private lemma pushMatrix_smul {ι κ : Type*} (e : ι ↪ κ) (r : ℝ) (m : Matrix ι ι ℂ) :
    pushMatrix e (r • m) = r • pushMatrix e m := by
  classical
  ext x y
  simp only [pushMatrix, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  split_ifs <;> simp_all [pushMatrix]

private lemma pushMatrix_sum {ι κ σ : Type*} [Fintype σ] (e : ι ↪ κ)
    (m : σ → Matrix ι ι ℂ) : pushMatrix e (∑ t, m t) = ∑ t, pushMatrix e (m t) := by
  classical
  ext x y
  by_cases hx : ∃ i, e i = x
  · obtain ⟨i,rfl⟩ := hx
    by_cases hy : ∃ j, e j = y
    · obtain ⟨j,rfl⟩ := hy
      simp only [Matrix.sum_apply, pushMatrix_apply]
    · simp only [Matrix.sum_apply, pushMatrix_off_right e _ _ _ hy, Finset.sum_const_zero]
  · simp only [Matrix.sum_apply, pushMatrix_off_left e _ _ _ hx, Finset.sum_const_zero]

private lemma pushMatrix_projector {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) :
    pushMatrix e (rankOneDensity c) = rankOneDensity (pushVector e c) := by
  classical
  ext x y
  by_cases hx : ∃ i, e i = x
  · obtain ⟨i,rfl⟩ := hx
    by_cases hy : ∃ j, e j = y
    · obtain ⟨j,rfl⟩ := hy
      simp only [pushMatrix_apply, rankOneDensity, vecMulVec_apply, Pi.star_apply, pushVector_apply]
    · rw [pushMatrix_off_right e _ _ _ hy]
      simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, pushVector_off e c y hy]
  · rw [pushMatrix_off_left e _ _ _ hx]
    simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, pushVector_off e c x hx]

private def phaseCutCoefficient {d : ℕ} (α β : ℝ) (θ : Fin d → ZMod 3) (ij : Fin d × Fin d) : ℂ :=
  if ij.1 = ij.2 then ((β + (α - β) / d : ℝ) : ℂ)
  else (((α - β) / d : ℝ) : ℂ) * phaseCharacter (pairCoefficient ij.1 ij.2) θ

private lemma phaseCutCoefficient_eq {d : ℕ} (hd : 0 < d) (α β : ℝ)
    (θ : Fin d → ZMod 3) (ij : Fin d × Fin d) :
    phaseCutCoefficient α β θ ij =
      (if ij.1 = ij.2 then (β : ℂ) else 0) +
        ((α - β : ℝ) : ℂ) * phaseVector θ ij.1 * star (phaseVector θ ij.2) := by
  rw [mul_assoc,phaseVector_pair hd]
  by_cases hij : ij.1 = ij.2
  · have hz : pairCoefficient ij.1 ij.2 = 0 := (pairCoefficient_eq_zero_iff _ _).mpr hij
    simp [phaseCutCoefficient,hij,pairCoefficient,phaseCharacter]
    push_cast
    ring
  · simp only [phaseCutCoefficient,hij,ite_false,zero_add]
    push_cast
    ring

private lemma phase_coefficient_gram {d : ℕ} (α β : ℝ) (ij kl : Fin d × Fin d) :
    (∑ θ : Fin d → ZMod 3, phaseCutCoefficient α β θ ij *
      star (phaseCutCoefficient α β θ kl)) =
      if ij.1 = ij.2 ∧ kl.1 = kl.2 then
        ((3 ^ d : ℕ) : ℂ) * (((β + (α - β) / d)^2 : ℝ) : ℂ)
      else if ij = kl then ((3 ^ d : ℕ) : ℂ) * ((((α - β) / d)^2 : ℝ) : ℂ) else 0 := by
  classical
  let γ : ℂ := ((β + (α - β) / d : ℝ) : ℂ)
  let δ : ℂ := (((α - β) / d : ℝ) : ℂ)
  have hγ : star γ = γ := by simp [γ]
  have hδ : star δ = δ := by simp [δ]
  have hstar (r : ℝ) (z : ℂ) : star ((r : ℂ) * z) = (r : ℂ) * star z := by
    simp only [star_mul]
    simp
    <;> ring
  by_cases hij : ij.1 = ij.2
  · by_cases hkl : kl.1 = kl.2
    · simp [phaseCutCoefficient,hij,hkl,pow_two]
    · have hne : ij ≠ kl := by intro h; exact hkl (h ▸ hij)
      simp only [phaseCutCoefficient,hij,hkl,ite_true,ite_false,true_and,and_false,
        if_neg hne,hstar]
      change (∑ θ, γ * (δ * star (phaseCharacter (pairCoefficient kl.1 kl.2) θ))) = 0
      simp only [← mul_assoc, ← Finset.mul_sum, ← star_sum, pair_phase_sum, if_neg hkl,
        Nat.cast_zero, star_zero, mul_zero]
  · by_cases hkl : kl.1 = kl.2
    · have hne : ij ≠ kl := by intro h; exact hij (h.symm ▸ hkl)
      simp only [phaseCutCoefficient,hij,hkl,ite_true,ite_false,false_and,
        if_neg hne]
      change (∑ θ, δ * phaseCharacter (pairCoefficient ij.1 ij.2) θ * star γ) = 0
      rw [hγ, ← Finset.sum_mul, ← Finset.mul_sum, pair_phase_sum, if_neg hij]
      simp
    · have he : ((ij.1 = kl.1 ∧ ij.2 = kl.2) ↔ ij = kl) := Prod.ext_iff.symm
      simp only [phaseCutCoefficient,hij,hkl,ite_false,false_and,hstar]
      change (∑ θ, (δ * phaseCharacter (pairCoefficient ij.1 ij.2) θ) *
        (δ * star (phaseCharacter (pairCoefficient kl.1 kl.2) θ))) = _
      have hterm (θ : Fin d → ZMod 3) :
          (δ * phaseCharacter (pairCoefficient ij.1 ij.2) θ) *
            (δ * star (phaseCharacter (pairCoefficient kl.1 kl.2) θ)) =
          δ^2 * (phaseCharacter (pairCoefficient ij.1 ij.2) θ *
            star (phaseCharacter (pairCoefficient kl.1 kl.2) θ)) := by ring
      simp only [hterm, ← Finset.mul_sum, pair_cross_phase_sum, hij, false_and, false_or, he]
      by_cases h : ij = kl <;> simp [h,δ,pow_two,mul_comm]

private lemma basis_coefficient_gram {d : ℕ} (α β : ℝ) (i k : Fin d) :
    (∑ j : Fin d, (if i = j then (α : ℂ) else β) *
      star (if k = j then (α : ℂ) else β)) =
      (((d : ℝ) * β^2 + 2 * β * (α - β) +
        (if i = k then (α - β)^2 else 0) : ℝ) : ℂ) := by
  classical
  have he (i j : Fin d) : (if i = j then (α : ℂ) else β) =
      (β : ℂ) + (if i = j then ((α - β : ℝ) : ℂ) else 0) := by
    by_cases h : i = j <;> simp [h] <;> push_cast <;> ring
  have ht (j : Fin d) :
      (if i = j then (α : ℂ) else β) * star (if k = j then (α : ℂ) else β) =
      (β^2 : ℝ) + (if i = j then ((β * (α - β) : ℝ) : ℂ) else 0) +
        (if k = j then ((β * (α - β) : ℝ) : ℂ) else 0) +
        (if i = j ∧ k = j then (((α - β)^2 : ℝ) : ℂ) else 0) := by
    by_cases hi : i = j <;> by_cases hk : k = j <;> simp [hi,hk] <;> push_cast <;> ring
  simp only [ht, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hlast : (∑ j : Fin d, if i = j ∧ k = j then (((α - β)^2 : ℝ) : ℂ) else 0) =
      if i = k then (((α - β)^2 : ℝ) : ℂ) else 0 := by
    by_cases hik : i = k
    · subst k
      simp
    · rw [if_neg hik]
      apply Finset.sum_eq_zero
      intro j hj
      have hh : ¬ (i = j ∧ k = j) := by rintro ⟨rfl,rfl⟩; exact hik rfl
      simp [hh,hik]
  rw [hlast]
  split_ifs <;> push_cast <;> ring

/-- The piecewise optimum is exactly the source's truncated radical on the
entire closed triangle, including the zero and fidelity boundaries. -/
theorem twoMeanOptimum_max {d : ℕ} (hd : 2 ≤ d) {f y : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) :
    twoMeanOptimum d f y =
      (max (Real.sqrt ((d - 1 : ℝ) * f) - Real.sqrt (y - f)) 0)^2 / d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hA : 0 ≤ (d - 1 : ℝ) * f := mul_nonneg (by linarith) hf
  have hB : 0 ≤ y - f := sub_nonneg.mpr hfy
  by_cases h : (d : ℝ) * f ≤ y
  · have hr : Real.sqrt ((d - 1 : ℝ) * f) ≤ Real.sqrt (y - f) :=
      Real.sqrt_le_sqrt (by nlinarith)
    simp [twoMeanOptimum,h,max_eq_right (sub_nonpos.mpr hr)]
  · have hr : Real.sqrt (y - f) ≤ Real.sqrt ((d - 1 : ℝ) * f) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [twoMeanOptimum,if_neg h,max_eq_left (sub_nonneg.mpr hr)]
    unfold twoMeanValue
    rw [Real.sqrt_mul hA]
    have hS := Real.sq_sqrt hA
    have hT := Real.sq_sqrt hB
    congr 1
    nlinarith

/-- The diagonal projector onto the constant computational words. -/
def constantProjector (n d : ℕ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ := by
  classical
  exact diagonal (fun x => if ∃ j : Fin d, ∀ k, x k = j then 1 else 0)

/-- The off-constant sector belonging to one actual bipartition. -/
def cutOffProjector {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ := by
  classical
  exact pushMatrix (cutEmbedding a ha hc) (diagonal (fun ij => if ij.1 ≠ ij.2 then 1 else 0))

private lemma cutEmbedding_diagonal {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (j : Fin d) : cutEmbedding a ha hc (j,j) = (fun _ => j) := by
  funext k
  simp [cutEmbedding,Finset.piecewise]

private lemma cutEmbedding_isConstant {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (ij : Fin d × Fin d) :
    (∃ j : Fin d, ∀ k, cutEmbedding a ha hc ij k = j) ↔ ij.1 = ij.2 := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨k,hk⟩ := ha
    obtain ⟨l,hl⟩ := hc
    have h1 := hj k
    have h2 := hj l
    simp [cutEmbedding,hk] at h1
    simp [cutEmbedding,Finset.mem_compl.mp hl] at h2
    exact h1.trans h2.symm
  · intro h
    refine ⟨ij.1,?_⟩
    intro k
    simp [cutEmbedding,Finset.piecewise,h]

private lemma ghz_cutEmbedding {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (ij : Fin d × Fin d) :
    ghz n d (cutEmbedding a ha hc ij) =
      if ij.1 = ij.2 then (Real.sqrt d : ℂ)⁻¹ else 0 := by
  simp only [ghz,cutEmbedding_isConstant]

private lemma ghz_off_cutEmbedding {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (x : Word (Fin d) n) (hx : ¬ ∃ ij, cutEmbedding a ha hc ij = x) :
    ghz n d x = 0 := by
  have h : ¬ ∃ j : Fin d, ∀ k, x k = j := by
    rintro ⟨j,hj⟩
    exact hx ⟨(j,j),(cutEmbedding_diagonal a ha hc j).trans (funext hj).symm⟩
  simp [ghz,h]

private lemma cut_coherent_matrix {n d : ℕ} (hd : 0 < d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    pushMatrix (cutEmbedding a ha hc)
      (Matrix.of fun ij kl => if ij.1 = ij.2 ∧ kl.1 = kl.2 then 1 else 0) =
      (d : ℝ) • rankOneDensity (ghz n d) := by
  classical
  have hroot : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hroot0 : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < d by exact_mod_cast hd)).ne'
  have hscalar : (d : ℂ) * (Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹ = 1 := by
    rw [← hroot]
    field_simp
  ext x y
  by_cases hx : ∃ ij, cutEmbedding a ha hc ij = x
  · obtain ⟨ij,rfl⟩ := hx
    by_cases hy : ∃ kl, cutEmbedding a ha hc kl = y
    · obtain ⟨kl,rfl⟩ := hy
      rw [pushMatrix_apply]
      simp only [Matrix.smul_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz_cutEmbedding,
        Complex.real_smul,Matrix.of_apply]
      by_cases hij : ij.1 = ij.2 <;> by_cases hkl : kl.1 = kl.2 <;>
        simp [hij,hkl,← mul_assoc,hscalar]
    · rw [pushMatrix_off_right _ _ _ _ hy]
      simp [rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz_off_cutEmbedding a ha hc y hy]
  · rw [pushMatrix_off_left _ _ _ _ hx]
    simp [rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz_off_cutEmbedding a ha hc x hx]

private lemma phase_raw_matrix {n d : ℕ} (hd : 0 < d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) (α β : ℝ) :
    (∑ θ : Fin d → ZMod 3, rankOneDensity (cutState a ha hc α β (phaseVector θ))) =
      ((3 ^ d : ℕ) * (β + (α - β) / d)^2 * d : ℝ) • rankOneDensity (ghz n d) +
        ((3 ^ d : ℕ) * ((α - β) / d)^2 : ℝ) • cutOffProjector a ha hc := by
  classical
  have he (θ : Fin d → ZMod 3) :
      cutState a ha hc α β (phaseVector θ) =
        pushVector (cutEmbedding a ha hc) (phaseCutCoefficient α β θ) := by
    unfold cutState
    congr 1
    funext ij
    exact (phaseCutCoefficient_eq hd α β θ ij).symm
  simp_rw [he, ← pushMatrix_projector]
  rw [← pushMatrix_sum]
  have hm : (∑ θ : Fin d → ZMod 3, rankOneDensity (phaseCutCoefficient α β θ)) =
      ((3 ^ d : ℕ) * (β + (α - β) / d)^2 : ℝ) •
        (Matrix.of fun ij kl => if ij.1 = ij.2 ∧ kl.1 = kl.2 then (1 : ℂ) else 0) +
      ((3 ^ d : ℕ) * ((α - β) / d)^2 : ℝ) •
        diagonal (fun ij : Fin d × Fin d => if ij.1 ≠ ij.2 then (1 : ℂ) else 0) := by
    ext ij kl
    simp only [Matrix.sum_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,phase_coefficient_gram,
      Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,diagonal_apply,Matrix.of_apply]
    by_cases hij : ij.1 = ij.2 <;> by_cases hkl : kl.1 = kl.2 <;>
      by_cases heq : ij = kl <;> simp_all <;> push_cast <;> ring
  rw [hm,pushMatrix_add,pushMatrix_smul,pushMatrix_smul,cut_coherent_matrix hd a ha hc]
  rw [smul_smul]
  rfl

private lemma ghz_constant_matrix {n d : ℕ} (hd : 0 < d) (i j : Fin d) :
    rankOneDensity (ghz n d) (fun _ => i) (fun _ => j) = (1 / (d : ℂ)) := by
  have hroot : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hinv : (Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹ = (d : ℂ)⁻¹ := by
    rw [← mul_inv,← pow_two,hroot]
  have hi : ∃ a : Fin d, ∀ _k : Fin n, i = a := ⟨i,fun _ => rfl⟩
  have hj : ∃ a : Fin d, ∀ _k : Fin n, j = a := ⟨j,fun _ => rfl⟩
  simpa [rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz,hi,hj] using hinv

private lemma constantProjector_constant {n d : ℕ} (hn : 0 < n) (i j : Fin d) :
    constantProjector n d (fun _ => i) (fun _ => j) = if i = j then 1 else 0 := by
  classical
  have he : ((fun _ : Fin n => i) = fun _ : Fin n => j) ↔ i = j :=
    ⟨fun h => constant_word_injective hn h,fun h => h ▸ rfl⟩
  have hi : ∃ a : Fin d, ∀ _k : Fin n, i = a := ⟨i,fun _ => rfl⟩
  simp [constantProjector,diagonal_apply,he,hi]

private lemma constantProjector_off {n d : ℕ} (x y : Word (Fin d) n)
    (hx : ¬ ∃ j : Fin d, ∀ k, x k = j) : constantProjector n d x y = 0 := by
  classical
  simp [constantProjector,diagonal_apply,hx]

private lemma basis_raw_matrix {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (α β : ℝ) :
    (∑ j : Fin d, rankOneDensity (chiVector hn j α β)) =
      ((d : ℝ)*((d : ℝ)*β^2+2*β*(α-β))) • rankOneDensity (ghz n d) +
        (α-β)^2 • constantProjector n d := by
  classical
  have hgoff (x : Word (Fin d) n) (hx : ¬ ∃ j : Fin d, ∀ k, x k = j) : ghz n d x = 0 := by
    simp [ghz,hx]
  have hcoff (j : Fin d) (x : Word (Fin d) n) (hx : ¬ ∃ j : Fin d, ∀ k, x k = j) :
      chiVector hn j α β x = 0 := constantVector_off hn _ _ hx
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  ext x y
  by_cases hx : ∃ i : Fin d, ∀ k, x k = i
  · obtain ⟨i,hi⟩ := hx
    have hxi := funext hi
    subst x
    by_cases hy : ∃ k : Fin d, ∀ l, y l = k
    · obtain ⟨k,hk⟩ := hy
      have hyk := funext hk
      subst y
      simp only [Matrix.sum_apply,chiVector,constantVector_apply,rankOneDensity,vecMulVec_apply,
        Pi.star_apply]
      rw [basis_coefficient_gram]
      change _ = (((d : ℝ)*((d : ℝ)*β^2+2*β*(α-β))) • rankOneDensity (ghz n d))
        (fun _ => i) (fun _ => k) + ((α-β)^2 • constantProjector n d) (fun _ => i) (fun _ => k)
      rw [Matrix.smul_apply,Matrix.smul_apply,ghz_constant_matrix hd,constantProjector_constant hn]
      split_ifs <;> simp only [Complex.real_smul,mul_one,mul_zero,add_zero] <;>
        push_cast <;> field_simp <;> ring
    · have hne : (fun _ : Fin n => i) ≠ y := by
        intro h
        exact hy ⟨i,fun k => (congrFun h k).symm⟩
      simp [Matrix.sum_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,hcoff _ y hy,
        hgoff y hy,constantProjector,diagonal_apply,hne]
  · simp [Matrix.sum_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,hcoff _ x hx,
      hgoff x hx,constantProjector_off x y hx]

private lemma pushVector_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (i : ι) : pushVector e (Pi.single i (1 : ℂ)) = Pi.single (e i) 1 := by
  ext x
  by_cases hx : ∃ j, e j = x
  · obtain ⟨j,rfl⟩ := hx
    rw [pushVector_apply]
    simp [Pi.single_apply,e.injective.eq_iff]
  · rw [pushVector_off e _ x hx]
    have hi : e i ≠ x := fun h => hx ⟨i,h⟩
    simp [Pi.single_apply,hi,Ne.symm hi]

lemma diagonal_projector_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop)
    [DecidablePred p] :
    diagonal (fun i => if p i then (1 : ℂ) else 0) =
      ∑ i : ι, if p i then rankOneDensity (Pi.single i (1 : ℂ)) else 0 := by
  rw [← Matrix.sum_single_eq_diagonal]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hp : p c
  · simp only [hp,ite_true]
    ext i j
    by_cases hi : i = c <;> by_cases hj : j = c <;>
      simp [Matrix.single,rankOneDensity,vecMulVec_apply,Pi.star_apply,
        Pi.single_apply,hi,hj,eq_comm] <;> aesop
  · simp [hp]

private lemma pushMatrix_diagonal_projector {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq κ] (e : ι ↪ κ) (p : ι → Prop) [DecidablePred p] :
    pushMatrix e (diagonal (fun i => if p i then (1 : ℂ) else 0)) =
      ∑ i : ι, if p i then rankOneDensity (Pi.single (e i) (1 : ℂ)) else 0 := by
  rw [diagonal_projector_sum,pushMatrix_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p i
  · simp only [h,ite_true,pushMatrix_projector,pushVector_single]
  · simp only [h,ite_false]
    ext x y
    simp [pushMatrix]

private lemma cutOffProjector_basis {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) :
    cutOffProjector a ha hc =
      ∑ ij : OffPair d, rankOneDensity (Pi.single (cutEmbedding a ha hc ij.1) (1 : ℂ)) := by
  classical
  rw [cutOffProjector,pushMatrix_diagonal_projector]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

private lemma constantProjector_basis {n d : ℕ} (hn : 0 < n) :
    constantProjector n d = ∑ j : Fin d, rankOneDensity (Pi.single (fun _ : Fin n => j) (1 : ℂ)) := by
  classical
  have he : (∑ x : Word (Fin d) n,
      if ∃ j : Fin d, ∀ k, x k = j then rankOneDensity (Pi.single x (1 : ℂ)) else 0) =
      ∑ j : Fin d, rankOneDensity (Pi.single (fun _ : Fin n => j) (1 : ℂ)) := by
    rw [sum_supported_constants hn _ (by intro x hx; simp [hx])]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos ⟨j,fun _ => rfl⟩]
  simpa only [constantProjector,diagonal_projector_sum] using he

private lemma sourceSector_eq {n d : ℕ} (hn : 0 < n) (s : SourceCut n hn) (ij : OffPair d) :
    cutEmbedding s.1ᶜ (sourceCut_complement hn s)
      (by simpa only [compl_compl] using sourceCut_nonempty hn s) ij.1 =
      sourceCutWord hn s ij := by
  classical
  funext k
  by_cases hk : k ∈ s.1 <;> simp [cutEmbedding,sourceCutWord,Finset.piecewise,hk]

/-- The source's full disjoint projector decomposition, as actual complex
matrices rather than a scalar rank count. -/
theorem support_projector_decomposition {n d : ℕ} (hn : 0 < n) :
    supportProjector n d = constantProjector n d +
      ∑ s : SourceCut n hn, cutOffProjector s.1ᶜ (sourceCut_complement hn s)
        (by simpa only [compl_compl] using sourceCut_nonempty hn s) := by
  classical
  have hfull : supportProjector n d =
      ∑ z : SupportIndex n d hn, rankOneDensity (Pi.single (supportIndexWord hn z) (1 : ℂ)) := by
    rw [supportProjector,diagonal_projector_sum]
    rw [sum_on_embedding ⟨supportIndexWord hn,supportIndexWord_injective hn⟩ _ (by
      intro x hx
      have hnot : ¬ (Finset.univ.image x).card ≤ 2 := by
        intro hs
        exact hx (supportIndexWord_surjective hn x hs)
      simp [hnot])]
    apply Finset.sum_congr rfl
    intro z hz
    simp [supportIndexWord_supported hn z]
  rw [hfull]
  change (∑ z : Fin d ⊕ (SourceCut n hn × OffPair d), _) = _
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,constantProjector_basis hn]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [cutOffProjector_basis]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [sourceSector_eq]
  rfl

private lemma optimal_matrix_parameters {d : ℕ} (hd : 2 ≤ d) {F : ℝ}
    (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    (optimalAlpha d F-optimalBeta d F)^2/d = (1-F)/(d-1 : ℝ) ∧
      (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2 = F ∧
      (d : ℝ)*(optimalBeta d F)^2+2*optimalBeta d F*(optimalAlpha d F-optimalBeta d F) =
        F-(1-F)/(d-1 : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d-1 : ℝ) ≠ 0 := by linarith
  obtain ⟨_,_,hnorm,hmean,_⟩ := optimal_amplitudes hd hF hF1
  have hm : (optimalAlpha d F+(d-1 : ℝ)*optimalBeta d F)^2 = F*d :=
    (div_eq_iff hd0).mp hmean
  have ht : (d-1 : ℝ)*(optimalAlpha d F-optimalBeta d F)^2 = (d : ℝ)*(1-F) := by
    linear_combination (d : ℝ)*hnorm-hm
  have ht' : (optimalAlpha d F-optimalBeta d F)^2/d = (1-F)/(d-1 : ℝ) := by
    field_simp
    linear_combination ht
  have hg : (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2 = F := by
    field_simp
    linear_combination hm
  refine ⟨ht',hg,?_⟩
  calc
    _ = (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2-
        (optimalAlpha d F-optimalBeta d F)^2/d := by field_simp <;> ring
    _ = _ := by rw [hg,ht']

/-- The actual finite d-component basis average from the source. -/
def basisAverage {n d : ℕ} (hn : 0 < n) (F : ℝ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  (1/(d : ℝ)) • ∑ j : Fin d, rankOneDensity (chiVector hn j (optimalAlpha d F) (optimalBeta d F))

/-- The actual finite 3^d-component independent-phase average from one cut. -/
def phaseAverage {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (F : ℝ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  (1/((3^d : ℕ) : ℝ)) • ∑ θ : Fin d → ZMod 3,
    rankOneDensity (cutState a ha hc (optimalAlpha d F) (optimalBeta d F) (phaseVector θ))

/-- The full actual basis-average matrix J_F. -/
theorem basis_average_matrix {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d)
    {F : ℝ} (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    basisAverage hn F = F • rankOneDensity (ghz n d) +
      ((1-F)/(d-1 : ℝ)) • (constantProjector n d-rankOneDensity (ghz n d)) := by
  obtain ⟨ht,hg,hb⟩ := optimal_matrix_parameters (by omega : 2 ≤ d) hF hF1
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [basisAverage,basis_raw_matrix hn (by omega : 0 < d),smul_add,smul_smul,smul_smul]
  have h1 : (1/(d : ℝ))*((d : ℝ)*((d : ℝ)*(optimalBeta d F)^2+
      2*optimalBeta d F*(optimalAlpha d F-optimalBeta d F))) = F-(1-F)/(d-1 : ℝ) := by
    calc
      _ = (d : ℝ)*(optimalBeta d F)^2+2*optimalBeta d F*(optimalAlpha d F-optimalBeta d F) := by
        field_simp
      _ = _ := hb
  have h2 : (1/(d : ℝ))*(optimalAlpha d F-optimalBeta d F)^2 = (1-F)/(d-1 : ℝ) := by
    simpa [div_eq_mul_inv,mul_comm] using ht
  rw [h1,h2,sub_smul,smul_sub]
  abel

/-- The full actual phase-average matrix H_{A,F}. Every off-diagonal entry
is controlled by the independent-coordinate Gram identity in arbitrary d. -/
theorem phase_average_matrix {n d : ℕ} (hd : 3 ≤ d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    {F : ℝ} (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    phaseAverage a ha hc F = F • rankOneDensity (ghz n d) +
      ((1-F)/((d : ℝ)*(d-1 : ℝ))) • cutOffProjector a ha hc := by
  obtain ⟨ht,hg,_⟩ := optimal_matrix_parameters (by omega : 2 ≤ d) hF hF1
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hN : ((3^d : ℕ) : ℝ) ≠ 0 := by positivity
  rw [phaseAverage,phase_raw_matrix (by omega : 0 < d) a ha hc,smul_add,smul_smul,smul_smul]
  have h1 : (1/((3^d : ℕ) : ℝ))*(((3^d : ℕ) : ℝ)*
      (optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2*d) = F := by
    calc
      _ = (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2 := by
        field_simp
        <;> ring
      _ = _ := hg
  have h2 : (1/((3^d : ℕ) : ℝ))*(((3^d : ℕ) : ℝ)*
      ((optimalAlpha d F-optimalBeta d F)/d)^2) = (1-F)/((d : ℝ)*(d-1 : ℝ)) := by
    calc
      _ = ((optimalAlpha d F-optimalBeta d F)^2/d)/d := by field_simp <;> ring
      _ = _ := by rw [ht]; field_simp <;> ring
  rw [h1,h2]

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
