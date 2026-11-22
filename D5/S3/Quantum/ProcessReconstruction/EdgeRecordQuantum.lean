/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordQuantum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proper paired Choi marginals are maximally mixed for the edge-record channels. -/

import D5.S3.Quantum.ProcessReconstruction.EdgeRecordEntropy
import D5.S3.Quantum.ProcessReconstruction.LiuWildChoiObstruction
import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
import D5.S3.Quantum.Information.InputInformationBalance

/-! Proper paired Choi marginals are maximally mixed for the edge-record channels. -/

namespace D5.S3.Quantum.EnvironmentRecords.EdgePath

open Matrix UnitaryReconstruction
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FinitePreparationChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open UnitaryReconstruction.LiuWildChoiObstruction (normalizedChoi normalizedChoi_entry pairMatrix)

noncomputable section

variable {n : ℕ}

private def diagonalState {A : Type*} [Fintype A] [DecidableEq A] (p : A → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : DensityState A :=
  ⟨CStarMatrix.ofMatrix (diagonal (fun i => (p i : ℂ))), by
    apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply (Matrix.posSemidef_diagonal_iff.mpr _).nonneg
    intro i
    exact_mod_cast hp i, by
    change (diagonal (fun i => (p i : ℂ))).trace = 1
    rw [Matrix.trace_diagonal]
    exact_mod_cast hs⟩

def prepared (b : Bit) (x : Word (n + 1)) : DensityState (Word (n + 1)) :=
  diagonalState (kernel b x) (kernel_nonneg b x) (kernel_sum b x)

def channel (b : Bit) : QuantumChannel (Word (n + 1)) (Word (n + 1)) :=
  (finite_preparation_quantum_channel (prepared (n := n) b)).choose

abbrev Action {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (C : QuantumChannel A B) (X : Matrix A A ℂ) : Matrix B B ℂ :=
  CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

theorem channel_action (b : Bit) (X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ) :
    Action (channel b) X =
      diagonal (fun y => ∑ x, X x x * (kernel b x y : ℂ)) := by
  have h := (finite_preparation_quantum_channel (prepared (n := n) b)).choose_spec X
  change Action (channel b) X = _ at h
  rw [h]
  ext y z
  by_cases hyz : y = z
  · subst z
    simp [prepared, diagonalState, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [prepared, diagonalState, Matrix.sum_apply, Matrix.smul_apply, hyz]

theorem choi_diagonal (b : Bit) :
    pairMatrix (normalizedChoi (channel (n := n) b)) =
      diagonal (fun p => (pairedWeight b p : ℂ)) := by
  ext ⟨i,y⟩ ⟨j,z⟩
  rw [normalizedChoi_entry]
  change _ * Action (channel b) (Matrix.single i j 1) y z = _
  rw [channel_action]
  have hc : (Fintype.card (Word (n + 1)) : ℂ) = (dimension n : ℂ) := by
    exact_mod_cast card_sites n
  rw [hc]
  by_cases hij : i = j <;> by_cases hyz : y = z
  · subst j
    subst z
    simp [Matrix.single_apply, pairedWeight, div_eq_mul_inv, mul_comm,
      eq_comm (a := i)]
  · simp [hyz]
  · subst z
    have hdiag (x : Word (n + 1)) : (Matrix.single i j (1 : ℂ)) x x = 0 := by
      have hn : ¬ (i = x ∧ j = x) := fun h => hij (h.1.trans h.2.symm)
      simp only [Matrix.single_apply, ite_eq_right hn]
    simp [hij, hdiag]
  · simp [hyz]

abbrev Discarded {n : ℕ} (s : Mask n) := {j : Fin (n + 1) // j ∉ s} → Bit

def splitWord (s : Mask n) : Word (n + 1) ≃ Discarded s × Kept s :=
  (Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ => Bit)).trans (Equiv.prodComm _ _)

def splitPair (s : Mask n) :
    Word (n + 1) × Word (n + 1) ≃
      (Discarded s × Discarded s) × (Kept s × Kept s) :=
  ((splitWord s).prodCongr (splitWord s)).trans (Equiv.prodProdProdComm _ _ _ _)

def pairedMarginal (s : Mask n) (ρ : DensityState (Word (n + 1) × Word (n + 1))) :
    DensityState (Kept s × Kept s) :=
  marginalLeft (relabelState (splitPair s).symm ρ)

private theorem sum_completions (s : Mask n) (v : Kept s) (f : Word (n + 1) → ℝ) :
    (∑ z : Discarded s, f ((splitWord s).symm (z,v))) =
      ∑ y : Word (n + 1), (if (fun i : s => y i.val) = v then f y else 0) := by
  have h := Equiv.sum_comp (splitWord s).symm
    (fun y => if (splitWord s y).2 = v then f y else 0)
  simp only [Equiv.apply_symm_apply] at h
  rw [Fintype.sum_prod_type_right] at h
  change (∑ j : Kept s, ∑ z : Discarded s,
    if j = v then f ((splitWord s).symm (z,j)) else 0) = _ at h
  simp_rw [← Finset.ite_sum_zero] at h
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)] at h
  exact h

theorem kernel_completions (b : Bit) (x : Word (n + 1)) (s : Mask n)
    (hs : s ≠ Finset.univ) (v : Kept s) :
    ∑ z : Discarded s, kernel b x ((splitWord s).symm (z,v)) =
      (Fintype.card (Kept s) : ℝ)⁻¹ := by
  rw [sum_completions, kernel_marginal b x s v hs]

theorem proper_output_replacer (b : Bit) (s : Mask n) (hs : s ≠ Finset.univ)
    (X : Matrix (Word (n + 1)) (Word (n + 1)) ℂ) :
    Action ((discard (splitWord s)).comp (channel b)) X =
      (X.trace / Fintype.card (Kept s)) • (1 : Matrix (Kept s) (Kept s) ℂ) := by
  ext y z
  change Action (discard (splitWord s)) (Action (channel b) X) y z = _
  have h : Action (discard (splitWord s)) (Action (channel b) X) =
      _ := discard_apply (splitWord s) (Action (channel b) X)
  rw [h, channel_action]
  change (∑ w : Discarded s,
    diagonal (fun v => ∑ x, X x x * (kernel b x v : ℂ))
      ((splitWord s).symm (w,y)) ((splitWord s).symm (w,z))) = _
  by_cases hyz : y = z
  · subst z
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← Complex.ofReal_sum, kernel_completions b _ s hs,
      Complex.ofReal_inv, Complex.ofReal_natCast, ← Finset.sum_mul, div_eq_mul_inv]
    rfl
  · have hne (w : Discarded s) :
        (splitWord s).symm (w,y) ≠ (splitWord s).symm (w,z) :=
      fun he => hyz (congrArg Prod.snd ((splitWord s).symm.injective he))
    simp [hne, Matrix.one_apply_ne hyz]

private theorem discarded_card_ratio (s : Mask n) :
    (Fintype.card (Discarded s) : ℝ) / dimension n = (Fintype.card (Kept s) : ℝ)⁻¹ := by
  rw [← card_sites, Fintype.card_congr (splitWord s), Fintype.card_prod, Nat.cast_mul]
  have h : (Fintype.card (Discarded s) : ℝ) ≠ 0 := by positivity
  field_simp

theorem proper_paired_mixed (b : Bit) (s : Mask n) (hs : s ≠ Finset.univ) :
    pairMatrix (pairedMarginal s (normalizedChoi (channel b))) =
      diagonal (fun _ : Kept s × Kept s => ((Fintype.card (Kept s × Kept s) : ℝ)⁻¹ : ℂ)) := by
  ext p q
  change (∑ w : Discarded s × Discarded s,
    pairMatrix (normalizedChoi (channel b)) ((splitPair s).symm (w,p))
      ((splitPair s).symm (w,q))) = _
  rw [choi_diagonal]
  by_cases hpq : p = q
  · subst q
    simp only [Matrix.diagonal_apply_eq, ← Complex.ofReal_sum]
    rw [← Complex.ofReal_inv, Complex.ofReal_inj, Fintype.sum_prod_type]
    change (∑ a : Discarded s, ∑ c : Discarded s,
      kernel b ((splitWord s).symm (a,p.1)) ((splitWord s).symm (c,p.2)) / dimension n) = _
    simp_rw [← Finset.sum_div, kernel_completions b _ s hs, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, mul_inv]
    rw [mul_comm (Fintype.card (Discarded s) : ℝ), mul_div_assoc, discarded_card_ratio]
  · have hne (w : Discarded s × Discarded s) :
        (splitPair s).symm (w,p) ≠ (splitPair s).symm (w,q) :=
      fun he => hpq (congrArg Prod.snd ((splitPair s).symm.injective he))
    simp [hne, hpq]

private theorem entropy_of_diagonal {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : DensityState A) (w : A → ℝ) (h : pairMatrix ρ = diagonal (fun p => (w p : ℂ))) :
    vonNeumannEntropy ρ = ∑ p, Real.negMulLog (w p) := by
  open D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation in
  rw [← entropy_diagonal, ← h, entropy, dite_eq_left (density_posSemidef ρ).isHermitian]
  exact D5.S3.Quantum.Information.InputInformationBalance.entropy_eq_sum ρ

theorem choi_entropy (b : Bit) :
    vonNeumannEntropy (normalizedChoi (channel (n := n) b)) =
      2 * Real.log (dimension n) - Real.log 2 / dimension n :=
  (entropy_of_diagonal _ _ (choi_diagonal b)).trans (pairedWeight_entropy b)

theorem proper_paired_entropy (b : Bit) (s : Mask n) (hs : s ≠ Finset.univ) :
    vonNeumannEntropy (pairedMarginal s (normalizedChoi (channel b))) =
      2 * s.card * Real.log 2 := by
  rw [entropy_of_diagonal _ (fun _ => (Fintype.card (Kept s × Kept s) : ℝ)⁻¹)
    (by simpa using proper_paired_mixed b s hs), ← log_pairedDimension]
  have hc : (Fintype.card (Kept s × Kept s) : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog_def,
    Real.log_inv]
  field_simp

@[instance_reducible] private def fullDiscardedUnique (n : ℕ) :
    Unique (Discarded (Finset.univ : Mask n)) :=
  ⟨⟨fun _ => 0⟩, fun _ => funext fun i => (i.property (Finset.mem_univ i.val)).elim⟩

theorem full_paired_entropy (ρ : DensityState (Word (n + 1) × Word (n + 1))) :
    vonNeumannEntropy (pairedMarginal Finset.univ ρ) = vonNeumannEntropy ρ := by
  let s : Mask n := Finset.univ
  let u : Unique (Discarded s) := fullDiscardedUnique n
  let : Unique (Discarded s × Discarded s) :=
    ⟨⟨(u.default, u.default)⟩, fun w => Prod.ext (u.uniq w.1) (u.uniq w.2)⟩
  let e : (Kept s × Kept s) ≃ (Word (n + 1) × Word (n + 1)) :=
    (Equiv.uniqueProd (Kept s × Kept s) (Discarded s × Discarded s)).symm.trans
      (splitPair s).symm
  have he : pairedMarginal s ρ = relabelState e ρ := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    ext p q
    change (∑ w : Discarded s × Discarded s,
      pairMatrix ρ ((splitPair s).symm (w,p)) ((splitPair s).symm (w,q))) = _
    rw [Fintype.sum_unique]
    rfl
  exact congrArg vonNeumannEntropy he |>.trans (entropy_relabelState e ρ)

theorem choi_pairedEntropy (b : Bit) (s : Mask n) :
    vonNeumannEntropy (pairedMarginal s (normalizedChoi (channel b))) = pairedEntropyProfile s := by
  by_cases hs : s = Finset.univ
  · subst s
    rw [full_paired_entropy, choi_entropy, profile_full]
  · rw [proper_paired_entropy b s hs]
    simp [pairedEntropyProfile, hs]

/-- CMI of the actual normalized Choi state with the input and output at each site paired. -/
def pairedCMI (ρ : DensityState (Word (n + 1) × Word (n + 1))) (L M R : Mask n) : ℝ :=
  vonNeumannEntropy (pairedMarginal (L ∪ M) ρ) +
  vonNeumannEntropy (pairedMarginal (M ∪ R) ρ) -
  vonNeumannEntropy (pairedMarginal M ρ) -
  vonNeumannEntropy (pairedMarginal (L ∪ M ∪ R) ρ)

theorem choi_pairedCMI (b : Bit) (L M R : Mask n)
    (hLM : Disjoint L M) (hLR : Disjoint L R) (hMR : Disjoint M R) :
    pairedCMI (normalizedChoi (channel b)) L M R =
      if L = ∅ ∨ R = ∅ then 0
      else if L ∪ M ∪ R = Finset.univ then Real.log 2 / dimension n else 0 := by
  simp only [pairedCMI, choi_pairedEntropy]
  exact pairedCMI_profile L M R hLM hLR hMR

end

end D5.S3.Quantum.EnvironmentRecords.EdgePath
