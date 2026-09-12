/- GID: D5/S3/Quantum/StationaryPreparation/StationaryOccupationPadding
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/StationaryOccupationPadding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite padding isometries and the physical stationary occupation gate. -/

import D5.S3.Quantum.StationaryPreparation.PaddingMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding

open D5.S3.Quantum.StationaryPreparation.PaddingMemory

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]

def weightedMatrix (next : K → A → K) (p : K → A → ℝ) : Matrix (A × K) K ℂ :=
  fun q j => if next j q.1 = q.2 then (Real.sqrt (p j q.1) : ℂ) else 0

theorem sqrt_gram (r : ℝ) (hr : 0 ≤ r) :
    star (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt hr]

/-- A deterministic transition with uniquely recoverable predecessors is an isometry. -/
theorem weighted_matrix_gram (next : K → A → K) (p : K → A → ℝ)
    (hp : ∀ j i, 0 ≤ p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (hinj : ∀ j l i, p j i ≠ 0 → p l i ≠ 0 → next j i = next l i → j = l) :
    (weightedMatrix next p).conjTranspose * weightedMatrix next p = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hjl : j = l
  · subst l
    simp only [if_pos rfl, Fintype.sum_prod_type]
    have hterm (i : A) (k : K) :
        star (weightedMatrix next p (i, k) j) * weightedMatrix next p (i, k) j =
          if next j i = k then (p j i : ℂ) else 0 := by
      by_cases h : next j i = k
      · simp only [weightedMatrix, if_pos h]
        exact sqrt_gram _ (hp j i)
      · simp [weightedMatrix, h]
    simp_rw [hterm]
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Complex.ofReal_sum,
      hsum, Complex.ofReal_one]
  · rw [if_neg hjl]
    apply Finset.sum_eq_zero
    rintro ⟨i, k⟩ _
    by_cases hpj : p j i = 0
    · simp [weightedMatrix, hpj]
    by_cases hpl : p l i = 0
    · simp [weightedMatrix, hpl]
    by_cases hj : next j i = k
    · have hl : next l i ≠ k := fun hl => hjl (hinj j l i hpj hpl (hj.trans hl.symm))
      simp [weightedMatrix, hl]
    · simp [weightedMatrix, hj]

theorem fixed_unitary_of_matrix [DecidableEq A] (blank : A)
    (V : Matrix (A × K) K ℂ) (hV : V.conjTranspose * V = 1) :
    ∃ U : Unitary (A × K),
      (∀ x : Space K,
        U (coordinateEmbedding (blankInjection blank (Function.Embedding.refl K)) x) =
          matrixIsometry V hV x) ∧
      ∀ j i k, U (basis (blank, j)) (i, k) = V (i, k) j := by
  obtain ⟨U, hU⟩ := exists_unitary_agree
    (coordinateEmbedding (blankInjection blank (Function.Embedding.refl K)))
    (matrixIsometry V hV)
  refine ⟨U, hU, ?_⟩
  intro j i k
  have h := congrArg (fun y : Space (A × K) => y (i, k)) (hU (basis j))
  rw [show coordinateEmbedding (blankInjection blank (Function.Embedding.refl K))
      (basis j) = basis (blank, j) from coordinate_embedding_basis _ j] at h
  exact h.trans (matrix_isometry_basis V hV j (i, k))

end D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding

open D5.S3.Quantum.StationaryPreparation.PaddingMemory

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

variable {I : Type*} [Fintype I] [DecidableEq I]

def paddingProbability (H : ℕ) (c : I → ℕ) : PaddingMemory H c → Option I → ℝ
  | none, none => 1
  | none, some _ => 0
  | some (b, h), none =>
      if tailSum b.val = 1 then (if h.val = 0 then 0 else 1)
      else headProbability h.val (tailSum b.val)
  | some (b, h), some i =>
      if tailSum b.val = 1 then (if h.val = 0 then ((b.val i).val : ℝ) else 0)
      else tailProbability h.val (tailSum b.val) (b.val i).val

theorem padding_probability_nonneg (H : ℕ) (c : I → ℕ) :
    ∀ s i, 0 ≤ paddingProbability H c s i := by
  intro s i
  cases s with
  | none => cases i <;> simp [paddingProbability]
  | some s =>
    rcases s with ⟨b, h⟩
    have hR := positive_tail_sum c b
    by_cases hr : tailSum b.val = 1
    · cases i <;> simp only [paddingProbability, if_pos hr] <;> split <;> positivity
    · have hR2 : (2 : ℝ) ≤ tailSum b.val := by exact_mod_cast (by omega : 2 ≤ tailSum b.val)
      have hden : (0 : ℝ) < (h.val : ℝ) + tailSum b.val - 1 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) h.val]
      cases i with
      | none =>
        simp only [paddingProbability, if_neg hr, headProbability]
        exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
      | some i =>
        change 0 ≤ if tailSum b.val = 1 then _ else _
        rw [if_neg hr]
        unfold tailProbability
        apply div_nonneg
        · exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
        · exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hden)

theorem padding_probability_sum (H : ℕ) (c : I → ℕ) :
    ∀ s, ∑ i, paddingProbability H c s i = 1 := by
  intro s
  cases s with
  | none => simp [Fintype.sum_option, paddingProbability]
  | some s =>
    rcases s with ⟨b, h⟩
    have hR := positive_tail_sum c b
    rw [Fintype.sum_option]
    by_cases hr : tailSum b.val = 1
    · by_cases hh : h.val = 0
      · simp only [paddingProbability, if_pos hr, if_pos hh, zero_add]
        rw [← Nat.cast_sum]
        change (tailSum b.val : ℝ) = 1
        exact_mod_cast hr
      · simp [paddingProbability, hr, hh]
    · simp only [paddingProbability, if_neg hr]
      apply padding_probabilities_sum (fun i => (b.val i).val) h.val
      change 2 ≤ tailSum b.val
      omega

theorem positive_head_of_probability (H : ℕ) (c : I → ℕ)
    (b : PositiveTail c) (h : Fin (H + 1))
    (hp : paddingProbability H c (some (b, h)) none ≠ 0) : 0 < h.val := by
  by_contra! hn
  have hh : h.val = 0 := by omega
  simp [paddingProbability, headProbability, hh] at hp

theorem positive_tail_of_probability (H : ℕ) (c : I → ℕ)
    (b : PositiveTail c) (h : Fin (H + 1)) (i : I)
    (hp : paddingProbability H c (some (b, h)) (some i) ≠ 0) :
    0 < (b.val i).val ∧ (tailSum b.val = 1 → h.val = 0) := by
  constructor
  · by_contra! hn
    have hz : (b.val i).val = 0 := by omega
    simp [paddingProbability, tailProbability, hz] at hp
  · intro hr
    by_contra hh
    simp [paddingProbability, hr, hh] at hp

theorem padding_predecessor_unique (H : ℕ) (c : I → ℕ) :
    ∀ s t i, paddingProbability H c s i ≠ 0 → paddingProbability H c t i ≠ 0 →
      paddingNext H c s i = paddingNext H c t i → s = t := by
  intro s t i hs ht heq
  cases i with
  | none =>
    cases s with
    | none => cases t <;> simp_all [paddingNext]
    | some s =>
      cases t with
      | none => simp [paddingNext] at heq
      | some t =>
        rcases s with ⟨b, h⟩
        rcases t with ⟨e, g⟩
        have hh := positive_head_of_probability H c b h hs
        have hg := positive_head_of_probability H c e g ht
        have hp := Option.some.inj heq
        have hb : b = e := congrArg Prod.fst hp
        have hv := congrArg (fun p : PositiveTail c × Fin (H + 1) => p.2.val) hp
        have hhg : h = g := by
          apply Fin.ext
          change h.val - 1 = g.val - 1 at hv
          omega
        simp [hb, hhg]
  | some i =>
    cases s with
    | none => exact False.elim (hs rfl)
    | some s =>
      cases t with
      | none => exact False.elim (ht rfl)
      | some t =>
        rcases s with ⟨b, h⟩
        rcases t with ⟨e, g⟩
        obtain ⟨hbi, hbh⟩ := positive_tail_of_probability H c b h i hs
        obtain ⟨hei, heh⟩ := positive_tail_of_probability H c e g i ht
        have hbpos := positive_tail_sum c b
        have hepos := positive_tail_sum c e
        simp only [paddingNext, dif_pos hbi, dif_pos hei] at heq
        by_cases hbR : 1 < tailSum b.val
        · rw [dif_pos hbR] at heq
          by_cases heR : 1 < tailSum e.val
          · rw [dif_pos heR] at heq
            have hp := Option.some.inj heq
            have hhg : h = g := congrArg Prod.snd hp
            have hdec := congrArg (fun p : PositiveTail c × Fin (H + 1) => p.1.val) hp
            have hbe : b = e := Subtype.ext (decrement_injective c b.val e.val i hbi hei hdec)
            simp [hbe, hhg]
          · simp [heR] at heq
        · rw [dif_neg hbR] at heq
          by_cases heR : 1 < tailSum e.val
          · simp [heR] at heq
          · have hb1 : tailSum b.val = 1 := by omega
            have he1 : tailSum e.val = 1 := by omega
            have hbe : b = e := Subtype.ext (sum_one_unique c b.val e.val hb1 he1 i hbi hei)
            have hhg : h = g := Fin.ext ((hbh hb1).trans (heh he1).symm)
            simp [hbe, hhg]

def paddingMatrix (H : ℕ) (c : I → ℕ) :
    Matrix (Option I × PaddingMemory H c) (PaddingMemory H c) ℂ :=
  weightedMatrix (paddingNext H c) (paddingProbability H c)

theorem padding_matrix_gram (H : ℕ) (c : I → ℕ) :
    (paddingMatrix H c).conjTranspose * paddingMatrix H c = 1 :=
  weighted_matrix_gram _ _ (padding_probability_nonneg H c)
    (padding_probability_sum H c) (padding_predecessor_unique H c)

theorem padding_unitary_exists (H : ℕ) (c : I → ℕ) :
    ∃ U : Unitary (Option I × PaddingMemory H c),
      ∀ j i k, U (basis (none, j)) (i, k) = paddingMatrix H c (i, k) j := by
  obtain ⟨U, _, hU⟩ := fixed_unitary_of_matrix none (paddingMatrix H c) (padding_matrix_gram H c)
  exact ⟨U, hU⟩

end D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding

open D5.S3.Quantum.StationaryPreparation.PaddingMemory

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

variable {I : Type*} [Fintype I] [DecidableEq I]

variable {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]

def relabelNext (H : ℕ) (c : I → ℕ) (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) :
    K → A → K := fun j i => eK (paddingNext H c (eK.symm j) (eA.symm i))

def relabelProbability (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) : K → A → ℝ :=
  fun j i => paddingProbability H c (eK.symm j) (eA.symm i)

def relabelMatrix (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) : Matrix (A × K) K ℂ :=
  weightedMatrix (relabelNext H c eA eK) (relabelProbability H c eA eK)

theorem relabel_matrix_gram (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) :
    (relabelMatrix H c eA eK).conjTranspose * relabelMatrix H c eA eK = 1 := by
  apply weighted_matrix_gram
  · intro j i
    exact padding_probability_nonneg H c _ _
  · intro j
    rw [← eA.sum_comp]
    simpa only [relabelProbability, Equiv.symm_apply_apply] using
      padding_probability_sum H c (eK.symm j)
  · intro j l i hj hl heq
    apply eK.symm.injective
    apply padding_predecessor_unique H c (eK.symm j) (eK.symm l) (eA.symm i) hj hl
    exact eK.injective heq

def relabelGate (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) : Unitary (A × K) :=
  Classical.choose (fixed_unitary_of_matrix (eA none) (relabelMatrix H c eA eK)
    (relabel_matrix_gram H c eA eK))

theorem relabel_gate_coefficients (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) (j : K) (i : A) (k : K) :
    relabelGate H c eA eK (basis (eA none, j)) (i, k) = relabelMatrix H c eA eK (i, k) j :=
  (Classical.choose_spec (fixed_unitary_of_matrix (eA none) (relabelMatrix H c eA eK)
    (relabel_matrix_gram H c eA eK))).2 j i k

def proposedDimension (a : Multiset A) : ℕ :=
  (∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count

variable [Nonempty A]

def maximalHead (a : Multiset A) : A := Classical.choose (maximal_head_exists a)

theorem maximal_head_spec (a : Multiset A) :
    a.count (maximalHead a) = Finset.univ.sup a.count := Classical.choose_spec (maximal_head_exists a)

def physicalMemoryEquiv (a : Multiset A) :
    OccupationMemory a (maximalHead a) ≃ Fin (proposedDimension a) :=
  occupationMemoryEquiv a (maximalHead a) (maximal_head_spec a)

def physicalMatrix (a : Multiset A) :
    Matrix (A × Fin (proposedDimension a)) (Fin (proposedDimension a)) ℂ :=
  relabelMatrix (a.count (maximalHead a))
    (fun i : TailAlphabet (maximalHead a) => a.count i.val)
    (Equiv.optionSubtypeNe (maximalHead a)) (physicalMemoryEquiv a)

def physicalFinal (a : Multiset A) : Space (Fin (proposedDimension a)) :=
  basis (physicalMemoryEquiv a none)

def physicalGate (a : Multiset A) : Unitary (A × Fin (proposedDimension a)) :=
  relabelGate (a.count (maximalHead a))
    (fun i : TailAlphabet (maximalHead a) => a.count i.val)
    (Equiv.optionSubtypeNe (maximalHead a)) (physicalMemoryEquiv a)

theorem physical_matrix_gram (a : Multiset A) :
    (physicalMatrix a).conjTranspose * physicalMatrix a = 1 :=
  relabel_matrix_gram _ _ _ _

theorem physical_final_norm (a : Multiset A) : ‖physicalFinal a‖ = 1 :=
  (EuclideanSpace.basisFun _ ℂ).norm_eq_one _

theorem physical_gate_coefficients (a : Multiset A) (j : Fin (proposedDimension a))
    (i : A) (k : Fin (proposedDimension a)) :
    physicalGate a (basis (maximalHead a, j)) (i, k) = physicalMatrix a (i, k) j :=
  relabel_gate_coefficients _ _ _ _ j i k

end D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding
