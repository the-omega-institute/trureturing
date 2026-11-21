/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreEnergy
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCounts, mathlib/module/Mathlib.Combinatorics.SimpleGraph.LapMatrix]
   utility: none
   digest: The compressed hard-core energy is a weighted Dirichlet form with exactly the constant amplitudes in its kernel. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCounts
import Mathlib.Analysis.Complex.Order
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Basic.Complex.BigOperators

/-! The compressed Hamiltonian of Section 6.1 at fugacity one, on the independent
configurations of a cycle. The two kinds of moves give separate graph Laplacians. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreEnergy

open PeriodicMPSUniformHardCoreCounts
open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {n : ℕ}

private theorem mem_insertionSites {S : Finset (Fin n)} {i : Fin n} :
    i ∈ insertionSites S ↔ i ∉ S ∧ Independent (insert i S) := by
  simp [insertionSites]

private theorem mem_directedHops {S : Finset (Fin n)} {p : Fin n × Fin n} :
    p ∈ directedHops S ↔ LegalHop S p.1 p.2 := by
  simp [directedHops]

private theorem deletion_card {S T : Configuration n} (h : DeletionStep S T) :
    T.val.card + 1 = S.val.card := by
  obtain ⟨i, hi, hT⟩ := h
  rw [hT, Finset.card_erase_add_one hi]

private theorem insertion_iff {S T : Configuration n} :
    DeletionStep T S ↔ ∃ i ∈ insertionSites S.val, T.val = insert i S.val := by
  constructor
  · rintro ⟨i, hi, hS⟩
    have hT : T.val = insert i S.val := by rw [hS, Finset.insert_erase hi]
    have hEmpty : i ∉ S.val := by rw [hS]; exact Finset.notMem_erase _ _
    exact ⟨i, mem_insertionSites.mpr ⟨hEmpty, hT ▸ T.property⟩, hT⟩
  · rintro ⟨i, hi, hT⟩
    refine ⟨i, ?_, ?_⟩
    · rw [hT]
      exact Finset.mem_insert_self i S.val
    · rw [hT, Finset.erase_insert (mem_insertionSites.mp hi).1]

/-- One legal nearest-neighbor replacement within the independent configurations. -/
def HopStep (S T : Configuration n) : Prop :=
  ∃ src dst, LegalHop S.val src dst ∧ T.val = insert dst (S.val.erase src)

private theorem hop_card {S T : Configuration n} (h : HopStep S T) :
    T.val.card = S.val.card := by
  obtain ⟨src, dst, ⟨_, hSrc, hDst, _⟩, hT⟩ := h
  rw [hT, Finset.card_insert_of_notMem (fun h => hDst (Finset.mem_of_mem_erase h)),
    Finset.card_erase_add_one hSrc]

private theorem hop_reverse {S T : Configuration n} (h : HopStep S T) : HopStep T S := by
  obtain ⟨src, dst, ⟨hAdj, hSrc, hDst, _⟩, hT⟩ := h
  have hne : src ≠ dst := fun h => hDst (h ▸ hSrc)
  have restore : insert src (T.val.erase dst) = S.val := by
    rw [hT, Finset.erase_insert (fun h => hDst (Finset.mem_of_mem_erase h)),
      Finset.insert_erase hSrc]
  refine ⟨dst, src, ⟨hAdj.symm, ?_, ?_, restore.symm ▸ S.property⟩, restore.symm⟩
  · simp [hT]
  · simp [hT, hne]

/-- The flip graph connects configurations that differ by one occupied site. -/
def flipGraph (n : ℕ) : SimpleGraph (Configuration n) where
  Adj S T := DeletionStep S T ∨ DeletionStep T S
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun S h => by
    have := deletion_card (h.elim id id)
    omega⟩

/-- The hop graph connects configurations related by one legal adjacent swap. -/
def hopGraph (n : ℕ) : SimpleGraph (Configuration n) where
  Adj := HopStep
  symm := ⟨fun _ _ => hop_reverse⟩
  loopless := ⟨fun S h => by
    obtain ⟨src, dst, ⟨_, _, hDst, _⟩, hS⟩ := h
    exact hDst (hS.symm ▸ Finset.mem_insert_self dst (S.val.erase src))⟩

instance (n : ℕ) : DecidableRel (flipGraph n).Adj := Classical.decRel _
instance (n : ℕ) : DecidableRel (hopGraph n).Adj := Classical.decRel _

private theorem flip_not_hop {S T : Configuration n} (h : (flipGraph n).Adj S T) :
    ¬ (hopGraph n).Adj S T := by
  intro hh
  have he := hop_card hh
  rcases h with hd | hd
  · have := deletion_card hd
    omega
  · have := deletion_card hd
    omega

private def deletionEndpoint (S : Configuration n) : {i // i ∈ S.val} ↪ Configuration n where
  toFun i := ⟨S.val.erase i.val, independent_erase S.property i.val⟩
  inj' := by
    intro i j h
    apply Subtype.ext
    by_contra hne
    have he : S.val.erase i.val = S.val.erase j.val := congrArg Subtype.val h
    exact Finset.notMem_erase i.val S.val
      (he.symm ▸ Finset.mem_erase.mpr ⟨hne, i.property⟩)

private def insertionEndpoint (S : Configuration n) :
    {i // i ∈ insertionSites S.val} ↪ Configuration n where
  toFun i := ⟨insert i.val S.val, (mem_insertionSites.mp i.property).2⟩
  inj' := by
    intro i j h
    apply Subtype.ext
    have he : insert i.val S.val = insert j.val S.val := congrArg Subtype.val h
    exact (Finset.mem_insert.mp (he ▸ Finset.mem_insert_self i.val S.val)).resolve_right
      (mem_insertionSites.mp i.property).1

private def hopEndpoint (S : Configuration n) :
    {p // p ∈ directedHops S.val} ↪ Configuration n where
  toFun p := ⟨insert p.val.2 (S.val.erase p.val.1), (mem_directedHops.mp p.property).2.2.2⟩
  inj' := by
    intro p q h
    obtain ⟨_, hpSrc, hpDst, _⟩ := mem_directedHops.mp p.property
    obtain ⟨_, hqSrc, hqDst, _⟩ := mem_directedHops.mp q.property
    have he : insert p.val.2 (S.val.erase p.val.1) =
        insert q.val.2 (S.val.erase q.val.1) := congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext
    · by_contra hne
      have hmem : p.val.1 ∈ insert q.val.2 (S.val.erase q.val.1) :=
        Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hpSrc⟩)
      have hp : p.val.1 ≠ p.val.2 := fun h => hpDst (h ▸ hpSrc)
      simpa [hp] using (he.symm ▸ hmem : p.val.1 ∈ insert p.val.2 (S.val.erase p.val.1))
    · exact (Finset.mem_insert.mp (he ▸ Finset.mem_insert_self p.val.2 _)).resolve_right
        (fun hm => hpDst (Finset.mem_of_mem_erase hm))

private theorem mem_deletionEndpoints {S T : Configuration n} :
    T ∈ S.val.attach.map (deletionEndpoint S) ↔ DeletionStep S T := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i.val, i.property, rfl⟩
  · rintro ⟨i, hi, hT⟩
    exact ⟨⟨i, hi⟩, Finset.mem_attach _ _, Subtype.ext hT.symm⟩

private theorem mem_insertionEndpoints {S T : Configuration n} :
    T ∈ (insertionSites S.val).attach.map (insertionEndpoint S) ↔ DeletionStep T S := by
  rw [Finset.mem_map, insertion_iff]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨i.val, i.property, rfl⟩
  · rintro ⟨i, hi, hT⟩
    exact ⟨⟨i, hi⟩, Finset.mem_attach _ _, Subtype.ext hT.symm⟩

private theorem mem_hopEndpoints {S T : Configuration n} :
    T ∈ (directedHops S.val).attach.map (hopEndpoint S) ↔ HopStep S T := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨p, _, rfl⟩
    exact ⟨p.val.1, p.val.2, mem_directedHops.mp p.property, rfl⟩
  · rintro ⟨src, dst, h, hT⟩
    exact ⟨⟨(src, dst), mem_directedHops.mpr h⟩, Finset.mem_attach _ _, Subtype.ext hT.symm⟩

private theorem flip_degree (S : Configuration n) :
    (flipGraph n).degree S = S.val.card + (insertionSites S.val).card := by
  have hDisjoint : Disjoint (S.val.attach.map (deletionEndpoint S))
      ((insertionSites S.val).attach.map (insertionEndpoint S)) := by
    rw [Finset.disjoint_left]
    intro T hd hi
    have := deletion_card (mem_deletionEndpoints.mp hd)
    have := deletion_card (mem_insertionEndpoints.mp hi)
    omega
  have hNeighbors : (flipGraph n).neighborFinset S = S.val.attach.map (deletionEndpoint S) ∪
      (insertionSites S.val).attach.map (insertionEndpoint S) := by
    ext T
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_union, mem_deletionEndpoints,
      mem_insertionEndpoints]
    rfl
  rw [SimpleGraph.degree, hNeighbors, Finset.card_union_of_disjoint hDisjoint]
  simp only [Finset.card_map, Finset.card_attach]

private theorem hop_degree (S : Configuration n) :
    (hopGraph n).degree S = (directedHops S.val).card := by
  have hNeighbors : (hopGraph n).neighborFinset S =
      (directedHops S.val).attach.map (hopEndpoint S) := by
    ext T
    rw [SimpleGraph.mem_neighborFinset, mem_hopEndpoints]
    rfl
  rw [SimpleGraph.degree, hNeighbors, Finset.card_map, Finset.card_attach]

/-- The symmetric positive transition weight for a genuine flip or hop. -/
def transitionWeight (S T : Configuration n) : ℝ :=
  (if (flipGraph n).Adj S T then 1 else 0) + (if (hopGraph n).Adj S T then 1 / 2 else 0)

theorem transitionWeight_comm (S T : Configuration n) :
    transitionWeight S T = transitionWeight T S := by
  unfold transitionWeight
  exact congrArg₂ (· + ·)
    (if_congr ((flipGraph n).adj_comm S T) rfl rfl)
    (if_congr ((hopGraph n).adj_comm S T) rfl rfl)

theorem transitionWeight_of_flip {S T : Configuration n} (h : (flipGraph n).Adj S T) :
    transitionWeight S T = 1 := by
  simp [transitionWeight, h, flip_not_hop h]

theorem transitionWeight_of_hop {S T : Configuration n} (h : (hopGraph n).Adj S T) :
    transitionWeight S T = 1 / 2 := by
  have hf : ¬ (flipGraph n).Adj S T := fun hf => flip_not_hop hf h
  simp [transitionWeight, h, hf]

private theorem transitionWeight_nonneg (S T : Configuration n) : 0 ≤ transitionWeight S T := by
  unfold transitionWeight
  split_ifs <;> norm_num

private theorem weighted_degree (hn : 7 ≤ n) (S : Configuration n) :
    ((flipGraph n).degree S : ℝ) + (1 / 2 : ℝ) * (hopGraph n).degree S =
      (n : ℝ) - S.val.card := by
  have h := normalized_row_sum hn S.property (1 : ℝ)
  rw [flip_degree, hop_degree, ← hopCount_eq_card_directedHops hn, Nat.cast_add]
  norm_num at h ⊢
  linarith

/-- The compressed Hamiltonian shifted by `n`, with diagonal `n - |S|`. -/
def shiftedHamiltonian (n : ℕ) : Matrix (Configuration n) (Configuration n) ℝ :=
  Matrix.diagonal (fun S : Configuration n => (n : ℝ) - S.val.card) -
    Matrix.of transitionWeight

theorem shiftedHamiltonian_eq_laplacians (hn : 7 ≤ n) :
    shiftedHamiltonian n = (flipGraph n).lapMatrix ℝ + (1 / 2 : ℝ) • (hopGraph n).lapMatrix ℝ := by
  ext S T
  simp only [shiftedHamiltonian, Matrix.sub_apply, Matrix.of_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, transitionWeight]
  by_cases he : S = T
  · subst T
    simpa using (weighted_degree hn S).symm
  · simp only [ite_eq_right he]
    split_ifs <;> norm_num

/-- The weighted degree is the sum of actual off-diagonal flip and hop weights. -/
theorem transitionWeight_row_sum (hn : 7 ≤ n) (S : Configuration n) :
    (∑ T, transitionWeight S T) = (n : ℝ) - S.val.card := by
  rw [← weighted_degree hn S]
  simp only [transitionWeight, Finset.sum_add_distrib, SimpleGraph.degree_eq_sum_if_adj,
    Finset.mul_sum, mul_ite, mul_one, mul_zero]

private theorem real_energy (hn : 7 ≤ n) (x : Configuration n → ℝ) :
    x ⬝ᵥ (shiftedHamiltonian n *ᵥ x) =
      (∑ S, ∑ T, transitionWeight S T * (x S - x T) ^ 2) / 2 := by
  rw [shiftedHamiltonian_eq_laplacians hn]
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    ← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
  have hHop (S T : Configuration n) :
      (if (hopGraph n).Adj S T then (1 / 2 : ℝ) * (x S - x T) ^ 2 else 0) =
        (1 / 2 : ℝ) * (if (hopGraph n).Adj S T then (x S - x T) ^ 2 else 0) := by
    split_ifs <;> simp
  simp only [transitionWeight, add_mul, ite_mul, one_mul, zero_mul, hHop,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem complex_energy_re (A : Matrix (Configuration n) (Configuration n) ℝ)
    (x : Configuration n → ℂ) :
    (star x ⬝ᵥ (A.map Complex.ofReal *ᵥ x)).re =
      (fun S => (x S).re) ⬝ᵥ (A *ᵥ fun S => (x S).re) +
      (fun S => (x S).im) ⬝ᵥ (A *ᵥ fun S => (x S).im) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Matrix.map_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The quadratic form of the shifted compressed Hamiltonian on complex amplitudes. -/
def shiftedEnergy (x : Configuration n → ℂ) : ℝ :=
  (star x ⬝ᵥ ((shiftedHamiltonian n).map Complex.ofReal *ᵥ x)).re

private theorem shiftedHamiltonian_isHermitian (n : ℕ) :
    ((shiftedHamiltonian n).map Complex.ofReal).IsHermitian := by
  have hWeight : (Matrix.of (transitionWeight (n := n))).IsHermitian := by
    exact Matrix.IsHermitian.ext fun S T => by simpa using transitionWeight_comm T S
  have hDiag : (Matrix.diagonal fun S : Configuration n => (n : ℝ) - S.val.card).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr fun _ => star_trivial _
  exact (hDiag.sub hWeight).map Complex.ofReal fun r => by simp

private theorem shiftedQuadratic_eq_energy (x : Configuration n → ℂ) :
    star x ⬝ᵥ ((shiftedHamiltonian n).map Complex.ofReal *ᵥ x) = (shiftedEnergy x : ℂ) := by
  refine Complex.ext ?_ ?_
  · rfl
  · have h := congrArg Complex.im
      ((shiftedHamiltonian_isHermitian n).star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def, Complex.conj_im] at h
    rw [Complex.ofReal_im]
    linarith

/-- The factor of one half accounts for the two orders of each configuration pair. -/
theorem shiftedEnergy_eq_dirichlet (hn : 7 ≤ n) (x : Configuration n → ℂ) :
    shiftedEnergy x = (∑ S, ∑ T, transitionWeight S T * Complex.normSq (x S - x T)) / 2 := by
  rw [shiftedEnergy, complex_energy_re, real_energy hn, real_energy hn, ← add_div]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem shiftedHamiltonian_quadratic_eq_dirichlet (hn : 7 ≤ n) (x : Configuration n → ℂ) :
    star x ⬝ᵥ ((shiftedHamiltonian n).map Complex.ofReal *ᵥ x) =
      (((∑ S, ∑ T, transitionWeight S T * Complex.normSq (x S - x T)) / 2 : ℝ) : ℂ) := by
  rw [shiftedQuadratic_eq_energy, shiftedEnergy_eq_dirichlet hn]

theorem shiftedEnergy_nonneg (hn : 7 ≤ n) (x : Configuration n → ℂ) :
    0 ≤ shiftedEnergy x := by
  rw [shiftedEnergy_eq_dirichlet hn]
  exact div_nonneg (Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun T _ =>
    mul_nonneg (transitionWeight_nonneg S T) (Complex.normSq_nonneg _)) (by norm_num)

theorem shiftedHamiltonian_posSemidef (hn : 7 ≤ n) :
    ((shiftedHamiltonian n).map Complex.ofReal).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (shiftedHamiltonian_isHermitian n) fun x => by
    rw [shiftedQuadratic_eq_energy, Complex.zero_le_real]
    exact shiftedEnergy_nonneg hn x

/-- A zero-energy amplitude is constant because every configuration can be emptied by flips. -/
theorem shiftedEnergy_eq_zero_iff (hn : 7 ≤ n) (x : Configuration n → ℂ) :
    shiftedEnergy x = 0 ↔ ∀ S, x S = x (emptyConfiguration n) := by
  rw [shiftedEnergy_eq_dirichlet hn]
  constructor
  · intro h
    have hNonneg (S T : Configuration n) : 0 ≤
        transitionWeight S T * Complex.normSq (x S - x T) :=
      mul_nonneg (transitionWeight_nonneg S T) (Complex.normSq_nonneg _)
    have hSum : (∑ S, ∑ T, transitionWeight S T * Complex.normSq (x S - x T)) = 0 := by
      linarith
    have hRow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun S _ => Finset.sum_nonneg fun T _ => hNonneg S T)).mp hSum
    have hDelete {S T : Configuration n} (hStep : DeletionStep S T) : x S = x T := by
      have hTerm := (Finset.sum_eq_zero_iff_of_nonneg (fun U _ => hNonneg S U)).mp
        (hRow S (Finset.mem_univ S)) T (Finset.mem_univ T)
      have hFlip : (flipGraph n).Adj S T := Or.inl hStep
      rw [transitionWeight_of_flip hFlip, one_mul] at hTerm
      exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hTerm)
    have along {S T : Configuration n} (chain : Relation.ReflTransGen DeletionStep S T) :
        x S = x T := by
      induction chain with
      | refl => rfl
      | tail _ hStep ih => exact ih.trans (hDelete hStep)
    exact fun S => along (deletion_reaches_empty S)
  · intro h
    have hSum : (∑ S, ∑ T, transitionWeight S T * Complex.normSq (x S - x T)) = 0 := by
      refine Finset.sum_eq_zero fun S _ => Finset.sum_eq_zero fun T _ => ?_
      rw [h S, h T, sub_self, Complex.normSq_zero, mul_zero]
    rw [hSum, zero_div]

theorem shiftedHamiltonian_mulVec_eq_zero_iff (hn : 7 ≤ n) (x : Configuration n → ℂ) :
    (shiftedHamiltonian n).map Complex.ofReal *ᵥ x = 0 ↔
      ∀ S, x S = x (emptyConfiguration n) := by
  rw [← (shiftedHamiltonian_posSemidef hn).dotProduct_mulVec_zero_iff,
    shiftedQuadratic_eq_energy, Complex.ofReal_eq_zero, shiftedEnergy_eq_zero_iff hn]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreEnergy
