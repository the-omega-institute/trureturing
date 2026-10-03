/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Jordan-Wigner operators compress to the hard-core Hilbert space. -/

/-
fullD_hardCore_iff:
  proof_shape: content
  escape_witness: fullD_hardCore_iff (form 2): An annihilation with both neighbours empty preserves and reflects every adjacent exclusion constraint.
  Direct frozen dependencies: Assignment.
restrictOp_fullD:
  proof_shape: content
  escape_witness: restrictOp_fullD (form 2): The Jordan-Wigner entry calculation and hard-core empty neighbours identify the compressed dressed tensor.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
restrictOp_fullNumber:
  proof_shape: content
  escape_witness: restrictOp_fullNumber (form 2): The occupation tensor has zero off-diagonal entries and its diagonal equals the occupied bit.
  Direct frozen dependencies: tensorOp, Assignment, visibleProjector.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel, D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts; freeze in topological import order.
Reused predicate: D5/S1/Words/AdmissibleWords/AdmissibleCount.Adm.
Pointwise exclusion: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true; sha256:1fd94a32ad20c5e9f47c8843c130133ce27a104e2f7f75cb9bf9916f8085bc2b.
Information-escape registration is paused under CLAUDE.md §3.9.
-/


import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Classical
set_option quotPrecheck false in
local notation "tensorOp" => (fun {N : ℕ} (w : Fin N → Matrix Bool Bool ℂ) =>
  Matrix.submatrix
    (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp (n := N)
      (fun i => Matrix.submatrix (w i) finTwoEquiv finTwoEquiv))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i)))
open PredictiveThermodynamic.Physical (Assignment visibleProjector)
open D5.S3.Quantum.FiniteDimensional (qubitZ)
local notation "spinZ" => (qubitZ.submatrix finTwoEquiv.symm finTwoEquiv.symm)
local notation "spinP" => ((1 : Matrix Bool Bool ℂ) - visibleProjector)

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
noncomputable section
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreModel

theorem fullD_hardCore_iff {N : ℕ} (i : Fin N) (s t : Assignment N)
    (h : D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD i s t ≠ 0) : Adm N s ↔ Adm N t := by
  have adjacent_iff {M : ℕ} (s : Assignment M) :
      Adm M s ↔ ∀ i k : Fin M, i.val + 1 = k.val → s i = true → s k = false := by
    simp only [adm_iff_no_adjacent_true, or_iff_not_imp_left, Bool.eq_true_eq_not_eq_false]
  have fullD_neighbour_empty {N : ℕ} (i k : Fin N)
      (hki : k.val + 1 = i.val ∨ i.val + 1 = k.val)
      (s t : Assignment N) (h : D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD i s t ≠ 0) : t k = false := by
    let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
    have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
      ext s t
      cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
    have hentry : fullD i s t = ∏ k : Fin N, dressedWord i k (s k) (t k) := by
      simp [fullD, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp, Matrix.submatrix_apply]
    rw [hentry] at h
    classical
    have hm : D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.dressedWord i k (s k) (t k) ≠ 0 := by
      intro hz
      apply h
      exact Finset.prod_eq_zero (Finset.mem_univ k) hz
    have hw : D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.dressedWord i k = spinP := by
      unfold D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.dressedWord
      rcases hki with hk | hk
      · simp [hk]
      · have hprev : ¬k.val + 1 = i.val := by omega
        have hlt : ¬k < i := by simp only [Fin.lt_def]; omega
        have hne : k ≠ i := by intro he; subst k; omega
        simp [hprev,hlt,hne,hk]
    rw [hw] at hm
    cases hsk : s k <;> cases htk : t k <;> simp_all [spinP_def, visibleProjector, Matrix.diagonal_apply]
  have erase_is_hard_core {N : ℕ} (t : HardCore N) (j : Fin N) :
      Adm N (Function.update t.val j false) := by
    rw [adjacent_iff]
    intro i k hik hi
    by_cases hij : i = j
    · subst i
      simp at hi
    by_cases hkj : k = j
    · subst k
      simp
    · simpa only [Function.update_of_ne hkj] using
        (((adjacent_iff t.val).mp t.property) i k hik (by simpa only [Function.update_of_ne hij] using hi))
  classical
  obtain ⟨hti,hst⟩ := D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts.fullD_support i s t h
  constructor
  · rw [adjacent_iff, adjacent_iff]
    intro hs u v huv htu
    by_cases hui : u = i
    · subst u
      exact fullD_neighbour_empty i v (Or.inr huv) s t h
    · by_cases hvi : v = i
      · subst v
        have hu := fullD_neighbour_empty i u (Or.inl huv) s t h
        simp [htu] at hu
      · have hsu : s u = true := by rw [hst,Function.update_of_ne hui]; exact htu
        have hsv := hs u v huv hsu
        simpa only [hst,Function.update_of_ne hvi] using hsv
  · intro ht
    rw [hst]
    exact erase_is_hard_core ⟨t,ht⟩ i

theorem restrictOp_fullD {N : ℕ} (i : Fin N) :
    (Matrix.submatrix (D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD i) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = annihilationAt i := by
  have adjacent_iff {M : ℕ} (s : Assignment M) :
      Adm M s ↔ ∀ i k : Fin M, i.val + 1 = k.val → s i = true → s k = false := by
    simp only [adm_iff_no_adjacent_true, or_iff_not_imp_left, Bool.eq_true_eq_not_eq_false]
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinZ_def : spinZ = Matrix.diagonal (fun b => if b then (-1 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> rfl
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  have fullC_entry {N : ℕ} (j : Fin N) (s t : Assignment N) :
      fullC j s t =
        if t j = true ∧ s = Function.update t j false
        then (-1 : ℂ) ^ prefixCount t j else 0 := by
    classical
    change tensorProduct (fermionWord j) s t = _
    rw [tensorOp_entries]
    change (∏ i : Fin N, fermionWord j i (s i) (t i)) = _
    by_cases h : t j = true ∧ s = Function.update t j false
    · rw [if_pos h]
      have he : (∏ i : Fin N, fermionWord j i (s i) (t i)) =
          ∏ i : Fin N, if i < j ∧ t i = true then (-1 : ℂ) else 1 := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [h.2]
        by_cases hij : i < j
        · have hne : i ≠ j := ne_of_lt hij
          simp only [fermionWord, if_pos hij, Function.update_of_ne hne,
            spinZ_def, qubitZ, finTwoEquiv, Matrix.diagonal_apply_eq]
          cases t i <;> simp [hij]
        · by_cases heq : i = j
          · subst i
            simp [fermionWord, Matrix.single, h.1]
          · simp [fermionWord, hij, heq, Matrix.one_apply, Function.update_of_ne heq]
      rw [he, ← Finset.prod_filter]
      simp [prefixCount, Finset.prod_const]
    · rw [if_neg h]
      by_cases ht : t j = true
      · have hs : s ≠ Function.update t j false := by tauto
        have hx : ∃ i, s i ≠ Function.update t j false i := by
          by_contra hh
          push Not at hh
          exact hs (funext hh)
        obtain ⟨i,hi⟩ := hx
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        by_cases heq : i = j
        · subst i
          simp only [Function.update_self] at hi
          have hsi : s j = true := by cases hsj : s j <;> simp_all
          simp [fermionWord, Matrix.single, hsi]
        · have hst : s i ≠ t i := by simpa only [Function.update_of_ne heq] using hi
          by_cases hij : i < j
          · simp only [fermionWord,if_pos hij,spinZ_def,Matrix.diagonal_apply,hst,if_false]
          · simp [fermionWord, hij, heq, hst, Matrix.one_apply]
      · apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [fermionWord, Matrix.single, ht]
  have annihilationAt_eq_fullC {N : ℕ} (i : Fin N) :
      annihilationAt i = (fun s t : HardCore N => fullC i s.val t.val) := by
    ext s t
    exact (fullC_entry i s.val t.val).symm
  classical
  ext s t
  change D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD i s.val t.val = _
  rw [annihilationAt_eq_fullC]
  change D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD i s.val t.val = D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.fullC i s.val t.val
  by_cases hh : t.val i = true ∧ s.val = Function.update t.val i false
  · change tensorProduct (dressedWord i) s.val t.val = tensorProduct (fermionWord i) s.val t.val
    rw [tensorOp_entries, tensorOp_entries]
    change (∏ k : Fin N, dressedWord i k (s.val k) (t.val k)) = ∏ k : Fin N, fermionWord i k (s.val k) (t.val k)
    apply Finset.prod_congr rfl
    intro k _hk
    by_cases hp : k.val + 1 = i.val
    · have hne : k ≠ i := by intro he; subst k; omega
      have hklt : k < i := by simp only [Fin.lt_def]; omega
      have htk : t.val k = false := by
        cases htk : t.val k
        · rfl
        · have hf := ((adjacent_iff t.val).mp t.property) k i hp htk
          simp [hh.1] at hf
      have hsk : s.val k = false := by rw [hh.2,Function.update_of_ne hne,htk]
      simp [D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.dressedWord,D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.fermionWord,hp,hklt,
        spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,htk,hsk,Matrix.diagonal_apply_eq]
    · by_cases hn : k.val = i.val + 1
      · have hne : k ≠ i := by intro he; subst k; omega
        have hnlt : ¬k < i := by simp only [Fin.lt_def]; omega
        have htk := ((adjacent_iff t.val).mp t.property) i k hn.symm hh.1
        have hsk : s.val k = false := by rw [hh.2,Function.update_of_ne hne,htk]
        simp [D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.dressedWord,D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.fermionWord,hp,hnlt,hne,hn,
          spinP_def, visibleProjector,htk,hsk,Matrix.diagonal_apply_eq,Matrix.one_apply]
      · simp [D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.dressedWord,D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner.fermionWord,hp,hn]
  · have hd : D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.fullD i s.val t.val = 0 := by
      by_contra hz
      exact hh (D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts.fullD_support i s.val t.val hz)
    rw [hd,fullC_entry,if_neg hh]

theorem restrictOp_fullNumber {N : ℕ} (i : Fin N) :
    (Matrix.submatrix (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)))) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = number (i.val + 1) := by
  have localOp_as_tensor {N : ℕ} (i : Fin N) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = tensorOp (numberWord i) := by
    classical
    ext s t
    simp only [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply, Matrix.of_apply]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = i
    · subst k
      simp [Function.update_self, numberWord, sub_sub_cancel]
    · simp [Function.update_of_ne h, numberWord, h, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  have tensorOp_diagonal {N : ℕ} (f : Fin N → Bool → ℂ) :
      tensorProduct (fun k => Matrix.diagonal (f k)) =
        Matrix.diagonal (fun s => ∏ k : Fin N, f k (s k)) := by
    classical
    ext s t
    by_cases hst : s = t
    · subst t
      simp [tensorOp_entries, Matrix.diagonal_apply_eq]
    · simp only [Matrix.diagonal_apply, if_neg hst]
      simp only [tensorOp_entries]
      have hx : ∃ i, s i ≠ t i := by
        by_contra h
        push Not at h
        exact hst (funext h)
      obtain ⟨i,hi⟩ := hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.diagonal_apply,hi])
  classical
  have hw : D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.numberWord i =
      (fun k => Matrix.diagonal (fun b : Bool =>
        if k = i then (if b then (1 : ℂ) else 0) else 1)) := by
    funext k
    ext s t
    by_cases hk : k = i <;> cases s <;> cases t <;>
      norm_num [D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators.numberWord,spinP_def, visibleProjector,hk,
        Matrix.diagonal_apply,Matrix.sub_apply,Matrix.one_apply]
  rw [localOp_as_tensor]
  change (Matrix.submatrix (tensorProduct (numberWord i)) (Subtype.val : HardCore N → Assignment N) (Subtype.val : HardCore N → Assignment N)) = _
  rw [hw,tensorOp_diagonal]
  ext s t
  have hi : 0 < i.val + 1 ∧ i.val + 1 ≤ N := by omega
  have he : occupied s.val (i.val + 1) = s.val i := by simp [occupied,hi]
  simp [Matrix.submatrix,number,Matrix.diagonal_apply,he,Subtype.ext_iff]

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
