/- GID: D5/S3/Quantum/Fermionic/OrderedSlaterCut
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/OrderedSlaterCut
   mirror-E: none(waiver:uniform-occupation-shuffle-and-alternating-witness)
   anchors: []
   utility: none
   digest: Alternating-cut spectra and prefix transfer for Slater determinants. -/

import D5.S3.Quantum.Fermionic.SlaterCutPhase
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Fintype.Sort

/-! # Ordered Slater determinant marginals at a spatial cut -/

namespace D5.S3.Quantum.Fermionic.OrderedSlaterCut

open scoped BigOperators
open D5.S3.Quantum.Fermionic.SlaterCutPhase

private theorem sign_of_ordered_blocks {m n : ℕ} (σ : Equiv.Perm (Fin (m + n)))
    (hleft : StrictMono (fun i : Fin m => σ (Fin.castAdd n i)))
    (hright : StrictMono (fun j : Fin n => σ (Fin.natAdd m j))) :
    σ.sign = ∏ i : Fin m, ∏ j : Fin n,
      if σ (Fin.natAdd m j) < σ (Fin.castAdd n i) then -1 else 1 := by
  classical
  let factor (i j : Fin (m + n)) : ℤˣ := if i < j ∧ σ j < σ i then -1 else 1
  have hsign : σ.sign = ∏ i, ∏ j, factor i j := by
    rw [σ.sign_eq_prod_prod_Ioi]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Fintype.prod_ite_mem]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hij : i < j
    · have hne := σ.injective.ne hij.ne
      rcases lt_or_gt_of_ne hne with h | h
      · simp [factor, hij, h, not_lt_of_gt h]
      · simp [factor, hij, h, not_lt_of_gt h]
    · simp [factor, hij]
  have hcross (i : Fin m) (j : Fin n) : Fin.castAdd n i < Fin.natAdd m j := by
    change i.val < m + j.val
    omega
  have hll (i j : Fin m) : factor (Fin.castAdd n i) (Fin.castAdd n j) = 1 := by
    by_cases h : Fin.castAdd n i < Fin.castAdd n j
    · have hi : i < j := h
      simp [factor, not_lt_of_gt (hleft hi)]
    · simp [factor, h]
  have hrr (i j : Fin n) : factor (Fin.natAdd m i) (Fin.natAdd m j) = 1 := by
    by_cases h : Fin.natAdd m i < Fin.natAdd m j
    · have hi : i < j := (Fin.natAdd_lt_natAdd_iff m).mp h
      simp [factor, not_lt_of_gt (hright hi)]
    · simp [factor, h]
  have hrl (i : Fin n) (j : Fin m) : factor (Fin.natAdd m i) (Fin.castAdd n j) = 1 := by
    simp [factor, not_lt_of_gt (hcross j i)]
  rw [hsign, Fin.prod_univ_add]
  simp only [Fin.prod_univ_add (factor _), hll, hrr, hrl, Finset.prod_const_one, one_mul, mul_one]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  simp [factor, hcross i j]

section OccupiedMinors

variable {ι : Type*} [LinearOrder ι]

private def groupedRows (a b : Finset ι) (h : Disjoint a b) :
    Fin (a.card + b.card) ≃ a.disjUnion b h :=
  finSumFinEquiv.symm.trans
    (((a.orderIsoOfFin rfl).toEquiv.sumCongr (b.orderIsoOfFin rfl).toEquiv).trans
      (Equiv.Finset.disjUnionEquiv a b h))

private def rowShuffle (a b : Finset ι) (h : Disjoint a b) :
    Equiv.Perm (Fin (a.card + b.card)) :=
  (groupedRows a b h).trans
    ((a.disjUnion b h).orderIsoOfFin (Finset.card_disjUnion a b h)).symm.toEquiv

private theorem row_shuffle_sign (a b : Finset ι) (h : Disjoint a b) :
    (rowShuffle a b h).sign =
      (-1 : ℤˣ) ^ (∑ i ∈ a, ∑ j ∈ b, if j < i then 1 else 0) := by
  classical
  let σ := rowShuffle a b h
  let sorted := (a.disjUnion b h).orderIsoOfFin (Finset.card_disjUnion a b h)
  have left (i : Fin a.card) :
      (sorted (σ (Fin.castAdd b.card i)) : ι) = a.orderEmbOfFin rfl i := by
    simp [σ, rowShuffle, groupedRows, sorted, Finset.coe_orderIsoOfFin_apply]
  have right (j : Fin b.card) :
      (sorted (σ (Fin.natAdd a.card j)) : ι) = b.orderEmbOfFin rfl j := by
    simp [σ, rowShuffle, groupedRows, sorted, Finset.coe_orderIsoOfFin_apply]
  have hleft : StrictMono (fun i : Fin a.card => σ (Fin.castAdd b.card i)) := by
    intro i j hij
    apply sorted.strictMono.lt_iff_lt.mp
    change (sorted (σ (Fin.castAdd b.card i)) : ι) < (sorted (σ (Fin.castAdd b.card j)) : ι)
    rw [left, left]
    exact (a.orderEmbOfFin rfl).strictMono hij
  have hright : StrictMono (fun i : Fin b.card => σ (Fin.natAdd a.card i)) := by
    intro i j hij
    apply sorted.strictMono.lt_iff_lt.mp
    change (sorted (σ (Fin.natAdd a.card i)) : ι) < (sorted (σ (Fin.natAdd a.card j)) : ι)
    rw [right, right]
    exact (b.orderEmbOfFin rfl).strictMono hij
  have hcmp (i : Fin a.card) (j : Fin b.card) :
      σ (Fin.natAdd a.card j) < σ (Fin.castAdd b.card i) ↔
        b.orderEmbOfFin rfl j < a.orderEmbOfFin rfl i := by
    rw [← sorted.strictMono.lt_iff_lt]
    change (sorted (σ (Fin.natAdd a.card j)) : ι) < (sorted (σ (Fin.castAdd b.card i)) : ι) ↔ _
    rw [right, left]
  change σ.sign = _
  rw [sign_of_ordered_blocks σ hleft hright]
  simp_rw [hcmp]
  have hpow (p : Prop) [Decidable p] :
      (if p then (-1 : ℤˣ) else 1) = (-1 : ℤˣ) ^ (if p then 1 else 0) := by
    split <;> simp
  simp_rw [hpow, Finset.prod_pow_eq_pow_sum]
  congr 1
  have reindex (s : Finset ι) (f : ι → ℕ) :
      (∑ i : Fin s.card, f (s.orderEmbOfFin rfl i)) = ∑ i ∈ s, f i := by
    calc
      _ = ∑ i : s, f i := Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv _ _ (by intro i; rfl)
      _ = _ := by simpa using Finset.sum_attach s f
  rw [reindex a (fun i => ∑ j : Fin b.card, if b.orderEmbOfFin rfl j < i then 1 else 0)]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact reindex b (fun j => if j < i then 1 else 0)

/-- Grouping occupied rows by a cut changes the increasing-row minor by the
sign of the occupied cross inversions. The order on each side is preserved. -/
private theorem grouped_minor {R : Type*} [CommRing R] (a b : Finset ι)
    (h : Disjoint a b) (V : Matrix ι (Fin (a.card + b.card)) R) :
    (V.submatrix (fun i => (groupedRows a b h i : ι)) id).det =
      (-1 : R) ^ (∑ i ∈ a, ∑ j ∈ b, if j < i then 1 else 0) *
        (V.submatrix ((a.disjUnion b h).orderEmbOfFin (Finset.card_disjUnion a b h)) id).det := by
  let sorted := (a.disjUnion b h).orderIsoOfFin (Finset.card_disjUnion a b h)
  let M : Matrix (Fin (a.card + b.card)) (Fin (a.card + b.card)) R :=
    V.submatrix (fun i => (sorted i : ι)) id
  have hrows : V.submatrix (fun i => (groupedRows a b h i : ι)) id =
      M.submatrix (rowShuffle a b h) id := by
    ext i j
    change V (groupedRows a b h i : ι) j =
      V (sorted (sorted.symm (groupedRows a b h i)) : ι) j
    rw [sorted.apply_symm_apply]
  rw [hrows, Matrix.det_permute, row_shuffle_sign]
  have hm : M = V.submatrix ((a.disjUnion b h).orderEmbOfFin
      (Finset.card_disjUnion a b h)) id := rfl
  rw [← hm]
  simp

private noncomputable def orderedAmplitude {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (a b : Finset ι) (hd : Disjoint a b) : ℂ :=
  if h : a.card + b.card = k then
    (V.submatrix ((a.disjUnion b hd).orderEmbOfFin
      ((Finset.card_disjUnion a b hd).trans h)) id).det
  else 0

private noncomputable def groupedAmplitude {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (a b : Finset ι) (hd : Disjoint a b) : ℂ :=
  if h : a.card + b.card = k then
    (V.submatrix (fun i => (groupedRows a b hd (Fin.cast h.symm i) : ι)) id).det
  else 0

private theorem grouped_amplitude_eq_signed {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (a b : Finset ι) (hd : Disjoint a b) :
    groupedAmplitude V a b hd = (-1 : ℂ) ^ crossCount a b * orderedAmplitude V a b hd := by
  by_cases h : a.card + b.card = k
  · subst k
    simpa [groupedAmplitude, orderedAmplitude, crossCount] using grouped_minor a b hd V
  · simp [groupedAmplitude, orderedAmplitude, h]

/-- Relabeling a stable partition as two consecutive blocks gives the same
occupied minor as listing the occupied rows of the retained side first. -/
private theorem ordered_amplitude_of_block_relabeling {κ : Type*} [LinearOrder κ]
    (e : ι ≃ κ) (a b : Finset ι) (hd : Disjoint a b)
    (ha : ∀ x ∈ a, ∀ y ∈ a, x < y → e x < e y)
    (hb : ∀ x ∈ b, ∀ y ∈ b, x < y → e x < e y)
    (hab : ∀ x ∈ a, ∀ y ∈ b, e x < e y)
    {k : ℕ} (V : Matrix ι (Fin k) ℂ) :
    orderedAmplitude (V.submatrix e.symm id) (a.map e.toEmbedding) (b.map e.toEmbedding)
      ((Finset.disjoint_map e.toEmbedding).mpr hd) = groupedAmplitude V a b hd := by
  let a' := a.map e.toEmbedding
  let b' := b.map e.toEmbedding
  let hd' : Disjoint a' b' := (Finset.disjoint_map e.toEmbedding).mpr hd
  change orderedAmplitude (V.submatrix e.symm id) a' b' hd' = _
  have hcard : a'.card + b'.card = a.card + b.card := by simp [a', b']
  by_cases hk : a.card + b.card = k
  · have hk' := hcard.trans hk
    have hrows : (fun i : Fin k => e (groupedRows a b hd (Fin.cast hk.symm i))) =
        (a'.disjUnion b' hd').orderEmbOfFin ((Finset.card_disjUnion a' b' hd').trans hk') := by
      apply Finset.orderEmbOfFin_unique
      · intro i
        have hi := (groupedRows a b hd (Fin.cast hk.symm i)).2
        rcases Finset.mem_disjUnion.mp hi with hi | hi
        · exact Finset.mem_disjUnion.mpr (Or.inl (Finset.mem_map.mpr ⟨_, hi, rfl⟩))
        · exact Finset.mem_disjUnion.mpr (Or.inr (Finset.mem_map.mpr ⟨_, hi, rfl⟩))
      · suffices hs : StrictMono (fun i => e (groupedRows a b hd i)) from
          hs.comp (Fin.cast_strictMono _)
        have left (i : Fin a.card) :
            (groupedRows a b hd (Fin.castAdd b.card i) : ι) = a.orderEmbOfFin rfl i := by
          simp [groupedRows, Finset.coe_orderIsoOfFin_apply]
        have right (i : Fin b.card) :
            (groupedRows a b hd (Fin.natAdd a.card i) : ι) = b.orderEmbOfFin rfl i := by
          simp [groupedRows, Finset.coe_orderIsoOfFin_apply]
        intro i j hij
        induction i using Fin.addCases with
        | left i =>
          induction j using Fin.addCases with
          | left j =>
            simp only [left]
            exact ha _ (a.orderEmbOfFin_mem rfl i) _ (a.orderEmbOfFin_mem rfl j)
              ((a.orderEmbOfFin rfl).strictMono (show i < j from hij))
          | right j =>
            simp only [left, right]
            exact hab _ (a.orderEmbOfFin_mem rfl i) _ (b.orderEmbOfFin_mem rfl j)
        | right i =>
          induction j using Fin.addCases with
          | left j =>
            change a.card + i.val < j.val at hij
            omega
          | right j =>
            simp only [right]
            exact hb _ (b.orderEmbOfFin_mem rfl i) _ (b.orderEmbOfFin_mem rfl j)
              ((b.orderEmbOfFin rfl).strictMono ((Fin.natAdd_lt_natAdd_iff a.card).mp hij))
    unfold orderedAmplitude groupedAmplitude
    rw [dite_eq_left hk', dite_eq_left hk]
    congr 1
    ext i j
    change V (e.symm ((a'.disjUnion b' hd').orderEmbOfFin _ i)) j =
      V (groupedRows a b hd (Fin.cast hk.symm i)) j
    rw [← congrFun hrows i, e.symm_apply_apply]
  · simp [orderedAmplitude, groupedAmplitude, hcard, hk]

end OccupiedMinors

private noncomputable def orbitalEntry {ι : Type*} [DecidableEq ι] (sites : Finset ι) (i : ι) : ℂ :=
  if i ∈ sites then ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) else 0

private noncomputable def pairedOrbitals {ι : Type*} [DecidableEq ι] (a b : Finset ι) :
    Matrix ι (Fin 2) ℂ :=
  fun i j => orbitalEntry (if j = 0 then a else b) i

private theorem halfRoot_mul :
    ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) * ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) =
      (1 : ℂ) / 2 := by
  have hp := Real.sq_sqrt (show 0 ≤ (1 : ℝ) / 2 by positivity)
  rw [pow_two] at hp
  rw [← Complex.ofReal_mul, hp, Complex.ofReal_div, Complex.ofReal_one]
  norm_num

private theorem orbital_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Finset ι) :
    (∑ i, star (orbitalEntry s i) * orbitalEntry t i) =
      ((s ∩ t).card : ℂ) / 2 := by
  calc
    _ = ∑ i, if i ∈ s ∩ t then (1 : ℂ) / 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have hstar : star ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) =
          ((Real.sqrt ((1 : ℝ) / 2) : ℝ) : ℂ) := by simp
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
        simp only [orbitalEntry, hs, ht, Finset.mem_inter, ite_true, ite_false, true_and,
          false_and, and_false, star_zero, zero_mul, mul_zero, hstar, halfRoot_mul]
    _ = _ := by
      rw [Fintype.sum_ite_mem]
      simp [div_eq_mul_inv, nsmul_eq_mul]

/-- Two disjoint two-site supports give orthonormal columns over the entire site type. -/
private theorem paired_orbitals_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : Finset ι) (ha : a.card = 2) (hb : b.card = 2) (h : Disjoint a b) :
    (pairedOrbitals a b).conjTranspose * pairedOrbitals a b = 1 := by
  have hab : a ∩ b = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h
  have hba : b ∩ a = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h.symm
  ext i j
  change (∑ l, star (orbitalEntry (if i = 0 then a else b) l) *
    orbitalEntry (if j = 0 then a else b) l) = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [orbital_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.one_apply, ha, hb, hab, hba]

private noncomputable def grouped : Matrix (Fin 2) (Fin 2) ℂ := fun _ _ => 1 / 2

private noncomputable def signed {ι : Type*} [LinearOrder ι]
    (a b : Fin 2 → ι) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (-1 : ℂ) ^ crossCount {a i} {b j} * grouped i j

private theorem groupedGram_charpoly :
    (grouped * grouped.conjTranspose).charpoly =
      Polynomial.X * (Polynomial.X - 1) := by
  have ht : (grouped * grouped.conjTranspose).trace = 1 := by
    rw [Matrix.trace_fin_two]
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, grouped]
  have hd : grouped.det = 0 := by simp [Matrix.det_fin_two, grouped]
  rw [Matrix.charpoly_fin_two, Matrix.det_mul, hd, zero_mul, ht]
  simp [pow_two, mul_sub]

private theorem distinct_padded_spectra (n m : ℕ) :
    Polynomial.X ^ n * (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 ≠
      Polynomial.X ^ m * (Polynomial.X - 1) := by
  intro h
  have he := congrArg (Polynomial.eval (1 : ℂ)) h
  norm_num [pow_two] at he

private def embedMatrix {ι κ : Type*} [DecidableEq ι] (e : κ ↪ ι) : Matrix ι κ ℂ :=
  fun i j => if i = e j then 1 else 0

private theorem embed_adjoint_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (e : κ ↪ ι) :
    (embedMatrix e).conjTranspose * embedMatrix e = 1 := by
  classical
  ext i j
  change (∑ k, star (if k = e i then (1 : ℂ) else 0) *
      (if k = e j then 1 else 0)) = (1 : Matrix κ κ ℂ) i j
  calc
    _ = ∑ k, if k = e i then (if i = j then (1 : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = e i
      · subst k
        simp [e.injective.eq_iff]
      · simp [h]
    _ = _ := by simp [Matrix.one_apply]

private theorem paddedGram_charpoly {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq α]
    (e : α ↪ ι) (f : β ↪ κ) (B : Matrix α β ℂ) :
    let padded := embedMatrix e * B * (embedMatrix f).conjTranspose
    (padded * padded.conjTranspose).charpoly =
      Polynomial.X ^ (Fintype.card ι - Fintype.card α) * (B * B.conjTranspose).charpoly := by
  classical
  intro padded
  let E := embedMatrix e
  let F := embedMatrix f
  have hE : E.conjTranspose * E = 1 := embed_adjoint_mul e
  have hF : F.conjTranspose * F = 1 := embed_adjoint_mul f
  have hm : padded * padded.conjTranspose = E * ((B * B.conjTranspose) * E.conjTranspose) := by
    change (E * B * F.conjTranspose) * (E * B * F.conjTranspose).conjTranspose = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc (E * B), ← Matrix.mul_assoc F.conjTranspose, hF, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  rw [hm, Matrix.charpoly_mul_comm_of_le E _ (Fintype.card_le_of_injective e e.injective)]
  rw [Matrix.mul_assoc (B * B.conjTranspose) E.conjTranspose E, hE, Matrix.mul_one]

/-- In a nonzero determinant, each occupied site lies in one of the two orbital supports. -/
private theorem grouped_nonzero_supported {ι : Type*} [LinearOrder ι]
    (s t a b : Finset ι) (hd : Disjoint a b)
    (hne : groupedAmplitude (pairedOrbitals s t) a b hd ≠ 0) :
    a ∪ b ⊆ s ∪ t := by
  intro x hx
  by_contra hxt
  apply hne
  by_cases h : a.card + b.card = 2
  · rw [groupedAmplitude, dite_eq_left h]
    let i := (groupedRows a b hd).symm
      ⟨x, Finset.mem_disjUnion.mpr (Finset.mem_union.mp hx)⟩
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.cast h i)
    intro j
    have hsite : (groupedRows a b hd i : ι) = x := by
      simp [i]
    change pairedOrbitals s t
      (groupedRows a b hd (Fin.cast h.symm (Fin.cast h i))) j = 0
    rw [Fin.cast_cast, Fin.cast_eq_self, hsite]
    have hs : x ∉ s := fun hm => hxt (Finset.mem_union_left _ hm)
    have ht : x ∉ t := fun hm => hxt (Finset.mem_union_right _ hm)
    by_cases hj : j = 0 <;> simp [pairedOrbitals, orbitalEntry, hj, hs, ht]
  · simp [groupedAmplitude, h]

/-- If the orbital supports lie on opposite sides, a nonzero entry has one particle
on each side and each particle lies in the corresponding support. -/
private theorem grouped_nonzero_singletons {ι : Type*} [LinearOrder ι] {I : Set ι}
    (s t a b : Finset ι) (hd : Disjoint a b)
    (hs : (↑s : Set ι) ⊆ I) (ht : (↑t : Set ι) ⊆ Iᶜ)
    (ha : (↑a : Set ι) ⊆ I) (hb : (↑b : Set ι) ⊆ Iᶜ)
    (hne : groupedAmplitude (pairedOrbitals s t) a b hd ≠ 0) :
    ∃ x ∈ s, ∃ y ∈ t, a = {x} ∧ b = {y} := by
  classical
  have hsupp := grouped_nonzero_supported s t a b hd hne
  have hsa : a ⊆ s := by
    intro x hx
    rcases Finset.mem_union.mp (hsupp (Finset.mem_union_left b hx)) with hx' | hx'
    · exact hx'
    · exact False.elim (ht hx' (ha hx))
  have htb : b ⊆ t := by
    intro x hx
    rcases Finset.mem_union.mp (hsupp (Finset.mem_union_right a hx)) with hx' | hx'
    · exact False.elim (hb hx (hs hx'))
    · exact hx'
  have hc : a.card + b.card = 2 := by
    by_contra hh
    exact hne (by simp [groupedAmplitude, hh])
  have hz (c : Fin 2) (hzero : ∀ x ∈ a ∪ b, pairedOrbitals s t x c = 0) : False := by
    apply hne
    rw [groupedAmplitude, dite_eq_left hc]
    apply Matrix.det_eq_zero_of_column_eq_zero c
    intro i
    let row := groupedRows a b hd (Fin.cast hc.symm i)
    exact hzero row (by simpa only [Finset.mem_disjUnion, Finset.mem_union] using row.2)
  have hapos : 0 < a.card := by
    by_contra! hh
    have he : a = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
    apply hz 0
    intro x hx
    have hxb : x ∈ b := by simpa [he] using hx
    have hxs : x ∉ s := fun hm => hb hxb (hs hm)
    simp [pairedOrbitals, orbitalEntry, hxs]
  have hbpos : 0 < b.card := by
    by_contra! hh
    have he : b = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
    apply hz 1
    intro x hx
    have hxa : x ∈ a := by simpa [he] using hx
    have hxt : x ∉ t := fun hm => ht hm (ha hxa)
    norm_num [pairedOrbitals, orbitalEntry, hxt]
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show a.card = 1 by omega)
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (show b.card = 1 by omega)
  exact ⟨x, hsa (Finset.mem_singleton_self x), y, htb (Finset.mem_singleton_self y), rfl, rfl⟩

private theorem grouped_singletons {ι : Type*} [LinearOrder ι] (V : Matrix ι (Fin 2) ℂ)
    (x y : ι) (hd : Disjoint ({x} : Finset ι) {y}) :
    groupedAmplitude V {x} {y} hd =
      V x 0 * V y 1 - V x 1 * V y 0 := by
  let a : Finset ι := {x}
  let b : Finset ι := {y}
  have hc : a.card + b.card = 2 := by simp [a, b]
  let left : Fin a.card := ⟨0, by simp [a]⟩
  let right : Fin b.card := ⟨0, by simp [b]⟩
  have h0 : Fin.cast hc.symm (0 : Fin 2) = Fin.castAdd b.card left := by
    apply Fin.ext
    rfl
  have h1 : Fin.cast hc.symm (1 : Fin 2) = Fin.natAdd a.card right := by
    apply Fin.ext
    simp [a, right]
  have hrow0 : (groupedRows a b hd (Fin.cast hc.symm (0 : Fin 2)) : ι) = x := by
    rw [h0]
    simp [groupedRows, Finset.coe_orderIsoOfFin_apply, a]
    exact Finset.mem_singleton.mp (a.orderEmbOfFin_mem rfl left)
  have hrow1 : (groupedRows a b hd (Fin.cast hc.symm (1 : Fin 2)) : ι) = y := by
    rw [h1]
    simp [groupedRows, Finset.coe_orderIsoOfFin_apply, b]
    exact Finset.mem_singleton.mp (b.orderEmbOfFin_mem rfl right)
  change groupedAmplitude V a b hd = _
  rw [groupedAmplitude, dite_eq_left hc, Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, id_eq, hrow0, hrow1]

private theorem grouped_singleton_orbitals {ι : Type*} [LinearOrder ι]
    {s t : Finset ι} {x y : ι} (hdisj : Disjoint s t) (hx : x ∈ s) (hy : y ∈ t)
    (hd : Disjoint ({x} : Finset ι) {y}) :
    groupedAmplitude (pairedOrbitals s t) {x} {y} hd = (1 : ℂ) / 2 := by
  have hxt : x ∉ t := fun hm => Finset.disjoint_left.mp hdisj hx hm
  have hys : y ∉ s := fun hm => Finset.disjoint_left.mp hdisj hm hy
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [grouped_singletons]
  simp only [pairedOrbitals, orbitalEntry, hx, hy, hxt, hys, ite_true, ite_false,
    zero_mul, sub_zero, h10, halfRoot_mul]

private theorem eq_padding {ι κ α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq ι] [DecidableEq κ]
    (e : α ↪ ι) (f : β ↪ κ) (M : Matrix ι κ ℂ) (A : Matrix α β ℂ)
    (active : ∀ i j, M (e i) (f j) = A i j)
    (row : ∀ i j, (¬ ∃ a, e a = i) → M i j = 0)
    (column : ∀ i j, (¬ ∃ b, f b = j) → M i j = 0) :
    M = embedMatrix e * A * (embedMatrix f).conjTranspose := by
  classical
  ext i j
  by_cases hrow : ∃ a, e a = i
  · obtain ⟨a, rfl⟩ := hrow
    by_cases hcol : ∃ b, f b = j
    · obtain ⟨b, rfl⟩ := hcol
      rw [active]
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedMatrix, e.injective.eq_iff,
        f.injective.eq_iff]
    · rw [column _ _ hcol]
      have hne (b : β) : j ≠ f b := fun h => hcol ⟨b, h.symm⟩
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedMatrix, hne]
  · rw [row _ _ hrow]
    have hne (a : α) : i ≠ e a := fun h => hrow ⟨a, h.symm⟩
    simp [Matrix.mul_apply, embedMatrix, hne]

abbrev Occupation {ι : Type*} (I : Set ι) :=
  {a : Finset ι // (↑a : Set ι) ⊆ I}

noncomputable local instance {ι : Type*} [Fintype ι] (I : Set ι) : Fintype (Occupation I) :=
  Fintype.ofFinite _

noncomputable local instance {ι : Type*} [Fintype ι] (I : Set ι) : Fintype I :=
  Fintype.ofFinite _

def retainedRows {ι : Type*} (I : Set ι) {k : ℕ} (V : Matrix ι (Fin k) ℂ) :
    Matrix I (Fin k) ℂ := V.submatrix Subtype.val id

private def occupySingle {ι : Type*} [DecidableEq ι] {I : Set ι}
    (v : Fin 2 ↪ ι) (hv : ∀ i, v i ∈ I) : Fin 2 ↪ Occupation I where
  toFun i := ⟨{v i}, by simpa using hv i⟩
  inj' := by
    intro i j hij
    apply v.injective
    exact Finset.singleton_injective (congrArg Subtype.val hij)

theorem cut_disjoint {ι : Type*} {I : Set ι} (a : Occupation I) (b : Occupation Iᶜ) :
    Disjoint a.1 b.1 :=
  Finset.disjoint_left.mpr fun _ ha hb => b.2 hb (a.2 ha)

noncomputable def orderedCut {ι : Type*} [LinearOrder ι] (I : Set ι) {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) : Matrix (Occupation I) (Occupation Iᶜ) ℂ :=
  fun a b => orderedAmplitude V a.1 b.1 (cut_disjoint a b)

noncomputable def groupedCut {ι : Type*} [LinearOrder ι] (I : Set ι) {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) : Matrix (Occupation I) (Occupation Iᶜ) ℂ :=
  fun a b => groupedAmplitude V a.1 b.1 (cut_disjoint a b)

/-- The grouped determinant differs from the ordered determinant by the shuffle sign. -/
theorem groupedCut_eq_signed {ι : Type*} [LinearOrder ι] {I : Set ι} {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) (a : Occupation I) (b : Occupation Iᶜ) :
    groupedCut I V a b = (-1 : ℂ) ^ crossCount a.val b.val * orderedCut I V a b :=
  grouped_amplitude_eq_signed V a.val b.val (cut_disjoint a b)

/-- The ordered determinant has support only at the prescribed particle number. -/
theorem orderedCut_eq_zero_of_card_ne {ι : Type*} [LinearOrder ι] {I : Set ι} {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) (a : Occupation I) (b : Occupation Iᶜ)
    (h : a.val.card + b.val.card ≠ k) : orderedCut I V a b = 0 := by
  simp [orderedCut, orderedAmplitude, h]

private theorem grouped_ordered_marginal_charpoly {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (h : ¬ Alternates I) {k : ℕ} (V : Matrix ι (Fin k) ℂ) :
    (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly := by
  classical
  have hphase : groupedCut I V = fun a b =>
      (-1 : ℂ) ^ crossCount a.1 b.1 * orderedCut I V a b := by
    ext a b
    exact groupedCut_eq_signed V a b
  rw [hphase]
  exact reduction_charpoly h Subtype.val Subtype.val (·.2) (·.2) k (orderedCut I V)
    (fun a b hab => orderedCut_eq_zero_of_card_ne V a b hab)

private def occupationCongr {ι κ : Type*} (e : ι ≃ κ) (I : Set ι) :
    Occupation I ≃ Occupation (e.symm ⁻¹' I) :=
  (e.finsetCongr).subtypeEquiv (fun a => by
    simp only [Equiv.finsetCongr_apply, Set.subset_def, Set.mem_preimage, Finset.mem_coe,
      Finset.mem_map_equiv]
    exact ⟨fun h i hi => h (e.symm i) hi, fun h i hi => by simpa using h (e i) (by simpa using hi)⟩)

private theorem groupedCut_relabeling {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (e : ι ≃ κ) (I : Set ι) (hI : StrictMonoOn e I) (hJ : StrictMonoOn e Iᶜ)
    (hIJ : ∀ x ∈ I, ∀ y ∈ Iᶜ, e x < e y)
    {k : ℕ} (V : Matrix ι (Fin k) ℂ) :
    (orderedCut (e.symm ⁻¹' I) (V.submatrix e.symm id)).submatrix
      (occupationCongr e I) (occupationCongr e Iᶜ) = groupedCut I V := by
  ext a b
  exact ordered_amplitude_of_block_relabeling e a.1 b.1
    (cut_disjoint a b) (fun _ hx _ hy hxy => hI (a.2 hx) (a.2 hy) hxy)
    (fun _ hx _ hy hxy => hJ (b.2 hx) (b.2 hy) hxy)
    (fun x hx y hy => hIJ x (a.2 hx) y (b.2 hy)) V

private noncomputable def prefixOrder {ι : Type*} [LinearOrder ι] [Fintype ι] (I : Set ι) :
    Fin (Fintype.card I + Fintype.card (Iᶜ : Set ι)) ≃ ι := by
  classical
  exact finSumFinEquiv.symm.trans
    (((monoEquivOfFin I rfl).toEquiv.sumCongr (monoEquivOfFin (Iᶜ : Set ι) rfl).toEquiv).trans
      (Equiv.Set.sumCompl I))

private theorem prefixOrder_left {ι : Type*} [LinearOrder ι] [Fintype ι]
    (I : Set ι) (i : Fin (Fintype.card I)) :
    prefixOrder I (Fin.castAdd (Fintype.card (Iᶜ : Set ι)) i) =
      (monoEquivOfFin I rfl i : ι) := by
  classical
  simp [prefixOrder]

private theorem prefixOrder_right {ι : Type*} [LinearOrder ι] [Fintype ι]
    (I : Set ι) (j : Fin (Fintype.card (Iᶜ : Set ι))) :
    prefixOrder I (Fin.natAdd (Fintype.card I) j) =
      (monoEquivOfFin (Iᶜ : Set ι) rfl j : ι) := by
  classical
  simp [prefixOrder]

private theorem prefixOrder_symm_left {ι : Type*} [LinearOrder ι] [Fintype ι]
    (I : Set ι) (i : I) :
    (prefixOrder I).symm i = Fin.castAdd (Fintype.card (Iᶜ : Set ι))
      ((monoEquivOfFin I rfl).symm i) := by
  apply (prefixOrder I).injective
  rw [Equiv.apply_symm_apply, prefixOrder_left, OrderIso.apply_symm_apply]

private theorem prefixOrder_symm_right {ι : Type*} [LinearOrder ι] [Fintype ι]
    (I : Set ι) (j : (Iᶜ : Set ι)) :
    (prefixOrder I).symm j = Fin.natAdd (Fintype.card I)
      ((monoEquivOfFin (Iᶜ : Set ι) rfl).symm j) := by
  apply (prefixOrder I).injective
  rw [Equiv.apply_symm_apply, prefixOrder_right, OrderIso.apply_symm_apply]

private theorem prefixOrder_preimage {ι : Type*} [LinearOrder ι] [Fintype ι]
    (I : Set ι) :
    (prefixOrder I) ⁻¹' I = {i | i.val < Fintype.card I} := by
  ext i
  induction i using Fin.addCases with
  | left i =>
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, prefixOrder_left, Fin.val_castAdd]
    exact iff_of_true (monoEquivOfFin I rfl i).2 i.isLt
  | right j =>
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, prefixOrder_right, Fin.val_natAdd]
    exact iff_of_false (monoEquivOfFin (Iᶜ : Set ι) rfl j).2 (by omega)

/-- Grouping a cut is a genuine ordered-prefix marginal after relabeling both
occupation carriers. The characteristic polynomial retains all zero modes. -/
private theorem groupedCut_prefix_charpoly {ι : Type*} [LinearOrder ι] [Fintype ι] (I : Set ι)
    {k : ℕ} (V : Matrix ι (Fin k) ℂ) :
    let W := V.submatrix (prefixOrder I) id
    let P : Set (Fin (Fintype.card I + Fintype.card (Iᶜ : Set ι))) := {i | i.val < Fintype.card I}
    W.conjTranspose * W = V.conjTranspose * V ∧
    (orderedCut P W * (orderedCut P W).conjTranspose).charpoly =
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly := by
  classical
  intro W P
  constructor
  · change (V.submatrix (prefixOrder I) id).conjTranspose *
      V.submatrix (prefixOrder I) id = V.conjTranspose * V
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hI : StrictMonoOn (prefixOrder I).symm I := by
    intro x hx y hy hxy
    rw [prefixOrder_symm_left I ⟨x, hx⟩, prefixOrder_symm_left I ⟨y, hy⟩]
    exact (monoEquivOfFin I rfl).symm.strictMono hxy
  have hJ : StrictMonoOn (prefixOrder I).symm Iᶜ := by
    intro x hx y hy hxy
    rw [prefixOrder_symm_right I ⟨x, hx⟩, prefixOrder_symm_right I ⟨y, hy⟩]
    exact (Fin.natAdd_lt_natAdd_iff _).mpr ((monoEquivOfFin (Iᶜ : Set ι) rfl).symm.strictMono hxy)
  have hIJ : ∀ x ∈ I, ∀ y ∈ Iᶜ, (prefixOrder I).symm x < (prefixOrder I).symm y := by
    intro x hx y hy
    rw [prefixOrder_symm_left I ⟨x, hx⟩, prefixOrder_symm_right I ⟨y, hy⟩]
    change ((monoEquivOfFin I rfl).symm ⟨x, hx⟩).val <
      Fintype.card I + ((monoEquivOfFin (Iᶜ : Set ι) rfl).symm ⟨y, hy⟩).val
    omega
  have hp : (prefixOrder I) ⁻¹' I = P := prefixOrder_preimage I
  change (orderedCut P W * (orderedCut P W).conjTranspose).charpoly = _
  rw [← hp]
  let e := (prefixOrder I).symm
  let A := orderedCut (e.symm ⁻¹' I) W
  let row := occupationCongr e I
  let col := occupationCongr e Iᶜ
  change (A * A.conjTranspose).charpoly = _
  rw [← groupedCut_relabeling e I hI hJ hIJ V]
  change _ = ((A.submatrix row col) * (A.submatrix row col).conjTranspose).charpoly
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (Matrix.charpoly_reindex row.symm (A * A.conjTranspose)).symm

private theorem orderedCut_apply {ι : Type*} [LinearOrder ι] {I : Set ι} {k : ℕ}
    (V : Matrix ι (Fin k) ℂ) (a : Occupation I) (b : Occupation Iᶜ) :
    orderedCut I V a b = (-1 : ℂ) ^ crossCount a.1 b.1 * groupedCut I V a b := by
  rw [groupedCut, grouped_amplitude_eq_signed]
  change _ = _ * (_ * orderedCut I V a b)
  rw [← mul_assoc, ← mul_pow]
  simp

private theorem compression_charpoly {ι : Type*} [LinearOrder ι] [Fintype ι] {I : Set ι}
    (v w : Fin 2 ↪ ι) (hv : ∀ i, v i ∈ I) (hw : ∀ i, w i ∈ Iᶜ) :
    let X := retainedRows I (pairedOrbitals (Finset.univ.image v) (Finset.univ.image w))
    (X * X.conjTranspose).charpoly =
      Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) := by
  classical
  intro X
  let vi : Fin 2 ↪ I := ⟨fun i => ⟨v i, hv i⟩, fun _ _ hij =>
    v.injective (congrArg Subtype.val hij)⟩
  let s := Finset.univ.image vi
  have hs : s.card = 2 := by simp [s, Finset.card_image_of_injective _ vi.injective]
  have first (i : I) : X i 0 = orbitalEntry s i := by
    have hm : i.1 ∈ Finset.univ.image v ↔ i ∈ s := by
      simp only [s, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨j, hj⟩ => ⟨j, Subtype.ext hj⟩, fun ⟨j, hj⟩ => ⟨j, congrArg Subtype.val hj⟩⟩
    simp [X, retainedRows, pairedOrbitals, orbitalEntry, hm]
  have second (i : I) : X i 1 = 0 := by
    have hm : i.1 ∉ Finset.univ.image w := by
      rintro h
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      exact hw j (hj.symm ▸ i.2)
    norm_num [X, retainedRows, pairedOrbitals, orbitalEntry, hm]
  have hinner : X.conjTranspose * X = Matrix.diagonal (![1, 0] : Fin 2 → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        first, second]
    change (∑ i, star (orbitalEntry s i) * orbitalEntry s i) = 1
    rw [orbital_inner]
    norm_num [hs]
  have hcard := Fintype.card_le_of_injective vi vi.injective
  simp only [Fintype.card_fin] at hcard
  rw [Matrix.charpoly_mul_comm_of_le X X.conjTranspose, hinner, Matrix.charpoly_diagonal]
  · rw [show Fintype.card I - 1 = Fintype.card I - 2 + 1 by omega, pow_succ]
    simp [Fin.prod_univ_two, mul_assoc, mul_left_comm, mul_comm]
  · simpa using hcard

private theorem orthonormal_cut_obstruction {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (v w : Fin 2 ↪ ι)
    (hv : ∀ i, v i ∈ I) (hw : ∀ i, w i ∈ Iᶜ)
    (hminor : (signed v w * (signed v w).conjTranspose).charpoly =
      (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2) :
    ∃ V : Matrix ι (Fin 2) ℂ, V.conjTranspose * V = 1 ∧
      ((retainedRows I V) * (retainedRows I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) ∧
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 1) * (Polynomial.X - 1) ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 2) *
          (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 ∧
      V = pairedOrbitals (Finset.univ.image v) (Finset.univ.image w) := by
  classical
  let s := Finset.univ.image v
  let t := Finset.univ.image w
  have hs : (↑s : Set ι) ⊆ I := by
    rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hv j
  have ht : (↑t : Set ι) ⊆ Iᶜ := by
    rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hw j
  have hst : Disjoint s t := Finset.disjoint_left.mpr fun _ hi hj => ht hj (hs hi)
  have hsc : s.card = 2 := by simp [s, Finset.card_image_of_injective _ v.injective]
  have htc : t.card = 2 := by simp [t, Finset.card_image_of_injective _ w.injective]
  let V := pairedOrbitals s t
  let e := occupySingle v hv
  let f := occupySingle w hw
  have hsupport (a : Occupation I) (b : Occupation Iᶜ) (hn : groupedCut I V a b ≠ 0) :
      (∃ i, e i = a) ∧ (∃ j, f j = b) := by
    obtain ⟨x, hx, y, hy, ha, hb⟩ :=
      grouped_nonzero_singletons s t a.1 b.1 (cut_disjoint a b) hs ht a.2 b.2 hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨i, Subtype.ext ha.symm⟩, ⟨j, Subtype.ext hb.symm⟩⟩
  have hentry (i j) : groupedCut I V (e i) (f j) = grouped i j :=
    grouped_singleton_orbitals hst (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)) (cut_disjoint (e i) (f j))
  have hrow (a b) (ha : ¬ ∃ i, e i = a) : groupedCut I V a b = 0 := by
    by_contra h
    exact ha (hsupport a b h).1
  have hcol (a b) (hb : ¬ ∃ j, f j = b) : groupedCut I V a b = 0 := by
    by_contra h
    exact hb (hsupport a b h).2
  have hg := eq_padding e f (groupedCut I V) grouped hentry hrow hcol
  have ho := eq_padding e f (orderedCut I V) (signed v w)
    (fun i j => by rw [orderedCut_apply, hentry]; rfl)
    (fun a b ha => by rw [orderedCut_apply, hrow a b ha, mul_zero])
    (fun a b hb => by rw [orderedCut_apply, hcol a b hb, mul_zero])
  refine ⟨V, paired_orbitals_orthonormal s t hsc htc hst,
    compression_charpoly v w hv hw, ?_, ?_, rfl⟩
  · rw [hg, paddedGram_charpoly e f grouped, groupedGram_charpoly,
      ← mul_assoc, ← pow_succ]
    have hcard := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_fin] at hcard ⊢
    congr 2
    omega
  · rw [ho, paddedGram_charpoly e f (signed v w), hminor, Fintype.card_fin]

private theorem alternatingActiveMinor {ι : Type*} [LinearOrder ι] {x y z w : ι}
    (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    let first := signed ![x, z] ![y, w]
    let second := signed ![y, w] ![x, z]
    (first * first.conjTranspose).charpoly = (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 ∧
    (second * second.conjTranspose).charpoly = (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 := by
  have hxw := hxy.trans (hyz.trans hzw)
  have hchar (A : Matrix (Fin 2) (Fin 2) ℂ)
      (h : A * A.conjTranspose = Matrix.diagonal (fun _ => (1 : ℂ) / 2)) :
      (A * A.conjTranspose).charpoly = (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 := by
    rw [h, Matrix.charpoly_diagonal]
    simp [pow_two]
  constructor
  · apply hchar
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signed, grouped, crossCount, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.diagonal_apply, Finset.filter_singleton, hyz, not_lt_of_gt hxy,
        not_lt_of_gt hxw, not_lt_of_gt hzw]
  · apply hchar
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [signed, grouped, crossCount, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.diagonal_apply, Finset.filter_singleton, hxy, hxw, hzw,
        not_lt_of_gt hyz]

private def pairEmbedding {ι : Type*} (a b : ι) (h : a ≠ b) : Fin 2 ↪ ι where
  toFun := ![a, b]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem pair_membership {ι : Type*} {I : Set ι} {a b : ι}
    (h : a ≠ b) (ha : a ∈ I) (hb : b ∈ I) (i : Fin 2) :
    pairEmbedding a b h i ∈ I := by
  fin_cases i
  · exact ha
  · exact hb

private theorem supported_pair_obstruction {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (v w : Fin 2 ↪ ι) (hv : ∀ i, v i ∈ I) (hw : ∀ i, w i ∈ Iᶜ)
    (hminor : (signed v w * (signed v w).conjTranspose).charpoly =
      (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2) :
    ∃ (A : Finset ι) (p : ι) (V : Matrix ι (Fin 2) ℂ),
      A.card = 4 ∧ p ∈ A ∧ p ∉ I ∧ V.conjTranspose * V = 1 ∧
      (∀ i ∉ I, V i 0 = 0) ∧ (∀ i ∈ I, V i 1 = 0) ∧
      (∀ i ∉ A, ∀ j, V i j = 0) ∧
      (retainedRows I V * (retainedRows I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) ∧
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 1) * (Polynomial.X - 1) ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 2) *
          (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 := by
  classical
  obtain ⟨V, hV, hc, hg, ho, hpair⟩ := orthonormal_cut_obstruction v w hv hw hminor
  let s := Finset.univ.image v
  let t := Finset.univ.image w
  have hs : (s : Set ι) ⊆ I := by
    rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hv j
  have ht : (t : Set ι) ⊆ Iᶜ := by
    rintro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hw j
  have hst : Disjoint s t := Finset.disjoint_left.mpr fun _ hi hj => ht hj (hs hi)
  have hsc : s.card = 2 := by simp [s, Finset.card_image_of_injective _ v.injective]
  have htc : t.card = 2 := by simp [t, Finset.card_image_of_injective _ w.injective]
  have hp : w 0 ∈ t := Finset.mem_image_of_mem _ (Finset.mem_univ (0 : Fin 2))
  change V = pairedOrbitals s t at hpair
  refine ⟨s ∪ t, w 0, V, ?_, Finset.mem_union_right s hp, hw 0, hV, ?_, ?_, ?_, hc, hg, ho⟩
  · rw [Finset.card_union_of_disjoint hst, hsc, htc]
  · intro i hi
    have hns : i ∉ s := fun h => hi (hs h)
    simp [hpair, pairedOrbitals, orbitalEntry, hns]
  · intro i hi
    have hnt : i ∉ t := fun h => ht h hi
    norm_num [hpair, pairedOrbitals, orbitalEntry, hnt]
  · intro i hi j
    have hns : i ∉ s := fun h => hi (Finset.mem_union_left _ h)
    have hnt : i ∉ t := fun h => hi (Finset.mem_union_right _ h)
    fin_cases j <;> norm_num [hpair, pairedOrbitals, orbitalEntry, hns, hnt]

/-- The two-orbital obstruction comes from a fixed set of four sites which
also contains a discarded coordinate choice for the retained-compression comparison. -/
theorem alternating_cut_supported_obstruction
    {ι : Type*} [LinearOrder ι] [Fintype ι] {I : Set ι} (h : Alternates I) :
    ∃ (A : Finset ι) (p : ι) (V : Matrix ι (Fin 2) ℂ),
      A.card = 4 ∧ p ∈ A ∧ p ∉ I ∧ V.conjTranspose * V = 1 ∧
      (∀ i ∉ I, V i 0 = 0) ∧ (∀ i ∈ I, V i 1 = 0) ∧
      (∀ i ∉ A, ∀ j, V i j = 0) ∧
      (retainedRows I V * (retainedRows I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) ∧
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 1) * (Polynomial.X - 1) ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 2) *
          (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 := by
  obtain ⟨x, y, z, w, hxy, hyz, hzw, hsites | hsites⟩ := h
  · obtain ⟨hx, hy, hz, hw⟩ := hsites
    let v := pairEmbedding x z (hxy.trans hyz).ne
    let u := pairEmbedding y w (hyz.trans hzw).ne
    exact supported_pair_obstruction v u
      (pair_membership _ hx hz) (pair_membership _ hy hw)
      (alternatingActiveMinor hxy hyz hzw).1
  · obtain ⟨hx, hy, hz, hw⟩ := hsites
    let v := pairEmbedding y w (hyz.trans hzw).ne
    let u := pairEmbedding x z (hxy.trans hyz).ne
    exact supported_pair_obstruction v u
      (pair_membership _ hy hw) (pair_membership _ hx hz)
      (alternatingActiveMinor hxy hyz hzw).2

/-- Alternation produces an orthonormal two-orbital Slater witness on the full cut. -/
theorem alternating_cut_obstruction {ι : Type*} [LinearOrder ι] [Fintype ι] {I : Set ι}
    (h : Alternates I) :
    ∃ V : Matrix ι (Fin 2) ℂ, V.conjTranspose * V = 1 ∧
      ((retainedRows I V) * (retainedRows I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card I - 1) * (Polynomial.X - 1) ∧
      (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 1) * (Polynomial.X - 1) ∧
      (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
        Polynomial.X ^ (Fintype.card (Occupation I) - 2) *
          (Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) ^ 2 := by
  obtain ⟨_, _, V, _, _, _, hV, _, _, _, hc, hg, ho⟩ :=
    alternating_cut_supported_obstruction h
  exact ⟨V, hV, hc, hg, ho⟩

open Polynomial in
private theorem one_nonzero_mode {α : Type*} [Fintype α] (ν : α → ℂ)
    (h : (∏ i : α, (X - C (ν i))) = X ^ (Fintype.card α - 1) * (X - 1)) :
    ∃ j, ν j = 1 ∧ ∀ i, i ≠ j → ν i = 0 := by
  classical
  let m := (Finset.univ : Finset α).val.map ν
  have hm : ((∏ i : α, (X - C (ν i))) : ℂ[X]).roots = m := by
    simpa only [m, Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_apply]
      using roots_multiset_prod_X_sub_C m
  have hfactor : (X - 1 : ℂ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℂ)
  have hval : m = (Fintype.card α - 1) • ({0} : Multiset ℂ) + {1} := by
    rw [← hm, h, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hfactor), roots_X_pow]
    rw [← C_1, roots_X_sub_C]
  have hcard : (Finset.univ.filter fun i => ν i = 1).card = 1 := by
    have hm1 : m.count 1 = 1 := by
      rw [hval]
      simp
    dsimp only [m] at hm1
    rw [Multiset.count_map] at hm1
    rw [Finset.card, Finset.filter_val]
    rw [Multiset.filter_congr
      (q := fun i => (1 : ℂ) = ν i) (fun _ _ => eq_comm)]
    exact hm1
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hs (i : α) : ν i = 1 ↔ i = j := by
    have hi : i ∈ Finset.univ.filter (fun t => ν t = 1) ↔ i ∈ ({j} : Finset α) := by
      rw [hj]
    simpa using hi
  refine ⟨j, (hs j).mpr rfl, fun i hi => ?_⟩
  have hm : ν i ∈ m := Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  rw [hval, Multiset.mem_add] at hm
  rcases hm with hm | hm
  · exact Multiset.mem_singleton.mp ((Multiset.mem_nsmul.mp hm).2)
  · exact False.elim (hi ((hs i).mp (Multiset.mem_singleton.mp hm)))

noncomputable def bernoulliWeight {ι : Type*} [LinearOrder ι] [Fintype ι] {I : Set ι}
    (ν : I → ℂ) (a : Occupation I) : ℂ :=
  ∏ i : I, if i.1 ∈ a.1 then ν i else 1 - ν i

private def siteCongr {ι κ : Type*} (e : ι ≃ κ) (I : Set ι) : I ≃ (e.symm ⁻¹' I : Set κ) :=
  e.subtypeEquiv fun i => by simp

private theorem bernoulliWeight_relabeling {ι κ : Type*}
    [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (I : Set ι) (ν : I → ℂ) (a : Occupation I) :
    bernoulliWeight (fun i => ν ((siteCongr e I).symm i)) (occupationCongr e I a) =
      bernoulliWeight ν a := by
  classical
  unfold bernoulliWeight
  symm
  apply Fintype.prod_equiv (siteCongr e I)
  intro i
  simp only [Equiv.symm_apply_apply]
  change (if i.1 ∈ a.1 then ν i else 1 - ν i) =
    (if e i.1 ∈ a.1.map e.toEmbedding then ν i else 1 - ν i)
  simp only [Finset.mem_map_equiv, e.symm_apply_apply]

/-- The product formula on all occupation sets, where the list of modes is
specified by the complete characteristic polynomial of the compression. -/
def HasProductSpectrum {ι : Type*} [LinearOrder ι] [Fintype ι]
    (I : Set ι) {k : ℕ} (V : Matrix ι (Fin k) ℂ) : Prop :=
  ∀ ν : I → ℂ,
    (retainedRows I V * (retainedRows I V).conjTranspose).charpoly =
      (∏ i : I, (Polynomial.X - Polynomial.C (ν i))) →
    (orderedCut I V * (orderedCut I V).conjTranspose).charpoly =
      (∏ a : Occupation I, (Polynomial.X - Polynomial.C (bernoulliWeight ν a)))

theorem grouped_product_from_prefix
    (hprefix : ∀ m n k : ℕ, ∀ W : Matrix (Fin (m + n)) (Fin k) ℂ,
      W.conjTranspose * W = 1 → HasProductSpectrum {i | i.val < m} W)
    {ι : Type*} [LinearOrder ι] [Fintype ι] (I : Set ι)
    {k : ℕ} (V : Matrix ι (Fin k) ℂ) (hV : V.conjTranspose * V = 1)
    (ν : I → ℂ) (hν : (retainedRows I V * (retainedRows I V).conjTranspose).charpoly =
      (∏ i : I, (Polynomial.X - Polynomial.C (ν i)))) :
    (groupedCut I V * (groupedCut I V).conjTranspose).charpoly =
      (∏ a : Occupation I, (Polynomial.X - Polynomial.C (bernoulliWeight ν a))) := by
  classical
  let e := (prefixOrder I).symm
  let W := V.submatrix e.symm id
  let J := e.symm ⁻¹' I
  let q := siteCongr e I
  let ν' : J → ℂ := fun i => ν (q.symm i)
  obtain ⟨hnorm, hgram⟩ := groupedCut_prefix_charpoly I V
  have hW : W.conjTranspose * W = 1 := hnorm.trans hV
  have hP := hprefix (Fintype.card I) (Fintype.card (Iᶜ : Set ι)) k W hW
  rw [← prefixOrder_preimage I] at hP hgram
  change HasProductSpectrum J W at hP
  have hcompression : retainedRows J W = (retainedRows I V).submatrix q.symm id := rfl
  have hν' : (retainedRows J W * (retainedRows J W).conjTranspose).charpoly =
      (∏ i : J, (Polynomial.X - Polynomial.C (ν' i))) := by
    rw [hcompression, Matrix.conjTranspose_submatrix]
    change ((retainedRows I V).submatrix q.symm (Equiv.refl _) *
      (retainedRows I V).conjTranspose.submatrix (Equiv.refl _) q.symm).charpoly = _
    rw [Matrix.submatrix_mul_equiv]
    change (Matrix.reindex q q (retainedRows I V * (retainedRows I V).conjTranspose)).charpoly = _
    rw [Matrix.charpoly_reindex, hν]
    exact Fintype.prod_equiv q _ _ (fun i => by simp [ν'])
  calc
    _ = (orderedCut J W * (orderedCut J W).conjTranspose).charpoly := hgram.symm
    _ = _ := hP ν' hν'
    _ = _ := (Fintype.prod_equiv (occupationCongr e I) _ _
      (fun a => by rw [bernoulliWeight_relabeling e I ν a])).symm

open Polynomial in
private theorem single_mode_bernoulli_charpoly {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (ν : I → ℂ)
    (h : (∏ i : I, (X - C (ν i))) = X ^ (Fintype.card I - 1) * (X - 1)) :
    (∏ a : Occupation I, (X - C (bernoulliWeight ν a))) =
      X ^ (Fintype.card (Occupation I) - 1) * (X - 1) := by
  classical
  obtain ⟨j, hj, h0⟩ := one_nonzero_mode ν h
  let single : Occupation I := ⟨{j.1}, by simp⟩
  have weight (a : Occupation I) : bernoulliWeight ν a = if a = single then 1 else 0 := by
    by_cases he : a = single
    · subst a
      rw [ite_eq_left rfl]
      unfold bernoulliWeight
      apply Finset.prod_eq_one
      intro i _
      by_cases hij : i = j
      · subst i
        simp [single, hj]
      · have hv : i.1 ≠ j.1 := fun hh => hij (Subtype.ext hh)
        simp [single, hv, h0 i hij]
    · rw [ite_eq_right he]
      unfold bernoulliWeight
      by_cases hja : j.1 ∈ a.1
      · have hex : ∃ i ∈ a.1, i ≠ j.1 := by
          by_contra! hn
          apply he
          apply Subtype.ext
          ext i
          constructor
          · intro hi
            exact Finset.mem_singleton.mpr (hn i hi)
          · intro hi
            simpa only [Finset.mem_singleton.mp hi] using hja
        obtain ⟨i, hi, hij⟩ := hex
        let l : I := ⟨i, a.2 hi⟩
        apply Finset.prod_eq_zero (Finset.mem_univ l)
        have hlj : l ≠ j := fun e => hij (congrArg Subtype.val e)
        simp [l, hi, h0 l hlj]
      · apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hja, hj]
  simp_rw [weight]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ single)]
  have hd : ∀ a ∈ (Finset.univ : Finset (Occupation I)) \ {single},
      X - C (if a = single then (1 : ℂ) else 0) = X := by
    intro a ha
    have hne : a ≠ single := by simpa using (Finset.mem_sdiff.mp ha).2
    simp [hne]
  rw [Finset.prod_congr rfl hd, Finset.prod_const]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [mul_comm]

open Polynomial in
/-- The two-particle witness defeats the product formula on both alternating orders.
The quantified mode labels cover every enumeration of the compression spectrum. -/
private theorem alternating_cut_bernoulli_obstruction {ι : Type*} [LinearOrder ι] [Fintype ι]
    {I : Set ι} (h : Alternates I) :
    ∃ V : Matrix ι (Fin 2) ℂ, V.conjTranspose * V = 1 ∧
      ∀ ν : I → ℂ,
        (retainedRows I V * (retainedRows I V).conjTranspose).charpoly =
          (∏ i : I, (X - C (ν i))) →
        (orderedCut I V * (orderedCut I V).conjTranspose).charpoly ≠
          (∏ a : Occupation I, (X - C (bernoulliWeight ν a))) := by
  obtain ⟨V, hV, hc, _, ho⟩ := alternating_cut_obstruction h
  refine ⟨V, hV, fun ν hν => ?_⟩
  rw [single_mode_bernoulli_charpoly ν (hν.symm.trans hc), ho]
  exact distinct_padded_spectra _ _

/-- The arbitrary-cut classification follows from the literal ordered-prefix
product formula. The alternating direction already has a two-orbital witness. -/
theorem universal_cut_product_iff_of_prefix
    (hprefix : ∀ m n k : ℕ, ∀ W : Matrix (Fin (m + n)) (Fin k) ℂ,
      W.conjTranspose * W = 1 → HasProductSpectrum {i | i.val < m} W)
    {ι : Type*} [LinearOrder ι] [Fintype ι] (I : Set ι) :
    ¬ Alternates I ↔ ∀ (k : ℕ) (V : Matrix ι (Fin k) ℂ),
      V.conjTranspose * V = 1 → HasProductSpectrum I V := by
  constructor
  · intro h k V hV ν hν
    exact (grouped_ordered_marginal_charpoly h V).symm.trans
      (grouped_product_from_prefix hprefix I V hV ν hν)
  · intro h hAlt
    obtain ⟨V, hV, hcontra⟩ := alternating_cut_bernoulli_obstruction hAlt
    let Q := retainedRows I V
    let hQ : (Q * Q.conjTranspose).IsHermitian :=
      Matrix.isHermitian_mul_conjTranspose_self Q
    let ν : I → ℂ := fun i => (hQ.eigenvalues i : ℂ)
    have hν : (Q * Q.conjTranspose).charpoly =
        (∏ i : I, (Polynomial.X - Polynomial.C (ν i))) := by
      rw [hQ.charpoly_eq]
      rfl
    exact hcontra ν hν (h 2 V hV ν hν)

end D5.S3.Quantum.Fermionic.OrderedSlaterCut
