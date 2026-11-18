import D5.S3.Quantum.Fermionic.SlaterCutPhase
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The permutation sign for a stable concatenation of two ordered blocks. -/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.SlaterCutPhase

namespace SlaterShuffleSignProbe

theorem sign_of_ordered_blocks {m n : ℕ} (σ : Equiv.Perm (Fin (m + n)))
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

variable {ι : Type*} [LinearOrder ι]

def groupedRows (a b : Finset ι) (h : Disjoint a b) :
    Fin (a.card + b.card) ≃ a.disjUnion b h :=
  finSumFinEquiv.symm.trans
    (((a.orderIsoOfFin rfl).toEquiv.sumCongr (b.orderIsoOfFin rfl).toEquiv).trans
      (Equiv.Finset.disjUnionEquiv a b h))

def rowShuffle (a b : Finset ι) (h : Disjoint a b) :
    Equiv.Perm (Fin (a.card + b.card)) :=
  (groupedRows a b h).trans
    ((a.disjUnion b h).orderIsoOfFin (Finset.card_disjUnion a b h)).symm.toEquiv

theorem row_shuffle_sign (a b : Finset ι) (h : Disjoint a b) :
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
theorem grouped_minor {R : Type*} [CommRing R] (a b : Finset ι)
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

noncomputable def orderedAmplitude {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (a b : Finset ι) (hd : Disjoint a b) : ℂ :=
  if h : a.card + b.card = k then
    (V.submatrix ((a.disjUnion b hd).orderEmbOfFin
      ((Finset.card_disjUnion a b hd).trans h)) id).det
  else 0

noncomputable def groupedAmplitude {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (a b : Finset ι) (hd : Disjoint a b) : ℂ :=
  if h : a.card + b.card = k then
    (V.submatrix (fun i => (groupedRows a b hd (Fin.cast h.symm i) : ι)) id).det
  else 0

theorem grouped_amplitude_eq_signed {k : ℕ} (V : Matrix ι (Fin k) ℂ)
    (a b : Finset ι) (hd : Disjoint a b) :
    groupedAmplitude V a b hd = (-1 : ℂ) ^ crossCount a b * orderedAmplitude V a b hd := by
  by_cases h : a.card + b.card = k
  · subst k
    simpa [groupedAmplitude, orderedAmplitude, crossCount] using grouped_minor a b hd V
  · simp [groupedAmplitude, orderedAmplitude, h]

/-- Relabeling a stable partition as two consecutive blocks gives the same
occupied minor as listing the occupied rows of the retained side first. -/
theorem ordered_amplitude_of_block_relabeling {κ : Type*} [LinearOrder κ]
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
        change e (groupedRows a b hd (Fin.cast hk.symm i)) ∈ a'.disjUnion b' hd'
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
    rw [dif_pos hk', dif_pos hk]
    congr 1
    ext i j
    change V (e.symm ((a'.disjUnion b' hd').orderEmbOfFin _ i)) j =
      V (groupedRows a b hd (Fin.cast hk.symm i)) j
    rw [← congrFun hrows i, e.symm_apply_apply]
  · simp [orderedAmplitude, groupedAmplitude, hcard, hk]

theorem grouped_ordered_marginal_charpoly {I : Set ι} (h : ¬ Alternates I)
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (a : A → Finset ι) (b : B → Finset ι)
    (ha : ∀ x, (↑(a x) : Set ι) ⊆ I) (hb : ∀ y, (↑(b y) : Set ι) ⊆ Iᶜ)
    {k : ℕ} (V : Matrix ι (Fin k) ℂ) :
    let hd : ∀ x y, Disjoint (a x) (b y) := fun x y =>
      Finset.disjoint_left.mpr fun _ hx hy => hb y hy (ha x hx)
    let original : Matrix A B ℂ := fun x y => orderedAmplitude V (a x) (b y) (hd x y)
    let grouped : Matrix A B ℂ := fun x y => groupedAmplitude V (a x) (b y) (hd x y)
    (grouped * grouped.conjTranspose).charpoly = (original * original.conjTranspose).charpoly := by
  intro hd original grouped
  have hsupport (x : A) (y : B) (hxy : (a x).card + (b y).card ≠ k) : original x y = 0 := by
    simp [original, orderedAmplitude, hxy]
  let signed : Matrix A B ℂ := fun x y => (-1 : ℂ) ^ crossCount (a x) (b y) * original x y
  have hg : grouped = signed := by
    ext x y
    exact grouped_amplitude_eq_signed V (a x) (b y) (hd x y)
  rw [hg]
  exact reduction_charpoly h a b ha hb k original hsupport

end SlaterShuffleSignProbe
