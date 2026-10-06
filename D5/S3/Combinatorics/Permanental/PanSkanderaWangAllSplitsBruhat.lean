/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBruhat
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: Ehresmann rank domination is realized by increasing transposition chains. -/

/- Mathematical classification:
   rank_lifting_step:
     proof_shape: content
     escape_witness: rank_gap: threshold-band surplus count
   exists_lifting_step:
     proof_shape: content
     escape_witness: first_difference_lt and rank_lifting_step: first admissible later value
   rank_to_chain:
     proof_shape: content
     escape_witness: exists_lifting_step: well-founded score descent
   admission_basis: escape-witness
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     none (the frozen PSW theorem is used through the supporting modules).
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsChain

open Finset Equiv

namespace PSW

/-- Integer-valued form of the Ehresmann prefix rank; values here are zero-based. -/
def rankF {n : ℕ} (w : Perm (Fin n)) (p q : ℕ) : ℤ :=
  ∑ k : Fin n, if k.val < p ∧ q ≤ (w k).val then 1 else 0

def RankLE {n : ℕ} (w u : Perm (Fin n)) : Prop :=
  ∀ p q : ℕ, rankF w p q ≤ rankF u p q

/-- Each generating edge has increasing row positions and increasing values. -/
def UpStep {n : ℕ} (w v : Perm (Fin n)) : Prop :=
  ∃ i j : Fin n, i < j ∧ w i < w j ∧ v = w * swap i j

/-- The common prefix cancels, and no intermediate source value lies in `(w i,u i]`. -/
private theorem rank_gap {n : ℕ} (w u : Perm (Fin n)) (i j : Fin n)
    (hij : i < j) (hwi : w i < u i)
    (hpre : ∀ k : Fin n, k < i → w k = u k)
    (hmid : ∀ k : Fin n, i < k → k < j → ¬ (w i < w k ∧ w k ≤ u i))
    (hord : RankLE w u) {p q : ℕ}
    (hip : i.val < p) (hpj : p ≤ j.val)
    (haq : (w i).val < q) (hqb : q ≤ (u i).val) :
    rankF w p q + 1 ≤ rankF u p q := by
  classical
  let b := (u i).val
  let delta : Fin n → ℤ := fun k =>
    (if k.val < p ∧ q ≤ (u k).val then 1 else 0) -
    (if k.val < p ∧ q ≤ (w k).val then 1 else 0) -
    ((if k.val < p ∧ b + 1 ≤ (u k).val then 1 else 0) -
     (if k.val < p ∧ b + 1 ≤ (w k).val then 1 else 0))
  have hdelta : ∀ k : Fin n, 0 ≤ delta k := by
    intro k
    by_cases hki : k < i
    · have he := hpre k hki
      simp [delta, he]
    · by_cases hkp : k.val < p
      · have hkge : i ≤ k := le_of_not_gt hki
        have hknmid : ¬ (w i < w k ∧ w k ≤ u i) := by
          by_cases hki' : k = i
          · subst k; simp
          · exact hmid k (lt_of_le_of_ne hkge (Ne.symm hki')) (by omega)
        have houtside : (w k).val < q ∨ b + 1 ≤ (w k).val := by
          dsimp [b]
          have hcase : w k ≤ w i ∨ u i < w k := by omega
          rcases hcase with hcase | hcase
          · left; omega
          · right; omega
        dsimp [delta]
        rcases houtside with houtside | houtside <;> split_ifs <;> omega
      · simp [delta, hkp]
  have hdi : delta i = 1 := by
    dsimp [delta, b]
    split_ifs <;> omega
  have hsum : 1 ≤ ∑ k : Fin n, delta k := by
    have h := single_le_sum (fun k _ => hdelta k) (mem_univ i)
    simpa [hdi] using h
  have hhigh := hord p (b + 1)
  dsimp [delta] at hsum
  simp only [sum_sub_distrib] at hsum
  change 1 ≤ (rankF u p q - rankF w p q) -
    (rankF u p (b + 1) - rankF w p (b + 1)) at hsum
  omega

/-- Swapping the first suitable later value is a legal upward step below the upper permutation. -/
theorem rank_lifting_step {n : ℕ} (w u : Perm (Fin n)) (i j : Fin n)
    (hij : i < j) (hwi : w i < w j) (hwj : w j ≤ u i)
    (hpre : ∀ k : Fin n, k < i → w k = u k)
    (hmid : ∀ k : Fin n, i < k → k < j → ¬ (w i < w k ∧ w k ≤ u i))
    (hord : RankLE w u) : RankLE (w * swap i j) u := by
  have rank_swap {n : ℕ} (w : Perm (Fin n)) {i j : Fin n} (hij : i ≠ j)
      (p q : ℕ) :
      rankF (w * swap i j) p q = rankF w p q +
        (if i.val < p then (1 : ℤ) else 0) *
          ((if q ≤ (w j).val then (1 : ℤ) else 0) - (if q ≤ (w i).val then 1 else 0)) +
        (if j.val < p then (1 : ℤ) else 0) *
          ((if q ≤ (w i).val then (1 : ℤ) else 0) - (if q ≤ (w j).val then 1 else 0)) := by
    classical
    unfold rankF
    have hterm : ∀ k : Fin n,
        (if k.val < p ∧ q ≤ ((w * swap i j) k).val then (1 : ℤ) else 0) =
        (if k.val < p ∧ q ≤ (w k).val then (1 : ℤ) else 0) +
        (if k = i then (if i.val < p then (1 : ℤ) else 0) *
          ((if q ≤ (w j).val then 1 else 0) - (if q ≤ (w i).val then 1 else 0)) else 0) +
        (if k = j then (if j.val < p then (1 : ℤ) else 0) *
          ((if q ≤ (w i).val then 1 else 0) - (if q ≤ (w j).val then 1 else 0)) else 0) := by
      intro k
      by_cases hki : k = i
      · subst k; simp only [Perm.mul_apply, swap_apply_left, if_neg hij]
        split_ifs <;> omega
      · by_cases hkj : k = j
        · subst k; simp only [Perm.mul_apply, swap_apply_right, if_neg hki]
          split_ifs <;> omega
        · simp [Perm.mul_apply, swap_apply_of_ne_of_ne hki hkj, hki, hkj]
    simp_rw [hterm, sum_add_distrib]
    simp
  intro p q
  rw [rank_swap w (ne_of_lt hij)]
  have hwiu : w i < u i := lt_of_lt_of_le hwi hwj
  have hbase := hord p q
  by_cases hip : i.val < p
  · by_cases hjp : j.val < p
    · simp only [if_pos hip, if_pos hjp, one_mul]; omega
    · simp only [if_pos hip, if_neg hjp, one_mul, zero_mul, add_zero]
      by_cases hqi : q ≤ (w i).val
      · have hqj : q ≤ (w j).val := by omega
        simp [hqi, hqj]; exact hbase
      · by_cases hqj : q ≤ (w j).val
        · simp only [if_pos hqj, if_neg hqi, sub_zero]
          exact rank_gap w u i j hij hwiu hpre hmid hord hip (by omega) (by omega) (by omega)
        · simpa [hqi, hqj] using hbase
  · have hjp : ¬ j.val < p := by omega
    simpa [hip, hjp] using hbase

private theorem first_difference_lt {n : ℕ} (w u : Perm (Fin n)) (i : Fin n)
    (hpre : ∀ k : Fin n, k < i → w k = u k) (hne : w i ≠ u i)
    (hord : RankLE w u) : w i < u i := by
  classical
  by_contra hbad
  have hlt : u i < w i := lt_of_le_of_ne (le_of_not_gt hbad) (Ne.symm hne)
  let q := (w i).val
  have hterm : ∀ k : Fin n,
      (if k.val < i.val + 1 ∧ q ≤ (w k).val then (1 : ℤ) else 0) =
      (if k.val < i.val + 1 ∧ q ≤ (u k).val then (1 : ℤ) else 0) +
        (if k = i then 1 else 0) := by
    intro k
    by_cases hki : k = i
    · subst k; dsimp [q]; split_ifs <;> omega
    · by_cases hkl : k < i
      · simp [hpre k hkl, hki]
      · have hkg : ¬ k.val < i.val + 1 := by
          have hkne : k.val ≠ i.val := by intro h; exact hki (Fin.ext h)
          omega
        simp [hkg, hki]
  have heq : rankF w (i.val + 1) q = rankF u (i.val + 1) q + 1 := by
    unfold rankF
    simp_rw [hterm, sum_add_distrib]
    simp
  have hh := hord (i.val + 1) q
  omega

/-- A strict rank comparison admits an upward transposition still below the upper endpoint. -/
theorem exists_lifting_step {n : ℕ} (w u : Perm (Fin n)) (hord : RankLE w u)
    (hne : w ≠ u) : ∃ v : Perm (Fin n), UpStep w v ∧ RankLE v u := by
  classical
  let bad : Finset (Fin n) := univ.filter (fun k => w k ≠ u k)
  have hbad : bad.Nonempty := by
    obtain ⟨k, hk⟩ := not_forall.mp (fun h => hne (Equiv.ext h))
    exact ⟨k, mem_filter.mpr ⟨mem_univ _, hk⟩⟩
  let i := bad.min' hbad
  have hi : i ∈ bad := min'_mem bad hbad
  have hnei : w i ≠ u i := (mem_filter.mp hi).2
  have hpre : ∀ k : Fin n, k < i → w k = u k := by
    intro k hki
    by_contra h
    have hkb : k ∈ bad := mem_filter.mpr ⟨mem_univ _, h⟩
    have him : i ≤ k := min'_le bad k hkb
    exact (not_le_of_gt hki) him
  have hwui : w i < u i := first_difference_lt w u i hpre hnei hord
  let candidates : Finset (Fin n) := univ.filter (fun k => i < k ∧ w i < w k ∧ w k ≤ u i)
  have hcandidates : candidates.Nonempty := by
    let k := w.symm (u i)
    have hwk : w k = u i := w.apply_symm_apply _
    have hik : i < k := by
      by_contra h
      have hki : k ≤ i := le_of_not_gt h
      rcases lt_or_eq_of_le hki with hki | hki
      · have heq := hpre k hki
        have hkui : u k = u i := by rw [← heq, hwk]
        have : k = i := u.injective hkui
        omega
      · exact hnei (by simpa only [hki] using hwk)
    exact ⟨k, mem_filter.mpr ⟨mem_univ _, hik, hwk ▸ hwui, hwk ▸ le_rfl⟩⟩
  let j := candidates.min' hcandidates
  have hj : j ∈ candidates := min'_mem candidates hcandidates
  rcases (mem_filter.mp hj).2 with ⟨hij, hwi, hwj⟩
  have hmid : ∀ k : Fin n, i < k → k < j → ¬ (w i < w k ∧ w k ≤ u i) := by
    intro k hik hkj hc
    have hkc : k ∈ candidates := mem_filter.mpr ⟨mem_univ _, hik, hc⟩
    have hjm : j ≤ k := min'_le candidates k hkc
    exact (not_le_of_gt hkj) hjm
  refine ⟨w * swap i j, ⟨i, j, hij, hwi, rfl⟩, ?_⟩
  exact rank_lifting_step w u i j hij hwi hwj hpre hmid hord

/-- The position-value dot product strictly decreases at each upward transposition. -/
private def score {n : ℕ} (w : Perm (Fin n)) : ℕ := ∑ k : Fin n, k.val * (w k).val

/-- The needed direction of the rank criterion: a finite chain of upward swaps. -/
theorem rank_to_chain {n : ℕ} (w u : Perm (Fin n)) (hord : RankLE w u) :
    Relation.ReflTransGen UpStep w u := by
  have score_step {n : ℕ} (w : Perm (Fin n)) {i j : Fin n}
      (hij : i < j) (hwi : w i < w j) : score (w * swap i j) < score w := by
    classical
    have hi : i ∈ (univ : Finset (Fin n)) := mem_univ _
    have hj : j ∈ (univ : Finset (Fin n)).erase i := mem_erase.mpr ⟨(ne_of_lt hij).symm, mem_univ _⟩
    unfold score
    rw [← add_sum_erase univ (fun k => k.val * ((w * swap i j) k).val) hi,
      ← add_sum_erase (univ.erase i) (fun k => k.val * ((w * swap i j) k).val) hj,
      ← add_sum_erase univ (fun k => k.val * (w k).val) hi,
      ← add_sum_erase (univ.erase i) (fun k => k.val * (w k).val) hj]
    have hrest : (∑ k ∈ (univ.erase i).erase j, k.val * ((w * swap i j) k).val) =
        ∑ k ∈ (univ.erase i).erase j, k.val * (w k).val := by
      apply sum_congr rfl
      intro k hk
      have hki : k ≠ i := (mem_erase.mp (mem_erase.mp hk).2).1
      have hkj : k ≠ j := (mem_erase.mp hk).1
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hki hkj]
    rw [hrest]
    simp only [Perm.mul_apply, swap_apply_left, swap_apply_right]
    have hijv : i.val < j.val := hij
    have hwiv : (w i).val < (w j).val := hwi
    nlinarith
  classical
  induction hs : score w using Nat.strong_induction_on generalizing w with
  | h s ih =>
    by_cases hwu : w = u
    · subst w; exact Relation.ReflTransGen.refl
    · obtain ⟨v, hv, hvu⟩ := exists_lifting_step w u hord hwu
      have hsv : score v < s := by
        rcases hv with ⟨i, j, hij, hwi, rfl⟩
        rw [← hs]
        exact score_step w hij hwi
      have hchain := ih (score v) hsv v hvu rfl
      exact (Relation.ReflTransGen.single hv).trans hchain

/-- Rank domination decreases the monomial on every TNN matrix. -/
private theorem monomial_of_rank {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A)
    (w u : Perm (Fin n)) (hord : RankLE w u) : monomial A u ≤ monomial A w := by
  let singletonEmbedding {n : ℕ} (i : Fin n) : Fin 1 ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun _ => i) (by intro a b hab; have : a.val < b.val := hab; omega)
  have entry_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A)
      (i j : Fin n) : 0 ≤ A i j := by
    have h := hA 1 (singletonEmbedding i) (singletonEmbedding j)
    simpa [singletonEmbedding, Matrix.det_unique, OrderEmbedding.ofStrictMono] using h
  let pairEmbedding {n : ℕ} (i j : Fin n) (hij : i < j) : Fin 2 ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun x => if x = 0 then i else j) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all)
  have minor_two_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A)
      {i j c d : Fin n} (hij : i < j) (hcd : c < d) :
      0 ≤ A i c * A j d - A i d * A j c := by
    have h := hA 2 (pairEmbedding i j hij) (pairEmbedding c d hcd)
    simpa [Matrix.det_fin_two, Matrix.submatrix_apply, pairEmbedding, OrderEmbedding.ofStrictMono] using h
  have monomial_swap_difference {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
      (w : Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
      monomial A w - monomial A (w * swap i j) =
      (∏ k ∈ (univ.erase i).erase j, A k (w k)) *
        (A i (w i) * A j (w j) - A i (w j) * A j (w i)) := by
    classical
    unfold monomial
    have hi : i ∈ (univ : Finset (Fin n)) := mem_univ _
    have hj : j ∈ (univ : Finset (Fin n)).erase i := mem_erase.mpr ⟨Ne.symm hij, mem_univ _⟩
    rw [← mul_prod_erase _ _ hi, ← mul_prod_erase _ _ hj]
    rw [← mul_prod_erase _ (fun k => A k ((w * swap i j) k)) hi,
      ← mul_prod_erase _ (fun k => A k ((w * swap i j) k)) hj]
    have hrest : (∏ k ∈ (univ.erase i).erase j, A k ((w * swap i j) k)) =
        ∏ k ∈ (univ.erase i).erase j, A k (w k) := by
      apply prod_congr rfl
      intro k hk
      have hki : k ≠ i := (mem_erase.mp (mem_erase.mp hk).2).1
      have hkj : k ≠ j := (mem_erase.mp hk).1
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hki hkj]
    rw [hrest]
    simp only [Perm.mul_apply, swap_apply_left, swap_apply_right]
    ring
  have chain_step {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A)
      (w : Perm (Fin n)) {i j : Fin n} (hij : i < j) (hw : w i < w j) :
      monomial A (w * swap i j) ≤ monomial A w := by
    rw [← sub_nonneg]
    rw [monomial_swap_difference A w (ne_of_lt hij)]
    apply mul_nonneg
    · exact prod_nonneg (fun k _ => entry_nonneg hA k (w k))
    · exact minor_two_nonneg hA hij hw
  have hc := rank_to_chain w u hord
  clear hord
  induction hc with
  | refl => exact le_rfl
  | @tail v u hchain hstep ih =>
      rcases hstep with ⟨i, j, hij, hwi, rfl⟩
      exact le_trans (chain_step hA v hij hwi) ih

#print axioms rank_lifting_step
#print axioms rank_to_chain
#print axioms monomial_of_rank
end PSW
