/- GID: D5/S3/Combinatorics/Graph/URSActualNonsingularity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/URSActualNonsingularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual commuting odd-order uniform reflection cross-Grams have trivial kernel. -/

import D5.S3.Combinatorics.Graph.URSComponentParity
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace URSActualBlocks
open Finset Matrix
open D5.S3.Combinatorics.Graph.URSComponentParity

noncomputable def H {n : ℕ} (ρ : Fin (2*n) → Equiv.Perm (Fin n))
    (x y : Fin n) : Matrix (Fin n) (Fin n) ℕ := pairCount ρ x y
noncomputable def B {n : ℕ} (ρ : Fin (2*n) → Equiv.Perm (Fin n))
    (x : Fin n) : Matrix (Fin (2*n)) (Fin n) ℝ :=
  fun i p => if ρ i x = p then 1 else 0
noncomputable def HR {n : ℕ} (ρ : Fin (2*n) → Equiv.Perm (Fin n))
    (x y : Fin n) : Matrix (Fin n) (Fin n) ℝ := fun p q => H ρ x y p q

/-- The support graph of one actual cross-Gram, on the original symbol set. -/
noncomputable def supportGraph {n : ℕ} (ρ : Fin (2*n) → Equiv.Perm (Fin n))
    (hr : ∀ x y p q, x ≠ y → p ≠ q →
      pairCount ρ x y p q = pairCount ρ x y q p) (u v : Fin n) : SimpleGraph (Fin n) where
  Adj p q := p ≠ q ∧ 0 < H ρ u v p q
  symm := ⟨by
    intro p q h
    refine ⟨h.1.symm, ?_⟩
    by_cases hxy : u = v
    · subst v
      by_cases hpq : p = q
      · subst q
        exact h.2
      · have hEq : H ρ u u p q = H ρ u u q p := by
          simp only [H, pairCount, Finset.card_eq_sum_ones, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hi
          have h1 : ¬(ρ i u = p ∧ ρ i u = q) := by
            rintro ⟨h1,h2⟩
            exact hpq (h1.symm.trans h2)
          have h2 : ¬(ρ i u = q ∧ ρ i u = p) := by
            rintro ⟨h1,h2⟩
            exact hpq (h2.symm.trans h1)
          simp [h1,h2]
        rw [← hEq]
        exact h.2
    · by_cases hpq : p = q
      · subst q
        exact h.2
      · change 0 < pairCount ρ u v q p
        rw [← hr u v p q hxy hpq]
        exact h.2⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

/-- A component is selected only from actual support reachability. -/
noncomputable def component {n : ℕ} (ρ : Fin (2*n) → Equiv.Perm (Fin n))
    (hr : ∀ x y p q, x ≠ y → p ≠ q →
      pairCount ρ x y p q = pairCount ρ x y q p) (u v a : Fin n) : Finset (Fin n) :=
  by
    classical
    exact univ.filter ((supportGraph ρ hr u v).Reachable a)

end URSActualBlocks

namespace D5.S3.Combinatorics.Graph.URSActualNonsingularity
open URSActualBlocks
open Finset Matrix
open D5.S3.Combinatorics.Graph.URSComponentParity

/-- Every actual off-diagonal cross-Gram in the same commuting odd-order
uniform reflection array has trivial real kernel. -/
theorem actual_crossGram_kernel_trivial {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n)
    (ρ : Fin (2*n) → Equiv.Perm (Fin n))
    (hf : ∀ x p, (fibre ρ x p).card = 2)
    (hr : ∀ x y p q, x ≠ y → p ≠ q →
      pairCount ρ x y p q = pairCount ρ x y q p)
    (hc : ∀ x y a b, ((B ρ x).transpose * B ρ y) * ((B ρ a).transpose * B ρ b) =
      ((B ρ a).transpose * B ρ b) * ((B ρ x).transpose * B ρ y))
    (u v : Fin n) (huv : u ≠ v) (z : Fin n → ℝ)
    (hz : HR ρ u v *ᵥ z = 0) : z = 0 := by
  classical
  have count_sum : ∀ x y p q : Fin n,
      H ρ x y p q = ∑ i, if ρ i x = p ∧ ρ i y = q then 1 else 0 := by
    intro x y p q
    simp only [H, pairCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  have actual_crossGram : ∀ x y : Fin n,
      HR ρ x y = (B ρ x).transpose * B ρ y := by
    intro x y
    ext p q
    simp only [HR, count_sum, Nat.cast_sum, Matrix.mul_apply, Matrix.transpose_apply, B]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  have row_sum : ∀ x y p : Fin n, ∑ q, H ρ x y p q = 2 := by
    intro x y p
    simp_rw [count_sum]
    rw [Finset.sum_comm]
    have h : ∀ i : Fin (2*n),
        (∑ q : Fin n, if ρ i x = p ∧ ρ i y = q then 1 else 0) =
        if ρ i x = p then 1 else 0 := by
      intro i
      by_cases hi : ρ i x = p <;> simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simpa only [fibre, Finset.card_eq_sum_ones, Finset.sum_filter] using hf x p
  have symbol_sum : ∀ x p q : Fin n, ∑ y, H ρ x y p q = 2 := by
    intro x p q
    simp_rw [count_sum]
    rw [Finset.sum_comm]
    have h : ∀ i : Fin (2*n),
        (∑ y : Fin n, if ρ i x = p ∧ ρ i y = q then 1 else 0) =
        if ρ i x = p then 1 else 0 := by
      intro i
      by_cases hi : ρ i x = p
      · simp only [hi, true_and]
        rw [Finset.sum_eq_single ((ρ i).symm q)]
        · simp
        · intro b hb hne
          have : ρ i b ≠ q := by
            intro he
            apply hne
            exact (ρ i).injective (he.trans ((ρ i).apply_symm_apply q).symm)
          simp [this]
        · simp
      · simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simpa only [fibre, Finset.card_eq_sum_ones, Finset.sum_filter] using hf x p
  have symmetry : ∀ x y p q : Fin n,
      H ρ x y p q = H ρ x y q p := by
    intro x y p q
    by_cases hxy : x = y
    · subst y
      by_cases hpq : p = q
      · subst q; rfl
      · simp only [count_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have h1 : ¬(ρ i x = p ∧ ρ i x = q) := by
          rintro ⟨h1,h2⟩
          exact hpq (h1.symm.trans h2)
        have h2 : ¬(ρ i x = q ∧ ρ i x = p) := by
          rintro ⟨h1,h2⟩
          exact hpq (h2.symm.trans h1)
        simp [h1,h2]
    · by_cases hpq : p = q
      · subst q; rfl
      · exact hr x y p q hxy hpq
  have diagonal_zero : ∀ p : Fin n, H ρ u v p p = 0 := by
    intro p
    rw [count_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have h : ¬(ρ i u = p ∧ ρ i v = p) := by
      rintro ⟨h1,h2⟩
      exact huv ((ρ i).injective (h1.trans h2.symm))
    simp [h]
  have harmonic_edge : ∀ (D : Matrix (Fin n) (Fin n) ℝ),
      (∀ i j, D i j = D j i) → (∀ i j, 0 ≤ D i j) →
      (z : Fin n → ℝ) → (∀ i, ∑ j, D i j * (z i - z j) = 0) →
      ∀ i j, 0 < D i j → z i = z j := by
    intro D hs hn z hz i j hij
    have left : (∑ a, ∑ b, D a b * z a * (z a-z b)) =
        ∑ a, z a * ∑ b, D a b * (z a-z b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    have right : (∑ a, ∑ b, D a b * z b * (z b-z a)) =
        ∑ a, ∑ b, D a b * z a * (z a-z b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [hs b a]
    have he : (∑ a, ∑ b, D a b * (z a-z b)^2) =
        2 * ∑ a, z a * ∑ b, D a b * (z a-z b) := by
      calc
        _ = (∑ a, ∑ b, D a b * z a * (z a-z b)) +
            (∑ a, ∑ b, D a b * z b * (z b-z a)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = _ := by rw [right, left]; ring
    have he0 : (∑ a, ∑ b, D a b * (z a-z b)^2) = 0 := by
      rw [he]
      simp_rw [hz]
      simp
    have hrow : ∀ a, (∑ b, D a b * (z a-z b)^2) = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
        mul_nonneg (hn a b) (sq_nonneg _)))).mp he0 a (mem_univ a)
    have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
        mul_nonneg (hn i b) (sq_nonneg (z i-z b)))).mp (hrow i) j (mem_univ j)
    have hsquare : (z i-z j)^2 = 0 :=
      (mul_eq_zero.mp hentry).resolve_left (ne_of_gt hij)
    nlinarith [sq_nonneg (z i-z j)]
  have component_mem : ∀ a p : Fin n,
      p ∈ component ρ hr u v a ↔ (supportGraph ρ hr u v).Reachable a p := by
    intro a p
    simp [component]
  have component_closed : ∀ a p q : Fin n,
      p ∈ component ρ hr u v a → 0 < H ρ u v p q →
      q ∈ component ρ hr u v a := by
    intro a p q hp hpq
    by_cases heq : p = q
    · simpa [← heq] using hp
    · apply (component_mem a q).mpr
      exact ((component_mem a p).mp hp).trans
        (SimpleGraph.Adj.reachable (show (supportGraph ρ hr u v).Adj p q from ⟨heq,hpq⟩))
  have component_sum : ∀ a p : Fin n,
      ∑ q ∈ component ρ hr u v a, H ρ u v p q =
        if p ∈ component ρ hr u v a then 2 else 0 := by
    intro a p
    classical
    by_cases hp : p ∈ component ρ hr u v a
    · rw [if_pos hp, ← row_sum u v p]
      apply Finset.sum_subset (subset_univ _)
      intro q hq hnot
      exact Nat.eq_zero_of_not_pos (fun hpos => hnot (component_closed a p q hp hpos))
    · rw [if_neg hp]
      apply Finset.sum_eq_zero
      intro q hq
      rw [symmetry u v p q]
      exact Nat.eq_zero_of_not_pos (fun hpos => hp (component_closed a q p hq hpos))
  have nat_commuting : ∀ x y a b : Fin n,
      H ρ x y * H ρ a b = H ρ a b * H ρ x y := by
    intro x y a b
    have h := hc x y a b
    rw [← actual_crossGram x y, ← actual_crossGram a b] at h
    ext p q
    have he := congrFun (congrFun h p) q
    simp only [Matrix.mul_apply, HR] at he ⊢
    exact_mod_cast he
  have block_harmonic : ∀ (x y b p : Fin n),
      ∑ j, H ρ u v p j * (∑ q ∈ component ρ hr u v b, H ρ x y j q) =
        2 * (∑ q ∈ component ρ hr u v b, H ρ x y p q) := by
    intro x y b p
    let Q := component ρ hr u v b
    calc
      _ = ∑ q ∈ Q, (H ρ u v * H ρ x y) p q := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ q ∈ Q, (H ρ x y * H ρ u v) p q := by rw [nat_commuting]
      _ = ∑ j, H ρ x y p j * ∑ q ∈ Q, H ρ u v j q := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := by
        change (∑ j, H ρ x y p j * ∑ q ∈ component ρ hr u v b, H ρ u v j q) = _
        simp_rw [component_sum]
        have hrestrict :
            (∑ j, H ρ x y p j * (if j ∈ Q then 2 else 0)) =
            ∑ j ∈ Q, H ρ x y p j * (if j ∈ Q then 2 else 0) := by
          apply (Finset.sum_subset (subset_univ Q) ?_).symm
          intro j hj hn
          simp only [if_neg hn, mul_zero]
        rw [hrestrict, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos hj, Nat.mul_comm]
  have block_rows_constant : ∀ (x y b p t : Fin n),
      (supportGraph ρ hr u v).Reachable p t →
      (∑ q ∈ component ρ hr u v b, H ρ x y p q) =
        ∑ q ∈ component ρ hr u v b, H ρ x y t q := by
    intro x y b p t hpt
    let zz : Fin n → ℝ := fun p => ∑ q ∈ component ρ hr u v b, (H ρ x y p q : ℝ)
    have hz' : ∀ p, ∑ j, (H ρ u v p j : ℝ) * (zz p-zz j) = 0 := by
      intro p
      have hrow' : (∑ j, (H ρ u v p j : ℝ)) = 2 := by exact_mod_cast row_sum u v p
      have hmul : (∑ j, (H ρ u v p j : ℝ) * zz j) = 2*zz p := by
        dsimp [zz]
        exact_mod_cast block_harmonic x y b p
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow', hmul]
      ring
    have hedge : ∀ p t, (supportGraph ρ hr u v).Adj p t → zz p = zz t := by
      intro p t h
      exact harmonic_edge (HR ρ u v)
        (fun i j => by dsimp [HR]; exact_mod_cast symmetry u v i j)
        (fun i j => Nat.cast_nonneg _) zz hz' p t
        (by dsimp [HR]; exact_mod_cast h.2)
    have heq : zz p = zz t := by
      obtain ⟨w⟩ := hpt
      induction w with
      | nil => rfl
      | cons hA _ ih => exact (hedge _ _ hA).trans ih
    dsimp [zz] at heq
    exact_mod_cast heq
  have actual_component_block_degrees : ∀ (x y a b : Fin n),
      (∃ p ∈ component ρ hr u v a, ∃ q ∈ component ρ hr u v b,
        0 < H ρ x y p q) →
      ∃ r s : ℕ, (r = 1 ∨ r = 2) ∧ (s = 1 ∨ s = 2) ∧
        (∀ p ∈ component ρ hr u v a, ∑ q ∈ component ρ hr u v b, H ρ x y p q = r) ∧
        (∀ q ∈ component ρ hr u v b, ∑ p ∈ component ρ hr u v a, H ρ x y p q = s) ∧
        (component ρ hr u v a).card*r = (component ρ hr u v b).card*s ∧
        (∀ p ∈ component ρ hr u v a, ∀ q ∈ component ρ hr u v b,
          (∑ k ∈ component ρ hr u v a, H ρ u v p k * H ρ x y k q) =
          ∑ k ∈ component ρ hr u v b, H ρ x y p k * H ρ u v k q) := by
    intro x y a b hnonzero
    let P := component ρ hr u v a
    let Q := component ρ hr u v b
    let r := ∑ q ∈ Q, H ρ x y a q
    let s := ∑ p ∈ P, H ρ x y b p
    have ha : a ∈ P := (component_mem a a).mpr (.refl a)
    have hb : b ∈ Q := (component_mem b b).mpr (.refl b)
    have hrow : ∀ p ∈ P, (∑ q ∈ Q, H ρ x y p q) = r := by
      intro p hp
      exact (block_rows_constant x y b a p
        ((component_mem a p).mp hp)).symm
    have hcol : ∀ q ∈ Q, (∑ p ∈ P, H ρ x y p q) = s := by
      intro q hq
      simp_rw [symmetry x y]
      exact (block_rows_constant x y a b q
        ((component_mem b q).mp hq)).symm
    obtain ⟨p,hp,q,hq,hpq⟩ := hnonzero
    have hrpos : 0 < r := by
      rw [← hrow p hp]
      exact lt_of_lt_of_le hpq (Finset.single_le_sum (fun j _ => Nat.zero_le (H ρ x y p j)) hq)
    have hspos : 0 < s := by
      rw [← hcol q hq]
      exact lt_of_lt_of_le hpq (Finset.single_le_sum (fun j _ => Nat.zero_le (H ρ x y j q)) hp)
    have hrle : r ≤ 2 := by
      dsimp [r]
      rw [← row_sum x y a]
      exact Finset.sum_le_sum_of_subset (subset_univ Q)
    have hsle : s ≤ 2 := by
      dsimp [s]
      rw [← row_sum x y b]
      exact Finset.sum_le_sum_of_subset (subset_univ P)
    have hsize : P.card*r = Q.card*s := by
      calc
        _ = ∑ p ∈ P, r := by simp
        _ = ∑ p ∈ P, ∑ q ∈ Q, H ρ x y p q :=
          Finset.sum_congr rfl (fun p hp => (hrow p hp).symm)
        _ = ∑ q ∈ Q, ∑ p ∈ P, H ρ x y p q := by rw [Finset.sum_comm]
        _ = ∑ q ∈ Q, s := Finset.sum_congr rfl hcol
        _ = _ := by simp
    refine ⟨r,s,by omega,by omega,hrow,hcol,hsize,?_⟩
    intro p hp q hq
    have hleft : (∑ k ∈ P, H ρ u v p k * H ρ x y k q) =
        (H ρ u v * H ρ x y) p q := by
      apply Finset.sum_subset (subset_univ P)
      intro k hk hnot
      have hz : H ρ u v p k = 0 := Nat.eq_zero_of_not_pos (fun hpos =>
        hnot (component_closed a p k hp hpos))
      rw [hz,zero_mul]
    have hright : (∑ k ∈ Q, H ρ x y p k * H ρ u v k q) =
        (H ρ x y * H ρ u v) p q := by
      apply Finset.sum_subset (subset_univ Q)
      intro k hk hnot
      have hz : H ρ u v k q = 0 := by
        rw [symmetry u v k q]
        exact Nat.eq_zero_of_not_pos (fun hpos =>
          hnot (component_closed b q k hq hpos))
      rw [hz,mul_zero]
    rw [hleft,hright,nat_commuting]
  let G := supportGraph ρ hr u v
  have hsizes_all : ∃ d : ℕ, Odd d ∧ 3 ≤ d ∧
      (∀ a, (component ρ hr u v a).card = d ∨
        (component ρ hr u v a).card = 2*d) ∧
      (∀ a, ¬ 4 ∣ (component ρ hr u v a).card) := by
    classical
    let G := supportGraph ρ hr u v
    let f := component ρ hr u v
    have hself : ∀ a, a ∈ f a := fun a => (component_mem a a).mpr (.refl a)
    have hsame : ∀ a b, f b = f a ↔ G.Reachable a b := by
      intro a b
      constructor
      · intro heq
        have hb := hself b
        rw [heq] at hb
        exact (component_mem a b).mp hb
      · intro hab
        ext p
        simp only [f, component_mem]
        constructor
        · intro hbp
          exact hab.trans hbp
        · intro hap
          exact hab.symm.trans hap
    have hpart : ∑ P ∈ (univ : Finset (Fin n)).image f, P.card = n := by
      have h := card_eq_sum_card_image f (univ : Finset (Fin n))
      have hfilter : ∀ P ∈ (univ : Finset (Fin n)).image f,
          (univ.filter fun b => f b = P) = P := by
        intro P hP
        obtain ⟨a,_,rfl⟩ := mem_image.mp hP
        ext b
        simp only [mem_filter, mem_univ, true_and, hsame, f, component_mem]
        rfl
      rw [sum_congr rfl (fun P hP => congrArg Finset.card (hfilter P hP))] at h
      simpa using h.symm
    have hodd : ∃ a : Fin n, Odd (f a).card := by
      by_contra he
      push Not at he
      have hev : ∀ P ∈ (univ : Finset (Fin n)).image f, Even P.card := by
        intro P hP
        obtain ⟨a,_,rfl⟩ := mem_image.mp hP
        exact Nat.not_odd_iff_even.mp (he a)
      have hevsum := Finset.even_sum (fun P : Finset (Fin n) => P.card) hev
      rw [hpart] at hevsum
      exact (Nat.not_even_iff_odd.mpr hn) hevsum
    obtain ⟨a,haodd⟩ := hodd
    let d := (f a).card
    have hmin : ∀ b : Fin n, 2 ≤ (f b).card := by
      intro b
      have hpos : ∃ q : Fin n, 0 < H ρ u v b q := by
        by_contra he
        push Not at he
        have hz : ∑ q, H ρ u v b q = 0 :=
          sum_eq_zero fun q _ => Nat.eq_zero_of_le_zero (he q)
        have ht := row_sum u v b
        omega
      obtain ⟨q,hq⟩ := hpos
      have hne : b ≠ q := by
        intro heq
        subst q
        rw [diagonal_zero b] at hq
        omega
      have hqmem : q ∈ f b := component_closed b b q (hself b) hq
      have hsub : {b,q} ⊆ f b := by
        intro t ht
        rcases mem_insert.mp ht with ht | ht
        · rw [ht]
          exact hself b
        · have heq := mem_singleton.mp ht
          simpa [heq] using hqmem
      have hcard := card_le_card hsub
      simpa [hne] using hcard
    have hd3 : 3 ≤ d := by
      have hm := hmin a
      obtain ⟨k,hk⟩ := haodd
      dsimp [d]
      omega
    have hratio : ∀ b, (f b).card = d ∨ (f b).card = 2*d := by
      intro b
      have hpos : ∃ y : Fin n, 0 < H ρ a y a b := by
        by_contra he
        push Not at he
        have hz : ∑ y, H ρ a y a b = 0 :=
          sum_eq_zero fun y _ => Nat.eq_zero_of_le_zero (he y)
        have ht := symbol_sum a a b
        omega
      obtain ⟨y,hy⟩ := hpos
      obtain ⟨r,s,hr,hs,_,_,hsize,_⟩ :=
        actual_component_block_degrees a y a b
          ⟨a,hself a,b,hself b,hy⟩
      change d*r = (f b).card*s at hsize
      rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
      · left; omega
      · obtain ⟨k,hk⟩ := haodd
        change d = 2*k+1 at hk
        omega
      · right; omega
      · left; omega
    refine ⟨d,haodd,hd3,hratio,?_⟩
    intro b hfour
    obtain ⟨k,hk⟩ := hfour
    change (f b).card = 4*k at hk
    obtain ⟨t,ht⟩ := haodd
    change d = 2*t+1 at ht
    rcases hratio b with heq | heq <;> omega
  have hsupport_all : (∀ p q, H ρ u v p q ≤ 1) ∧ G.IsCycles := by
    classical
    let G := supportGraph ρ hr u v
    obtain ⟨d,hd,hd3,hsizes,_⟩ :=
      hsizes_all
    have hsmall : ∀ p q, H ρ u v p q ≤ 1 := by
      intro p q
      have hle : H ρ u v p q ≤ 2 := by
        rw [← row_sum u v p]
        exact single_le_sum (fun k _ => Nat.zero_le _) (mem_univ q)
      by_contra hnot
      have htwo : H ρ u v p q = 2 := by omega
      have hqp : H ρ u v q p = 2 := by rw [symmetry u v q p]; exact htwo
      have honly : ∀ a b, H ρ u v a b = 2 → ∀ k, 0 < H ρ u v a k → k = b := by
        intro a b hab k hk
        by_contra hne
        have hsum := sum_erase_add (univ : Finset (Fin n)) (fun t => H ρ u v a t) (mem_univ b)
        have hbound := single_le_sum (fun t _ => Nat.zero_le (H ρ u v a t))
          (mem_erase.mpr ⟨hne,mem_univ k⟩)
        have hrow := row_sum u v a
        omega
      have hclosed : ∀ a b, a = p ∨ a = q → G.Adj a b → b = p ∨ b = q := by
        intro a b ha hab
        rcases ha with ha | ha
        · rw [ha] at hab
          exact Or.inr (honly p q htwo b hab.2)
        · rw [ha] at hab
          exact Or.inl (honly q p hqp b hab.2)
      have hwalk : ∀ {a b : Fin n}, G.Walk a b →
          a = p ∨ a = q → b = p ∨ b = q := by
        intro a b w
        induction w with
        | nil => exact id
        | cons hab w ih => intro ha; exact ih (hclosed _ _ ha hab)
      have hsub : component ρ hr u v p ⊆ {p,q} := by
        intro t ht
        obtain ⟨w⟩ := (component_mem p t).mp ht
        have hm := hwalk w (Or.inl rfl)
        simpa only [mem_insert, mem_singleton] using hm
      have hcard := card_le_card hsub
      have hpair : ({p,q} : Finset (Fin n)).card ≤ 2 := by by_cases heq : p = q <;> simp [heq]
      rcases hsizes p with heq | heq <;> omega
    refine ⟨hsmall,?_⟩
    intro p hp
    have hsum : ∑ q : Fin n, H ρ u v p q = G.degree p := by
      rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, card_eq_sum_ones, sum_filter]
      apply sum_congr rfl
      intro q hq
      by_cases hadj : G.Adj p q
      · have hval : H ρ u v p q = 1 := by have := hsmall p q; have := hadj.2; omega
        simp only [if_pos hadj, hval]
      · have hval : H ρ u v p q = 0 := by
          by_cases heq : p = q
          · subst q; exact diagonal_zero p
          · exact Nat.eq_zero_of_not_pos (fun hpos => hadj ⟨heq,hpos⟩)
        simp only [if_neg hadj, hval]
    have hdeg : G.degree p = 2 := by rw [← hsum, row_sum u v p]
    simpa only [SimpleGraph.degree, ← Set.ncard_coe_finset, G.coe_neighborFinset] using hdeg
  obtain ⟨hsmall,hcyc⟩ := hsupport_all
  obtain ⟨d,hd,hd3,hsizes,hfour⟩ :=
    hsizes_all
  have hval : ∀ a b, G.Adj a b → H ρ u v a b = 1 := by
    intro a b hab
    have := hsmall a b
    have := hab.2
    omega
  have hkernel : ∀ a b c, G.Adj b a → G.Adj b c → a ≠ c → z a + z c = 0 := by
    intro a b c hba hbc hac
    have honly : ∀ k, G.Adj b k → k = a ∨ k = c := by
      intro k hbk
      by_cases hka : k = a
      · exact Or.inl hka
      · have hu := hcyc.existsUnique_ne_adj hba
        obtain ⟨t,ht,hunique⟩ := hu
        have hct : c = t := hunique c ⟨hac,hbc⟩
        have hkt : k = t := hunique k ⟨Ne.symm hka,hbk⟩
        exact Or.inr (hkt.trans hct.symm)
    have hsum : (∑ k : Fin n, (H ρ u v b k : ℝ)*z k) = z a+z c := by
      have hrestrict : (∑ k ∈ ({a,c} : Finset (Fin n)), (H ρ u v b k : ℝ)*z k) =
          ∑ k : Fin n, (H ρ u v b k : ℝ)*z k := by
        apply sum_subset (subset_univ _)
        intro k hk hnot
        have he : H ρ u v b k = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hpos
          have hne : b ≠ k := by
            intro heq
            subst k
            rw [diagonal_zero b] at hpos
            omega
          have hm := honly k ⟨hne,hpos⟩
          apply hnot
          simpa only [mem_insert,mem_singleton] using hm
        rw [he,Nat.cast_zero,zero_mul]
      rw [← hrestrict, sum_pair hac, hval b a hba, hval b c hbc]
      simp
    have he := congrFun hz b
    simpa only [Matrix.mulVec, dotProduct, HR, Pi.zero_apply, hsum] using he
  ext p
  let C := G.connectedComponentMk p
  have hnode : (G.neighborSet p).Nonempty := by
    have hpos : ∃ q : Fin n, 0 < H ρ u v p q := by
      by_contra he
      push Not at he
      have he0 : ∑ q, H ρ u v p q = 0 :=
        sum_eq_zero fun q _ => Nat.eq_zero_of_le_zero (he q)
      have he2 := row_sum u v p
      omega
    obtain ⟨q,hq⟩ := hpos
    refine ⟨q,?_⟩
    show G.Adj p q
    refine ⟨?_,hq⟩
    intro heq
    subst q
    rw [diagonal_zero p] at hq
    omega
  obtain ⟨w,hw,hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (show p ∈ C.supp from rfl) hnode
  let L := w.length
  have hL3 : 3 ≤ L := hw.three_le_length
  have hvertices : (range L).image w.getVert = component ρ hr u v p := by
    ext a
    constructor
    · intro ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      apply (component_mem p _).mpr
      have hm : w.getVert i ∈ C.supp := by
        rw [← hverts, SimpleGraph.Walk.mem_verts_toSubgraph]
        exact w.getVert_mem_support i
      exact (SimpleGraph.ConnectedComponent.eq.mp hm).symm
    · intro ha
      have hm : a ∈ C.supp := by
        exact SimpleGraph.ConnectedComponent.sound ((component_mem p a).mp ha).symm
      rw [← hverts, SimpleGraph.Walk.mem_verts_toSubgraph] at hm
      obtain ⟨i,hei,hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hm
      by_cases hil : i < L
      · exact mem_image.mpr ⟨i,mem_range.mpr hil,hei⟩
      · have heL : i = L := by change i ≤ L at hi; omega
        subst i
        have hap : a = p := by simpa [L] using hei.symm
        exact mem_image.mpr ⟨0,mem_range.mpr (by omega),by simp [hap]⟩
  have hLcard : L = (component ρ hr u v p).card := by
    have hinj : Set.InjOn w.getVert (range L : Finset ℕ) := by
      intro i hi j hj heq
      apply hw.getVert_injOn' _ _ heq <;> simp only [Set.mem_ofPred_eq]
      · have := mem_range.mp hi; omega
      · have := mem_range.mp hj; omega
    have hcard := card_image_of_injOn hinj
    rw [hvertices, card_range] at hcard
    exact hcard.symm
  have hnotfour : ¬4 ∣ L := by rw [hLcard]; exact hfour p
  let t : ℕ → ℝ := fun i => z (w.getVert i)
  have hrec : ∀ i, i+2 ≤ L → t (i+2) = -t i := by
    intro i hi
    have hne : w.getVert i ≠ w.getVert (i+2) := by
      have h := hw.getVert_sub_one_ne_getVert_add_one (i := i+1) (by change i+1 ≤ L; omega)
      simpa using h
    have he := hkernel (w.getVert i) (w.getVert (i+1)) (w.getVert (i+2))
      (w.adj_getVert_succ (by change i < L; omega)).symm
      (w.adj_getVert_succ (by change i+1 < L; omega)) hne
    dsimp [t]
    linarith
  have hroot : t 1 + t (L-1) = 0 := by
    apply hkernel
    · exact w.adj_getVert_succ (by change 0 < L; omega)
    · have h := w.adj_getVert_succ (i := L-1) (by change L-1 < L; omega)
      have he : L-1+1 = w.length := by change L-1+1 = L; omega
      rw [he,w.getVert_length] at h
      simpa only [w.getVert_zero] using h.symm
    · exact hw.snd_ne_penultimate
  have hperiod : ∀ i, i ≤ L → t i =
      if i%4 = 0 then t 0 else if i%4 = 1 then t 1 else
        if i%4 = 2 then -t 0 else -t 1 := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero => intro hi; simp
    | one => intro hi; simp
    | more i ih0 ih1 =>
      intro hi
      rw [hrec i hi, ih0 (by omega)]
      have hm : i%4 < 4 := Nat.mod_lt _ (by omega)
      have hm2 : (i+2)%4 = (i%4+2)%4 := by omega
      interval_cases h : i%4 <;> simp [hm2]
  have hend : t L = t 0 := by simp [t,L]
  have hpL := hperiod L (le_refl L)
  have hpLm := hperiod (L-1) (by omega)
  have hm : L%4 < 4 := Nat.mod_lt _ (by omega)
  have hm0 : L%4 ≠ 0 := by intro he; exact hnotfour (Nat.dvd_of_mod_eq_zero he)
  have ht0 : t 0 = 0 := by
    interval_cases h : L%4
    · exact False.elim (hm0 rfl)
    · have hprev : (L-1)%4 = 0 := by omega
      simp at hpL
      simp [hprev] at hpLm
      linarith
    · simp at hpL
      linarith
    · have hprev : (L-1)%4 = 2 := by omega
      simp at hpL
      simp [hprev] at hpLm
      linarith
  simpa [t] using ht0

#print axioms actual_crossGram_kernel_trivial
#check actual_crossGram_kernel_trivial
end D5.S3.Combinatorics.Graph.URSActualNonsingularity
