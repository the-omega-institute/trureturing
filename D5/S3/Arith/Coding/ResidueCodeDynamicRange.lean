/- GID: D5/S3/Arith/Coding/ResidueCodeDynamicRange
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/ResidueCodeDynamicRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For positive pairwise-coprime moduli in ascending order, the RRNS code on [0,K) has Hamming distance at least d exactly when K is at most the product of the first n-d+1 moduli. -/

import Mathlib.Data.Finset.Sort
import Mathlib.InformationTheory.Hamming
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'maximum_dynamic_range_iff_min_distance' D5 Golden/Frozen/accepted`
     returned no matches.
   * Public/private repository searches for RRNS, `MinDistanceAtLeast`, `hammingDist`
     with residues, and product divisibility found no covering declaration. The 12 direct
     `D5/S3/Arith` digests were read; `ResidueSeparation` is only a one-modulus result.
   * Pinned Mathlib searches found `Nat.modEq_iff_dvd'`,
     `Fintype.prod_dvd_of_coprime`, `Nat.Coprime.isCoprime`, `Finset.prod_le_prod`,
     `Finset.exists_subset_card_eq`, and Mathlib's `hammingDist`; these supply the CRT
     divisibility, ordered-product, subset-selection, and distance machinery used below.
   * `D5/S3/Arith/ChineseRemainder` packages the two-factor `ZMod.chineseRemainder`
     equivalence, but its signature does not cover a finite family or Hamming distance.
     The proof below therefore reuses the listed Mathlib primitives rather than reproving CRT. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Coding.ResidueCodeDynamicRange

/-- The length-`n` residue word of a natural number for the modulus sequence `m`. -/
def residueWord (m : ℕ → ℕ) (n x : ℕ) : Fin n → ℕ :=
  fun i ↦ x % m i

/-- Every ordered pair of distinct messages below `K` has Hamming distance at least `d`. -/
def MinDistanceAtLeast (m : ℕ → ℕ) (n K d : ℕ) : Prop :=
  ∀ x y, x < y → y < K → d ≤ hammingDist (residueWord m n x) (residueWord m n y)

/-- Product of the first `k` moduli. -/
def prefixProduct (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∏ i : Fin k, m i

/-- A strictly increasing selection of `k` natural indices selects indices no smaller than
their ranks `0, ..., k - 1`. -/
theorem fin_index_le_strict_mono {k n : ℕ} (f : Fin k → Fin n) (hf : StrictMono f)
    (i : Fin k) : (i : ℕ) ≤ (f i : ℕ) := by
  have rank_bound : ∀ r, ∀ j : Fin k, (j : ℕ) = r → (j : ℕ) ≤ (f j : ℕ) := by
    intro r
    induction r with
    | zero =>
        intro j hj
        omega
    | succ r ih =>
        intro j hj
        have hrk : r < k := by omega
        let previous : Fin k := ⟨r, hrk⟩
        have hpreviousValue : (previous : ℕ) = r := rfl
        have hprevious : previous < j := by
          change (previous : ℕ) < (j : ℕ)
          omega
        have hrank := ih previous hpreviousValue
        have hstep : (f previous : ℕ) < (f j : ℕ) := hf hprevious
        omega
  exact rank_bound i i rfl

/-- Residue words agree at pairwise-coprime selected positions exactly when the product of
those moduli divides the ordered message difference. -/
theorem agree_on_iff_prod_dvd {k n : ℕ} (m : ℕ → ℕ) (f : Fin k ↪ Fin n)
    (x y : ℕ) (hxy : x ≤ y)
    (hcoprime : ∀ i j : Fin k, i ≠ j → Nat.Coprime (m (f i)) (m (f j))) :
    (∀ i : Fin k, residueWord m n x (f i) = residueWord m n y (f i)) ↔
      (∏ i : Fin k, m (f i)) ∣ y - x := by
  constructor
  · intro hagree
    have hdivInt :
        (∏ i : Fin k, (m (f i) : ℤ)) ∣ (y : ℤ) - (x : ℤ) := by
      apply Fintype.prod_dvd_of_coprime
      · intro i j hij
        exact (hcoprime i j hij).isCoprime
      · intro i
        exact Nat.modEq_iff_dvd.mp (hagree i)
    have hcast :
        ((∏ i : Fin k, m (f i) : ℕ) : ℤ) ∣ ((y - x : ℕ) : ℤ) := by
      simpa [Int.ofNat_sub hxy] using hdivInt
    exact Int.natCast_dvd_natCast.mp hcast
  · intro hdiv i
    apply (Nat.modEq_iff_dvd' hxy).mpr
    exact (Finset.dvd_prod_of_mem (fun j : Fin k ↦ m (f j)) (Finset.mem_univ i)).trans hdiv

/-- For an ascending positive pairwise-coprime RRNS, distance `d` on messages below `K`
is equivalent to the classical maximum-dynamic-range bound by the first `n - d + 1`
moduli. The reverse implication is witnessed concretely by messages `0` and that prefix
product. -/
theorem maximum_dynamic_range_iff_min_distance (m : ℕ → ℕ) (n d K : ℕ)
    (hdpos : 1 ≤ d) (hdn : d ≤ n)
    (hmonotone : ∀ i j, i ≤ j → j < n → m i ≤ m j)
    (hpositive : ∀ i, i < n → 0 < m i)
    (hcoprime : ∀ i j, i < n → j < n → i ≠ j → Nat.Coprime (m i) (m j)) :
    MinDistanceAtLeast m n K d ↔ K ≤ prefixProduct m (n - d + 1) := by
  let k := n - d + 1
  have hk_le_n : k ≤ n := by
    simp only [k]
    omega
  have hk_pos : 0 < k := by
    simp only [k]
    omega
  constructor
  · intro hdistance
    by_contra hbound
    have hprefix_lt : prefixProduct m k < K := by
      simpa only [k] using Nat.lt_of_not_ge hbound
    have hprefix_pos : 0 < prefixProduct m k := by
      simp only [prefixProduct]
      apply Finset.prod_pos
      intro i _
      exact hpositive i (lt_of_lt_of_le i.isLt hk_le_n)
    let prefixEmbedding : Fin k ↪ Fin n := Fin.castLEEmb hk_le_n
    have hprefixCoprime :
        ∀ i j : Fin k, i ≠ j → Nat.Coprime (m (prefixEmbedding i))
          (m (prefixEmbedding j)) := by
      intro i j hij
      apply hcoprime (prefixEmbedding i) (prefixEmbedding j)
          (prefixEmbedding i).isLt (prefixEmbedding j).isLt
      intro heq
      apply hij
      apply prefixEmbedding.injective
      exact Fin.ext heq
    have hprefixAgree :
        ∀ i : Fin k,
          residueWord m n 0 (prefixEmbedding i) =
            residueWord m n (prefixProduct m k) (prefixEmbedding i) := by
      apply (agree_on_iff_prod_dvd m prefixEmbedding 0 (prefixProduct m k)
        (Nat.zero_le _) hprefixCoprime).mpr
      simp [prefixEmbedding, prefixProduct]
    let disagreements : Finset (Fin n) :=
      Finset.univ.filter fun i ↦
        residueWord m n 0 i ≠ residueWord m n (prefixProduct m k) i
    let agreements : Finset (Fin n) :=
      Finset.univ.filter fun i ↦
        residueWord m n 0 i = residueWord m n (prefixProduct m k) i
    have hpartition : disagreements.card + agreements.card = n := by
      simpa only [disagreements, agreements, not_ne_iff, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.card_filter_add_card_filter_not
          (s := Finset.univ)
          (p := fun i : Fin n ↦
            residueWord m n 0 i ≠ residueWord m n (prefixProduct m k) i))
    let prefixPositions : Finset (Fin n) := Finset.univ.map prefixEmbedding
    have hprefixSubset : prefixPositions ⊆ agreements := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      simp only [agreements, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hprefixAgree j
    have hprefixCard : prefixPositions.card = k := by
      simp only [prefixPositions, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hk_agreements : k ≤ agreements.card := by
      rw [← hprefixCard]
      exact Finset.card_le_card hprefixSubset
    have hsmallDistance :
        hammingDist (residueWord m n 0) (residueWord m n (prefixProduct m k)) < d := by
      change disagreements.card < d
      simp only [k] at hpartition hk_agreements
      omega
    exact (Nat.not_lt_of_ge
      (hdistance 0 (prefixProduct m k) hprefix_pos hprefix_lt)) hsmallDistance
  · intro hbound x y hxy hyK
    by_contra hdistance
    have hdistance_lt :
        hammingDist (residueWord m n x) (residueWord m n y) < d :=
      Nat.lt_of_not_ge hdistance
    let disagreements : Finset (Fin n) :=
      Finset.univ.filter fun i ↦ residueWord m n x i ≠ residueWord m n y i
    let agreements : Finset (Fin n) :=
      Finset.univ.filter fun i ↦ residueWord m n x i = residueWord m n y i
    have hpartition : disagreements.card + agreements.card = n := by
      simpa only [disagreements, agreements, not_ne_iff, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.card_filter_add_card_filter_not
          (s := Finset.univ)
          (p := fun i : Fin n ↦ residueWord m n x i ≠ residueWord m n y i))
    have hdisagreements : disagreements.card < d := by
      simpa only [disagreements, hammingDist] using hdistance_lt
    have hk_agreements : k ≤ agreements.card := by
      simp only [k]
      omega
    obtain ⟨S, hS_subset, hS_card⟩ := Finset.exists_subset_card_eq hk_agreements
    let selection : Fin k ↪o Fin n := S.orderEmbOfFin hS_card
    have hagree :
        ∀ i : Fin k,
          residueWord m n x (selection i) = residueWord m n y (selection i) := by
      intro i
      have hiS : selection i ∈ S := Finset.orderEmbOfFin_mem S hS_card i
      have hiAgree := hS_subset hiS
      simpa only [agreements, Finset.mem_filter, Finset.mem_univ, true_and] using hiAgree
    have hselectedCoprime :
        ∀ i j : Fin k, i ≠ j → Nat.Coprime (m (selection i)) (m (selection j)) := by
      intro i j hij
      apply hcoprime (selection i) (selection j) (selection i).isLt (selection j).isLt
      intro heq
      apply hij
      apply selection.injective
      exact Fin.ext heq
    have hdiv : (∏ i : Fin k, m (selection i)) ∣ y - x :=
      (agree_on_iff_prod_dvd m selection.toEmbedding x y hxy.le
        hselectedCoprime).mp hagree
    have hprefix_le_selected :
        prefixProduct m k ≤ ∏ i : Fin k, m (selection i) := by
      simp only [prefixProduct]
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.zero_le _
      · intro i _
        exact hmonotone i (selection i)
          (fin_index_le_strict_mono selection selection.strictMono i) (selection i).isLt
    have hselected_le_difference : (∏ i : Fin k, m (selection i)) ≤ y - x :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hxy) hdiv
    have hdifference_lt : y - x < K :=
      lt_of_le_of_lt (Nat.sub_le y x) hyK
    have hprefix_bound : K ≤ prefixProduct m k := by simpa only [k] using hbound
    omega

example : MinDistanceAtLeast (fun i ↦ if i = 0 then 2 else 3) 2 2 2 := by
  intro x y hxy hy
  have hx : x = 0 := by omega
  have hy' : y = 1 := by omega
  subst x
  subst y
  decide

#print axioms maximum_dynamic_range_iff_min_distance

end D5.S3.Arith.Coding.ResidueCodeDynamicRange
