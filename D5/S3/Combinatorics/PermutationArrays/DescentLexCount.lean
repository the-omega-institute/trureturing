/- GID: D5/S3/Combinatorics/PermutationArrays/DescentLexCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationArrays/DescentLexCount
   mirror-E: none(waiver:actual-array-count)
   anchors: [mathlib/module/Mathlib.Data.Sym.Card, mathlib/module/Mathlib.Data.Multiset.Sort]
   utility: none
   digest: Three-column permutation arrays split into two constants and four-symbol multisets. -/

import Mathlib.Data.Sym.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationArrays.DescentLexCount

/-- An actual three-element permutation. Coordinates 0,1,2 label the source columns. -/
abbrev Row := Equiv.Perm (Fin 3)

/-- The source symbols 1,2,3, using the strictly increasing relabeling x ↦ x.val + 1. -/
def sourceEntry (r : Row) (j : Fin 3) : ℕ := (r j).val + 1

/-- The literal number of the two adjacent downsteps. -/
def descents (r : Row) : ℕ :=
  (if sourceEntry r 1 < sourceEntry r 0 then 1 else 0) +
    (if sourceEntry r 2 < sourceEntry r 1 then 1 else 0)

/-- Non-strict lexicographic comparison of the three actual entries. -/
def lexLE (r s : Row) : Prop :=
  sourceEntry r 0 < sourceEntry s 0 ∨ sourceEntry r 0 = sourceEntry s 0 ∧
    (sourceEntry r 1 < sourceEntry s 1 ∨ sourceEntry r 1 = sourceEntry s 1 ∧
      sourceEntry r 2 ≤ sourceEntry s 2)

/-- Rows may repeat. The two order conditions refer to the original row indices. -/
def Arrays (n : ℕ) := {a : Fin n → Row //
  Monotone (fun i => descents (a i)) ∧ ∀ i j, i ≤ j → lexLE (a j) (a i)}

private def entries (k : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]] k

private def row (k : Fin 6) : Row where
  toFun := entries k
  invFun := entries (![0, 1, 2, 4, 3, 5] k)
  left_inv := by fin_cases k <;> decide
  right_inv := by fin_cases k <;> decide

private def rank (r : Row) : Fin 6 :=
  if r 0 = 0 then (if r 1 = 1 then 0 else 1)
  else if r 0 = 1 then (if r 1 = 0 then 2 else 3)
  else (if r 1 = 0 then 4 else 5)

private def degree (k : Fin 6) : ℕ := if k = 0 then 0 else if k = 5 then 2 else 1

private theorem row_rank : ∀ r : Row, row (rank r) = r := by decide
private theorem rank_row : ∀ k : Fin 6, rank (row k) = k := by decide
private theorem descents_rank : ∀ r : Row, descents r = degree (rank r) := by decide
private theorem lex_rank : ∀ r s : Row, lexLE r s ↔ rank r ≤ rank s := by
  unfold lexLE
  decide

private abbrev Ranked (n : ℕ) := {f : Fin n → Fin 6 //
  Antitone f ∧ Monotone (fun i => degree (f i))}

private def arrayRankEquiv (n : ℕ) : Arrays n ≃ Ranked n where
  toFun a := ⟨fun i => rank (a.1 i),
    by
      constructor
      · intro i j hij
        exact (lex_rank _ _).mp (a.2.2 i j hij)
      · intro i j hij
        simpa only [descents_rank] using a.2.1 hij⟩
  invFun f := ⟨fun i => row (f.1 i),
    by
      constructor
      · intro i j hij
        simpa only [descents_rank, rank_row] using f.2.2 hij
      · intro i j hij
        apply (lex_rank _ _).mpr
        simpa only [rank_row] using f.2.1 hij⟩
  left_inv a := Subtype.ext (funext fun i => row_rank (a.1 i))
  right_inv f := Subtype.ext (funext fun i => rank_row (f.1 i))

private theorem degree_monotone : Monotone degree := by decide

private theorem degree_fibers : ∀ k : Fin 6,
    (degree k = 0 ↔ k = 0) ∧ (degree k = 2 ↔ k = 5) ∧
    (degree k = 1 ↔ 1 ≤ k.val ∧ k.val ≤ 4) := by decide

/-- Both row conditions force one descent class throughout the same array. -/
private theorem degree_constant {n : ℕ} (f : Ranked n) (i j : Fin n) :
    degree (f.1 i) = degree (f.1 j) := by
  rcases le_total i j with hij | hji
  · exact le_antisymm (f.2.2 hij) (degree_monotone (f.2.1 hij))
  · exact le_antisymm (degree_monotone (f.2.1 hji)) (f.2.2 hji)

private abbrev Weak (n : ℕ) := {f : Fin n → Fin 4 // Antitone f}

private def middleRank (k : Fin 4) : Fin 6 := ⟨k.val + 1, by omega⟩

private theorem middle_degree : ∀ k : Fin 4, degree (middleRank k) = 1 := by decide

private def assemble (n : ℕ) : Bool ⊕ Weak n → Ranked n
  | .inl b => ⟨fun _ => if b then 5 else 0, by
      constructor <;> intro i j hij <;> exact le_rfl⟩
  | .inr w => ⟨fun i => middleRank (w.1 i), by
      constructor
      · intro i j hij
        exact Nat.add_le_add_right (w.2 hij) 1
      · intro i j hij
        simp only [middle_degree, le_refl]⟩

/-- The two extreme constant arrays and every descending middle word are exhaustive. -/
private theorem assemble_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (assemble n) := by
  let z : Fin n := ⟨0, by omega⟩
  constructor
  · intro x y h
    have hv (i : Fin n) := congrArg (fun f : Ranked n => (f.1 i).val) h
    rcases x with b | w <;> rcases y with c | v
    · cases b <;> cases c <;> try rfl
      · have := hv z; simp [assemble] at this
      · have := hv z; simp [assemble] at this
    · cases b <;> have hh := hv z <;> simp [assemble, middleRank] at hh
      have := (v.1 z).isLt
      omega
    · cases c <;> have hh := hv z <;> simp [assemble, middleRank] at hh
      have := (w.1 z).isLt
      omega
    · congr 1
      apply Subtype.ext
      funext i
      apply Fin.ext
      have hh := hv i
      simp only [assemble, middleRank] at hh
      omega
  · intro f
    by_cases h0 : degree (f.1 z) = 0
    · refine ⟨.inl false, Subtype.ext ?_⟩
      funext i
      have hi := (degree_constant f i z).trans h0
      exact ((degree_fibers (f.1 i)).1.mp hi).symm
    · by_cases h2 : degree (f.1 z) = 2
      · refine ⟨.inl true, Subtype.ext ?_⟩
        funext i
        have hi := (degree_constant f i z).trans h2
        exact ((degree_fibers (f.1 i)).2.1.mp hi).symm
      · have hm : ∀ i, 1 ≤ (f.1 i).val ∧ (f.1 i).val ≤ 4 := by
          intro i
          have hc := degree_constant f i z
          have hdegree : degree (f.1 i) = 1 := by
            have := (f.1 i).isLt
            simp only [degree] at hc h0 h2 ⊢
            split_ifs at hc h0 h2 ⊢ <;> omega
          exact (degree_fibers (f.1 i)).2.2.mp hdegree
        let w : Weak n := ⟨fun i => ⟨(f.1 i).val - 1, by have := hm i; omega⟩,
          by
            intro i j hij
            exact Nat.sub_le_sub_right (f.2.1 hij) 1⟩
        refine ⟨.inr w, Subtype.ext ?_⟩
        funext i
        apply Fin.ext
        change (f.1 i).val - 1 + 1 = (f.1 i).val
        have := hm i
        omega

private def weakMultiset (n : ℕ) (w : Weak n) : Sym (Fin 4) n :=
  ⟨(List.ofFn w.1 : Multiset (Fin 4)), by simp⟩

private theorem weakMultiset_bijective (n : ℕ) :
    Function.Bijective (weakMultiset n) := by
  constructor
  · intro w v h
    apply Subtype.ext
    apply List.ofFn_injective
    apply List.Perm.eq_of_sortedGE w.2.sortedGE_ofFn v.2.sortedGE_ofFn
    exact Multiset.coe_eq_coe.mp (congrArg Subtype.val h)
  · intro m
    let l := m.1.sort (· ≥ ·)
    have hl : l.length = n := (Multiset.length_sort (· ≥ ·)).trans m.2
    let w : Weak n := ⟨fun i => l.get ⟨i.val, by omega⟩, by
      intro i j hij
      exact (Multiset.pairwise_sort _ _).sortedGE.antitone_get hij⟩
    refine ⟨w, Subtype.ext ?_⟩
    change (List.ofFn w.1 : Multiset (Fin 4)) = m.1
    have hw : List.ofFn w.1 = l := by
      apply List.ext_getElem
      · simpa using hl.symm
      · intro i hi hj
        simp [w, List.get_eq_getElem]
    rw [hw]
    exact Multiset.sort_eq _ _

/-- A concrete equivalence on the actual array carrier, valid only at positive length. -/
private noncomputable def arrayDecomposition (n : ℕ) (hn : 1 ≤ n) :
    Arrays n ≃ Bool ⊕ Sym (Fin 4) n :=
  (arrayRankEquiv n).trans
    ((Equiv.ofBijective (assemble n) (assemble_bijective n hn)).symm.trans
      (Equiv.sumCongr (Equiv.refl Bool)
        (Equiv.ofBijective (weakMultiset n) (weakMultiset_bijective n))))

/-- The exact OEIS A222001 count for every positive length, on actual permutation arrays. -/
theorem count_arrays (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Arrays n) = 2 + (n + 1) * (n + 2) * (n + 3) / 6 := by
  rw [Nat.card_congr (arrayDecomposition n hn), Nat.card_eq_fintype_card,
    Fintype.card_sum, Fintype.card_bool, Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have heq : 4 + n - 1 = n + 3 := by omega
  rw [heq, ← Nat.choose_symm (by omega : n ≤ n + 3)]
  have hsub : n + 3 - n = 3 := by omega
  rw [hsub, Nat.choose_eq_descFactorial_div_factorial]
  have hp : (n + 3).descFactorial 3 = (n + 1) * (n + 2) * (n + 3) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.mul_one]
    have h1 : n + 3 - 1 = n + 2 := by omega
    have h2 : n + 3 - 2 = n + 1 := by omega
    rw [Nat.sub_zero, h1, h2]
    ring
  rw [hp]
  norm_num [Nat.factorial]

end D5.S3.Combinatorics.PermutationArrays.DescentLexCount
