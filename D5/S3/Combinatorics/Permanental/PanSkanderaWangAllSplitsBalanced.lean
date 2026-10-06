/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBalanced
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBalanced
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: The balanced permanental inequality follows from the frozen Bruhat map. -/

/- Mathematical classification:
   balanced:
     proof_shape: content
     escape_witness: pairedPerm_bijective: finite-cardinality surjectivity of the paired map
   admission_basis: escape-witness
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     D5/S3/Combinatorics/PanSkanderaWangBruhat.result
     D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.A
     D5/S3/Combinatorics/PanSkanderaWangBruhatDefs.f
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsBijection
import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsBlock

open Finset Equiv
open D5.S3.Combinatorics.PanSkanderaWangBruhat
namespace PSW
open scoped Classical

private noncomputable def prefixEquiv (n h : ℕ) (hh : h ≤ n) : Fin h ≃ prefixIndices n h :=
  Equiv.ofBijective (fun i : Fin h => ⟨⟨i.val, by omega⟩, by simp [prefixIndices, i.isLt]⟩) (by
    constructor
    · intro i j hij; apply Fin.ext; exact congrArg (fun k => k.val.val) hij
    · intro i
      have hi : i.val.val < h := by simpa [prefixIndices] using i.property
      refine ⟨⟨i.val.val, hi⟩, ?_⟩
      apply Subtype.ext; rfl)

private noncomputable def prefixComplEquiv (n h : ℕ) (hh : h ≤ n) : Fin (n - h) ≃
    {i : Fin n // i ∉ prefixIndices n h} :=
  Equiv.ofBijective (fun i : Fin (n - h) => ⟨⟨h + i.val, by omega⟩, by simp [prefixIndices] <;> omega⟩) (by
    constructor
    · intro i j hij; apply Fin.ext; have he := congrArg (fun k => k.val.val) hij; dsimp at he; omega
    · intro i
      have hi : h ≤ i.val.val := by simpa [prefixIndices] using i.property
      refine ⟨⟨i.val.val - h, by have hn := i.val.isLt; omega⟩, ?_⟩
      apply Subtype.ext; apply Fin.ext; simp; omega)

private noncomputable def evenEquiv (n : ℕ) : Fin (n / 2) ≃ evenIndices n :=
  Equiv.ofBijective (fun i : Fin (n / 2) => ⟨⟨2 * i.val + 1, by omega⟩, by simp [evenIndices] <;> omega⟩) (by
    constructor
    · intro i j hij; apply Fin.ext; have he := congrArg (fun k => k.val.val) hij; dsimp at he; omega
    · intro i
      have hi : (i.val.val + 1) % 2 = 0 := by simpa [evenIndices] using i.property
      refine ⟨⟨i.val.val / 2, by have hn := i.val.isLt; omega⟩, ?_⟩
      apply Subtype.ext; apply Fin.ext; simp; omega)

private noncomputable def oddEquiv (n : ℕ) : Fin (n - n / 2) ≃ {i : Fin n // i ∉ evenIndices n} :=
  Equiv.ofBijective (fun i : Fin (n - n / 2) => ⟨⟨2 * i.val, by omega⟩, by simp [evenIndices] <;> omega⟩) (by
    constructor
    · intro i j hij; apply Fin.ext; have he := congrArg (fun k => k.val.val) hij; dsimp at he; omega
    · intro i
      have hi : (i.val.val + 1) % 2 ≠ 0 := by simpa [evenIndices] using i.property
      refine ⟨⟨i.val.val / 2, by have hn := i.val.isLt; omega⟩, ?_⟩
      apply Subtype.ext; apply Fin.ext; simp; omega)

private noncomputable def pairedPerm {n : ℕ} (hn : 4 ≤ n)
    (w : {w : Perm (Fin n) // Preserves (prefixIndices n (n / 2)) w}) :
    {u : Perm (Fin n) // Preserves (evenIndices n) u} := by
  have word_permutation {n : ℕ} (w : Perm (Fin n)) : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n (word w) := by
    unfold D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm word
    apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_range' (s := 1) (n := n))).mpr
    · intro x
      simp only [List.mem_ofFn, List.mem_range']
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(w i).val, (w i).isLt, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨w.symm ⟨j, hj⟩, by simp [Nat.add_comm]⟩
    · rw [List.nodup_ofFn]
      intro i j hij
      apply w.injective
      apply Fin.ext
      change (w i).val + 1 = (w j).val + 1 at hij
      omega
  have prefix_word {n h : ℕ} (hh : h ≤ n) (w : Perm (Fin n)) :
      ((word w).take h).Perm (List.range' 1 h) ↔ Preserves (prefixIndices n h) w := by
    classical
    have hl : (word w).length = n := by simp [word]
    have hclosed : ((word w).take h).Perm (List.range' 1 h) ↔
        ∀ i : Fin n, i.val < h → (w i).val < h := by
      constructor
      · intro hp i hi
        have him : (w i).val + 1 ∈ (word w).take h := by
          have hig : i.val < ((word w).take h).length := by simp [word]; omega
          have hget := List.getElem_mem (l := (word w).take h) hig
          simpa [word] using hget
        have hr := hp.subset him
        simp only [List.mem_range'] at hr
        obtain ⟨j, hj, he⟩ := hr
        omega
      · intro hc
        have hnd : ((word w).take h).Nodup := (word_permutation w).nodup_iff.mpr
          (List.nodup_range' (s := 1) (n := n)) |>.take
        apply (List.perm_ext_iff_of_nodup hnd (List.nodup_range' (s := 1) (n := h))).mpr
        intro v
        constructor
        · intro hv
          obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hv
          have hin : i < n := by simp [word] at hi; omega
          have hih : i < h := by simp [word] at hi; omega
          have hbound := hc ⟨i, hin⟩ hih
          simp only [List.getElem_take, word, List.getElem_ofFn] at he
          apply List.mem_range'.mpr
          exact ⟨(w ⟨i, hin⟩).val, hbound, by omega⟩
        · intro hv
          obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hv
          let t : Fin n := ⟨j, by omega⟩
          have ht : t ∈ prefixIndices n h := by simp [prefixIndices, t, hj]
          have hc' : ∀ i ∈ prefixIndices n h, w i ∈ prefixIndices n h := by
            intro i hi
            simp only [prefixIndices, mem_filter, mem_univ, true_and] at hi ⊢
            exact hc i hi
          have hwt := Equiv.Perm.perm_symm_on_of_perm_on_finset hc' ht
          have hih : (w.symm t).val < h := by simpa [prefixIndices] using hwt
          have him : (w.symm t).val < ((word w).take h).length := by simp [word]; omega
          have hhmem := List.getElem_mem (l := (word w).take h) him
          simpa [word, t, Nat.add_comm] using hhmem
    rw [hclosed]
    constructor
    · intro hc i
      have hc' : ∀ i ∈ prefixIndices n h, w i ∈ prefixIndices n h := by
        intro i hi
        simp only [prefixIndices, mem_filter, mem_univ, true_and] at hi ⊢
        exact hc i hi
      constructor
      · intro hwi
        simpa using Equiv.Perm.perm_symm_on_of_perm_on_finset hc' hwi
      · exact hc' i
    · intro hp i hi
      have h := (hp i).2 (by simp [prefixIndices, hi])
      simpa [prefixIndices] using h

  have word_A {n : ℕ} (w : Perm (Fin n)) :
      D5.S3.Combinatorics.PanSkanderaWangBruhat.A n (word w) ↔ Preserves (prefixIndices n (n / 2)) w := by
    unfold D5.S3.Combinatorics.PanSkanderaWangBruhat.A
    rw [and_iff_right (word_permutation w)]
    exact prefix_word (by omega) w

  have word_B {n : ℕ} (w : Perm (Fin n)) :
      B n (word w) ↔ Preserves (evenIndices n) w := by
    constructor
    · intro hb i
      have hp := hb.2 i.val (by simpa [word] using i.isLt)
      simp only [word, List.getElem_ofFn, Fin.eta] at hp
      change ((w i).val + 1) % 2 = (i.val + 1) % 2 at hp
      simp only [evenIndices, mem_filter, mem_univ, true_and]
      omega
    · intro hb
      refine ⟨word_permutation w, ?_⟩
      intro k hk
      have hkn : k < n := by simpa [word] using hk
      have hp := hb ⟨k, hkn⟩
      simp only [evenIndices, mem_filter, mem_univ, true_and] at hp
      simp only [word, List.getElem_ofFn]
      omega
  have ofWord_value_bounds {n : ℕ} {x : List ℕ} (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) (i : Fin n) :
      1 ≤ x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ∧
      x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ≤ n := by
    have hl : x.length = n := by simpa [D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm] using hx.length_eq
    have hm := hx.subset (List.getElem_mem (l := x) (n := i.val) (by omega))
    simp only [List.mem_range'] at hm
    obtain ⟨j, hj, he⟩ := hm
    omega
  have ofWord_apply {n : ℕ} (x : List ℕ) (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) (i : Fin n) :
      (ofWord x hx i).val + 1 = x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) := by
    change (x[i.val]'_ - 1) + 1 = _
    have h := ofWord_value_bounds hx i
    omega
  have word_ofWord {n : ℕ} (x : List ℕ) (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) :
      word (ofWord x hx) = x := by
    have hl : x.length = n := by simpa [D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm] using hx.length_eq
    apply List.ext_getElem
    · simp [word, hl]
    · intro i hi h'i
      simp only [word, List.getElem_ofFn]
      have hin : i < n := by simpa [word] using hi
      exact ofWord_apply x hx ⟨i, hin⟩
  have hw : A n (word w.1) := (word_A w.1).mpr w.2
  have hu := f_image_B n hn (word w.1) hw
  refine ⟨ofWord (f n (word w.1)) hu.1, ?_⟩
  apply (word_B _).mp
  rw [word_ofWord]
  exact hu

private theorem pairedPerm_bijective {n : ℕ} (hn : 4 ≤ n) : Function.Bijective (pairedPerm hn) := by
  have word_injective {n : ℕ} : Function.Injective (word : Perm (Fin n) → List ℕ) := by
    intro w u h
    have he := List.ofFn_injective h
    apply Equiv.ext
    intro i
    have hh := congrFun he i
    apply Fin.ext
    omega
  have word_permutation {n : ℕ} (w : Perm (Fin n)) : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n (word w) := by
    unfold D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm word
    apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_range' (s := 1) (n := n))).mpr
    · intro x
      simp only [List.mem_ofFn, List.mem_range']
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(w i).val, (w i).isLt, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨w.symm ⟨j, hj⟩, by simp [Nat.add_comm]⟩
    · rw [List.nodup_ofFn]
      intro i j hij
      apply w.injective
      apply Fin.ext
      change (w i).val + 1 = (w j).val + 1 at hij
      omega
  have prefix_word {n h : ℕ} (hh : h ≤ n) (w : Perm (Fin n)) :
      ((word w).take h).Perm (List.range' 1 h) ↔ Preserves (prefixIndices n h) w := by
    classical
    have hl : (word w).length = n := by simp [word]
    have hclosed : ((word w).take h).Perm (List.range' 1 h) ↔
        ∀ i : Fin n, i.val < h → (w i).val < h := by
      constructor
      · intro hp i hi
        have him : (w i).val + 1 ∈ (word w).take h := by
          have hig : i.val < ((word w).take h).length := by simp [word]; omega
          have hget := List.getElem_mem (l := (word w).take h) hig
          simpa [word] using hget
        have hr := hp.subset him
        simp only [List.mem_range'] at hr
        obtain ⟨j, hj, he⟩ := hr
        omega
      · intro hc
        have hnd : ((word w).take h).Nodup := (word_permutation w).nodup_iff.mpr
          (List.nodup_range' (s := 1) (n := n)) |>.take
        apply (List.perm_ext_iff_of_nodup hnd (List.nodup_range' (s := 1) (n := h))).mpr
        intro v
        constructor
        · intro hv
          obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hv
          have hin : i < n := by simp [word] at hi; omega
          have hih : i < h := by simp [word] at hi; omega
          have hbound := hc ⟨i, hin⟩ hih
          simp only [List.getElem_take, word, List.getElem_ofFn] at he
          apply List.mem_range'.mpr
          exact ⟨(w ⟨i, hin⟩).val, hbound, by omega⟩
        · intro hv
          obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hv
          let t : Fin n := ⟨j, by omega⟩
          have ht : t ∈ prefixIndices n h := by simp [prefixIndices, t, hj]
          have hc' : ∀ i ∈ prefixIndices n h, w i ∈ prefixIndices n h := by
            intro i hi
            simp only [prefixIndices, mem_filter, mem_univ, true_and] at hi ⊢
            exact hc i hi
          have hwt := Equiv.Perm.perm_symm_on_of_perm_on_finset hc' ht
          have hih : (w.symm t).val < h := by simpa [prefixIndices] using hwt
          have him : (w.symm t).val < ((word w).take h).length := by simp [word]; omega
          have hhmem := List.getElem_mem (l := (word w).take h) him
          simpa [word, t, Nat.add_comm] using hhmem
    rw [hclosed]
    constructor
    · intro hc i
      have hc' : ∀ i ∈ prefixIndices n h, w i ∈ prefixIndices n h := by
        intro i hi
        simp only [prefixIndices, mem_filter, mem_univ, true_and] at hi ⊢
        exact hc i hi
      constructor
      · intro hwi
        simpa using Equiv.Perm.perm_symm_on_of_perm_on_finset hc' hwi
      · exact hc' i
    · intro hp i hi
      have h := (hp i).2 (by simp [prefixIndices, hi])
      simpa [prefixIndices] using h

  have word_A {n : ℕ} (w : Perm (Fin n)) :
      D5.S3.Combinatorics.PanSkanderaWangBruhat.A n (word w) ↔ Preserves (prefixIndices n (n / 2)) w := by
    unfold D5.S3.Combinatorics.PanSkanderaWangBruhat.A
    rw [and_iff_right (word_permutation w)]
    exact prefix_word (by omega) w
  have ofWord_value_bounds {n : ℕ} {x : List ℕ} (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) (i : Fin n) :
      1 ≤ x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ∧
      x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ≤ n := by
    have hl : x.length = n := by simpa [D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm] using hx.length_eq
    have hm := hx.subset (List.getElem_mem (l := x) (n := i.val) (by omega))
    simp only [List.mem_range'] at hm
    obtain ⟨j, hj, he⟩ := hm
    omega
  have ofWord_apply {n : ℕ} (x : List ℕ) (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) (i : Fin n) :
      (ofWord x hx i).val + 1 = x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) := by
    change (x[i.val]'_ - 1) + 1 = _
    have h := ofWord_value_bounds hx i
    omega
  have word_ofWord {n : ℕ} (x : List ℕ) (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) :
      word (ofWord x hx) = x := by
    have hl : x.length = n := by simpa [D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm] using hx.length_eq
    apply List.ext_getElem
    · simp [word, hl]
    · intro i hi h'i
      simp only [word, List.getElem_ofFn]
      have hin : i < n := by simpa [word] using hi
      exact ofWord_apply x hx ⟨i, hin⟩
  have pairedPerm_injective {n : ℕ} (hn : 4 ≤ n) : Function.Injective (pairedPerm hn) := by
    intro w z h
    have hw : A n (word w.1) := (word_A w.1).mpr w.2
    have hz : A n (word z.1) := (word_A z.1).mpr z.2
    have he := congrArg (fun v => word v.val) h
    change word (ofWord (f n (word w.val)) (f_image_B n hn (word w.val) hw).1) =
      word (ofWord (f n (word z.val)) (f_image_B n hn (word z.val) hz).1) at he
    rw [word_ofWord, word_ofWord] at he
    have hwords := f_injective n hn (word w.val) (word z.val) hw hz he
    exact Subtype.ext (word_injective hwords)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨pairedPerm_injective hn, ?_⟩
  rw [← Fintype.card_congr (blockEquiv (prefixIndices n (n / 2))),
    ← Fintype.card_congr (blockEquiv (evenIndices n)), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_perm, Fintype.card_perm, Fintype.card_perm, Fintype.card_perm]
  have hp := Fintype.card_congr (prefixEquiv n (n / 2) (by omega))
  have hc := Fintype.card_congr (prefixComplEquiv n (n / 2) (by omega))
  have he := Fintype.card_congr (evenEquiv n)
  have ho := Fintype.card_congr (oddEquiv n)
  simp only [Fintype.card_fin] at hp hc he ho
  rw [← hp, ← hc, ← he, ← ho]

private theorem chain_monomial {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A)
    {w u : Perm (Fin n)} (hc : Relation.ReflTransGen UpStep w u) : monomial A u ≤ monomial A w := by
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
  apply hc.trans_induction_on (motive := fun {w u} _ => monomial A u ≤ monomial A w)
  · intro w; exact le_rfl
  · intro w u hstep
    rcases hstep with ⟨i, j, hij, hwi, rfl⟩
    exact chain_step hA w hij hwi
  · intro w v u _ _ h1 h2
    exact le_trans h2 h1

/-- The balanced permanental inequality for the complete range of the frozen theorem. -/
theorem balanced {n : ℕ} (hn : 4 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : TNN A) :
    principalPermanent A (evenIndices n) * principalPermanent A (univ \ evenIndices n) ≤
    principalPermanent A (prefixIndices n (n / 2)) *
      principalPermanent A (univ \ prefixIndices n (n / 2)) := by
  have word_permutation {n : ℕ} (w : Perm (Fin n)) : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n (word w) := by
    unfold D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm word
    apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_range' (s := 1) (n := n))).mpr
    · intro x
      simp only [List.mem_ofFn, List.mem_range']
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(w i).val, (w i).isLt, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨w.symm ⟨j, hj⟩, by simp [Nat.add_comm]⟩
    · rw [List.nodup_ofFn]
      intro i j hij
      apply w.injective
      apply Fin.ext
      change (w i).val + 1 = (w j).val + 1 at hij
      omega
  have ofWord_value_bounds {n : ℕ} {x : List ℕ} (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) (i : Fin n) :
      1 ≤ x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ∧
      x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) ≤ n := by
    have hl : x.length = n := by simpa [D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm] using hx.length_eq
    have hm := hx.subset (List.getElem_mem (l := x) (n := i.val) (by omega))
    simp only [List.mem_range'] at hm
    obtain ⟨j, hj, he⟩ := hm
    omega
  have ofWord_apply {n : ℕ} (x : List ℕ) (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) (i : Fin n) :
      (ofWord x hx i).val + 1 = x[i.val]'(by have hh := hx.length_eq; simp at hh; omega) := by
    change (x[i.val]'_ - 1) + 1 = _
    have h := ofWord_value_bounds hx i
    omega
  have ofWord_word {n : ℕ} (w : Perm (Fin n)) : ofWord (word w) (word_permutation w) = w := by
    apply Equiv.ext
    intro i
    have hh := ofWord_apply (word w) (word_permutation w) i
    simp only [word, List.getElem_ofFn, Fin.eta] at hh
    change (ofWord (word w) (word_permutation w) i).val + 1 = (w i).val + 1 at hh
    apply Fin.ext
    omega

  have prefix_word {n h : ℕ} (hh : h ≤ n) (w : Perm (Fin n)) :
      ((word w).take h).Perm (List.range' 1 h) ↔ Preserves (prefixIndices n h) w := by
    classical
    have hl : (word w).length = n := by simp [word]
    have hclosed : ((word w).take h).Perm (List.range' 1 h) ↔
        ∀ i : Fin n, i.val < h → (w i).val < h := by
      constructor
      · intro hp i hi
        have him : (w i).val + 1 ∈ (word w).take h := by
          have hig : i.val < ((word w).take h).length := by simp [word]; omega
          have hget := List.getElem_mem (l := (word w).take h) hig
          simpa [word] using hget
        have hr := hp.subset him
        simp only [List.mem_range'] at hr
        obtain ⟨j, hj, he⟩ := hr
        omega
      · intro hc
        have hnd : ((word w).take h).Nodup := (word_permutation w).nodup_iff.mpr
          (List.nodup_range' (s := 1) (n := n)) |>.take
        apply (List.perm_ext_iff_of_nodup hnd (List.nodup_range' (s := 1) (n := h))).mpr
        intro v
        constructor
        · intro hv
          obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hv
          have hin : i < n := by simp [word] at hi; omega
          have hih : i < h := by simp [word] at hi; omega
          have hbound := hc ⟨i, hin⟩ hih
          simp only [List.getElem_take, word, List.getElem_ofFn] at he
          apply List.mem_range'.mpr
          exact ⟨(w ⟨i, hin⟩).val, hbound, by omega⟩
        · intro hv
          obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hv
          let t : Fin n := ⟨j, by omega⟩
          have ht : t ∈ prefixIndices n h := by simp [prefixIndices, t, hj]
          have hc' : ∀ i ∈ prefixIndices n h, w i ∈ prefixIndices n h := by
            intro i hi
            simp only [prefixIndices, mem_filter, mem_univ, true_and] at hi ⊢
            exact hc i hi
          have hwt := Equiv.Perm.perm_symm_on_of_perm_on_finset hc' ht
          have hih : (w.symm t).val < h := by simpa [prefixIndices] using hwt
          have him : (w.symm t).val < ((word w).take h).length := by simp [word]; omega
          have hhmem := List.getElem_mem (l := (word w).take h) him
          simpa [word, t, Nat.add_comm] using hhmem
    rw [hclosed]
    constructor
    · intro hc i
      have hc' : ∀ i ∈ prefixIndices n h, w i ∈ prefixIndices n h := by
        intro i hi
        simp only [prefixIndices, mem_filter, mem_univ, true_and] at hi ⊢
        exact hc i hi
      constructor
      · intro hwi
        simpa using Equiv.Perm.perm_symm_on_of_perm_on_finset hc' hwi
      · exact hc' i
    · intro hp i hi
      have h := (hp i).2 (by simp [prefixIndices, hi])
      simpa [prefixIndices] using h

  have word_A {n : ℕ} (w : Perm (Fin n)) :
      D5.S3.Combinatorics.PanSkanderaWangBruhat.A n (word w) ↔ Preserves (prefixIndices n (n / 2)) w := by
    unfold D5.S3.Combinatorics.PanSkanderaWangBruhat.A
    rw [and_iff_right (word_permutation w)]
    exact prefix_word (by omega) w

  have word_ofWord {n : ℕ} (x : List ℕ) (hx : D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm n x) :
      word (ofWord x hx) = x := by
    have hl : x.length = n := by simpa [D5.S3.Combinatorics.PanSkanderaWangBruhat.IsPerm] using hx.length_eq
    apply List.ext_getElem
    · simp [word, hl]
    · intro i hi h'i
      simp only [word, List.getElem_ofFn]
      have hin : i < n := by simpa [word] using hi
      exact ofWord_apply x hx ⟨i, hin⟩
  have rank_word {n : ℕ} (w : Perm (Fin n)) (p q : ℕ) :
      (D5.S3.Combinatorics.PanSkanderaWangBruhat.rank (word w) p (q + 1) : ℤ) = rankF w p q := by
    classical
    have hcount : ∀ l : List ℕ,
        (((l.filter (fun v => decide (q + 1 ≤ v))).length : ℕ) : ℤ) =
        (l.map (fun v => if q + 1 ≤ v then (1 : ℤ) else 0)).sum := by
      intro l
      simpa using (List.sum_map_ite (fun v : ℕ => q + 1 ≤ v)
        (fun _ => (1 : ℤ)) (fun _ => (0 : ℤ)) l).symm
    unfold D5.S3.Combinatorics.PanSkanderaWangBruhat.rank
    rw [hcount, List.map_take]
    unfold word
    rw [← List.ofFn_comp', List.sum_take_ofFn]
    unfold rankF
    rw [sum_filter]
    apply sum_congr rfl
    intro k hk
    by_cases hkp : k.val < p <;> simp [hkp]
  have frozen_bruhat_chain {n : ℕ} (x y : List ℕ) (hxy : D5.S3.Combinatorics.PanSkanderaWangBruhat.BruhatLE n x y) :
      Relation.ReflTransGen UpStep (ofWord x hxy.1) (ofWord y hxy.2.1) := by
    apply rank_to_chain
    intro p q
    have h := hxy.2.2 p (q + 1)
    have hz : (D5.S3.Combinatorics.PanSkanderaWangBruhat.rank x p (q + 1) : ℤ) ≤ D5.S3.Combinatorics.PanSkanderaWangBruhat.rank y p (q + 1) := by exact_mod_cast h
    have hxrank := rank_word (ofWord x hxy.1) p q
    have hyrank := rank_word (ofWord y hxy.2.1) p q
    rw [word_ofWord] at hxrank hyrank
    rw [← hxrank, ← hyrank]
    exact hz
  rw [permanent_block_expansion, permanent_block_expansion]
  rw [← Equiv.sum_comp (Equiv.ofBijective (pairedPerm hn) (pairedPerm_bijective hn))]
  apply Finset.sum_le_sum
  intro w _
  have hw : D5.S3.Combinatorics.PanSkanderaWangBruhat.A n (word w.1) := (word_A w.1).mpr w.2
  have hbr := D5.S3.Combinatorics.PanSkanderaWangBruhat.result n hn (word w.1) hw
  have hc := frozen_bruhat_chain (word w.1) (f n (word w.1)) hbr
  have hm : monomial A (ofWord (f n (word w.1)) hbr.2.1) ≤ monomial A (ofWord (word w.1) hbr.1) := by
    exact chain_monomial hA hc
  have he : ofWord (word w.1) hbr.1 = w.1 := ofWord_word _
  rw [he] at hm
  exact hm

#print axioms balanced
end PSW
