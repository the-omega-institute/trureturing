/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicOrders
   mirror-E: none(waiver:position-calculus-for-doubled-words)
   anchors: [mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: Relates doubled-word nonnesting to equal first and second occurrence orders. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.Data.List.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

def secondPos (a : ℕ) (w : List ℕ) : ℕ :=
  (w).idxOf a + 1 + (w.drop ((w).idxOf a + 1)).idxOf a

theorem count_two_decomposition (a : ℕ) (w : List ℕ)
    (hw : w.count a = 2) :
    ∃ u v z : List ℕ, a ∉ u ∧ a ∉ v ∧ a ∉ z ∧
      w = u ++ [a] ++ v ++ [a] ++ z := by
  have one : ∀ t : List ℕ, t.count a = 1 →
      ∃ u v : List ℕ, a ∉ u ∧ a ∉ v ∧ t = u ++ [a] ++ v := by
    intro t
    induction t with
    | nil => simp
    | cons b t ih =>
      intro h
      by_cases hba : b = a
      · subst b
        have ht : t.count a = 0 := by simpa using h
        refine ⟨[], t, by simp, ?_, by simp⟩
        simpa [List.count_eq_zero] using ht
      · have ht : t.count a = 1 := by simpa [hba] using h
        obtain ⟨u, v, hu, hv, heq⟩ := ih ht
        refine ⟨b :: u, v, ?_, hv, ?_⟩
        · simp [Ne.symm hba, hu]
        · simp [heq]
  induction w with
  | nil => simp at hw
  | cons b w ih =>
    by_cases hba : b = a
    · subst b
      have htail : w.count a = 1 := by simpa using hw
      obtain ⟨v, z, hv, hz, heq⟩ := one w htail
      refine ⟨[], v, z, by simp, hv, hz, ?_⟩
      simp [heq]
    · have htail : w.count a = 2 := by simpa [hba] using hw
      obtain ⟨u, v, z, hu, hv, hz, heq⟩ := ih htail
      refine ⟨b :: u, v, z, ?_, hv, hz, ?_⟩
      · simp [Ne.symm hba, hu]
      · simp [heq]

theorem doubled_count (n a : ℕ) (w : List ℕ)
    (hw : w.Perm ((List.range' 1 n).flatMap fun i => [i, i]))
    (ha : a ∈ List.range' 1 n) : w.count a = 2 := by
  rw [hw.count_eq]
  have hcount : ∀ l : List ℕ,
      (l.flatMap fun i => [i, i]).count a = 2 * l.count a := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        simp [ih]
        omega
      · simp [ih, hxa]
  rw [hcount]
  have hnodup : (List.range' 1 n).Nodup := List.nodup_range'
  rw [List.count_eq_one_of_mem hnodup ha]

theorem nesting_of_reversal (w : List ℕ) (a b : ℕ)
    (ha : w.count a = 2) (hb : w.count b = 2) (hab : a ≠ b)
    (hfirst : (w).idxOf a < (w).idxOf b)
    (hsecond : secondPos b w < secondPos a w) :
    NonnestingDefs.Occurs [1, 2, 2, 1] w ∨
      NonnestingDefs.Occurs [2, 1, 1, 2] w := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  have pa := count_two_positions a w ha
  have pb := count_two_positions b w hb
  have hfa : (w).idxOf a < w.length := by
    exact (List.getElem?_eq_some_iff.mp pa.2.1).1
  have hfb : (w).idxOf b < w.length := by
    exact (List.getElem?_eq_some_iff.mp pb.2.1).1
  have hsb : secondPos b w < w.length := by
    exact (List.getElem?_eq_some_iff.mp pb.2.2).1
  have hsa : secondPos a w < w.length := by
    exact (List.getElem?_eq_some_iff.mp pa.2.2).1
  have hmiddle : (w).idxOf b < secondPos b w := pb.1
  have vfa : w[(w).idxOf a] = a := (List.getElem?_eq_some_iff.mp pa.2.1).2
  have vfb : w[(w).idxOf b] = b := (List.getElem?_eq_some_iff.mp pb.2.1).2
  have vsb : w[secondPos b w] = b := (List.getElem?_eq_some_iff.mp pb.2.2).2
  have vsa : w[secondPos a w] = a := (List.getElem?_eq_some_iff.mp pa.2.2).2
  let p : Fin 4 → ℕ := fun j =>
    if j.val = 0 then (w).idxOf a else
    if j.val = 1 then (w).idxOf b else
    if j.val = 2 then secondPos b w else secondPos a w
  have hp : ∀ j : Fin 4, p j < w.length := by
    intro j
    fin_cases j <;> simp [p, hfa, hfb, hsb, hsa]
  let f : Fin 4 ↪o Fin w.length :=
    OrderEmbedding.ofMapLEIff (fun j => ⟨p j, hp j⟩) (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [p] <;> omega)
  have hsub : List.Sublist [a, b, b, a] w := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨f, ?_⟩
    intro j
    fin_cases j <;> simp [f, p, vfa, vfb, vsb, vsa]
  rcases lt_or_gt_of_ne hab with hab | hba
  · left
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨(fun i => if i = 1 then a else b), ?_, ?_, ?_, by simp⟩
    · intro i hi hik
      simp [NonnestingDefs.letters] at hik
      have : i = 1 := by omega
      simpa [this] using hab
    · intro i hi hik
      simp [NonnestingDefs.letters] at hik
      have hi' : i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl
      · simpa using (List.mem_of_getElem? pa.2.1)
      · simpa using (List.mem_of_getElem? pb.2.1)
    · simpa using hsub
  · right
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨(fun i => if i = 1 then b else a), ?_, ?_, ?_, by simp⟩
    · intro i hi hik
      simp [NonnestingDefs.letters] at hik
      have : i = 1 := by omega
      simpa [this] using hba
    · intro i hi hik
      simp [NonnestingDefs.letters] at hik
      have hi' : i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl
      · simpa using (List.mem_of_getElem? pb.2.1)
      · simpa using (List.mem_of_getElem? pa.2.1)
    · simpa using hsub

theorem nonnesting_iff_equal_orders (w : List ℕ)
    (hcount : ∀ a ∈ w, w.count a = 2) :
    (¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) ↔
      ∀ a ∈ w, ∀ b ∈ w,
        (w).idxOf a < (w).idxOf b → secondPos a w < secondPos b w := by
  have count_two_positions (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) :
      (w).idxOf a < secondPos a w ∧
        w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
    obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    constructor
    · rw [hfirst, hsecond]
      omega
    constructor
    · rw [hfirst]
      simp
    · rw [hsecond]
      have hle : ¬ u.length + 1 + v.length < u.length := by omega
      simp [List.getElem?_append, hle]
      have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
      rw [heq]
      simp
  have count_two_position_iff (a : ℕ) (w : List ℕ)
      (hw : w.count a = 2) (i : ℕ) :
      w[i]? = some a ↔ i = (w).idxOf a ∨ i = secondPos a w := by
    obtain ⟨u, v, z, hu, hv, hz, rfl⟩ := count_two_decomposition a w hw
    have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
      simp [List.idxOf_append, hu]
    have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
        u.length + 1 + v.length := by
      have hdrop : u.drop (u.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
    rw [hfirst, hsecond]
    constructor
    · intro hi
      by_cases h0 : i < u.length
      · have hmem : a ∈ u := by
          have : u[i]? = some a := by simpa [List.getElem?_append, h0] using hi
          exact List.mem_of_getElem? this
        exact (hu hmem).elim
      by_cases h1 : i = u.length
      · exact Or.inl h1
      by_cases h2 : i < u.length + 1 + v.length
      · have hmem : a ∈ v := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hlt : i - u.length - 1 < v.length := by omega
          have hiv : v[i - u.length - 1]? = some a := by
            simpa [List.getElem?_append, hlt] using hi''
          exact List.mem_of_getElem? hiv
        exact (hv hmem).elim
      by_cases h3 : i = u.length + 1 + v.length
      · exact Or.inr h3
      · have hmem : a ∈ z := by
          have hi' : (a :: (v ++ a :: z))[i - u.length]? = some a := by
            simpa [List.getElem?_append, h0] using hi
          have heq : i - u.length = (i - u.length - 1) + 1 := by omega
          rw [heq] at hi'
          have hi'' : (v ++ a :: z)[i - u.length - 1]? = some a := by
            simpa using hi'
          have hle : ¬ i - u.length - 1 < v.length := by omega
          have hi''' : (a :: z)[i - u.length - 1 - v.length]? = some a := by
            simpa [List.getElem?_append, hle] using hi''
          have heq' : i - u.length - 1 - v.length =
              (i - u.length - 1 - v.length - 1) + 1 := by omega
          rw [heq'] at hi'''
          have hiz : z[i - u.length - 1 - v.length - 1]? = some a := by
            simpa using hi'''
          exact List.mem_of_getElem? hiz
        exact (hz hmem).elim
    · rintro (rfl | rfl)
      · simp at *
      · have h := (count_two_positions a _ hw).2.2
        rw [hsecond] at h
        exact h
  have reversal_of_abba_sublist (w : List ℕ) (a b : ℕ)
      (ha : w.count a = 2) (hb : w.count b = 2)
      (hsub : List.Sublist [a, b, b, a] w) :
      (w).idxOf a < (w).idxOf b ∧ secondPos b w < secondPos a w := by
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    have h0 : w[(f 0).val]? = some a := by
      rw [List.getElem?_eq_getElem (f 0).isLt]
      have h := hf (0 : Fin 4)
      simpa using h.symm
    have h1 : w[(f 1).val]? = some b := by
      rw [List.getElem?_eq_getElem (f 1).isLt]
      have h := hf (1 : Fin 4)
      simpa using h.symm
    have h2 : w[(f 2).val]? = some b := by
      rw [List.getElem?_eq_getElem (f 2).isLt]
      have h := hf (2 : Fin 4)
      simpa using h.symm
    have h3 : w[(f 3).val]? = some a := by
      rw [List.getElem?_eq_getElem (f 3).isLt]
      have h := hf (3 : Fin 4)
      simpa using h.symm
    have h01 : (f 0).val < (f 1).val :=
      f.strictMono (show (0 : Fin 4) < 1 by decide)
    have h12 : (f 1).val < (f 2).val :=
      f.strictMono (show (1 : Fin 4) < 2 by decide)
    have h23 : (f 2).val < (f 3).val :=
      f.strictMono (show (2 : Fin 4) < 3 by decide)
    have ha0 := (count_two_position_iff a w ha _).mp h0
    have hb1 := (count_two_position_iff b w hb _).mp h1
    have hb2 := (count_two_position_iff b w hb _).mp h2
    have ha3 := (count_two_position_iff a w ha _).mp h3
    have haa := (count_two_positions a w ha).1
    have hbb := (count_two_positions b w hb).1
    rcases ha0 with ha0 | ha0 <;> rcases ha3 with ha3 | ha3 <;>
      rcases hb1 with hb1 | hb1 <;> rcases hb2 with hb2 | hb2 <;> omega
  constructor
  · rintro ⟨h1221, h2112⟩ a ha b hb hfirst
    have hca := hcount a ha
    have hcb := hcount b hb
    have hab : a ≠ b := by
      intro heq
      subst b
      exact (Nat.lt_irrefl _ hfirst)
    have hne : secondPos a w ≠ secondPos b w := by
      intro heq
      have hva := (count_two_positions a w hca).2.2
      have hvb := (count_two_positions b w hcb).2.2
      rw [heq] at hva
      have hab' : a = b := by simpa [hva] using hvb
      exact hab hab'
    by_contra hnot
    have hreverse : secondPos b w < secondPos a w := by omega
    rcases nesting_of_reversal w a b hca hcb hab hfirst hreverse with h | h
    · exact h1221 h
    · exact h2112 h
  · intro horders
    constructor
    · intro hocc
      obtain ⟨x, _, hmem, hsub, _⟩ := hocc
      have hx1 : x 1 ∈ w := hmem 1 (by omega) (by simp [NonnestingDefs.letters])
      have hx2 : x 2 ∈ w := hmem 2 (by omega) (by simp [NonnestingDefs.letters])
      have hsub' : List.Sublist [x 1, x 2, x 2, x 1] w := by
        simpa using hsub
      obtain ⟨hf, hs⟩ :=
        reversal_of_abba_sublist w (x 1) (x 2)
          (hcount (x 1) hx1) (hcount (x 2) hx2) hsub'
      exact (Nat.lt_asymm (horders (x 1) hx1 (x 2) hx2 hf) hs)
    · intro hocc
      obtain ⟨x, _, hmem, hsub, _⟩ := hocc
      have hx1 : x 1 ∈ w := hmem 1 (by omega) (by simp [NonnestingDefs.letters])
      have hx2 : x 2 ∈ w := hmem 2 (by omega) (by simp [NonnestingDefs.letters])
      have hsub' : List.Sublist [x 2, x 1, x 1, x 2] w := by
        simpa using hsub
      obtain ⟨hf, hs⟩ :=
        reversal_of_abba_sublist w (x 2) (x 1)
          (hcount (x 2) hx2) (hcount (x 1) hx1) hsub'
      exact (Nat.lt_asymm (horders (x 2) hx2 (x 1) hx1 hf) hs)

end D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders.nonnesting_iff_equal_orders
