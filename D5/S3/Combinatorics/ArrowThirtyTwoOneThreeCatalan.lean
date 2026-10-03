/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan
   mirror-E: none(waiver:catalan-enumeration-of-132-avoiders)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Catalan.Basic, mathlib/module/Mathlib.Data.List.GetD, mathlib/module/Mathlib.Data.List.Nodup]
   utility: none
   digest: Adjacent 132 occurrences are equivalent to ordinary 132 occurrences on distinct-entry lists. -/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.SDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan

def Has132 (w : List ℕ) : Prop :=
  ∃ i j k, i < j ∧ j < k ∧ k < w.length ∧
    w.getD i 0 < w.getD k 0 ∧ w.getD k 0 < w.getD j 0

def HasAdj132 (w : List ℕ) : Prop :=
  ∃ i k, i + 1 < k ∧ k < w.length ∧
    w.getD i 0 < w.getD k 0 ∧ w.getD k 0 < w.getD (i + 1) 0

theorem hasAdj132_iff (w : List ℕ) (hw : w.Nodup) : HasAdj132 w ↔ Has132 w := by
  constructor
  · rintro ⟨i, k, hik, hkl, hil, hki⟩
    exact ⟨i, i + 1, k, by omega, hik, hkl, hil, hki⟩
  · rintro ⟨i, j, k, hij, hjk, hkl, hik, hkj⟩
    have bridge : ∀ d : ℕ, ∀ i j k : ℕ,
        j - i = d → i < j → j < k → k < w.length →
        w.getD i 0 < w.getD k 0 → w.getD k 0 < w.getD j 0 →
        ∃ t, i < t ∧ t ≤ j ∧ t < w.length ∧
          w.getD (t - 1) 0 < w.getD k 0 ∧ w.getD k 0 < w.getD t 0 := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
          intro i j k hd hij hjk hkl hik hkj
          by_cases hstep : j = i + 1
          · refine ⟨j, hij, le_rfl, by omega, ?_, hkj⟩
            simpa [hstep] using hik
          · have hij2 : i + 1 < j := by omega
            have hjm : j - 1 < w.length := by omega
            have hne : w.getD (j - 1) 0 ≠ w.getD k 0 := by
              intro heq
              have heq' : w[j - 1] = w[k] := by
                simpa only [List.getD_eq_getElem _ 0 (by omega),
                  List.getD_eq_getElem _ 0 hkl] using heq
              have hidx := (hw.getElem_inj_iff (i := j - 1) (j := k)).mp heq'
              omega
            by_cases hprev : w.getD (j - 1) 0 < w.getD k 0
            · exact ⟨j, hij, le_rfl, by omega, hprev, hkj⟩
            · have hgt : w.getD k 0 < w.getD (j - 1) 0 := by omega
              have hrec : (j - 1) - i < d := by omega
              obtain ⟨t, hit, htj, htl, hprev', hcurr'⟩ :=
                ih ((j - 1) - i) hrec i (j - 1) k rfl (by omega) (by omega)
                  hkl hik hgt
              exact ⟨t, hit, by omega, htl, hprev', hcurr'⟩
    obtain ⟨t, hit, htj, htl, hprev, hcurr⟩ :=
      bridge (j - i) i j k rfl hij hjk hkl hik hkj
    have htpos : 1 ≤ t := by omega
    refine ⟨t - 1, k, by omega, hkl, hprev, ?_⟩
    simpa [Nat.sub_add_cancel htpos] using hcurr


theorem avoids132_append_max_iff (L R : List ℕ) (m : ℕ)
    (hL : ∀ a ∈ L, a < m) (hR : ∀ c ∈ R, c < m) :
    ¬ Has132 (L ++ m :: R) ↔
      ¬ Has132 L ∧ ¬ Has132 R ∧ ∀ a ∈ L, ∀ c ∈ R, c ≤ a := by
  have left (t : ℕ) (ht : t < L.length) :
      (L ++ m :: R).getD t 0 = L.getD t 0 :=
    List.getD_append _ _ _ _ ht
  have middle : (L ++ m :: R).getD L.length 0 = m := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have right (t : ℕ) (ht : t < R.length) :
      (L ++ m :: R).getD (L.length + 1 + t) 0 = R.getD t 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have heq : L.length + 1 + t - L.length = t + 1 := by omega
    rw [heq]
    rfl
  have left_mem (t : ℕ) (ht : t < L.length) : L.getD t 0 ∈ L := by
    rw [List.getD_eq_getElem _ 0 ht]
    exact List.getElem_mem _
  have right_mem (t : ℕ) (ht : t < R.length) : R.getD t 0 ∈ R := by
    rw [List.getD_eq_getElem _ 0 ht]
    exact List.getElem_mem _
  have cross_occurrence (a c : ℕ) (ha : a ∈ L) (hc : c ∈ R)
      (hac : a < c) (hcm : c < m) : Has132 (L ++ m :: R) := by
    obtain ⟨i, hi, hai⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨k, hk, hck⟩ := List.mem_iff_getElem.mp hc
    have hfirst : (L ++ m :: R).getD i 0 = a := by
      rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ 0 hi]
      exact hai
    have hmiddle : (L ++ m :: R).getD L.length 0 = m := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have hlast : (L ++ m :: R).getD (L.length + 1 + k) 0 = c := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have heq : L.length + 1 + k - L.length = k + 1 := by omega
      rw [heq]
      rw [List.getD_eq_getElem _ 0 (by simp; omega)]
      simpa using hck
    refine ⟨i, L.length, L.length + 1 + k, hi, by omega, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      omega
    · rw [hfirst, hlast]
      exact hac
    · rw [hlast, hmiddle]
      exact hcm
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨i, j, k, hij, hjk, hk, hijk, hkji⟩
      apply h
      refine ⟨i, j, k, hij, hjk, by simp; omega, ?_, ?_⟩
      · simpa only [left i (by omega), left k hk] using hijk
      · simpa only [left k hk, left j (by omega)] using hkji
    · rintro ⟨i, j, k, hij, hjk, hk, hijk, hkji⟩
      apply h
      refine ⟨L.length + 1 + i, L.length + 1 + j, L.length + 1 + k,
        by omega, by omega, by simp; omega, ?_, ?_⟩
      · simpa only [right i (by omega), right k hk] using hijk
      · simpa only [right k hk, right j (by omega)] using hkji
    · intro a ha c hc
      by_contra hca
      have hac : a < c := by omega
      exact h (cross_occurrence a c ha hc hac (hR c hc))
  · rintro ⟨hnotL, hnotR, hcross⟩ ⟨i, j, k, hij, hjk, hk, hik, hkj⟩
    have hklength : k < L.length + 1 + R.length := by
      simp only [List.length_append, List.length_cons] at hk
      omega
    by_cases hjL : j < L.length
    · have hiL : i < L.length := by omega
      by_cases hkL : k < L.length
      · apply hnotL
        exact ⟨i, j, k, hij, hjk, hkL,
          by simpa only [left i hiL, left k hkL] using hik,
          by simpa only [left k hkL, left j hjL] using hkj⟩
      · by_cases hkM : k = L.length
        · have hjm : L.getD j 0 < m := hL _ (left_mem j hjL)
          rw [hkM, middle, left j hjL] at hkj
          omega
        · have hkR : k - (L.length + 1) < R.length := by omega
          have hkEq : L.length + 1 + (k - (L.length + 1)) = k := by omega
          have hcross' := hcross _ (left_mem i hiL) _ (right_mem _ hkR)
          rw [left i hiL, ← hkEq, right _ hkR] at hik
          omega
    · by_cases hjM : j = L.length
      · have hiL : i < L.length := by omega
        have hkR : k - (L.length + 1) < R.length := by omega
        have hkEq : L.length + 1 + (k - (L.length + 1)) = k := by omega
        have hcross' := hcross _ (left_mem i hiL) _ (right_mem _ hkR)
        rw [left i hiL, ← hkEq, right _ hkR] at hik
        omega
      · have hjR : L.length + 1 ≤ j := by omega
        have hkR : k - (L.length + 1) < R.length := by omega
        have hkEq : L.length + 1 + (k - (L.length + 1)) = k := by omega
        by_cases hiL : i < L.length
        · have hcross' := hcross _ (left_mem i hiL) _ (right_mem _ hkR)
          rw [left i hiL, ← hkEq, right _ hkR] at hik
          omega
        · by_cases hiM : i = L.length
          · have hrm : R.getD (k - (L.length + 1)) 0 < m :=
              hR _ (right_mem _ hkR)
            rw [hiM, middle, ← hkEq, right _ hkR] at hik
            omega
          · have hiR : i - (L.length + 1) < R.length := by omega
            have hjR' : j - (L.length + 1) < R.length := by omega
            have hiEq : L.length + 1 + (i - (L.length + 1)) = i := by omega
            have hjEq : L.length + 1 + (j - (L.length + 1)) = j := by omega
            apply hnotR
            refine ⟨i - (L.length + 1), j - (L.length + 1),
              k - (L.length + 1), by omega, by omega, hkR, ?_, ?_⟩
            · simpa only [← right _ hiR, ← right _ hkR, hiEq, hkEq] using hik
            · simpa only [← right _ hkR, ← right _ hjR', hkEq, hjEq] using hkj

theorem upper_parts_unique (s A B : Finset ℕ)
    (hA : A ⊆ s) (hB : B ⊆ s)
    (hAu : ∀ x ∈ A, ∀ y ∈ s, x < y → y ∈ A)
    (hBu : ∀ x ∈ B, ∀ y ∈ s, x < y → y ∈ B)
    (hcard : A.card = B.card) : A = B := by
  by_contra hne
  have hAB : ¬ A ⊆ B := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hcard.ge)
  have hBA : ¬ B ⊆ A := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hcard.le).symm
  obtain ⟨a, ha, haB⟩ := Finset.not_subset.mp hAB
  obtain ⟨b, hb, hbA⟩ := Finset.not_subset.mp hBA
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact hbA (hAu a ha b (hB hb) hab)
  · exact haB hb
  · exact haB (hBu b hb a (hA ha) hba)

theorem exists_upper_part (s : Finset ℕ) :
    ∀ i ≤ s.card, ∃ A : Finset ℕ,
      A ⊆ s ∧ A.card = i ∧
      ∀ x ∈ A, ∀ y ∈ s, x < y → y ∈ A := by
  induction s using Finset.induction_on_max with
  | empty =>
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      exact ⟨∅, by simp, by simp, by simp⟩
  | insert m t hmax ih =>
      intro i hi
      cases i with
      | zero => exact ⟨∅, by simp, by simp, by simp⟩
      | succ j =>
          have hm : m ∉ t := by
            intro hm
            exact (Nat.lt_irrefl m) (hmax m hm)
          have hj : j ≤ t.card := by
            simp only [Finset.card_insert_of_notMem hm] at hi
            omega
          obtain ⟨A, hAt, hcard, hupper⟩ := ih j hj
          refine ⟨insert m A, ?_, ?_, ?_⟩
          · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_self _ _,
              hAt.trans (Finset.subset_insert _ _)⟩
          · have hmA : m ∉ A := fun h => hm (hAt h)
            simp [Finset.card_insert_of_notMem hmA, hcard]
          · intro x hx y hy hxy
            rcases Finset.mem_insert.mp hx with rfl | hx
            · rcases Finset.mem_insert.mp hy with rfl | hy
              · omega
              · exact False.elim (by have := hmax y hy; omega)
            · rcases Finset.mem_insert.mp hy with rfl | hy
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (hupper x hx y hy hxy)

theorem ncard_avoid132 (s : Finset ℕ) :
    {w : List ℕ | w.Perm s.toList ∧ ¬ Has132 w}.ncard = catalan s.card := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hs : s = ∅
      · subst s
        have heq : {w : List ℕ | w.Perm (∅ : Finset ℕ).toList ∧ ¬ Has132 w} =
            {([] : List ℕ)} := by
          ext w
          constructor
          · intro hw
            simpa using hw.1
          · intro hw
            subst w
            simp [Has132]
        have hn0 : n = 0 := by simpa using hn.symm
        rw [hn0, heq]
        simp
      · classical
        have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        let m := s.max' hne
        let t := s.erase m
        have hm : m ∈ s := s.max'_mem hne
        have htcard : t.card + 1 = n := by
          calc
            t.card + 1 = s.card - 1 + 1 := by
              dsimp [t]
              rw [Finset.card_erase_of_mem hm]
            _ = s.card := Nat.sub_add_cancel (Finset.card_pos.mpr hne)
            _ = n := hn
        let A (i : Fin (t.card + 1)) : Finset ℕ :=
          Classical.choose (exists_upper_part t i.val (Nat.le_of_lt_succ i.isLt))
        have hA (i : Fin (t.card + 1)) :
            A i ⊆ t ∧ (A i).card = i.val ∧
            ∀ x ∈ A i, ∀ y ∈ t, x < y → y ∈ A i :=
          Classical.choose_spec (exists_upper_part t i.val (Nat.le_of_lt_succ i.isLt))
        let B (i : Fin (t.card + 1)) : Finset ℕ := t \ A i
        have hBcard (i : Fin (t.card + 1)) : (B i).card = t.card - i.val := by
          dsimp [B]
          rw [Finset.card_sdiff_of_subset (hA i).1, (hA i).2.1]
        let Avoid (u : Finset ℕ) : Set (List ℕ) :=
          {w | w.Perm u.toList ∧ ¬ Has132 w}
        have hfinite (u : Finset ℕ) : (Avoid u).Finite := by
          apply (List.permutations u.toList).finite_toSet.subset
          intro w hw
          exact (List.mem_permutations).mpr hw.1
        letI (u : Finset ℕ) : Finite (Avoid u) := (hfinite u).to_subtype
        let Code := Σ i : Fin (t.card + 1), Avoid (A i) × Avoid (B i)
        let decode : Code → Avoid s := by
          intro z
          obtain ⟨i, ⟨L, hL⟩, ⟨R, hR⟩⟩ := z
          have hLset : L.toFinset = A i := by
            rw [List.toFinset_eq_of_perm _ _ hL.1, Finset.toList_toFinset]
          have hRset : R.toFinset = B i := by
            rw [List.toFinset_eq_of_perm _ _ hR.1, Finset.toList_toFinset]
          have hLnd : L.Nodup := hL.1.nodup_iff.mpr (Finset.nodup_toList _)
          have hRnd : R.Nodup := hR.1.nodup_iff.mpr (Finset.nodup_toList _)
          have hmnot : m ∉ L ++ R := by
            simp only [List.mem_append, not_or]
            constructor
            · intro hmL
              have hmT : m ∈ t := (hA i).1 (by rw [← hLset]; simpa using hmL)
              exact (Finset.notMem_erase m s) hmT
            · intro hmR
              have hmB : m ∈ B i := by
                rw [← hRset]
                simpa using hmR
              have hmT : m ∈ t := (Finset.sdiff_subset : B i ⊆ t) hmB
              exact (Finset.notMem_erase m s) hmT
          have hdis : List.Disjoint L R := by
            intro x hxL hxR
            have hxA : x ∈ A i := by rw [← hLset]; simpa using hxL
            have hxB : x ∈ B i := by rw [← hRset]; simpa using hxR
            exact (Finset.mem_sdiff.mp hxB).2 hxA
          have hnd : (L ++ m :: R).Nodup := by
            apply List.nodup_middle.mpr
            exact List.nodup_cons.mpr ⟨hmnot,
              List.nodup_append'.mpr ⟨hLnd, hRnd, hdis⟩⟩
          have hparts : A i ∪ B i = t := by
            dsimp [B]
            exact Finset.union_sdiff_of_subset (hA i).1
          have hset : (L ++ m :: R).toFinset = s := by
            rw [List.toFinset_append, List.toFinset_cons, hLset, hRset]
            calc
              A i ∪ insert m (B i) = insert m (A i ∪ B i) := by
                ext x
                simp only [Finset.mem_union, Finset.mem_insert]
                tauto
              _ = insert m t := congrArg _ hparts
              _ = s := Finset.insert_erase hm
          have hperm : (L ++ m :: R).Perm s.toList :=
            List.perm_of_nodup_nodup_toFinset_eq hnd s.nodup_toList
              (by rwa [Finset.toList_toFinset])
          have hLb : ∀ a ∈ L, a < m := by
            intro a ha
            have hat : a ∈ t := (hA i).1 (by rw [← hLset]; simpa using ha)
            exact s.lt_max'_of_mem_erase_max' hne hat
          have hRb : ∀ c ∈ R, c < m := by
            intro c hc
            have hcB : c ∈ B i := by
              rw [← hRset]
              simpa using hc
            have hct : c ∈ t := (Finset.sdiff_subset : B i ⊆ t) hcB
            exact s.lt_max'_of_mem_erase_max' hne hct
          have hcross : ∀ a ∈ L, ∀ c ∈ R, c ≤ a := by
            intro a ha c hc
            have haA : a ∈ A i := by rw [← hLset]; simpa using ha
            have hcB : c ∈ B i := by rw [← hRset]; simpa using hc
            have hct := (Finset.mem_sdiff.mp hcB).1
            have hcnot := (Finset.mem_sdiff.mp hcB).2
            by_contra hca
            exact hcnot ((hA i).2.2 a haA c hct (by omega))
          exact ⟨L ++ m :: R, hperm,
            (avoids132_append_max_iff L R m hLb hRb).mpr ⟨hL.2, hR.2, hcross⟩⟩
        have code_left_length (i : Fin (t.card + 1)) (L : Avoid (A i)) :
            L.val.length = i.val := by
          have hnd : L.val.Nodup := L.property.1.nodup_iff.mpr (Finset.nodup_toList _)
          have hset : L.val.toFinset = A i := by
            rw [List.toFinset_eq_of_perm _ _ L.property.1, Finset.toList_toFinset]
          calc
            L.val.length = L.val.toFinset.card := by
              rw [List.card_toFinset, List.dedup_eq_self.mpr hnd]
            _ = (A i).card := congrArg Finset.card hset
            _ = i.val := (hA i).2.1
        have decode_idx (z : Code) : (decode z).val.idxOf m = z.1.val := by
          obtain ⟨i, ⟨L, hL⟩, ⟨R, hR⟩⟩ := z
          have hlen : L.length = i.val := code_left_length i ⟨L, hL⟩
          have hmnotL : m ∉ L := by
            intro hmL
            have hset : L.toFinset = A i := by
              rw [List.toFinset_eq_of_perm _ _ hL.1, Finset.toList_toFinset]
            have hmT : m ∈ t := (hA i).1 (by rw [← hset]; simpa using hmL)
            exact (Finset.notMem_erase m s) hmT
          change (L ++ m :: R).idxOf m = i.val
          rw [List.idxOf_append_of_notMem hmnotL]
          simp [hlen]
        have decode_inj : Function.Injective decode := by
          intro z z' hzz
          obtain ⟨i, ⟨L, hL⟩, ⟨R, hR⟩⟩ := z
          obtain ⟨j, ⟨L', hL'⟩, ⟨R', hR'⟩⟩ := z'
          have hij : i = j := Fin.ext (by
            have hx := congrArg (fun w : List ℕ => w.idxOf m) (congrArg Subtype.val hzz)
            simpa only [decode_idx] using hx)
          subst j
          have hlen : L.length = i.val := code_left_length i ⟨L, hL⟩
          have hlen' : L'.length = i.val := code_left_length i ⟨L', hL'⟩
          have hw : L ++ m :: R = L' ++ m :: R' := congrArg Subtype.val hzz
          have hLL : L = L' := by
            have hx := congrArg (List.take i.val) hw
            simpa [hlen, hlen'] using hx
          have hRR : R = R' := by
            have hx := congrArg (List.drop (i.val + 1)) hw
            have hdrop (Q T : List ℕ) (hQ : Q.length = i.val) :
                (Q ++ m :: T).drop (i.val + 1) = T := by
              convert List.drop_append_length (l₁ := Q ++ [m]) (l₂ := T) using 1
              · simp [hQ]
            simpa only [hdrop L R hlen, hdrop L' R' hlen'] using hx
          subst L'
          subst R'
          rfl
        have decode_surj : Function.Surjective decode := by
          rintro ⟨w, hw⟩
          have hmw : m ∈ w := hw.1.mem_iff.mpr (by simpa using hm)
          let j := w.idxOf m
          let L := w.take j
          let R := w.drop (j + 1)
          have hj : j < w.length := List.idxOf_lt_length_of_mem hmw
          have hLlen : L.length = j := by simp [L, List.length_take, Nat.min_eq_left hj.le]
          have hsplit : w = L ++ m :: R := by
            have hget : w[j] = m := List.getElem_idxOf hj
            calc
              w = w.take j ++ w.drop j := (List.take_append_drop j w).symm
              _ = w.take j ++ w[j] :: w.drop (j + 1) := by
                rw [List.drop_eq_getElem_cons hj]
              _ = L ++ m :: R := by simp [L, R, hget]
          have hnd : w.Nodup := hw.1.nodup_iff.mpr (Finset.nodup_toList s)
          have hndsplit : (L ++ m :: R).Nodup := hsplit ▸ hnd
          have hmnotLR : m ∉ L ++ R :=
            (List.nodup_cons.mp (List.nodup_middle.mp hndsplit)).1
          have hLRnd : (L ++ R).Nodup :=
            (List.nodup_cons.mp (List.nodup_middle.mp hndsplit)).2
          have hLnd : L.Nodup := (List.nodup_append'.mp hLRnd).1
          have hRnd : R.Nodup := (List.nodup_append'.mp hLRnd).2.1
          have hdis : List.Disjoint L R := (List.nodup_append'.mp hLRnd).2.2
          have hwset : w.toFinset = s := by
            rw [List.toFinset_eq_of_perm _ _ hw.1, Finset.toList_toFinset]
          have hLsub : L.toFinset ⊆ t := by
            intro x hx
            have hxL : x ∈ L := List.mem_toFinset.mp hx
            have hxW : x ∈ w := by rw [hsplit]; simp [hxL]
            have hxS : x ∈ s := by rw [← hwset]; simpa using hxW
            have hxm : x ≠ m := by
              intro heq
              subst x
              exact hmnotLR (List.mem_append.mpr (Or.inl hxL))
            exact Finset.mem_erase.mpr ⟨hxm, hxS⟩
          have hRsub : R.toFinset ⊆ t := by
            intro x hx
            have hxR : x ∈ R := List.mem_toFinset.mp hx
            have hxW : x ∈ w := by rw [hsplit]; simp [hxR]
            have hxS : x ∈ s := by rw [← hwset]; simpa using hxW
            have hxm : x ≠ m := by
              intro heq
              subst x
              exact hmnotLR (List.mem_append.mpr (Or.inr hxR))
            exact Finset.mem_erase.mpr ⟨hxm, hxS⟩
          have hparts : L.toFinset ∪ R.toFinset = t := by
            ext x
            constructor
            · intro hx
              rcases Finset.mem_union.mp hx with hx | hx
              · exact hLsub hx
              · exact hRsub hx
            · intro hx
              have hxS : x ∈ s := (Finset.mem_erase.mp hx).2
              have hxW : x ∈ w := by
                have : x ∈ w.toFinset := by rwa [hwset]
                simpa using this
              have hxm : x ≠ m := (Finset.mem_erase.mp hx).1
              rw [hsplit] at hxW
              rcases List.mem_append.mp hxW with hxL | hxMR
              · exact Finset.mem_union_left _ (List.mem_toFinset.mpr hxL)
              · rcases List.mem_cons.mp hxMR with rfl | hxR
                · exact False.elim (hxm rfl)
                · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hxR)
          have hLb : ∀ a ∈ L, a < m := by
            intro a ha
            exact s.lt_max'_of_mem_erase_max' hne
              (hLsub (List.mem_toFinset.mpr ha))
          have hRb : ∀ c ∈ R, c < m := by
            intro c hc
            exact s.lt_max'_of_mem_erase_max' hne
              (hRsub (List.mem_toFinset.mpr hc))
          have hsplitAvoid : ¬ Has132 (L ++ m :: R) := by
            rw [← hsplit]
            exact hw.2
          have hcriteria := (avoids132_append_max_iff L R m hLb hRb).mp hsplitAvoid
          have hLupper : ∀ x ∈ L.toFinset, ∀ y ∈ t, x < y → y ∈ L.toFinset := by
            intro x hx y hy hxy
            have hyLR : y ∈ L.toFinset ∪ R.toFinset := by rw [hparts]; exact hy
            rcases Finset.mem_union.mp hyLR with hyL | hyR
            · exact hyL
            · have hle := hcriteria.2.2 x (List.mem_toFinset.mp hx)
                y (List.mem_toFinset.mp hyR)
              omega
          have hLcard : L.toFinset.card = j := by
            rw [List.card_toFinset, List.dedup_eq_self.mpr hLnd, hLlen]
          have hwlen : w.length = n := by
            calc
              w.length = s.toList.length := hw.1.length_eq
              _ = s.card := Finset.length_toList _
              _ = n := hn
          have hji : j < t.card + 1 := by omega
          let i : Fin (t.card + 1) := ⟨j, hji⟩
          have hLset : L.toFinset = A i :=
            upper_parts_unique t L.toFinset (A i) hLsub (hA i).1
              hLupper (hA i).2.2 (by rw [hLcard]; exact (hA i).2.1.symm)
          have hRset : R.toFinset = B i := by
            ext x
            constructor
            · intro hxR
              have hxT : x ∈ t := hRsub hxR
              have hxNotA : x ∉ A i := by
                intro hxA
                have hxLFin : x ∈ L.toFinset := by rwa [hLset]
                have hxL : x ∈ L := List.mem_toFinset.mp hxLFin
                exact hdis hxL (List.mem_toFinset.mp hxR)
              exact Finset.mem_sdiff.mpr ⟨hxT, hxNotA⟩
            · intro hxB
              have hxT : x ∈ t := (Finset.mem_sdiff.mp hxB).1
              have hxNotA : x ∉ A i := (Finset.mem_sdiff.mp hxB).2
              have hxLR : x ∈ L.toFinset ∪ R.toFinset := by rw [hparts]; exact hxT
              rcases Finset.mem_union.mp hxLR with hxL | hxR
              · exact False.elim (hxNotA (by rwa [← hLset]))
              · exact hxR
          have hLperm : L.Perm (A i).toList :=
            List.perm_of_nodup_nodup_toFinset_eq hLnd (Finset.nodup_toList _)
              (by rwa [Finset.toList_toFinset])
          have hRperm : R.Perm (B i).toList :=
            List.perm_of_nodup_nodup_toFinset_eq hRnd (Finset.nodup_toList _)
              (by rwa [Finset.toList_toFinset])
          let z : Code := ⟨i, ⟨L, hLperm, hcriteria.1⟩,
            ⟨R, hRperm, hcriteria.2.1⟩⟩
          refine ⟨z, ?_⟩
          apply Subtype.ext
          exact hsplit.symm
        have e : Avoid s ≃ Code :=
          (Equiv.ofBijective decode ⟨decode_inj, decode_surj⟩).symm
        have hcount : (Avoid s).ncard =
            ∑ i : Fin (t.card + 1), (Avoid (A i)).ncard * (Avoid (B i)).ncard := by
          rw [← Nat.card_coe_set_eq]
          calc
            Nat.card (Avoid s) =
                Nat.card (Σ i : Fin (t.card + 1), Avoid (A i) × Avoid (B i)) :=
              Nat.card_congr e
            _ = ∑ i : Fin (t.card + 1),
                  Nat.card (Avoid (A i)) * Nat.card (Avoid (B i)) := by
              rw [Nat.card_sigma]
              simp_rw [Nat.card_prod]
            _ = _ := by simp only [Nat.card_coe_set_eq]
        change (Avoid s).ncard = catalan n
        rw [hcount, ← htcard, catalan_succ]
        apply Finset.sum_congr rfl
        intro i hi
        have hltA : (A i).card < n := by rw [(hA i).2.1]; omega
        have hltB : (B i).card < n := by rw [hBcard i]; omega
        rw [ih (A i).card hltA (A i) rfl,
          ih (B i).card hltB (B i) rfl, (hA i).2.1, hBcard]


end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan
