/- GID: D5/S3/Combinatorics/PanSkanderaWangBruhat
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PanSkanderaWangBruhat
   mirror-E: none(waiver:direct-Lean-proof-of-the-pan-skandera-wang-bruhat-conjecture)
   anchors: [mathlib/module/Mathlib.Data.List.InsertIdx]
   utility: none
   digest: The Pan-Skandera-Wang map raises every source permutation in Bruhat order. -/

import D5.S3.Combinatorics.PanSkanderaWangBruhatInvariant
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sort
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PanSkanderaWangBruhat

/-- For odd size, reverse-complementation sends the long-prefix source family to `A`. -/
theorem ru_mem_A_of_longPrefix {m : ℕ} {a : List ℕ}
    (ha : IsPerm m a) (hodd : m % 2 = 1)
    (hpre : (a.take (m / 2 + 1)).Perm (List.range' 1 (m / 2 + 1))) :
    A m (RU m a) := by
  let k := m / 2
  have hm : m = 2 * k + 1 := by simp only [k]; omega
  have halen : a.length = m := by simpa [IsPerm] using ha.length_eq
  have hrangeSplit :
      List.range' 1 m = List.range' 1 (k + 1) ++ List.range' (k + 2) k := by
    rw [hm, show 2 * k + 1 = (k + 1) + k by omega, ← List.range'_append]
    congr 2
    omega
  have hprefix : (a.take (k + 1)).Perm ((List.range' 1 m).take (k + 1)) := by
    rw [hrangeSplit]
    simpa [k] using hpre
  have htail := ha.drop hprefix
  rw [hrangeSplit] at htail
  simp at htail
  have hcomp :
      (List.range' (k + 2) k).reverse.map (fun v => m + 1 - v) = List.range' 1 k := by
    apply List.ext_getElem
    · simp
    · intro i hi h'i
      simp only [List.length_map, List.length_reverse, List.length_range'] at hi
      simp only [List.getElem_map, List.getElem_reverse, List.getElem_range'_1,
        List.length_range']
      omega
  have hrev : (a.drop (k + 1)).reverse.Perm (List.range' (k + 2) k).reverse :=
    (a.drop (k + 1)).reverse_perm.trans (htail.trans (List.reverse_perm _).symm)
  have hmapped := hrev.map (fun v => m + 1 - v)
  rw [hcomp] at hmapped
  refine ⟨ru_isPerm ha, ?_⟩
  change ((a.reverse.map (fun v => m + 1 - v)).take k).Perm (List.range' 1 k)
  rw [← List.map_take, List.take_reverse]
  have hdrop : a.length - k = k + 1 := by omega
  rw [hdrop]
  exact hmapped

set_option maxHeartbeats 4000000 in
-- The four explicit base words require bounded normalization of all legal selection shapes.
/-- Pan-Skandera-Wang Conjecture 7.8. -/
theorem result : claim := by
  have hinsert : ∀ (l : List ℕ) (j x : ℕ), j ≤ l.length →
      l.insertIdx j x = l.take j ++ x :: l.drop j := by
    intro l j x hj
    induction l generalizing j with
    | nil => simp at hj; subst j; rfl
    | cons y l ih =>
        cases j with
        | zero => rfl
        | succ j =>
            simp only [List.insertIdx_succ_cons, List.take_succ_cons,
              List.drop_succ_cons, List.cons_append, List.cons.injEq, true_and,
              List.length_cons] at hj ⊢
            exact ih j (by omega)
  let rec swapPerm : ∀ x : List ℕ, (swapPairs x).Perm x
    | [] => .refl []
    | [a] => .refl [a]
    | a :: b :: t => by
        simpa [swapPairs] using
          (List.Perm.swap a b (swapPairs t)).trans (((swapPerm t).cons b).cons a)
  have hinss : ∀ (q : ℕ) (x : List ℕ),
      (inss q x).Perm ((x.length + 1) :: x) := by
    intro q x
    unfold inss
    have hs := swapPerm (x.drop (q - 1))
    have hsplit : x.take (q - 1) ++ x.drop (q - 1) = x := List.take_append_drop _ _
    have happ := (hs.cons (x.length + 1)).append_left (x.take (q - 1))
    exact happ.trans (by
      simpa only [hsplit] using
        (List.perm_middle (l₁ := x.take (q - 1)) (l₂ := x.drop (q - 1))
          (a := x.length + 1)))
  have hcountMono : ∀ (q : ℕ) {x y : List ℕ}, List.Forall₂ (· ≤ ·) x y →
      countGE q x ≤ countGE q y := by
    intro q x y hxy
    induction x generalizing y with
    | nil => cases hxy; rfl
    | cons a x ih =>
        cases y with
        | nil => cases hxy
        | cons b y =>
            cases hxy with
            | cons hab htail =>
                have hrest := ih htail
                unfold countGE at hrest ⊢
                simp only [List.countP_cons]
                by_cases ha : q ≤ a
                · have hb : q ≤ b := le_trans ha hab
                  simp only [decide_eq_true_eq, if_pos ha, if_pos hb]
                  exact Nat.add_le_add_right hrest 1
                · by_cases hb : q ≤ b
                  · simp only [decide_eq_true_eq, if_neg ha, if_pos hb, Nat.add_zero]
                    omega
                  · simpa only [decide_eq_true_eq, if_neg ha, if_neg hb, Nat.add_zero] using hrest
  have hcountSort : ∀ (q : ℕ) (x y : List ℕ),
      List.Forall₂ (· ≤ ·)
        (x.mergeSort (fun a b => decide (a ≤ b)))
        (y.mergeSort (fun a b => decide (a ≤ b))) → countGE q x ≤ countGE q y := by
    intro q x y hxy
    have h := hcountMono q hxy
    unfold countGE at h ⊢
    rw [← (List.mergeSort_perm x (fun a b => decide (a ≤ b))).countP_eq,
      ← (List.mergeSort_perm y (fun a b => decide (a ≤ b))).countP_eq]
    exact h
  have hmain : ∀ n : ℕ, 4 ≤ n → ∀ w : List ℕ, A n w →
      IsPerm n (f n w) ∧ SelectionInvariant n w (f n w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn w hw
      by_cases hn4 : n = 4
      · subst n
        rcases hw with ⟨hperm, htake⟩
        have hprefix : (w.take 2).Perm ((List.range' 1 4).take 2) := by
          simpa using htake
        have hdrop := hperm.drop hprefix
        have htakeCases : w.take 2 = [1, 2] ∨ w.take 2 = [2, 1] := by
          apply List.perm_pair.mp
          rw [show List.range' 1 2 = [1, 2] by decide] at htake
          exact htake
        have hdropCases : w.drop 2 = [3, 4] ∨ w.drop 2 = [4, 3] := by
          apply List.perm_pair.mp
          rw [show (List.range' 1 4).drop 2 = [3, 4] by decide] at hdrop
          exact hdrop
        have hsplit := (List.take_append_drop 2 w).symm
        rcases htakeCases with htakeCases | htakeCases <;>
          rcases hdropCases with hdropCases | hdropCases <;>
          simp only [htakeCases, hdropCases] at hsplit <;> subst w
        all_goals
          refine ⟨?_, ?_⟩
          · unfold IsPerm
            norm_num [f, f4, List.range'_succ] <;>
              apply (List.perm_ext_iff_of_nodup (by decide) (by decide)).mpr <;>
              intro x <;> simp only [List.mem_cons] <;> aesop
          intro p d q hp hdp hdn hq1 hqn
          interval_cases p <;> interval_cases d <;> try omega
          all_goals
            apply hcountSort
            norm_num [f, f4, selection, selectionPositions, List.range_succ,
              List.getD, List.Forall₂, List.mergeSort]
      · have hn5 : 5 ≤ n := by omega
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        have hm4 : 4 ≤ m := by omega
        have hrec := ih m (by omega)
        let nn := m + 1
        let i := w.idxOf nn
        let r := i + 1
        let a := w.eraseIdx i
        have hnrange : nn ∈ List.range' 1 nn :=
          List.mem_range'.mpr ⟨nn - 1, by omega, by omega⟩
        have hnmem : nn ∈ w := hw.1.symm.subset hnrange
        have hi : i < w.length := List.idxOf_lt_length_iff.mpr hnmem
        have hget : w[i] = nn := List.getElem_idxOf hi
        have hwlen : w.length = nn := by simpa [IsPerm] using hw.1.length_eq
        have halen : a.length + 1 = w.length := List.length_eraseIdx_add_one hi
        have hna : (nn :: a).Perm w := by
          simpa [a, hget] using (List.getElem_cons_eraseIdx_perm hi)
        have hrange : List.range' 1 m ++ [nn] = List.range' 1 nn := by
          simp only [nn]
          rw [List.range'_concat]
          congr 2
          omega
        have hmove : (List.range' 1 nn).Perm (nn :: List.range' 1 m) := by
          rw [← hrange]
          simpa only [List.append_nil] using
            (List.perm_middle (l₁ := List.range' 1 m) (a := nn) (l₂ := []))
        have ha : IsPerm m a := by
          exact (hna.trans (hw.1.trans hmove)).cons_inv
        have hwInsert : insertMax nn r a = w := by
          rw [insertMax]
          simp only [r, Nat.add_sub_cancel]
          rw [← hinsert a i nn (by omega)]
          simpa [a, hget] using (List.insertIdx_eraseIdx_getElem hi)
        have hrLower : nn / 2 + 1 ≤ r := by
          by_contra hbad
          have hnTake : nn ∈ w.take (nn / 2) :=
            (List.mem_take_iff_idxOf_lt hnmem).mpr (by simpa [i, r] using hbad)
          have hnLow : nn ∈ List.range' 1 (nn / 2) := hw.2.subset hnTake
          simp only [List.mem_range'] at hnLow
          rcases hnLow with ⟨j, hj, heq⟩
          omega
        have hpreErase : a.take (nn / 2) = w.take (nn / 2) := by
          exact List.take_eraseIdx_eq_take_of_le w (nn / 2) i (by omega)
        have hpreA : (a.take (nn / 2)).Perm (List.range' 1 (nn / 2)) := by
          rw [hpreErase]
          exact hw.2
        have hrn : r ≤ nn := by simp only [r]; omega
        rcases Nat.mod_two_eq_zero_or_one m with hmEven | hmOdd
        · have hmEq : m = 2 * (m / 2) := by omega
          have hhalf : nn / 2 = m / 2 := by simp only [nn]; omega
          have hAm : A m a := by
            refine ⟨ha, ?_⟩
            simpa only [hhalf] using hpreA
          rcases hrec hm4 a hAm with ⟨hb, hF⟩
          let s := 2 * r - nn
          have hs1 : 1 ≤ s := by simp only [s]; omega
          have hsn : s ≤ nn := by simp only [s]; omega
          have hstep := selectionInvariant_insert (n := nn) (m := m) (r := r) (s := s)
            (a := a) (b := f m a) (by simp [nn]) ha hb hF (by simp [r]) (by omega)
            rfl hs1
          have hbLen : (f m a).length = m := by simpa [IsPerm] using hb.length_eq
          have houtPerm : IsPerm nn (inss s (f m a)) := by
            unfold IsPerm
            have hp := hinss s (f m a)
            rw [hbLen] at hp
            exact hp.trans ((hb.cons nn).trans hmove.symm)
          have hsAlg : 2 * (r - m / 2) - 1 = s := by
            simp only [s]
            omega
          have hf : f nn w = inss s (f m a) := by
            simp only [nn, f]
            rw [if_neg (by omega), if_pos hmEven]
            simp only [i, a, Nat.add_sub_cancel]
            rw [hsAlg]
          rw [hf]
          exact ⟨houtPerm, hwInsert ▸ hstep⟩
        · have hmEq : m = 2 * (m / 2) + 1 := by omega
          have hhalf : nn / 2 = m / 2 + 1 := by simp only [nn]; omega
          have hlong : (a.take (m / 2 + 1)).Perm (List.range' 1 (m / 2 + 1)) := by
            simpa only [hhalf] using hpreA
          have hruA := ru_mem_A_of_longPrefix ha hmOdd hlong
          rcases hrec hm4 (RU m a) hruA with ⟨hcPerm, hFc⟩
          let c := RU m a
          let b := RU m (f m c)
          have hb : IsPerm m b := ru_isPerm hcPerm
          have hF : SelectionInvariant m a b := by
            have hruF := selectionInvariant_ru (ru_isPerm ha) hcPerm hFc
            have hruInv : RU m (RU m a) = a := by
              unfold RU
              rw [← List.map_reverse, List.reverse_reverse, List.map_map]
              calc
                List.map ((fun v => m + 1 - v) ∘ fun v => m + 1 - v) a =
                    List.map id a := by
                  apply List.map_congr_left
                  intro v hv
                  have hv' : v ∈ List.range' 1 m := ha.subset hv
                  simp only [List.mem_range'] at hv'
                  rcases hv' with ⟨j, hj, rfl⟩
                  simp only [Function.comp_apply, id_eq]
                  omega
                _ = a := by simp
            simpa only [c, b, hruInv] using hruF
          let s := 2 * r - nn
          have hs1 : 1 ≤ s := by simp only [s]; omega
          have hsn : s ≤ nn := by simp only [s]; omega
          have hstep := selectionInvariant_insert (n := nn) (m := m) (r := r) (s := s)
            (a := a) (b := b) (by simp [nn]) ha hb hF (by simp [r]) (by omega) rfl hs1
          have hbLen : b.length = m := by simpa [IsPerm] using hb.length_eq
          have houtPerm : IsPerm nn (inss s b) := by
            unfold IsPerm
            have hp := hinss s b
            rw [hbLen] at hp
            exact hp.trans ((hb.cons nn).trans hmove.symm)
          have hsAlg : 2 * (r - m / 2 - 1) = s := by
            simp only [s]
            omega
          have hf : f nn w = inss s b := by
            have hmNotEven : ¬m % 2 = 0 := by omega
            simp only [nn, f]
            rw [if_neg (by omega), if_neg hmNotEven]
            simp only [i, a, Nat.add_sub_cancel, c, b]
            rw [hsAlg]
          rw [hf]
          exact ⟨houtPerm, hwInsert ▸ hstep⟩
  intro n hn w hw
  rcases hmain n hn w hw with ⟨hfperm, hF⟩
  refine ⟨hw.1, hfperm, ?_⟩
  intro p q
  by_cases hp : p ≤ n
  · by_cases hq0 : q = 0
    · subst q
      have hwlen : w.length = n := by simpa [IsPerm] using hw.1.length_eq
      have hflen : (f n w).length = n := by simpa [IsPerm] using hfperm.length_eq
      simp [rank, hwlen, hflen]
    · by_cases hqn : q ≤ n + 1
      · have h := hF p 0 q hp (Nat.zero_le _) (Nat.zero_le _) (by omega) hqn
        have hsel : selection (f n w) p 0 = (f n w).take p := by
          have hfLen : (f n w).length = n := by simpa [IsPerm] using hfperm.length_eq
          unfold selection selectionPositions
          simp only [Nat.sub_zero, List.range_zero, List.map_nil, List.append_nil]
          apply List.ext_getElem
          · simp [hp, show (f n w).length = n by simpa [IsPerm] using hfperm.length_eq]
          · intro j hj h'j
            simp only [List.length_map, List.length_range] at hj
            simp only [List.getElem_map, List.getElem_range]
            have hjlen : j < (f n w).length := by omega
            rw [List.getD_eq_getElem _ 0 hjlen]
            exact (f n w).getElem_take' hjlen hj
        rw [hsel] at h
        simpa [rank, countGE, List.countP_eq_length_filter] using h
      · have hzero : rank w p q = 0 := by
          have hempty : (w.take p).filter (fun v => decide (q ≤ v)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro v hv
            simp only [decide_eq_true_eq, not_le]
            have hvw : v ∈ w := List.mem_of_mem_take hv
            have hvrange : v ∈ List.range' 1 n := hw.1.subset hvw
            simp only [List.mem_range'] at hvrange
            rcases hvrange with ⟨j, hj, rfl⟩
            omega
          simp [rank, hempty]
        rw [hzero]
        exact Nat.zero_le _
  · have hwlen : w.length = n := by simpa [IsPerm] using hw.1.length_eq
    have hflen : (f n w).length = n := by simpa [IsPerm] using hfperm.length_eq
    have htakeW : w.take p = w := (List.take_eq_self_iff w).mpr (by omega)
    have htakeF : (f n w).take p = f n w :=
      (List.take_eq_self_iff (f n w)).mpr (by omega)
    unfold rank
    rw [htakeW, htakeF]
    exact (hw.1.trans hfperm.symm).filter (fun v => decide (q ≤ v)) |>.length_eq.le

end D5.S3.Combinatorics.PanSkanderaWangBruhat
