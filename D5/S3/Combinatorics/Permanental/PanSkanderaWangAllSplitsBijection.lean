/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsBijection
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: The recursive Pan-Skandera-Wang image is injective and parity preserving. -/

/- Mathematical classification:
   f_injective:
     proof_shape: content
     escape_witness: inss_injective: recovery of the pair-swapped suffix
   f_image_B:
     proof_shape: content
     escape_witness: inss_parity: verified parity of the inserted output
   admission_basis: escape-witness
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     D5/S3/Combinatorics/PanSkanderaWangBruhat.result
     D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant.swapPairs_length
     Definitions and reverse-complement lemmas from the frozen PSW owners.
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsWord

open Finset Equiv
open D5.S3.Combinatorics.PanSkanderaWangBruhat
namespace PSW

/-- One-based parity preservation, as in the paper's literal target family. -/
def B (n : ℕ) (x : List ℕ) : Prop :=
  IsPerm n x ∧ ∀ k : ℕ, (hk : k < x.length) → x[k]'hk % 2 = (k + 1) % 2

private theorem swapPairs_involution : ∀ x : List ℕ, swapPairs (swapPairs x) = x
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => by simpa only [swapPairs] using congrArg (fun l => a :: b :: l) (swapPairs_involution t)

private theorem inss_injective (q : ℕ) {x y : List ℕ}
    (hqx : q - 1 ≤ x.length) (hqy : q - 1 ≤ y.length)
    (h : inss q x = inss q y) : x = y := by
  have ht := congrArg (List.take (q - 1)) h
  have hd := congrArg (List.drop (q - 1 + 1)) h
  simp only [inss] at ht hd
  have htx : (x.take (q - 1)).length = q - 1 := by simp; omega
  have hty : (y.take (q - 1)).length = q - 1 := by simp; omega
  have hpref : x.take (q - 1) = y.take (q - 1) := by
    simpa [List.take_append, htx, hty] using ht
  have hdx : (x.take (q - 1)).drop (q - 1 + 1) = [] := by
    apply List.drop_eq_nil_iff.mpr; omega
  have hdy : (y.take (q - 1)).drop (q - 1 + 1) = [] := by
    apply List.drop_eq_nil_iff.mpr; omega
  have hsuff : swapPairs (x.drop (q - 1)) = swapPairs (y.drop (q - 1)) := by
    simpa [List.drop_append, htx, hty, hdx, hdy] using hd
  have he := congrArg swapPairs hsuff
  rw [swapPairs_involution, swapPairs_involution] at he
  calc
    x = x.take (q - 1) ++ x.drop (q - 1) := (List.take_append_drop _ _).symm
    _ = y.take (q - 1) ++ y.drop (q - 1) := by rw [hpref, he]
    _ = y := List.take_append_drop _ _

set_option maxHeartbeats 4000000 in
/-- The algorithm's two reverse-complement branches are injective on the literal source family. -/
theorem f_injective : ∀ n : ℕ, 4 ≤ n → ∀ w z : List ℕ, A n w → A n z →
    f n w = f n z → w = z := by
  have inss_idxOf_max {m : ℕ} (x : List ℕ) (hx : IsPerm m x) (q : ℕ)
      (hq : 1 ≤ q) (hqm : q ≤ m + 1) : (inss q x).idxOf (m + 1) = q - 1 := by
    have hxlen : x.length = m := by simpa [IsPerm] using hx.length_eq
    have hn : m + 1 ∉ x := by
      intro hm
      have hr := hx.subset hm
      simp only [List.mem_range'] at hr
      obtain ⟨i, hi, he⟩ := hr
      omega
    have hnt : m + 1 ∉ x.take (q - 1) := fun h => hn (List.mem_of_mem_take h)
    rw [inss, hxlen]
    rw [List.idxOf_append_of_notMem hnt]
    simp [hxlen]
    omega
  have delete_source {m : ℕ} (w : List ℕ) (hw : A (m + 1) w) :
      let p := w.idxOf (m + 1)
      let a := w.eraseIdx p
      IsPerm m a ∧ (m + 1) / 2 ≤ p ∧ p ≤ m ∧
        (a.take ((m + 1) / 2)).Perm (List.range' 1 ((m + 1) / 2)) := by
    dsimp
    let p := w.idxOf (m + 1)
    have hnmem : m + 1 ∈ w := hw.1.symm.subset (List.mem_range'.mpr ⟨m, by omega, by omega⟩)
    have hp : p < w.length := List.idxOf_lt_length_iff.mpr hnmem
    have hwlen : w.length = m + 1 := by simpa [IsPerm] using hw.1.length_eq
    have hget : w[p] = m + 1 := List.getElem_idxOf hp
    have hrange : (List.range' 1 (m + 1)).Perm ((m + 1) :: List.range' 1 m) := by
      have hh : List.range' 1 m ++ [m + 1] = List.range' 1 (m + 1) := by
        rw [List.range'_concat]
        congr 2
        omega
      rw [← hh]
      simpa only [List.append_nil] using
        (List.perm_middle (l₁ := List.range' 1 m) (a := m + 1) (l₂ := []))
    have ha : IsPerm m (w.eraseIdx p) := by
      have hna := List.getElem_cons_eraseIdx_perm hp
      rw [hget] at hna
      exact (hna.trans (hw.1.trans hrange)).cons_inv
    have hlow : (m + 1) / 2 ≤ p := by
      by_contra hb
      have hin := (List.mem_take_iff_idxOf_lt hnmem).mpr (by simpa [p] using hb)
      have hr := hw.2.subset hin
      simp only [List.mem_range'] at hr
      obtain ⟨j, hj, he⟩ := hr
      omega
    refine ⟨ha, hlow, by omega, ?_⟩
    rw [List.take_eraseIdx_eq_take_of_le w ((m + 1) / 2) p hlow]
    exact hw.2
  have ru_involution {m : ℕ} {a : List ℕ} (ha : IsPerm m a) : RU m (RU m a) = a := by
    unfold RU
    rw [← List.map_reverse, List.reverse_reverse, List.map_map]
    calc
      List.map ((fun v => m + 1 - v) ∘ fun v => m + 1 - v) a = List.map id a := by
        apply List.map_congr_left
        intro v hv
        have hv' := ha.subset hv
        simp only [List.mem_range'] at hv'
        rcases hv' with ⟨j, hj, rfl⟩
        simp only [Function.comp_apply, id_eq]
        omega
      _ = a := by simp
  have ru_injective {m : ℕ} {a b : List ℕ} (ha : IsPerm m a) (hb : IsPerm m b)
      (h : RU m a = RU m b) : a = b := by
    have he := congrArg (RU m) h
    simpa [ru_involution ha, ru_involution hb] using he
  have a4_cases (w : List ℕ) (hw : A 4 w) :
      w = [1, 2, 3, 4] ∨ w = [1, 2, 4, 3] ∨ w = [2, 1, 3, 4] ∨ w = [2, 1, 4, 3] := by
    rcases hw with ⟨hperm, htake⟩
    have hprefix : (w.take 2).Perm ((List.range' 1 4).take 2) := by simpa [List.range'_succ] using htake
    have hdrop := hperm.drop hprefix
    have htakeCases : w.take 2 = [1, 2] ∨ w.take 2 = [2, 1] := by
      apply List.perm_pair.mp
      simpa [List.range'_succ] using htake
    have hdropCases : w.drop 2 = [3, 4] ∨ w.drop 2 = [4, 3] := by
      apply List.perm_pair.mp
      simpa [List.range'_succ] using hdrop
    have hsplit := (List.take_append_drop 2 w).symm
    rcases htakeCases with htakeCases | htakeCases <;>
      rcases hdropCases with hdropCases | hdropCases <;>
      simp only [htakeCases, hdropCases] at hsplit <;> simp [hsplit]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn w z hw hz heq
    by_cases hn4 : n = 4
    · subst n
      rcases a4_cases w hw with rfl | rfl | rfl | rfl <;>
        rcases a4_cases z hz with rfl | rfl | rfl | rfl <;>
        simp only [f, f4, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceIte, List.cons.injEq,
          Nat.reduceEqDiff, and_false, false_and] at heq ⊢ <;> simp_all
    · have hn5 : 5 ≤ n := by omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hm4 : 4 ≤ m := by omega
      let p := w.idxOf (m + 1)
      let q := z.idxOf (m + 1)
      let a := w.eraseIdx p
      let b := z.eraseIdx q
      have hda := delete_source w hw
      have hdb := delete_source z hz
      change IsPerm m a ∧ (m + 1) / 2 ≤ p ∧ p ≤ m ∧
        (a.take ((m + 1) / 2)).Perm (List.range' 1 ((m + 1) / 2)) at hda
      change IsPerm m b ∧ (m + 1) / 2 ≤ q ∧ q ≤ m ∧
        (b.take ((m + 1) / 2)).Perm (List.range' 1 ((m + 1) / 2)) at hdb
      let c := if m % 2 = 0 then a else RU m a
      let d := if m % 2 = 0 then b else RU m b
      have hc : A m c := by
        dsimp [c]
        split_ifs with hm
        · refine ⟨hda.1, ?_⟩
          have hh : (m + 1) / 2 = m / 2 := by omega
          simpa only [hh] using hda.2.2.2
        · apply ru_mem_A_of_longPrefix hda.1 (by omega)
          have hh : (m + 1) / 2 = m / 2 + 1 := by omega
          simpa only [hh] using hda.2.2.2
      have hd : A m d := by
        dsimp [d]
        split_ifs with hm
        · refine ⟨hdb.1, ?_⟩
          have hh : (m + 1) / 2 = m / 2 := by omega
          simpa only [hh] using hdb.2.2.2
        · apply ru_mem_A_of_longPrefix hdb.1 (by omega)
          have hh : (m + 1) / 2 = m / 2 + 1 := by omega
          simpa only [hh] using hdb.2.2.2
      let outc := if m % 2 = 0 then f m c else RU m (f m c)
      let outd := if m % 2 = 0 then f m d else RU m (f m d)
      have hoc : IsPerm m outc := by
        dsimp [outc]; split_ifs
        · exact (D5.S3.Combinatorics.PanSkanderaWangBruhat.result m hm4 c hc).2.1
        · exact ru_isPerm (D5.S3.Combinatorics.PanSkanderaWangBruhat.result m hm4 c hc).2.1
      have hod : IsPerm m outd := by
        dsimp [outd]; split_ifs
        · exact (D5.S3.Combinatorics.PanSkanderaWangBruhat.result m hm4 d hd).2.1
        · exact ru_isPerm (D5.S3.Combinatorics.PanSkanderaWangBruhat.result m hm4 d hd).2.1
      let s := 2 * (p + 1) - (m + 1)
      let t := 2 * (q + 1) - (m + 1)
      have hs : 1 ≤ s ∧ s ≤ m + 1 := by dsimp [s]; omega
      have ht : 1 ≤ t ∧ t ≤ m + 1 := by dsimp [t]; omega
      have hfw : f (m + 1) w = inss s outc := by
        simp only [f, if_neg (by omega : ¬ m + 1 ≤ 4)]
        dsimp [p, a, c, outc, s]
        split_ifs with hm <;> congr 1 <;> omega
      have hfz : f (m + 1) z = inss t outd := by
        simp only [f, if_neg (by omega : ¬ m + 1 ≤ 4)]
        dsimp [q, b, d, outd, t]
        split_ifs with hm <;> congr 1 <;> omega
      rw [hfw, hfz] at heq
      have hpositions := congrArg (List.idxOf (m + 1)) heq
      rw [inss_idxOf_max outc hoc s hs.1 hs.2, inss_idxOf_max outd hod t ht.1 ht.2] at hpositions
      have hst : s = t := by omega
      have hpq : p = q := by dsimp [s, t] at hst; omega
      rw [← hst] at heq
      have hout : outc = outd := inss_injective s
        (by have hh := hoc.length_eq; simp at hh; omega)
        (by have hh := hod.length_eq; simp at hh; omega) heq
      have hfd : f m c = f m d := by
        dsimp [outc, outd] at hout
        split_ifs at hout
        · exact hout
        · exact ru_injective (D5.S3.Combinatorics.PanSkanderaWangBruhat.result m hm4 c hc).2.1
            (D5.S3.Combinatorics.PanSkanderaWangBruhat.result m hm4 d hd).2.1 hout
      have hcd := ih m (by omega) hm4 c d hc hd hfd
      have hab : a = b := by
        dsimp [c, d] at hcd
        split_ifs at hcd
        · exact hcd
        · exact ru_injective hda.1 hdb.1 hcd
      have hpw : p < w.length := by have hh := hw.1.length_eq; simp at hh; omega
      have hqz : q < z.length := by have hh := hz.1.length_eq; simp at hh; omega
      have hwp : w[p] = m + 1 := List.getElem_idxOf hpw
      have hzq : z[q] = m + 1 := List.getElem_idxOf hqz
      have hwrec := List.insertIdx_eraseIdx_getElem hpw
      have hzrec := List.insertIdx_eraseIdx_getElem hqz
      rw [hwp] at hwrec
      rw [hzq] at hzrec
      change a.insertIdx p (m + 1) = w at hwrec
      change b.insertIdx q (m + 1) = z at hzrec
      rw [hab, hpq] at hwrec
      exact hwrec.symm.trans hzrec

private def ParityFrom (s : ℕ) (x : List ℕ) : Prop :=
  ∀ k : ℕ, ∀ hk : k < x.length, x[k]'hk % 2 = (s + k) % 2

private theorem swapPairs_parity : ∀ x : List ℕ, ∀ s : ℕ,
    x.length % 2 = 0 → ParityFrom s x → ParityFrom (s + 1) (swapPairs x)
  | [] => by simp [ParityFrom, swapPairs]
  | [a] => by simp
  | a :: b :: t => by
      intro s heven hx
      have htEven : t.length % 2 = 0 := by simp only [List.length_cons] at heven; omega
      have ht : ParityFrom (s + 2) t := by
        intro k hk
        have hh := hx (k + 2) (by simp; omega)
        simp only [List.getElem_cons_succ] at hh
        change t[k] % 2 = (s + 2 + k) % 2
        omega
      have ih := swapPairs_parity t (s + 2) htEven ht
      intro k hk
      cases k with
      | zero =>
        have hh := hx 1 (by simp)
        simpa only [swapPairs, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using hh
      | succ k =>
        cases k with
        | zero =>
          have hh := hx 0 (by simp)
          simp only [swapPairs, List.getElem_cons_succ, List.getElem_cons_zero]
          simp only [List.getElem_cons_zero, Nat.add_zero] at hh
          omega
        | succ k =>
          have hlen : (swapPairs t).length = t.length := D5.S3.Combinatorics.PanSkanderaWangBruhat.swapPairs_length t
          have hkn : k < (swapPairs t).length := by simp only [swapPairs, List.length_cons] at hk; omega
          have hh := ih k hkn
          simp only [swapPairs, List.getElem_cons_succ]
          omega

private theorem inss_parity {m : ℕ} (x : List ℕ) (hx : B m x) (q : ℕ)
    (hq : 1 ≤ q) (hqm : q ≤ m + 1) (hqpar : q % 2 = (m + 1) % 2) :
    ParityFrom 1 (inss q x) := by
  have hxlen : x.length = m := by simpa [IsPerm] using hx.1.length_eq
  have htake : (x.take (q - 1)).length = q - 1 := by simp [hxlen]; omega
  have hdrop : (x.drop (q - 1)).length = m - (q - 1) := by simp [hxlen]
  have heven : (x.drop (q - 1)).length % 2 = 0 := by rw [hdrop]; omega
  have htail : ParityFrom q (x.drop (q - 1)) := by
    intro k hk
    have hidx : q - 1 + k < x.length := by simp [List.length_drop] at hk; omega
    have hh := hx.2 (q - 1 + k) hidx
    rw [List.getElem_drop]
    omega
  have hswap := swapPairs_parity (x.drop (q - 1)) q heven htail
  intro k hk
  dsimp [inss] at hk ⊢
  by_cases hkt : k < q - 1
  · rw [List.getElem_append_left (by omega), List.getElem_take]
    have hh := hx.2 k (by omega)
    omega
  · rw [List.getElem_append_right (by omega : (x.take (q - 1)).length ≤ k)]
    simp only [htake]
    by_cases hkq : k = q - 1
    · subst k
      simp only [Nat.sub_self, List.getElem_cons_zero]
      rw [hxlen]
      omega
    · have hks : k - (q - 1) = (k - q) + 1 := by omega
      simp only [hks, List.getElem_cons_succ]
      have hh := hswap (k - q) (by
        have hlen := D5.S3.Combinatorics.PanSkanderaWangBruhat.swapPairs_length (x.drop (q - 1))
        simp only [List.length_append, List.length_cons] at hk
        omega)
      omega

set_option maxHeartbeats 4000000 in
/-- Every algorithm output has the paper's literal odd-even parity membership. -/
theorem f_image_B : ∀ n : ℕ, 4 ≤ n → ∀ w : List ℕ, A n w → B n (f n w) := by
  have delete_source {m : ℕ} (w : List ℕ) (hw : A (m + 1) w) :
      let p := w.idxOf (m + 1)
      let a := w.eraseIdx p
      IsPerm m a ∧ (m + 1) / 2 ≤ p ∧ p ≤ m ∧
        (a.take ((m + 1) / 2)).Perm (List.range' 1 ((m + 1) / 2)) := by
    dsimp
    let p := w.idxOf (m + 1)
    have hnmem : m + 1 ∈ w := hw.1.symm.subset (List.mem_range'.mpr ⟨m, by omega, by omega⟩)
    have hp : p < w.length := List.idxOf_lt_length_iff.mpr hnmem
    have hwlen : w.length = m + 1 := by simpa [IsPerm] using hw.1.length_eq
    have hget : w[p] = m + 1 := List.getElem_idxOf hp
    have hrange : (List.range' 1 (m + 1)).Perm ((m + 1) :: List.range' 1 m) := by
      have hh : List.range' 1 m ++ [m + 1] = List.range' 1 (m + 1) := by
        rw [List.range'_concat]
        congr 2
        omega
      rw [← hh]
      simpa only [List.append_nil] using
        (List.perm_middle (l₁ := List.range' 1 m) (a := m + 1) (l₂ := []))
    have ha : IsPerm m (w.eraseIdx p) := by
      have hna := List.getElem_cons_eraseIdx_perm hp
      rw [hget] at hna
      exact (hna.trans (hw.1.trans hrange)).cons_inv
    have hlow : (m + 1) / 2 ≤ p := by
      by_contra hb
      have hin := (List.mem_take_iff_idxOf_lt hnmem).mpr (by simpa [p] using hb)
      have hr := hw.2.subset hin
      simp only [List.mem_range'] at hr
      obtain ⟨j, hj, he⟩ := hr
      omega
    refine ⟨ha, hlow, by omega, ?_⟩
    rw [List.take_eraseIdx_eq_take_of_le w ((m + 1) / 2) p hlow]
    exact hw.2
  have a4_cases (w : List ℕ) (hw : A 4 w) :
      w = [1, 2, 3, 4] ∨ w = [1, 2, 4, 3] ∨ w = [2, 1, 3, 4] ∨ w = [2, 1, 4, 3] := by
    rcases hw with ⟨hperm, htake⟩
    have hprefix : (w.take 2).Perm ((List.range' 1 4).take 2) := by simpa [List.range'_succ] using htake
    have hdrop := hperm.drop hprefix
    have htakeCases : w.take 2 = [1, 2] ∨ w.take 2 = [2, 1] := by
      apply List.perm_pair.mp
      simpa [List.range'_succ] using htake
    have hdropCases : w.drop 2 = [3, 4] ∨ w.drop 2 = [4, 3] := by
      apply List.perm_pair.mp
      simpa [List.range'_succ] using hdrop
    have hsplit := (List.take_append_drop 2 w).symm
    rcases htakeCases with htakeCases | htakeCases <;>
      rcases hdropCases with hdropCases | hdropCases <;>
      simp only [htakeCases, hdropCases] at hsplit <;> simp [hsplit]
  have ru_B {m : ℕ} {x : List ℕ} (hx : B m x) : B m (RU m x) := by
    refine ⟨ru_isPerm hx.1, ?_⟩
    have hxlen : x.length = m := by simpa [IsPerm] using hx.1.length_eq
    intro k hk
    have hkn : k < m := by simpa [RU, hxlen] using hk
    have hj : m - 1 - k < x.length := by omega
    have hpar := hx.2 (m - 1 - k) hj
    have hm := hx.1.subset (List.getElem_mem hj)
    simp only [List.mem_range'] at hm
    obtain ⟨j, hjn, he⟩ := hm
    simp only [RU, List.getElem_map, List.getElem_reverse, hxlen]
    omega
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn w hw
    have hfperm := (D5.S3.Combinatorics.PanSkanderaWangBruhat.result n hn w hw).2.1
    by_cases hn4 : n = 4
    · subst n
      refine ⟨hfperm, ?_⟩
      rcases a4_cases w hw with rfl | rfl | rfl | rfl
      all_goals
        norm_num [f, f4]
        intro k hk
        interval_cases k <;> norm_num
    · have hn5 : 5 ≤ n := by omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hm4 : 4 ≤ m := by omega
      let p := w.idxOf (m + 1)
      let a := w.eraseIdx p
      have hda := delete_source w hw
      change IsPerm m a ∧ (m + 1) / 2 ≤ p ∧ p ≤ m ∧
        (a.take ((m + 1) / 2)).Perm (List.range' 1 ((m + 1) / 2)) at hda
      let c := if m % 2 = 0 then a else RU m a
      have hc : A m c := by
        dsimp [c]
        split_ifs with hm
        · refine ⟨hda.1, ?_⟩
          have hh : (m + 1) / 2 = m / 2 := by omega
          simpa only [hh] using hda.2.2.2
        · apply ru_mem_A_of_longPrefix hda.1 (by omega)
          have hh : (m + 1) / 2 = m / 2 + 1 := by omega
          simpa only [hh] using hda.2.2.2
      let outc := if m % 2 = 0 then f m c else RU m (f m c)
      have hoc : B m outc := by
        dsimp [outc]; split_ifs
        · exact ih m (by omega) hm4 c hc
        · exact ru_B (ih m (by omega) hm4 c hc)
      let s := 2 * (p + 1) - (m + 1)
      have hs : 1 ≤ s ∧ s ≤ m + 1 := by dsimp [s]; omega
      have hfw : f (m + 1) w = inss s outc := by
        simp only [f, if_neg (by omega : ¬ m + 1 ≤ 4)]
        dsimp [p, a, c, outc, s]
        split_ifs with hm <;> congr 1 <;> omega
      refine ⟨hfperm, ?_⟩
      have hh := inss_parity outc hoc s hs.1 hs.2 (by dsimp [s]; omega)
      rw [hfw]
      intro k hk
      have hp := hh k hk
      omega

#print axioms f_injective
#print axioms f_image_B
end PSW
