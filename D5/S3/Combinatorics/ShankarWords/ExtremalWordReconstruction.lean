/- GID: D5/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ShankarWords/ExtremalWordReconstruction
   mirror-E: none(waiver:structural-word-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.List.Triplewise, mathlib/module/Mathlib.Data.List.Induction]
   utility: none
   digest: Actual extremal-word reconstruction through a whole-pair cut. -/

import D5.S3.Combinatorics.ShankarWords.OddWordConstruction
import Mathlib.Data.List.Triplewise
import Mathlib.Data.List.Induction
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction
open D5.S3.Combinatorics.ShankarWords.ActualWordExtremal

/-- Original-word reconstruction through the whole-pair cut, with the legal
singleton-two cuts and reverse-complement identification left outside the conclusion. -/
theorem extremal_word_cut_reconstruction (k : ℕ) (hk : 2 ≤ k) (w : List ℕ)
    (hw : w ∈ actualWords k) (hd : descents w = extremalValue k) :
    (∃ t : ℕ, 1 ≤ t ∧ k = 2 * t ∧ w = evenWord t) ∨
    (∃ t : ℕ, 1 ≤ t ∧ k = 2 * t + 1 ∧
      ((∃ q : Fin (2*t), w = oddOneWord t q) ∨
       (∃ j : ℕ, j ≤ 3*t ∧
         w = [1] ++ (pairBlocks 2 1 t ++ pairBlocks 3 1 t ++
           pairBlocks 3 2 t).take (2*j) ++ [2] ++
           (pairBlocks 2 1 t ++ pairBlocks 3 1 t ++ pairBlocks 3 2 t).drop (2*j) ++ [3]) ∨
       (∃ j : ℕ, j ≤ 3*t ∧
         w = [1] ++ (pairBlocks 2 1 (t+1) ++ pairBlocks 3 1 (t-1) ++
           pairBlocks 3 2 t).take (2*j) ++ [3] ++
           (pairBlocks 2 1 (t+1) ++ pairBlocks 3 1 (t-1) ++
           pairBlocks 3 2 t).drop (2*j) ++ [3]))) := by
  classical
  have hrec (a b : ℕ) (x : List ℕ) :
      descents (a :: b :: x) = (if b < a then 1 else 0) + descents (b :: x) := by
    simp only [descents, List.tail_cons, List.zip_cons_cons, List.filter_cons]
    split_ifs <;> simp_all <;> omega
  have hsmall (a : ℕ) : descents [a] = 0 := by simp [descents]
  have hnil : descents [] = 0 := by simp [descents]
  have hpack (x : List ℕ)
      (ha : ∀ a ∈ x, 1 ≤ a ∧ a ≤ 3)
      (hs : x.Triplewise (fun a b c => ¬ (a = 3 ∧ b = 2 ∧ c = 1))) :
      2 * descents x ≤ x.length ∧
      (x.length ≤ 2 * descents x + 1 →
       ∃ U V : List (List ℕ),
        (∀ q ∈ U ++ V, ∃ a b, q = [a,b] ∧ 1 ≤ b ∧ b < a ∧ a ≤ 3) ∧
        ((x = U.flatten ++ V.flatten ∧ x.length = 2 * descents x) ∨
         ∃ s, x = U.flatten ++ [s] ++ V.flatten ∧ x.length = 2 * descents x + 1)) := by
    induction x using List.twoStepInduction with
    | nil =>
      simp only [hnil, List.length_nil, Nat.mul_zero, Nat.zero_le, true_and]
      intro _
      refine ⟨[], [], ?_, Or.inl ?_⟩ <;> simp
    | singleton a =>
      simp only [hsmall, List.length_singleton, Nat.mul_zero, Nat.zero_le, true_and]
      intro _
      refine ⟨[], [], ?_, Or.inr ⟨a, ?_, by simp⟩⟩ <;> simp
    | cons_cons a b x ih ih' =>
      have hax : ∀ z ∈ x, 1 ≤ z ∧ z ≤ 3 := by
        intro z hz; exact ha z (by simp [hz])
      have hbx : ∀ z ∈ b :: x, 1 ≤ z ∧ z ≤ 3 := by
        intro z hz; exact ha z (by simp [hz])
      have hsb := (List.triplewise_cons.mp hs).2
      have hsx := (List.triplewise_cons.mp hsb).2
      have ha' := ha a (by simp)
      have hb' := ha b (by simp)
      by_cases hab : b < a
      · have hdb : descents (b :: x) = descents x := by
          cases x with
          | nil => simp [descents]
          | cons c z =>
            have hc := hax c (by simp)
            have hn : ¬ c < b := by
              intro hcb
              have hbad := (List.pairwise_cons.mp (List.triplewise_cons.mp hs).1).1 c (by simp)
              apply hbad
              exact ⟨by omega, by omega, by omega⟩
            rw [hrec, if_neg hn, zero_add]
        have he : descents (a :: b :: x) = 1 + descents x := by
          rw [hrec, if_pos hab, hdb]
        obtain ⟨hle, hp⟩ := ih hax hsx
        constructor
        · simp only [he, List.length_cons]; omega
        · intro hlen
          have hh : x.length ≤ 2 * descents x + 1 := by
            simp only [he, List.length_cons] at hlen; omega
          obtain ⟨U,V,hq,hform⟩ := hp hh
          refine ⟨[a,b] :: U, V, ?_, ?_⟩
          · intro q hmem
            simp only [List.cons_append, List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact ⟨a,b,rfl,hb'.1,hab,ha'.2⟩
            · exact hq q hmem
          · rcases hform with ⟨hform,hlen⟩ | ⟨s,hform,hlen⟩
            · left; constructor
              · simpa [List.flatten_cons, List.append_assoc] using
                  congrArg (fun z => a :: b :: z) hform
              · simp only [he, List.length_cons]; omega
            · right; refine ⟨s, ?_, ?_⟩
              · simpa [List.flatten_cons, List.append_assoc] using
                  congrArg (fun z => a :: b :: z) hform
              · simp only [he, List.length_cons]; omega
      · have he : descents (a :: b :: x) = descents (b :: x) := by
          rw [hrec, if_neg hab, zero_add]
        obtain ⟨hle,hp⟩ := ih' b hbx hsb
        constructor
        · simp only [List.length_cons] at hle
          simp only [he, List.length_cons]; omega
        · intro hlen
          have hh : (b :: x).length ≤ 2 * descents (b :: x) + 1 := by
            simp only [he, List.length_cons] at hlen ⊢; omega
          obtain ⟨U,V,hq,hform⟩ := hp hh
          rcases hform with ⟨hform,hlen'⟩ | ⟨s,hform,hlen'⟩
          · refine ⟨[], U ++ V, ?_, Or.inr ⟨a, ?_, ?_⟩⟩
            · simpa using hq
            · simpa [List.flatten_append] using congrArg (List.cons a) hform
            · simp only [he, List.length_cons] at *; omega
          · simp only [he, List.length_cons] at *; omega
  have hadm : IsAdmissible k w := by
    have h := hw
    simp only [actualWords, Finset.mem_filter] at h
    exact h.2
  obtain ⟨hlen,halpha,hc1,hc2,hc3,hlat,havoid⟩ := hadm
  have hne : w ≠ [] := by intro he; simp [he] at hlen; omega
  obtain ⟨a,v,rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha := halpha a (by simp)
  have hf : ([a] : List ℕ).count 2 ≤ ([a] : List ℕ).count 1 ∧
      ([a] : List ℕ).count 3 ≤ ([a] : List ℕ).count 2 := by
    simpa using hlat ⟨1, by simp⟩
  have ha1 : a = 1 := by
    by_contra h
    have hh : a = 2 ∨ a = 3 := by omega
    rcases hh with rfl | rfl <;> simp at hf
  subst a
  rcases v.eq_nil_or_concat' with rfl | ⟨x,b,rfl⟩
  · simp at hlen; omega
  have hb := halpha b (by simp)
  have hpre := hlat ⟨(1 :: x).length, by simp⟩
  have hpre' : (1 :: x).count 2 ≤ (1 :: x).count 1 ∧
      (1 :: x).count 3 ≤ (1 :: x).count 2 := by
    change (( (1 :: x) ++ [b]).take (1 :: x).length).count 2 ≤
      (( (1 :: x) ++ [b]).take (1 :: x).length).count 1 ∧
      (( (1 :: x) ++ [b]).take (1 :: x).length).count 3 ≤
      (( (1 :: x) ++ [b]).take (1 :: x).length).count 2 at hpre
    simpa only [List.take_append, List.take_length,
      Nat.sub_self, List.take_zero, List.append_nil] using hpre
  have hc1' : (1 :: x).count 1 + (if b = 1 then 1 else 0) = k := by
    simpa only [← List.cons_append, List.count_append, List.count_singleton, beq_iff_eq] using hc1
  have hc2' : (1 :: x).count 2 + (if b = 2 then 1 else 0) = k := by
    simpa only [← List.cons_append, List.count_append, List.count_singleton, beq_iff_eq] using hc2
  have hc3' : (1 :: x).count 3 + (if b = 3 then 1 else 0) = k := by
    simpa only [← List.cons_append, List.count_append, List.count_singleton, beq_iff_eq] using hc3
  have hb3 : b = 3 := by split_ifs at hc1' hc2' hc3' <;> omega
  subst b
  have hax : ∀ a ∈ x, 1 ≤ a ∧ a ≤ 3 := by
    intro a ha; exact halpha a (by simp [ha])
  have hs : x.Triplewise (fun a b c => ¬ (a = 3 ∧ b = 2 ∧ c = 1)) := by
    apply List.triplewise_iff_getElem.mpr
    intro i j l hij hjl hll hbad
    apply havoid ⟨i+1,by simp;omega⟩ ⟨j+1,by simp;omega⟩
      ⟨l+1,by simp;omega⟩ (by change i+1<j+1;omega) (by change j+1<l+1;omega)
    simpa only [List.get_eq_getElem, List.getElem_cons_succ,
      List.getElem_append_left (by omega : i < x.length),
      List.getElem_append_left (by omega : j < x.length),
      List.getElem_append_left hll] using hbad
  have hend (z : List ℕ) (hz : ∀ a ∈ z, a ≤ 3) :
      descents (z ++ [3]) = descents z := by
    induction z with
    | nil => simp [descents]
    | cons a z ih =>
      cases z with
      | nil =>
        have ha := hz a (by simp)
        simp [hrec, hsmall, show ¬ 3 < a by omega]
      | cons b z =>
        have hz' : ∀ c ∈ b :: z, c ≤ 3 := by
          intro c hc; exact hz c (by simp [hc])
        simpa only [List.cons_append, hrec] using
          congrArg (fun d => (if b < a then 1 else 0) + d) (ih hz')
  have hstart : descents (1 :: x) = descents x := by
    cases x with
    | nil => simp [descents]
    | cons a z =>
      have ha := hax a (by simp)
      rw [hrec, if_neg (by omega), zero_add]
  have hxdesc : descents x = extremalValue k := by
    rw [← List.cons_append, hend _ (by
      intro a ha; exact (halpha a (by
        simp only [List.mem_cons] at ha
        simpa only [List.mem_cons, List.mem_append, List.mem_singleton] using
          ha.imp_right Or.inl)).2), hstart] at hd
    exact hd
  have hxlen : x.length = 3 * k - 2 := by
    simp only [List.length_cons, List.length_append, List.length_nil] at hlen
    omega
  have hsat : x.length ≤ 2 * descents x + 1 := by
    rw [hxdesc, extremalValue, hxlen]; omega
  obtain ⟨hbound,hpack'⟩ := hpack x hax hs
  obtain ⟨U,V,hq,hform⟩ := hpack' hsat
  have hsub (u v : List ℕ) (huv : List.Sublist u v)
      (hv : v.Triplewise (fun a b c => ¬ (a = 3 ∧ b = 2 ∧ c = 1))) :
      u.Triplewise (fun a b c => ¬ (a = 3 ∧ b = 2 ∧ c = 1)) := by
    induction huv with
    | slnil => exact List.Triplewise.nil
    | cons a h ih => exact ih (List.triplewise_cons.mp hv).2
    | cons_cons a h ih =>
      exact List.Triplewise.cons ((List.triplewise_cons.mp hv).1.sublist h)
        (ih (List.triplewise_cons.mp hv).2)
  have hqsub : List.Sublist (U ++ V).flatten x := by
    rcases hform with ⟨he,_⟩ | ⟨s,he,_⟩
    · rw [he, List.flatten_append]
    · rw [he, List.flatten_append]
      simpa only [List.append_assoc, List.singleton_append] using
        (List.Sublist.refl U.flatten).append (List.sublist_cons_self s V.flatten)
  have hqs := hsub _ _ hqsub hs
  have horder (Q : List (List ℕ))
      (hq : ∀ q ∈ Q, ∃ a b, q = [a,b] ∧ 1 ≤ b ∧ b < a ∧ a ≤ 3)
      (hs : Q.flatten.Triplewise (fun a b c => ¬ (a = 3 ∧ b = 2 ∧ c = 1))) :
      ∃ a b c, Q = List.replicate a [2,1] ++ List.replicate b [3,1] ++
        List.replicate c [3,2] := by
    induction Q with
    | nil => exact ⟨0,0,0,rfl⟩
    | cons q Q ih =>
      obtain ⟨a,b,hQ⟩ := hq q (by simp)
      rcases hQ with ⟨rfl,hb,hab,ha⟩
      have hqt : ∀ q ∈ Q, ∃ a b, q = [a,b] ∧ 1 ≤ b ∧ b < a ∧ a ≤ 3 := by
        intro q h; exact hq q (by simp [h])
      have hst : Q.flatten.Triplewise (fun a b c => ¬ (a = 3 ∧ b = 2 ∧ c = 1)) := by
        exact (List.triplewise_cons.mp (List.triplewise_cons.mp hs).2).2
      obtain ⟨A,B,C,he⟩ := ih hqt hst
      have hcases : (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 1) ∨ (a = 3 ∧ b = 2) := by
        omega
      rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · refine ⟨A+1,B,C,?_⟩
        simp only [List.replicate_succ, List.cons_append, he]
      · have hA : A = 0 := by
          by_contra hn
          obtain ⟨A',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          rw [he] at hs
          simp only [List.flatten_cons, List.flatten_append, List.replicate_succ,
            List.flatten_cons, List.cons_append, List.nil_append] at hs
          have hh := (List.triplewise_cons.mp hs).1
          have hh' := (List.pairwise_cons.mp hh).2
          have hh'' := (List.pairwise_cons.mp hh').1 1 (by simp)
          exact hh'' ⟨rfl,rfl,rfl⟩
        subst A
        refine ⟨0,B+1,C,?_⟩
        simp only [he, List.replicate_zero, List.nil_append, List.replicate_succ,
          List.cons_append]
      · have hA : A = 0 := by
          by_contra hn
          obtain ⟨A',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          rw [he] at hs
          simp only [List.flatten_cons, List.flatten_append, List.replicate_succ,
            List.flatten_cons, List.cons_append, List.nil_append] at hs
          have hh := (List.triplewise_cons.mp hs).1
          have hh' := (List.pairwise_cons.mp hh).1 1 (by simp)
          exact hh' ⟨rfl,rfl,rfl⟩
        subst A
        have hB : B = 0 := by
          by_contra hn
          obtain ⟨B',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          rw [he] at hs
          simp only [List.flatten_cons, List.flatten_append, List.replicate_zero,
            List.nil_append, List.replicate_succ, List.flatten_cons, List.cons_append] at hs
          have hh := (List.triplewise_cons.mp hs).1
          have hh' := (List.pairwise_cons.mp hh).1 1 (by simp)
          exact hh' ⟨rfl,rfl,rfl⟩
        subst B
        refine ⟨0,0,C+1,?_⟩
        simp only [he, List.replicate_zero, List.nil_append, List.replicate_succ]
  obtain ⟨A,B,C,hQ⟩ := horder (U ++ V) hq hqs
  have hbase : U.flatten ++ V.flatten =
      pairBlocks 2 1 A ++ pairBlocks 3 1 B ++ pairBlocks 3 2 C := by
    simpa only [List.flatten_append, pairBlocks] using congrArg List.flatten hQ
  have pair_count (a b c n : ℕ) :
      (pairBlocks a b n).count c = n * (([a,b] : List ℕ).count c) := by
    simp [pairBlocks, List.count_flatten]
  have pair_succ (a b n : ℕ) :
      pairBlocks a b (n+1) = a :: b :: pairBlocks a b n := by
    simp [pairBlocks, List.replicate_succ]
  have pair_end (a b n : ℕ) :
      pairBlocks a b (n+1) = pairBlocks a b n ++ [a,b] := by
    simp [pairBlocks, List.replicate_succ', List.flatten_append]
  have shift (a b n : ℕ) :
      [a] ++ pairBlocks b a n = pairBlocks a b n ++ [a] := by
    induction n with
    | zero => simp [pairBlocks]
    | succ n ih =>
      simpa only [pair_succ, List.singleton_append, List.cons_append, List.nil_append] using
        congrArg (fun z => a :: b :: z) ih
  have pair_len (a b n : ℕ) : (pairBlocks a b n).length = 2*n := by
    simp [pairBlocks, Nat.mul_comm]
  rcases hform with ⟨he,hlen'⟩ | ⟨s,he,hlen'⟩
  · have hxform : x = pairBlocks 2 1 A ++ pairBlocks 3 1 B ++ pairBlocks 3 2 C :=
      he.trans hbase
    rw [hxform] at hc1 hc2 hc3
    simp only [List.count_cons, List.count_append, pair_count] at hc1 hc2 hc3
    norm_num at hc1 hc2 hc3
    have hA : 1 ≤ A := by omega
    have hC : C = A := by omega
    have hB : B = A-1 := by omega
    have hkA : k = 2*A := by omega
    subst C B
    left
    refine ⟨A,hA,hkA,?_⟩
    have hmiddle : [1] ++ pairBlocks 3 1 (A-1) ++ [3] = pairBlocks 1 3 A := by
      rw [shift, List.append_assoc]
      have heA : A = (A-1)+1 := by omega
      conv_rhs => rw [heA, pair_end]
      rfl
    have he1 := congrArg (fun z => z ++ pairBlocks 3 1 (A-1) ++
      pairBlocks 3 2 A ++ [3]) (shift 1 2 A)
    have he2 := congrArg (fun z => pairBlocks 1 2 A ++
      ([1] ++ pairBlocks 3 1 (A-1) ++ z)) (shift 3 2 A).symm
    have he3 := congrArg (fun z => pairBlocks 1 2 A ++ z ++
      pairBlocks 2 3 A) hmiddle
    change [1] ++ (x ++ [3]) = evenWord A
    rw [hxform]
    calc
      _ = pairBlocks 1 2 A ++ ([1] ++ pairBlocks 3 1 (A-1) ++
          (pairBlocks 3 2 A ++ [3])) := by
        simpa only [List.append_assoc] using he1
      _ = pairBlocks 1 2 A ++ ([1] ++ pairBlocks 3 1 (A-1) ++
          ([3] ++ pairBlocks 2 3 A)) := he2
      _ = evenWord A := by
        simpa only [evenWord, List.append_assoc] using he3
  · have hsalpha := hax s (by rw [he]; simp)
    have ht : ∃ t : ℕ, 1 ≤ t ∧ k = 2*t+1 := by
      rw [hxdesc, extremalValue, hxlen] at hlen'
      refine ⟨k/2,?_,?_⟩ <;> omega
    obtain ⟨t,ht,hkt⟩ := ht
    have hflatlen (Q : List (List ℕ)) (hQ : ∀ q ∈ Q, q.length = 2) :
        Q.flatten.length = 2 * Q.length := by
      induction Q with
      | nil => simp
      | cons q Q ih =>
        have hlq := hQ q (by simp)
        have hlQ : ∀ q ∈ Q, q.length = 2 := by
          intro q h; exact hQ q (by simp [h])
        simp only [List.flatten_cons, List.length_append, List.length_cons, hlq, ih hlQ]
        omega
    have hU : U.flatten.length = 2 * U.length := hflatlen U (by
      intro q h; obtain ⟨a,b,rfl,_⟩ := hq q (by simp [h]); simp)
    have hV : V.flatten.length = 2 * V.length := hflatlen V (by
      intro q h; obtain ⟨a,b,rfl,_⟩ := hq q (by simp [h]); simp)
    have hj : U.length ≤ 3*t := by
      rw [he] at hxlen
      simp only [List.length_append, List.length_singleton, hU,hV] at hxlen
      omega
    have htake : U.flatten =
        (pairBlocks 2 1 A ++ pairBlocks 3 1 B ++ pairBlocks 3 2 C).take (2*U.length) := by
      rw [← hbase, ← hU, List.take_append, List.take_length, Nat.sub_self,
        List.take_zero, List.append_nil]
    have hdrop : V.flatten =
        (pairBlocks 2 1 A ++ pairBlocks 3 1 B ++ pairBlocks 3 2 C).drop (2*U.length) := by
      rw [← hbase, ← hU, List.drop_append, List.drop_length, Nat.sub_self,
        List.drop_zero, List.nil_append]
    have hword : 1 :: (x ++ [3]) = [1] ++
        (pairBlocks 2 1 A ++ pairBlocks 3 1 B ++ pairBlocks 3 2 C).take (2*U.length) ++
        [s] ++ (pairBlocks 2 1 A ++ pairBlocks 3 1 B ++ pairBlocks 3 2 C).drop
        (2*U.length) ++ [3] := by
      rw [he, ← htake, ← hdrop]
      simp only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append]
    have hcounts (z : ℕ) :
        x.count z = (pairBlocks 2 1 A ++ pairBlocks 3 1 B ++ pairBlocks 3 2 C).count z
          + ([s] : List ℕ).count z := by
      have hh := congrArg (fun w => w.count z) hbase
      rw [he]
      simp only [List.count_append] at hh ⊢
      omega
    have hc1n : 1 + A + B + (if s = 1 then 1 else 0) = k := by
      have hh := hcounts 1
      simp only [List.count_append, pair_count, List.count_singleton, beq_iff_eq] at hh
      norm_num at hh
      have hc : x.count 1 + 1 = k := by simpa using hc1
      omega
    have hc2n : A + C + (if s = 2 then 1 else 0) = k := by
      have hh := hcounts 2
      simp only [List.count_append, pair_count, List.count_singleton, beq_iff_eq] at hh
      norm_num at hh
      have hc : x.count 2 = k := by simpa using hc2
      omega
    have hc3n : 1 + B + C + (if s = 3 then 1 else 0) = k := by
      have hh := hcounts 3
      simp only [List.count_append, pair_count, List.count_singleton, beq_iff_eq] at hh
      norm_num at hh
      have hc : x.count 3 + 1 = k := by simpa using hc3
      omega
    obtain ⟨Au,Bu,Cu,hUF⟩ := horder U (by
      intro q h; exact hq q (by simp [h]))
      ((List.triplewise_append.mp (by
        simpa only [List.flatten_append] using hqs)).1)
    obtain ⟨Av,Bv,Cv,hVF⟩ := horder V (by
      intro q h; exact hq q (by simp [h]))
      ((List.triplewise_append.mp (by
        simpa only [List.flatten_append] using hqs)).2.1)
    have hsumA : Au+Av=A := by
      have hh := congrArg (fun z => z.count [2,1]) hQ
      rw [hUF,hVF] at hh
      simpa [List.count_replicate] using hh
    have hsumB : Bu+Bv=B := by
      have hh := congrArg (fun z => z.count [3,1]) hQ
      rw [hUF,hVF] at hh
      simpa [List.count_replicate] using hh
    have hsumC : Cu+Cv=C := by
      have hh := congrArg (fun z => z.count [3,2]) hQ
      rw [hUF,hVF] at hh
      simpa [List.count_replicate] using hh
    have hUlength : U.length = Au+Bu+Cu := by simp [hUF, Nat.add_assoc]
    have hVlength : V.length = Av+Bv+Cv := by simp [hVF, Nat.add_assoc]
    have hUFflat : U.flatten = pairBlocks 2 1 Au ++ pairBlocks 3 1 Bu ++
        pairBlocks 3 2 Cu := by
      simpa only [List.flatten_append, pairBlocks] using congrArg List.flatten hUF
    have hVFflat : V.flatten = pairBlocks 2 1 Av ++ pairBlocks 3 1 Bv ++
        pairBlocks 3 2 Cv := by
      simpa only [List.flatten_append, pairBlocks] using congrArg List.flatten hVF
    have hcases : s = 1 ∨ s = 2 ∨ s = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · have hA : A = t := by simp at hc1n hc2n hc3n; omega
      have hB : B = t-1 := by simp at hc1n hc2n hc3n; omega
      have hC : C = t+1 := by simp at hc1n hc2n hc3n; omega
      rw [hA,hB,hC] at hword hbase hQ
      have hone : 1 :: (x ++ [3]) = [1] ++ (oddOneBase t).take (2*U.length) ++ [1] ++
          (oddOneBase t).drop (2*U.length) ++ [3] := by
        simpa only [oddOneBase] using hword
      have hCu : Cu = 0 := by
        have hx := hs
        rw [he, List.append_assoc] at hx
        have hp := (List.triplewise_append.mp hx).2.2.2 1 (by simp)
        rw [hUFflat] at hp
        have hpC := (List.pairwise_append.mp hp).2.1
        by_contra h
        obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
        rw [pair_succ] at hpC
        exact (List.pairwise_cons.mp hpC).1 2 (by simp) ⟨rfl,rfl,rfl⟩
      have hjlt : U.length < 2*t := by omega
      right
      refine ⟨t,ht,hkt,Or.inl ⟨⟨U.length,hjlt⟩,?_⟩⟩
      simpa only [oddOneWord] using hone
    · have hA : A = t := by simp at hc1n hc2n hc3n; omega
      have hB : B = t := by simp at hc1n hc2n hc3n; omega
      have hC : C = t := by simp at hc1n hc2n hc3n; omega
      rw [hA,hB,hC] at hword hbase hQ
      right
      exact ⟨t,ht,hkt,Or.inr (Or.inl ⟨U.length,hj,hword⟩)⟩
    · have hA : A = t+1 := by simp at hc1n hc2n hc3n; omega
      have hB : B = t-1 := by simp at hc1n hc2n hc3n; omega
      have hC : C = t := by simp at hc1n hc2n hc3n; omega
      rw [hA,hB,hC] at hword hbase hQ
      right
      exact ⟨t,ht,hkt,Or.inr (Or.inr ⟨U.length,hj,hword⟩)⟩

#print axioms extremal_word_cut_reconstruction

end D5.S3.Combinatorics.ShankarWords.ExtremalWordReconstruction
