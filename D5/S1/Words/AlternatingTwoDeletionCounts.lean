/- GID: D5/S1/Words/AlternatingTwoDeletionCounts
   generality: I
   mirror-B: D5/B/S1/Words/AlternatingTwoDeletionCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary run counts and entropy comparisons for two deletions. -/

/-
admission_basis: escape-witness
Module escape_witness: count_alt_two.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19498.
The alternating list uses the frozen alternatingBit; ofFn_altFrom proves the parity correspondence.
Frozen dependency identifiers refer to declarations at the pinned base:
F1: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternatingBit; statement_id: sha256:cf75864c00a72d48d77507be601672dea7f3c33509b8c7ec9c231241206a8c1f.
F2: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternating_bit_succ; statement_id: sha256:6936ec95b02ee5eb5b16201a9e3c9c70a5035dc5763a91e1eb84fb2d55be9f66.
F3: D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.scatteredCount_eq_count_sublistsLen; statement_id: sha256:1ef019efa27fa73883b2c484815d0895ff1d4e12bfaa8beb7e837b90c59ca23f.
F4: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c.
F5: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_3; generated statement_id: sha256:eeb4ba1dc42c97107933499a696fff58308201b57cdaa0e2d6b01318dfe85988.
F6: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_1; generated statement_id: sha256:607874708dedb4dcfc543f03f8a4e0696951869b05e14db52394fc154de855d9.
F7: D5/S1/Words/Complexity/VivionBinomialConverseFails.congr_simp; statement_id: sha256:08caa00f2d10a6074fe321122becd2a661a58047e87908bd0b2e539bd8628b72.
sum_binary_real_succ: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: sum_one_extra_alt.
sum_indicator_increment: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: sum_one_extra_alt.
altList: proof_shape: bind-only (definition); frozen: F1; escape_witness: none; consumer: count_alt_opposite.
altList_zero: proof_shape: bind-only; frozen: F1; escape_witness: none; consumer: sum_one_extra_alt.
altList_succ: proof_shape: bind-only; frozen: F2,F1; escape_witness: none; consumer: count_alt_opposite.
count_equal_length: proof_shape: bind-only; frozen: F3,F4; escape_witness: none; consumer: count_alt_opposite.
count_alt_cons_same: proof_shape: bind-only; frozen: F5,F2,F1,F4; escape_witness: none; consumer: sum_one_two_joint.
count_alt_cons_opposite: proof_shape: bind-only; frozen: F5,F2,F1,F4; escape_witness: none; consumer: count_alt_cons_opposite_pos.
altList_not: proof_shape: bind-only; frozen: F2,F1; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.ofFn_complement_alternating.
altList_length: proof_shape: bind-only; frozen: F1; escape_witness: none; consumer: count_alt_opposite.
ofFn_altFrom: proof_shape: bind-only; frozen: F1; escape_witness: none; consumer: ofFn_alternating.
count_alt_one_opposite: proof_shape: bind-only; frozen: F1,F3,F4,F5,F2; escape_witness: none; consumer: sum_one_extra_alt.
count_alt_cons_opposite_pos: proof_shape: bind-only; frozen: F5,F2,F1,F4; escape_witness: none; consumer: sum_one_two_joint.
count_alt_opposite: proof_shape: bind-only; frozen: F1,F3,F4,F5,F2; escape_witness: none; consumer: count_alt_two.
count_alt_one_le: proof_shape: content; frozen: F1,F4,F3,F5,F2,F6,F7; escape_witness: none; consumer: count_alt_two.
ofFn_alternating: proof_shape: bind-only; frozen: F1; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.other_alternating_embedding_le_one.
count_alt_equal_word: proof_shape: bind-only; frozen: F1,F3,F4; escape_witness: none; consumer: sum_one_extra_alt.
count_alt_two: proof_shape: content; frozen: F1,F4,F3,F5,F2,F6,F7; escape_witness: count_alt_two; consumer: sum_one_two_joint.
sum_one_extra_alt: proof_shape: content; frozen: F1,F3,F4,F5,F2,F6,F7; escape_witness: none; consumer: sum_one_two_joint.
sum_one_two_joint: proof_shape: content; frozen: F1,F4,F3,F5,F2,F6,F7; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.altDeletionPhi_step.
-/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace D5.S1.Words.AlternatingTwoDeletionCounts

open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore (scatteredCount_eq_count_sublistsLen)


lemma sum_binary_real_succ {n : ℕ} (F : (Fin (n+1) → Bool) → ℝ) (b : Bool) :
    (∑ x,F x)=(∑ x : Fin n → Bool,F (Fin.cons b x))+
      ∑ x : Fin n → Bool,F (Fin.cons (!b) x) := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool))
    (fun p : Bool × (Fin n → Bool) => F (Fin.cons p.1 p.2)) F (fun _ => rfl)
  rw [Fintype.sum_prod_type] at h
  cases b <;> simpa [add_comm] using h.symm

private lemma sum_indicator_increment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (B : ι → ℕ) (z : ι) (F : ℕ → ℕ → ℝ) :
    (∑ x,F (a x + if x=z then 1 else 0) (B x)) =
      (∑ x,F (a x) (B x))+F (a z+1) (B z)-F (a z) (B z) := by
  have he : (fun x => F (a x+if x=z then 1 else 0) (B x)) =
      (fun x => F (a x) (B x)+if x=z then F (a z+1) (B z)-F (a z) (B z) else 0) := by
    funext x
    by_cases hx : x=z
    · subst x; simp
    · simp [hx]
  rw [he,Finset.sum_add_distrib]
  simp
  ring


def altList (b : Bool) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val)

lemma altList_zero (b : Bool) : altList b 0 = [] := by
  rfl

lemma altList_succ (b : Bool) (n : ℕ) : altList b (n+1) = b :: altList (!b) n := by
  rw [altList, List.ofFn_succ]
  change b :: List.ofFn (fun i : Fin n => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b (i.val+1)) =
    b :: List.ofFn (fun i : Fin n => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit (!b) i.val)
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternating_bit_succ]
  cases b <;> by_cases hi : i.val % 2 = 0 <;>
    simp [D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit, hi]


lemma count_equal_length (p q : List Bool) (h : p.length=q.length) :
    scatteredCount p q = if p=q then 1 else 0 := by
  rw [scatteredCount_eq_count_sublistsLen,h,List.sublistsLen_length]
  by_cases he : p=q <;> simp [he,eq_comm]

lemma count_alt_cons_same (b : Bool) (m : ℕ) (q : List Bool) :
    scatteredCount (altList b (m+1)) (b::q)=
      scatteredCount (altList b (m+1)) q+scatteredCount (altList (!b) m) q := by
  rw [altList_succ,scatteredCount,if_pos rfl]

lemma count_alt_cons_opposite (b : Bool) (m : ℕ) (q : List Bool) :
    scatteredCount (altList b (m+1)) ((!b)::q)=scatteredCount (altList b (m+1)) q := by
  have hn : b ≠ !b := by exact Bool.not_eq_not.mpr rfl
  rw [altList_succ,scatteredCount,if_neg hn,add_zero]

lemma altList_not (b : Bool) (n : ℕ) : altList (!b) n=(altList b n).map Bool.not := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simpa only [altList_zero,altList_succ,List.map_cons] using congrArg (List.cons (!b)) (ih (!b))

private lemma altList_length (b : Bool) (n : ℕ) : (altList b n).length=n := by
  exact List.length_ofFn

private lemma ofFn_altFrom (b : Bool) (n : ℕ) :
    List.ofFn (fun i : Fin n => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val) = altList b n := by
  rfl



private lemma count_alt_one_opposite (b : Bool) (m : ℕ) :
    scatteredCount (altList (!b) m) (altList b (m+1))=1 := by
  cases m with
  | zero => rfl
  | succ m =>
    have hn : (!b) ≠ b := by exact Bool.not_not_eq.mpr rfl
    rw [altList_succ,altList_succ,Bool.not_not,scatteredCount,if_neg hn,add_zero]
    rw [count_equal_length _ _ (by simp [altList_length])]
    simp [altList_zero,altList_succ]

private lemma count_alt_cons_opposite_pos (b : Bool) (m : ℕ) (hm : 1 ≤ m) (q : List Bool) :
    scatteredCount (altList b m) ((!b)::q)=scatteredCount (altList b m) q := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact count_alt_cons_opposite b k q

private lemma count_alt_opposite (a b : Bool) (p : List Bool) (hab : a≠b) :
    scatteredCount (a::p) (altList b (p.length+2)) =
      if a::p=altList (!b) (p.length+1) then 1 else 0 := by
  rw [altList_succ,scatteredCount,if_neg hab,add_zero]
  exact count_equal_length _ _ (by simp [altList_length])

private lemma count_alt_one_le (n : ℕ) (p : List Bool) (b : Bool) (hp : p.length=n) :
    scatteredCount p (altList b (n+1)) ≤ 1 := by
  induction n generalizing p b with
  | zero => have he : p=[] := List.length_eq_zero_iff.mp hp; simp [he,scatteredCount]
  | succ n ih =>
    cases p with
    | nil => simp at hp
    | cons a p =>
      have hp' : p.length=n := by exact Nat.add_right_cancel hp
      rw [altList_succ,scatteredCount]
      have he := count_equal_length (a::p) (altList (!b) (n+1)) (by simp [hp',altList_length])
      rw [he]
      by_cases hab : a=b
      · subst a
        have hne : b::p ≠ altList (!b) (n+1) := by
          simp only [altList_zero,altList_succ,List.cons.injEq]
          cases b <;> simp
        rw [if_neg hne,if_pos rfl,zero_add]
        exact ih p (!b) hp'
      · rw [if_neg hab,add_zero]
        split_ifs <;> omega

lemma ofFn_alternating (n : ℕ) : List.ofFn ((fun i : Fin n => decide (i.val % 2 = 1))) = altList false n := by
  rw [← ofFn_altFrom false n]
  congr 1
  funext i

  unfold D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit
  by_cases hp : i.val%2=0
  · have hn : i.val%2≠1 := by omega
    simp [hp,hn]
  · have hn : i.val%2=1 := by omega
    simp [hp,hn]


private lemma count_alt_equal_word (b : Bool) (n : ℕ) (y : Fin n → Bool) :
    scatteredCount (altList b n) (List.ofFn y)=if y=(fun i : Fin n => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val) then 1 else 0 := by
  rw [count_equal_length _ _ (by simp [altList_length]),←ofFn_altFrom]
  simp only [List.ofFn_inj,eq_comm]

lemma count_alt_two (n : ℕ) (b : Bool) :
    scatteredCount (altList b n) (altList b (n+2))=n+1 ∧
    ∀ p : List Bool, p.length=n → p≠altList b n →
      scatteredCount p (altList b (n+2)) ≤ 1 := by
  induction n generalizing b with
  | zero =>
    constructor
    · rfl
    · intro p hp hn
      have he : p=[] := List.length_eq_zero_iff.mp hp
      exact (hn he).elim
  | succ n ih =>
    have ih' := ih (!b)
    have hnot : b≠!b := by exact Bool.not_eq_not.mpr rfl
    have hfirst : scatteredCount (b::altList (!b) n) (altList (!b) (n+2))=1 := by
      simpa [altList_length,altList_zero,altList_succ] using count_alt_opposite b (!b) (altList (!b) n) hnot
    constructor
    · rw [altList_succ, altList_succ]
      rw [scatteredCount,if_pos rfl,hfirst,ih'.1]
      omega
    · intro p hp hn
      cases p with
      | nil => simp at hp
      | cons a p =>
        have hp' : p.length=n := by exact Nat.add_right_cancel hp
        rw [altList_succ,scatteredCount]
        by_cases hab : a=b
        · subst a
          have ht : p≠altList (!b) n := by
            intro h
            apply hn
            simp [altList_zero,altList_succ,h]
          have hf : scatteredCount (b::p) (altList (!b) (n+2))=0 := by
            have h := count_alt_opposite b (!b) p hnot
            simpa only [hp',Bool.not_not,if_neg hn] using h
          rw [hf,if_pos rfl,zero_add]
          exact ih'.2 p hp' ht
        · rw [if_neg hab,add_zero]
          exact count_alt_one_le (n+1) (a::p) (!b) hp

lemma sum_one_extra_alt (m : ℕ) (b : Bool) (F : ℕ → ℝ) (hF : F 0=0) :
    (∑ y : Fin (m+1) → Bool,F (scatteredCount (altList b m) (List.ofFn y))) =
      2*F 1+(m:ℝ)*F 2 := by
  classical
  induction m generalizing b with
  | zero => simp [altList_zero,altList_succ,scatteredCount]
  | succ m ih =>
    rw [sum_binary_real_succ _ b]
    simp only [List.ofFn_cons,altList_zero,altList_succ,scatteredCount,if_pos rfl]
    have hn : b≠!b := by exact Bool.not_eq_not.mpr rfl
    simp only [if_neg hn,add_zero,ite_true]
    have hc : ∀ y : Fin (m+1) → Bool,
        scatteredCount (b::altList (!b) m) (List.ofFn y)=
          if y=(fun i : Fin (m+1) => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val) then 1 else 0 := by
      intro y
      simpa only [altList_succ] using count_alt_equal_word b (m+1) y
    simp_rw [hc]
    have hinc := sum_indicator_increment
      (fun y : Fin (m+1) → Bool => scatteredCount (altList (!b) m) (List.ofFn y))
      (fun _ => 0) ((fun i : Fin (m+1) => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val)) (fun a _ => F a)
    have hc1 : scatteredCount (altList (!b) m) (List.ofFn ((fun i : Fin (m+1) => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val)))=1 := by
      rw [ofFn_altFrom]; exact count_alt_one_opposite b m
    simp only [hc1] at hinc
    have hcomm : (∑ y : Fin (m+1) → Bool,
        F ((if y=(fun i : Fin (m+1) => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val) then 1 else 0)+scatteredCount (altList (!b) m) (List.ofFn y))) =
      (∑ y : Fin (m+1) → Bool,F (scatteredCount (altList (!b) m) (List.ofFn y)))+F 2-F 1 := by
      simpa only [Nat.add_comm,show 1+1=2 by rfl] using hinc
    rw [hcomm,ih]
    simp_rw [apply_ite]
    simp only [hF,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Nat.cast_add,Nat.cast_one]
    ring

lemma sum_one_two_joint (m : ℕ) (hm : 1 ≤ m) (b : Bool)
    (F : ℕ → ℕ → ℝ) (hF : ∀ d,F 0 d=0) :
    (∑ y : Fin (m+2) → Bool,
      F (scatteredCount (altList b (m+1)) (List.ofFn y))
        (scatteredCount (altList (!b) m) (List.ofFn y))) =
      F 1 (m+1)+F 1 1+F 2 1+(m:ℝ)*F 2 2 := by
  classical
  rw [sum_binary_real_succ _ b]
  simp only [List.ofFn_cons,count_alt_cons_same,count_alt_cons_opposite]
  have hskip : ∀ q,scatteredCount (altList (!b) m) (b::q)=scatteredCount (altList (!b) m) q := by
    intro q
    simpa only [Bool.not_not] using count_alt_cons_opposite_pos (!b) m hm q
  simp_rw [hskip,count_alt_equal_word]
  let D : (Fin (m+1) → Bool) → ℕ := fun y => scatteredCount (altList (!b) m) (List.ofFn y)
  let z := (fun i : Fin (m+1) => D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails.alternatingBit b i.val)
  have hDz : D z=1 := by
    dsimp [D,z]
    rw [ofFn_altFrom]
    exact count_alt_one_opposite b m
  have hs := sum_indicator_increment D D z F
  rw [hDz] at hs
  have hbase := sum_one_extra_alt m (!b) (fun t => F t t) (hF 0)
  have hfirst : (∑ y : Fin (m+1) → Bool,
      F ((if y=z then 1 else 0)+D y) (D y)) =
        F 1 1+(m:ℝ)*F 2 2+F 2 1 := by
    simpa only [Nat.add_comm,show 1+1=2 by rfl] using hs.trans (by
      dsimp [D]
      rw [hbase]
      ring)
  have hzB : scatteredCount (altList (!b) m) ((!b)::List.ofFn z)=m+1 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    dsimp [z]
    rw [count_alt_cons_same,ofFn_altFrom,Bool.not_not]
    rw [count_alt_one_opposite b (k+1),(count_alt_two k b).1]
    omega
  have hsecond : (∑ y : Fin (m+1) → Bool,
      F (if y=z then 1 else 0) (scatteredCount (altList (!b) m) ((!b)::List.ofFn y))) =
        F 1 (m+1) := by
    have he : ∀ y : Fin (m+1) → Bool,
        F (if y=z then 1 else 0) (scatteredCount (altList (!b) m) ((!b)::List.ofFn y)) =
          if y=z then F 1 (m+1) else 0 := by
      intro y
      by_cases hy : y=z
      · subst y; simp only [ite_true,hzB]
      · simp only [hy,ite_false,hF]
    simp_rw [he]
    simp
  change (∑ y : Fin (m+1) → Bool,F ((if y=z then 1 else 0)+D y) (D y))+
    (∑ y : Fin (m+1) → Bool,
      F (if y=z then 1 else 0) (scatteredCount (altList (!b) m) ((!b)::List.ofFn y))) = _
  rw [hfirst,hsecond]
  ring

end D5.S1.Words.AlternatingTwoDeletionCounts
