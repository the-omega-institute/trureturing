/- GID: D5/S3/Entropy/BinaryRunSupersequenceCounts
   generality: I
   mirror-B: D5/B/S3/Entropy/BinaryRunSupersequenceCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary run counts and entropy comparisons for two deletions. -/

/-
admission_basis: escape-witness
Module escape_witness: jointWordSum_runs.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19498.
Frozen dependency identifiers refer to declarations at the pinned base:
F1: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_3; generated statement_id: sha256:eeb4ba1dc42c97107933499a696fff58308201b57cdaa0e2d6b01318dfe85988.
F2: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_1; generated statement_id: sha256:607874708dedb4dcfc543f03f8a4e0696951869b05e14db52394fc154de855d9.
F3: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c.
F4: D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.scatteredCount_eq_count_sublistsLen; statement_id: sha256:1ef019efa27fa73883b2c484815d0895ff1d4e12bfaa8beb7e837b90c59ca23f.
F5: D5/S1/Words/Complexity/VivionBinomialConverseFails.congr_simp; statement_id: sha256:08caa00f2d10a6074fe321122becd2a661a58047e87908bd0b2e539bd8628b72.
wordSum: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: wordSum_add.
count_cons_skip: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: jointWordSum_cons_other.
replicate_head_of_pos: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: runWord_head_other.
count_self: proof_shape: bind-only; frozen: F4,F3; escape_witness: none; consumer: count_prefix_bridge.
leadingWeight: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: count_prefix_bridge.
wordSum_succ: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: jointWordSum_cons_other.
wordSum_congr: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: jointWordSum_cons_other.
wordSum_add: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: wordSum_update.
wordSum_single: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: wordSum_update.
oneWordSum: proof_shape: bind-only (definition); frozen: F3; escape_witness: none; consumer: oneWordSum_replicate.
jointWordSum: proof_shape: bind-only (definition); frozen: F3; escape_witness: none; consumer: jointWordSum_runs.
runWord_head_other: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: count_prefix_bridge.
count_drop_opposite: proof_shape: bind-only; frozen: F4,F3,F1; escape_witness: none; consumer: count_prefix_drop_one.
wordSum_update: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: jointWordSum_cons_other.
wordSum_hit: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: jointWordSum_cons_other.
oneWordSum_nil: proof_shape: bind-only; frozen: F3; escape_witness: none; consumer: oneWordSum_runs.
count_prefix_drop_one: proof_shape: content; frozen: F3,F4,F1,F5; escape_witness: D5.S3.Entropy.BinaryRunSupersequenceCounts.count_prefix_drop_one; consumer: count_prefix_bridge.
oneWordSum_cons: proof_shape: bind-only; frozen: F4,F3,F1; escape_witness: none; consumer: oneWordSum_replicate.
jointWordSum_cons_other: proof_shape: bind-only; frozen: F4,F3,F1,F2; escape_witness: none; consumer: jointWordSum_runs.
jointWordSum_cons_same: proof_shape: bind-only; frozen: F4,F3,F1; escape_witness: none; consumer: jointWordSum_runs.
count_prefix_drop_two: proof_shape: content; frozen: F3,F4,F1,F5; escape_witness: D5.S3.Entropy.BinaryRunSupersequenceCounts.count_prefix_drop_two; consumer: jointWordSum_runs.
count_prefix_bridge: proof_shape: content; frozen: F3,F4,F1,F5; escape_witness: D5.S3.Entropy.BinaryRunSupersequenceCounts.count_prefix_bridge; consumer: jointWordSum_runs.
oneWordSum_replicate: proof_shape: content; frozen: F3,F5,F4,F1; escape_witness: D5.S3.Entropy.BinaryRunSupersequenceCounts.oneWordSum_replicate; consumer: oneWordSum_runs.
oneWordSum_runs: proof_shape: content; frozen: F3,F5,F4,F1; escape_witness: D5.S3.Entropy.BinaryRunSupersequenceCounts.oneWordSum_runs; consumer: jointWordSum_runs.
jointWordSum_runs: proof_shape: content; frozen: F3,F4,F1,F5,F2; escape_witness: jointWordSum_runs; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.twoWordPhi_run_step.
-/

import D5.S3.Entropy.AlternatingTwoDeletionCounts
import D5.S1.Words.TwoDeletionRunDecks
import D5.S1.Words.Complexity.VivionBinomialConverseFails

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace D5.S3.Entropy.BinaryRunSupersequenceCounts

open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)
open D5.S3.Entropy.AlternatingTwoDeletionCounts
open D5.S1.Words.TwoDeletionRunDecks

noncomputable def wordSum (n : ℕ) (F : List Bool → ℝ) : ℝ :=
  ∑ x : Fin n → Bool,F (List.ofFn x)

private lemma count_cons_skip (b : Bool) (w q : List Bool) (hw : w.head?≠some b) :
    scatteredCount w (b::q)=scatteredCount w q := by
  cases w with
  | nil => simp [scatteredCount]
  | cons a w =>
    have hn : a≠b := by simpa using hw
    rw [scatteredCount,if_neg hn,add_zero]

private lemma replicate_head_of_pos {α : Type*} (b : α) (n : ℕ) (hn : 0<n) :
    List.replicate n b=b::List.replicate (n-1) b := by
  cases n with
  | zero => omega
  | succ n => simp [List.replicate_succ]

private lemma count_self (w : List Bool) : scatteredCount w w=1 := by
  simpa using count_equal_length w w rfl

def leadingWeight : List ℕ → ℕ
  | [] => 0
  | r::rs => if r=1 then 1+leadingWeight rs else r

lemma wordSum_succ (n : ℕ) (b : Bool) (F : List Bool → ℝ) :
    wordSum (n+1) F=wordSum n (fun w => F (b::w))+wordSum n (fun w => F ((!b)::w)) := by
  unfold wordSum
  rw [sum_binary_real_succ _ b]
  simp only [List.ofFn_cons]

lemma wordSum_congr (n : ℕ) (F G : List Bool → ℝ)
    (h : ∀ x,x.length=n → F x=G x) : wordSum n F=wordSum n G := by
  apply Finset.sum_congr rfl
  intro x _
  exact h _ (List.length_ofFn)

lemma wordSum_add (n : ℕ) (F G : List Bool → ℝ) :
    wordSum n (fun x => F x+G x)=wordSum n F+wordSum n G := by
  exact Finset.sum_add_distrib

private lemma wordSum_single (w : List Bool) (c : ℝ) :
    wordSum w.length (fun x => if x=w then c else 0)=c := by
  classical
  let z : Fin w.length → Bool := fun i => w[i]
  have hz : List.ofFn z=w := by
    apply List.ext_getElem
    · simp
    · simp [z]
  have he : ∀ x : Fin w.length → Bool,List.ofFn x=w ↔ x=z := by
    intro x
    constructor
    · intro h
      exact List.ofFn_injective (h.trans hz.symm)
    · intro h
      subst x
      exact hz
  unfold wordSum
  simp_rw [he]
  simp

noncomputable def oneWordSum (w : List Bool) (G : ℕ → ℝ) : ℝ :=
  wordSum (w.length+1) (fun x => G (scatteredCount w x))

noncomputable def jointWordSum (w : List Bool) (F : ℕ → ℕ → ℝ) : ℝ :=
  wordSum (w.length+1) (fun x => F (scatteredCount w x) (scatteredCount w.tail x))

private lemma runWord_head_other (b : Bool) (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    (runWord (!b) rs).head?≠some b := by
  cases rs with
  | nil => simp [runWord]
  | cons r rs =>
    have hr := hp r (by simp)
    rw [runWord,replicate_head_of_pos (!b) r hr,List.cons_append,List.head?_cons]
    cases b <;> decide

private lemma count_drop_opposite (b : Bool) (w : List Bool) (h : w.head?≠some b) :
    scatteredCount w (b::w)=1 := by
  cases w with
  | nil => rfl
  | cons a w =>
    have hn : a≠b := by simpa using h
    rw [scatteredCount,if_neg hn,add_zero,count_self]

private lemma wordSum_update (w : List Bool) (D B : List Bool → ℕ) (F : ℕ → ℕ → ℝ) :
    wordSum w.length (fun x => F ((if x=w then 1 else 0)+D x) (B x))=
      wordSum w.length (fun x => F (D x) (B x))+
        F (1+D w) (B w)-F (D w) (B w) := by
  classical
  have hpoint : ∀ x : List Bool,
      F ((if x=w then 1 else 0)+D x) (B x)=
        F (D x) (B x)+(if x=w then F (1+D w) (B w)-F (D w) (B w) else 0) := by
    intro x
    by_cases hx : x=w
    · subst x; simp
    · simp [hx]
  simp_rw [hpoint]
  rw [wordSum_add,wordSum_single]
  ring

private lemma wordSum_hit (w : List Bool) (B : List Bool → ℕ) (F : ℕ → ℕ → ℝ)
    (hF : ∀ d,F 0 d=0) :
    wordSum w.length (fun x => F (if x=w then 1 else 0) (B x))=F 1 (B w) := by
  have hh : ∀ x,F (if x=w then 1 else 0) (B x)=if x=w then F 1 (B w) else 0 := by
    intro x
    by_cases hx : x=w
    · subst x; simp
    · simp [hx,hF]
  simp_rw [hh]
  exact wordSum_single w _

private lemma oneWordSum_nil (G : ℕ → ℝ) : oneWordSum [] G=2*G 1 := by
  unfold oneWordSum
  rw [List.length_nil,wordSum_succ 0 false]
  simp [wordSum,scatteredCount]
  ring

private lemma count_prefix_drop_one (b : Bool) (w : List Bool) (hw : w.head?≠some b)
    (r : ℕ) :
    scatteredCount (List.replicate r b++w) (List.replicate (r+1) b++w)=r+1 := by
  induction r with
  | zero => simpa using count_drop_opposite b w hw
  | succ r ih =>
    rw [List.replicate_succ,List.replicate_succ,List.cons_append,List.cons_append,
      scatteredCount,if_pos rfl]
    have hs : b::(List.replicate r b++w)=List.replicate (r+1) b++w := by
      simp only [List.replicate_succ,List.cons_append]
    rw [hs,count_self,ih]
    omega

private lemma oneWordSum_cons (b : Bool) (w : List Bool) (G : ℕ → ℝ) (hG : G 0=0) :
    oneWordSum (b::w) G=oneWordSum w G+
      G (1+scatteredCount w (b::w))-G (scatteredCount w (b::w))+G 1 := by
  unfold oneWordSum
  rw [List.length_cons,wordSum_succ (w.length+1) b]
  have hn : b≠!b := by exact Bool.not_eq_not.mpr rfl
  have he : wordSum (w.length+1) (fun q => G (scatteredCount (b::w) (b::q)))=
      wordSum (b::w).length (fun q => G ((if q=b::w then 1 else 0)+scatteredCount w q)) := by
    apply wordSum_congr
    intro q hq
    rw [scatteredCount,if_pos rfl,count_equal_length (b::w) q (by simp [hq])]
    simp only [eq_comm]
  rw [he,wordSum_update (b::w) (fun q => scatteredCount w q) (fun _ => 0) (fun a _ => G a)]
  have ho : wordSum (w.length+1) (fun q => G (scatteredCount (b::w) ((!b)::q)))=G 1 := by
    have hh : wordSum (w.length+1) (fun q => G (scatteredCount (b::w) ((!b)::q)))=
        wordSum (b::w).length (fun q => if q=b::w then G 1 else 0) := by
      apply wordSum_congr
      intro q hq
      rw [scatteredCount,if_neg hn,add_zero,count_equal_length (b::w) q (by simp [hq])]
      simp only [eq_comm]
      split_ifs <;> simp_all
    rw [hh,wordSum_single]
  rw [ho]
  rfl
open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)

private lemma jointWordSum_cons_other (b : Bool) (w : List Bool) (hw : w.head?≠some b)
    (F : ℕ → ℕ → ℝ) (hF : ∀ d,F 0 d=0) :
    jointWordSum (b::w) F=oneWordSum w (fun d => F d d)+F 2 1-F 1 1+
      F 1 (scatteredCount w ((!b)::b::w)) := by
  unfold jointWordSum
  rw [List.length_cons,wordSum_succ (w.length+1) b]
  have hn : b≠!b := by exact Bool.not_eq_not.mpr rfl
  have hs : wordSum (w.length+1) (fun q =>
      F (scatteredCount (b::w) (b::q)) (scatteredCount w (b::q)))=
      wordSum (b::w).length (fun q => F ((if q=b::w then 1 else 0)+scatteredCount w q) (scatteredCount w q)) := by
    apply wordSum_congr
    intro q hq
    rw [scatteredCount,if_pos rfl,count_cons_skip b w q hw,
      count_equal_length (b::w) q (by simp [hq])]
    simp only [eq_comm]
  have ho : wordSum (w.length+1) (fun q =>
      F (scatteredCount (b::w) ((!b)::q)) (scatteredCount w ((!b)::q)))=
      F 1 (scatteredCount w ((!b)::b::w)) := by
    have he : wordSum (w.length+1) (fun q =>
        F (scatteredCount (b::w) ((!b)::q)) (scatteredCount w ((!b)::q)))=
        wordSum (b::w).length (fun q => F (if q=b::w then 1 else 0) (scatteredCount w ((!b)::q))) := by
      apply wordSum_congr
      intro q hq
      rw [scatteredCount,if_neg hn,add_zero,count_equal_length (b::w) q (by simp [hq])]
      simp only [eq_comm]
    rw [he,wordSum_hit _ _ F hF]
  simp only [List.tail_cons]
  rw [hs,ho,wordSum_update,count_drop_opposite b w hw]
  change _+F (1+1) 1-F 1 1+_= _
  rfl

private lemma jointWordSum_cons_same (b : Bool) (u : List Bool)
    (F : ℕ → ℕ → ℝ) (hF : ∀ d,F 0 d=0) :
    jointWordSum (b::b::u) F=jointWordSum (b::u) (fun a d => F a (a+d))+
      F (1+scatteredCount (b::u) (b::b::u)) (scatteredCount (b::u) (b::b::b::u))-
      F (scatteredCount (b::u) (b::b::u)) (scatteredCount (b::u) (b::b::b::u))+
      F 1 (scatteredCount (b::u) (b::b::u)) := by
  unfold jointWordSum
  rw [List.length_cons,wordSum_succ ((b::u).length+1) b]
  have hn : b≠!b := by exact Bool.not_eq_not.mpr rfl
  have hs : wordSum ((b::u).length+1) (fun q =>
      F (scatteredCount (b::b::u) (b::q)) (scatteredCount (b::u) (b::q)))=
      wordSum (b::b::u).length (fun q =>
        F ((if q=b::b::u then 1 else 0)+scatteredCount (b::u) q)
          (scatteredCount (b::u) (b::q))) := by
    apply wordSum_congr
    intro q hq
    rw [scatteredCount,if_pos rfl,
      count_equal_length (b::b::u) q (by simp [hq])]
    simp only [eq_comm]
  have ho : wordSum ((b::u).length+1) (fun q =>
      F (scatteredCount (b::b::u) ((!b)::q)) (scatteredCount (b::u) ((!b)::q)))=
      F 1 (scatteredCount (b::u) (b::b::u)) := by
    have he : wordSum ((b::u).length+1) (fun q =>
        F (scatteredCount (b::b::u) ((!b)::q)) (scatteredCount (b::u) ((!b)::q)))=
        wordSum (b::b::u).length (fun q => F (if q=b::b::u then 1 else 0) (scatteredCount (b::u) q)) := by
      apply wordSum_congr
      intro q hq
      rw [scatteredCount,if_neg hn,add_zero,scatteredCount,if_neg hn,add_zero,
        count_equal_length (b::b::u) q (by simp [hq])]
      simp only [eq_comm]
    rw [he,wordSum_hit _ _ F hF]
  simp only [List.tail_cons]
  rw [hs,ho,wordSum_update]
  have hbase : wordSum (b::b::u).length (fun q =>
      F (scatteredCount (b::u) q) (scatteredCount (b::u) (b::q)))=
      wordSum ((b::u).length+1) (fun q => F (scatteredCount (b::u) q)
        (scatteredCount (b::u) q+scatteredCount u q)) := by
    apply wordSum_congr
    intro q _
    rw [scatteredCount,if_pos rfl]
  rw [hbase]
open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)

private lemma count_prefix_drop_two (b : Bool) (w : List Bool) (hw : w.head?≠some b)
    (r : ℕ) :
    scatteredCount (List.replicate r b++w) (List.replicate (r+2) b++w)=(r+2).choose 2 := by
  induction r with
  | zero =>
    cases w with
    | nil => rfl
    | cons a w =>
      have hn : a≠b := by simpa using hw
      simp only [List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append]
      rw [scatteredCount,if_neg hn,add_zero,scatteredCount,if_neg hn,add_zero,count_self]
      rfl
  | succ r ih =>
    rw [List.replicate_succ,List.replicate_succ,List.cons_append,List.cons_append,
      scatteredCount,if_pos rfl]
    have hs : b::(List.replicate r b++w)=List.replicate (r+1) b++w := by
      simp only [List.replicate_succ,List.cons_append]
    rw [hs,count_prefix_drop_one b w hw (r+1),ih]
    have hc := Nat.choose_succ_succ (r+2) 1
    norm_num only [Nat.choose_one_right,Nat.succ_eq_add_one] at hc
    rw [show r+1+2=r+2+1 by omega]
    omega


private lemma count_prefix_bridge (b : Bool) (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    scatteredCount (runWord b rs) (b::(!b)::runWord b rs)=1+leadingWeight rs := by
  induction rs generalizing b with
  | nil => rfl
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht : ∀ a∈rs,0<a := fun a ha => hp a (by simp [ha])
    have ho := runWord_head_other b rs ht
    cases r with
    | zero => omega
    | succ r =>
      have hn : b≠!b := by exact Bool.not_eq_not.mpr rfl
      rw [runWord,List.replicate_succ,List.cons_append,scatteredCount,
        if_pos rfl,scatteredCount,if_neg hn,add_zero,count_self]
      cases r with
      | zero =>
        simpa only [List.replicate_zero,List.nil_append,runWord,Bool.not_not,
          leadingWeight,ite_true,one_add_one_eq_two] using congrArg (fun n : ℕ => 1+n) (ih (!b) ht)
      | succ r =>
        have hn' : b≠!b := by exact Bool.not_eq_not.mpr rfl
        simp only [List.replicate_succ,List.cons_append]
        rw [scatteredCount,if_neg hn',add_zero]
        have hd := count_prefix_drop_one b (runWord (!b) rs) ho (r+1)
        simp only [List.replicate_succ,List.cons_append] at hd
        rw [hd]
        simp [leadingWeight]
open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)

private lemma oneWordSum_replicate (b : Bool) (w : List Bool) (hw : w.head?≠some b)
    (r : ℕ) (G : ℕ → ℝ) (hG : G 0=0) :
    oneWordSum (List.replicate (r+1) b++w) G=
      oneWordSum w G+G (r+2)+(r:ℝ)*G 1 := by
  induction r with
  | zero =>
    simp only [zero_add,List.replicate_one,List.singleton_append,Nat.cast_zero,zero_mul,add_zero]
    rw [oneWordSum_cons b w G hG,count_drop_opposite b w hw]
    norm_num
  | succ r ih =>
    rw [List.replicate_succ,List.cons_append,oneWordSum_cons b _ G hG]
    have hc := count_prefix_drop_one b w hw (r+1)
    have hc' : scatteredCount (List.replicate (r+1) b++w)
        (b::(List.replicate (r+1) b++w))=r+2 := by
      simpa only [List.replicate_succ,List.cons_append,Nat.add_assoc] using hc
    rw [hc',ih]
    push_cast
    rw [show 1+(r+1+1)=r+3 by omega]
    ring

lemma oneWordSum_runs (b : Bool) (rs : List ℕ) (hp : ∀ r∈rs,0<r)
    (G : ℕ → ℝ) (hG : G 0=0) :
    oneWordSum (runWord b rs) G=(rs.map (fun r => G (r+1))).sum+
      ((rs.sum:ℝ)+2-rs.length)*G 1 := by
  induction rs generalizing b with
  | nil => simpa [runWord] using oneWordSum_nil G
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht : ∀ a∈rs,0<a := fun a ha => hp a (by simp [ha])
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
    rw [runWord,oneWordSum_replicate b _ (runWord_head_other b rs ht) r G hG,ih (!b) ht]
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_succ,Nat.cast_add,Nat.cast_one]
    rw [show r+1+1=r+2 by omega]
    ring
open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)

lemma jointWordSum_runs (b : Bool) (rs : List ℕ) (hp : ∀ r∈rs,0<r)
    (r : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ d,F 0 d=0) :
    jointWordSum (runWord b ((r+1)::rs)) F=
      F (r+2) ((r+2).choose 2)+
      (rs.map (fun t => F (t+1) ((r+1)*(t+1)))).sum+
      ((r:ℝ)+1+rs.sum-rs.length)*F 1 (r+1)+
      F 1 (r+1+leadingWeight rs) := by
  induction r generalizing F with
  | zero =>
    simp only [zero_add,runWord,List.replicate_one,List.singleton_append]
    rw [jointWordSum_cons_other b _ (runWord_head_other b rs hp) F hF]
    rw [oneWordSum_runs (!b) rs hp (fun d => F d d) (hF 0)]
    have hc := count_prefix_bridge (!b) rs hp
    simp only [Bool.not_not] at hc
    rw [hc]
    norm_num only [Nat.cast_zero,Nat.choose_self,one_mul]
    ring
  | succ r ih =>
    have ho := runWord_head_other b rs hp
    have hc1 := count_prefix_drop_one b (runWord (!b) rs) ho (r+1)
    have hc2 := count_prefix_drop_two b (runWord (!b) rs) ho (r+1)
    have hn : runWord b ((r+1+1)::rs)=b::runWord b ((r+1)::rs) := by
      simp [runWord,List.replicate_succ]
    rw [hn]
    have hn' : runWord b ((r+1)::rs)=b::(List.replicate r b++runWord (!b) rs) := by
      simp [runWord,List.replicate_succ]
    rw [hn',jointWordSum_cons_same b _ F hF]
    have h1 : scatteredCount
        (b::(List.replicate r b++runWord (!b) rs))
        (b::b::(List.replicate r b++runWord (!b) rs))=r+2 := by
      simpa only [List.replicate_succ,List.cons_append] using hc1
    have h2 : scatteredCount
        (b::(List.replicate r b++runWord (!b) rs))
        (b::b::b::(List.replicate r b++runWord (!b) rs))=(r+3).choose 2 := by
      simpa only [List.replicate_succ,List.cons_append] using hc2
    rw [h1,h2,←hn',ih (fun a d => F a (a+d)) (fun d => by simpa only [zero_add] using hF d)]
    have hchoose : (r+2)+(r+2).choose 2=(r+3).choose 2 := by
      have hc := Nat.choose_succ_succ (r+2) 1
      simpa using hc.symm
    rw [hchoose]
    have hmap : (rs.map (fun t => F (t+1) ((t+1)+(r+1)*(t+1)))).sum=
        (rs.map (fun t => F (t+1) ((r+2)*(t+1)))).sum := by
      congr 1
      apply List.map_congr_left
      intro t _
      congr 1
      ring
    rw [hmap]
    simp only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one]
    simp only [show 1+(r+2)=r+3 by omega,
      show 1+(r+1)=r+2 by omega,
      show 1+(r+1+leadingWeight rs)=r+2+leadingWeight rs by omega]
    ring

end D5.S3.Entropy.BinaryRunSupersequenceCounts
