/- GID: D5/S1/Words/AssociatedMersenne/SingleRunDegrees
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/SingleRunDegrees
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact degree of one-run circular words, including the shared gap endpoints. -/

/-
admission_basis: escape-witness
Module content theorem: singleRun_degree
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  none (the other D5 imports belong to this delivery).
Declarations:
  run_interior_delete_illegal: proof_shape: content; escape_witness: SingleRunDegrees.run_interior_delete_illegal;
  cycSub_val_one: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.inserted_original_start
  singleRun_start: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.delete_interior_not_admissible
  singleRun_admissible_iff: proof_shape: content; escape_witness: RunTupleBijection.raw_encoding_admissible_iff;
  delete_last_eq: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.delete_last_admissible
  singleRun_zero: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.delete_first_admissible
  delete_last_admissible: proof_shape: content; escape_witness: SingleRunDegrees.delete_last_admissible;
  delete_interior_not_admissible: proof_shape: content; escape_witness: SingleRunDegrees.delete_interior_not_admissible;
  insert_right_eq: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.insert_right_admissible_iff
  insert_right_admissible_iff: proof_shape: content; escape_witness: SingleRunDegrees.insert_right_admissible_iff;
  delete_first_rotate: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.delete_first_admissible
  delete_first_admissible: proof_shape: content; escape_witness: SingleRunDegrees.delete_first_admissible;
  singleRun_delete_iff: proof_shape: content; escape_witness: SingleRunDegrees.singleRun_delete_iff;
  insert_left_rotate: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.insert_left_admissible_iff
  insert_left_admissible_iff: proof_shape: content; escape_witness: SingleRunDegrees.insert_left_admissible_iff;
  inserted_true_iff: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.insert_interior_admissible_iff
  inserted_false_iff: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.insert_interior_admissible_iff
  inserted_original_start: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.insert_interior_admissible_iff
  inserted_singleton_start: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.insert_interior_admissible_iff
  inserted_start_pos_iff: proof_shape: content; escape_witness: SingleRunDegrees.inserted_start_pos_iff;
  insert_interior_admissible_iff: proof_shape: content; escape_witness: SingleRunDegrees.insert_interior_admissible_iff;
  singleRun_flip_iff: proof_shape: content; escape_witness: SingleRunDegrees.singleRun_flip_iff;
  singleRun_delete_count: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.singleRun_degree
  singleRun_zero_flip_pred: proof_shape: content; escape_witness: SingleRunDegrees.delete_first_admissible;
  zeroInsertionIndex_val: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.singleRun_insert_count
  zeroInsertionIndex_inj: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.singleRun_insert_count
  singleRun_insert_count: proof_shape: content; escape_witness: SingleRunDegrees.singleRun_insert_count;
  singleRun_degree: proof_shape: content; escape_witness: SingleRunDegrees.singleRun_degree;
  rotate_single_raw: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.degree_raw_singleton
  degree_raw_singleton: proof_shape: content; escape_witness: SingleRunDegrees.degree_raw_singleton;
-/

import D5.S1.Words.AssociatedMersenne.RunTupleBijection

open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection

namespace D5.S1.Words.AssociatedMersenne.SingleRunDegrees

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

theorem run_interior_delete_illegal {n : Nat} {w : Fin n → Bool} {a : Fin n}
    {r p : Nat} (hs : IsOneRunStart w a r) (hp : 0 < p) (hp' : p+1 < r) :
    ¬ Admissible (CircularWords.flip w (cycAdd a p)) := by
  have hrn : r < n := by
    by_contra h
    exact start_large_false w a r (by omega) hs
  have hpn : p < n := by omega
  have hbit : w (cycAdd a p) = true := hs.2.1 p (by omega)
  have hnew : IsOneRunStart (CircularWords.flip w (cycAdd a p)) a p := by
    refine ⟨?_, ?_, ?_⟩
    · have hne : cycSub a 1 ≠ cycAdd a p := by
        rw [← cycAdd_sub_one]
        intro h
        have := (cycAdd_inj a (by omega) hpn).mp h
        omega
      rw [CircularWords.flip, Function.update_of_ne hne]
      exact hs.1
    · intro j hj
      have hne : cycAdd a j ≠ cycAdd a p := by
        intro h
        have := (cycAdd_inj a (by omega) hpn).mp h
        omega
      rw [CircularWords.flip, Function.update_of_ne hne]
      exact hs.2.1 j (by omega)
    · simp [CircularWords.flip, hbit]
  intro ha
  have hz := ha.2 a p hnew 1 hp
  rw [cycAdd_assoc] at hz
  have hne : cycAdd a (p+1) ≠ cycAdd a p := by
    intro h
    have := (cycAdd_inj a (by omega) hpn).mp h
    omega
  rw [CircularWords.flip, Function.update_of_ne hne] at hz
  have ht := hs.2.1 (p+1) hp'
  exact Bool.noConfusion (hz.symm.trans ht)

def singleRun (n r : Nat) : Fin n → Bool := fun j => decide (j.val < r)

private lemma cycSub_val_one {n : Nat} (i : Fin n) :
    (cycSub i 1).val = if i.val = 0 then n - 1 else i.val - 1 := by
  change (i.val + n - 1) % n = _
  have hn := Nat.zero_lt_of_lt i.isLt
  split_ifs with hi
  · rw [hi, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · have h : i.val + n - 1 = (i.val - 1) + n := by omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private lemma singleRun_start {n r : Nat} (hr : 0 < r) (hrn : r < n) :
    IsOneRunStart (singleRun n r) ⟨0, by omega⟩ r := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [singleRun, decide_eq_false_iff_not, cycSub_val_one]
    simp
    omega
  · intro j hj
    have hjn : j < n := by omega
    simp [singleRun, cycAdd, Nat.mod_eq_of_lt hjn, hj]
  · simp [singleRun, cycAdd, Nat.mod_eq_of_lt hrn]

private theorem singleRun_admissible_iff {n r : Nat} (hr : 0 < r) (hrn : r < n) :
    Admissible (singleRun n r) ↔ 2 * r < n := by
  have he : linearize (singleRun n r) ⟨0, by omega⟩ = rawWord [(r,n-r)] := by
    apply List.ext_getElem
    · simp [linearize, rawWord]
      omega
    · intro k hk hk'
      have hkn : k < n := by simpa [linearize] using hk
      by_cases hkr : k < r
      · simp [linearize, singleRun, cycAdd_val, rawWord,
          Nat.mod_eq_of_lt hkn, hkr]
      · simp [linearize, singleRun, cycAdd_val, rawWord, List.getElem_append,
          Nat.mod_eq_of_lt hkn, hkr]
  rw [raw_encoding_admissible_iff (singleRun n r) ⟨0, by omega⟩ [(r,n-r)]
    (by simp) (by simp; omega) he]
  simp only [List.mem_singleton, forall_eq]
  omega

private lemma delete_last_eq {n r : Nat} (hr : 0 < r) (hrn : r < n) :
    CircularWords.flip (singleRun n r) ⟨r-1, by omega⟩ = singleRun n (r-1) := by
  funext j
  by_cases h : j = ⟨r-1, by omega⟩
  · subst j
    simp [CircularWords.flip, singleRun, show r-1 < r by omega]
  · have hv : j.val ≠ r-1 := by intro he; exact h (Fin.ext he)
    rw [CircularWords.flip, Function.update_of_ne h]
    change decide (j.val < r) = decide (j.val < r-1)
    have he : (j.val < r) ↔ (j.val < r-1) := by omega
    simp only [he]

private lemma singleRun_zero (n : Nat) : singleRun n 0 = fun _ => false := by
  funext j; simp [singleRun]

private lemma delete_last_admissible {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) :
    Admissible (CircularWords.flip (singleRun n r) ⟨r-1, by omega⟩) := by
  rw [delete_last_eq hr (by omega)]
  by_cases hz : r-1 = 0
  · rw [hz, singleRun_zero]; exact zero_admissible n
  · exact (singleRun_admissible_iff (by omega) (by omega)).mpr (by omega)

private theorem delete_interior_not_admissible {n r : Nat} (hrn : r < n) (p : Fin n)
    (hp : 0 < p.val) (hp' : p.val + 1 < r) :
    ¬ Admissible (CircularWords.flip (singleRun n r) p) := by
  let z : Fin n := ⟨0, by omega⟩
  have hs := singleRun_start (by omega : 0 < r) hrn
  have he : cycAdd z p.val = p := by
    apply Fin.ext; simp [z, cycAdd_val, Nat.mod_eq_of_lt p.isLt]
  rw [← he]
  exact run_interior_delete_illegal hs hp hp'

private lemma insert_right_eq {n r : Nat} (hrn : r < n) :
    CircularWords.flip (singleRun n r) ⟨r, hrn⟩ = singleRun n (r+1) := by
  funext j
  by_cases h : j = ⟨r, hrn⟩
  · subst j; simp [singleRun, CircularWords.flip]
  · have hv : j.val ≠ r := by intro he; exact h (Fin.ext he)
    rw [CircularWords.flip, Function.update_of_ne h]
    change decide (j.val < r) = decide (j.val < r+1)
    have he : (j.val < r) ↔ (j.val < r+1) := by omega
    simp only [he]

private lemma insert_right_admissible_iff {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) :
    Admissible (CircularWords.flip (singleRun n r) ⟨r, by omega⟩) ↔ 2*(r+1) < n := by
  rw [insert_right_eq]
  have hrn : r+1 < n := by omega
  exact singleRun_admissible_iff (by omega) hrn

private lemma delete_first_rotate {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) :
    rotateWord (CircularWords.flip (singleRun n r) ⟨0, by omega⟩) ⟨1, by omega⟩ =
      singleRun n (r-1) := by
  funext j
  by_cases hj : j.val = n-1
  · have hval : (cycAdd (⟨1, by omega⟩ : Fin n) j.val).val = 0 := by
      rw [cycAdd_val, hj]
      have he : 1+(n-1) = n := by omega
      simp [he]
    have he : cycAdd (⟨1, by omega⟩ : Fin n) j.val = ⟨0, by omega⟩ := Fin.ext hval
    unfold rotateWord
    rw [he]
    simp [CircularWords.flip, singleRun, hj, show ¬n-1 < r-1 by omega, hr]
  · have hlt : 1+j.val < n := by have := j.isLt; omega
    have hval : (cycAdd (⟨1, by omega⟩ : Fin n) j.val).val = 1+j.val := by
      simp [cycAdd_val, Nat.mod_eq_of_lt hlt]
    have hne : cycAdd (⟨1, by omega⟩ : Fin n) j.val ≠ ⟨0, by omega⟩ := by
      intro he; have := congrArg Fin.val he; simpa [hval] using this
    unfold rotateWord
    rw [CircularWords.flip, Function.update_of_ne hne]
    have he : 1+j.val < r ↔ j.val < r-1 := by omega
    simp [singleRun, hval, he]

private lemma delete_first_admissible {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) :
    Admissible (CircularWords.flip (singleRun n r) ⟨0, by omega⟩) := by
  rw [← rotateWord_admissible_iff _ (⟨1, by omega⟩ : Fin n), delete_first_rotate hr hbig]
  by_cases hz : r-1 = 0
  · rw [hz, singleRun_zero]; exact zero_admissible n
  · exact (singleRun_admissible_iff (by omega) (by omega)).mpr (by omega)

private theorem singleRun_delete_iff {n r : Nat} (hr : 0 < r) (hbig : 2*r < n)
    (q : Fin n) (hq : q.val < r) :
    Admissible (CircularWords.flip (singleRun n r) q) ↔ q.val = 0 ∨ q.val + 1 = r := by
  constructor
  · intro ha
    by_contra h
    have hqpos : 0 < q.val := by omega
    have hqint : q.val+1 < r := by omega
    exact delete_interior_not_admissible (by omega) q hqpos hqint ha
  · rintro (hz | he)
    · have hq0 : q = ⟨0, by omega⟩ := Fin.ext hz
      rw [hq0]; exact delete_first_admissible hr hbig
    · have hv : q.val = r-1 := by omega
      have hql : q = ⟨r-1, by omega⟩ := Fin.ext hv
      rw [hql]; exact delete_last_admissible hr hbig

private lemma insert_left_rotate {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) :
    rotateWord (CircularWords.flip (singleRun n r) ⟨n-1, by omega⟩) ⟨n-1, by omega⟩ =
      singleRun n (r+1) := by
  funext j
  by_cases hj : j.val = 0
  · have hcyc : cycAdd (⟨n-1, by omega⟩ : Fin n) j.val = ⟨n-1, by omega⟩ := by
      rw [hj, cycAdd_zero]
    unfold rotateWord
    rw [hcyc]
    simp [CircularWords.flip, singleRun, show ¬n-1 < r by omega, hj]
  · have hjpos : 0 < j.val := by omega
    have hv : (cycAdd (⟨n-1, by omega⟩ : Fin n) j.val).val = j.val-1 := by
      rw [cycAdd_val]
      change (n-1+j.val) % n = j.val-1
      have he : n-1+j.val = (j.val-1)+n := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    have hne : cycAdd (⟨n-1, by omega⟩ : Fin n) j.val ≠ ⟨n-1, by omega⟩ := by
      intro he
      have hv' : (cycAdd (⟨n-1, by omega⟩ : Fin n) j.val).val = n-1 := congrArg Fin.val he
      rw [hv] at hv'
      have := j.isLt
      omega
    unfold rotateWord
    rw [CircularWords.flip, Function.update_of_ne hne]
    have he : j.val-1 < r ↔ j.val < r+1 := by omega
    simp [singleRun, hv, he]

private theorem insert_left_admissible_iff {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) :
    Admissible (CircularWords.flip (singleRun n r) ⟨n-1, by omega⟩) ↔ 2*(r+1) < n := by
  rw [← rotateWord_admissible_iff _ (⟨n-1, by omega⟩ : Fin n), insert_left_rotate hr hbig]
  exact singleRun_admissible_iff (by omega) (by omega)

private lemma inserted_true_iff {n r : Nat} (q a : Fin n) (hq : r ≤ q.val) :
    CircularWords.flip (singleRun n r) q a = true ↔ a = q ∨ a.val < r := by
  simp [CircularWords.flip, Function.update_apply, singleRun, show ¬q.val < r by omega]

private lemma inserted_false_iff {n r : Nat} (q a : Fin n) (hq : r ≤ q.val) :
    CircularWords.flip (singleRun n r) q a = false ↔ a ≠ q ∧ r ≤ a.val := by
  simp [CircularWords.flip, Function.update_apply, singleRun, show ¬q.val < r by omega]

private lemma inserted_original_start {n r : Nat} (hr : 0 < r) (hrn : r < n)
    (q : Fin n) (hq : r < q.val) (hqn : q.val+1 < n) :
    IsOneRunStart (CircularWords.flip (singleRun n r) q) ⟨0, by omega⟩ r := by
  let z : Fin n := ⟨0, by omega⟩
  have hbase := singleRun_start hr hrn
  refine ⟨?_, ?_, ?_⟩
  · have hval : (cycSub z 1).val = n-1 := by simp [z, cycSub_val_one]
    have hne : cycSub z 1 ≠ q := by intro he; have := congrArg Fin.val he; omega
    rw [CircularWords.flip, Function.update_of_ne hne]
    exact hbase.1
  · intro j hj
    have hv : (cycAdd z j).val = j := by
      simp [z, cycAdd_val, Nat.mod_eq_of_lt (show j < n by omega)]
    have hne : cycAdd z j ≠ q := by intro he; have := congrArg Fin.val he; omega
    rw [CircularWords.flip, Function.update_of_ne hne]
    exact hbase.2.1 j hj
  · have hv : (cycAdd z r).val = r := by simp [z, cycAdd_val, Nat.mod_eq_of_lt hrn]
    have hne : cycAdd z r ≠ q := by intro he; have := congrArg Fin.val he; omega
    rw [CircularWords.flip, Function.update_of_ne hne]
    exact hbase.2.2

private lemma inserted_singleton_start {n r : Nat} (hr : 0 < r) (q : Fin n)
    (hq : r < q.val) (hqn : q.val+1 < n) :
    IsOneRunStart (CircularWords.flip (singleRun n r) q) q 1 := by
  refine ⟨?_, ?_, ?_⟩
  · apply (inserted_false_iff q _ (by omega)).mpr
    have hv : (cycSub q 1).val = q.val-1 := by
      rw [cycSub_val_one, if_neg (by omega)]
    exact ⟨by intro he; have := congrArg Fin.val he; omega, by omega⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [cycAdd_zero]
    exact (inserted_true_iff q q (by omega)).mpr (Or.inl rfl)
  · apply (inserted_false_iff q _ (by omega)).mpr
    have hv : (cycAdd q 1).val = q.val+1 := by rw [cycAdd_val, Nat.mod_eq_of_lt hqn]
    exact ⟨by intro he; have := congrArg Fin.val he; omega, by omega⟩

private theorem inserted_start_pos_iff {n r t : Nat} (hr : 0 < r) (hrn : r < n)
    (q a : Fin n) (hq : r < q.val) (hqn : q.val+1 < n) (ht : 0 < t) :
    IsOneRunStart (CircularWords.flip (singleRun n r) q) a t ↔
      (a.val = 0 ∧ t = r) ∨ (a = q ∧ t = 1) := by
  constructor
  · intro hs
    have hat := hs.2.1 0 ht
    rw [cycAdd_zero] at hat
    rcases (inserted_true_iff q a (by omega)).mp hat with he | ha
    · right
      subst a
      exact ⟨rfl, one_run_length_unique hs (inserted_singleton_start hr q hq hqn)⟩
    · left
      have hp := (inserted_false_iff q (cycSub a 1) (by omega)).mp hs.1
      have haz : a.val = 0 := by
        by_contra haz
        rw [cycSub_val_one, if_neg haz] at hp
        omega
      refine ⟨haz, ?_⟩
      have hae : a = ⟨0, by omega⟩ := Fin.ext haz
      rw [hae] at hs
      exact one_run_length_unique hs (inserted_original_start hr hrn q hq hqn)
  · rintro (h | h)
    · obtain ⟨haz, htr⟩ := h
      have hae : a = ⟨0, by omega⟩ := Fin.ext haz
      rw [hae, htr]
      exact inserted_original_start hr hrn q hq hqn
    · obtain ⟨hae, htr⟩ := h
      rw [hae, htr]
      exact inserted_singleton_start hr q hq hqn

private theorem insert_interior_admissible_iff {n r : Nat} (hr : 0 < r)
    (q : Fin n) (hq : r < q.val) (hqn : q.val+1 < n) :
    Admissible (CircularWords.flip (singleRun n r) q) ↔ 2*r < q.val ∧ q.val+2 < n := by
  have hrn : r < n := by have := q.isLt; omega
  let z : Fin n := ⟨0, by omega⟩
  constructor
  · intro ha
    constructor
    · by_contra h
      have hj : q.val-r ≤ r := by omega
      have hs := inserted_original_start hr hrn q hq hqn
      have hb := ha.2 z r hs (q.val-r) hj
      rw [cycAdd_assoc] at hb
      have hsum : r+(q.val-r) = q.val := by omega
      have he : cycAdd z q.val = q := by
        apply Fin.ext; simp [z, cycAdd_val, Nat.mod_eq_of_lt q.isLt]
      rw [hsum, he] at hb
      have ht := (inserted_true_iff (r := r) q q (by omega)).mpr (Or.inl rfl)
      exact Bool.noConfusion (hb.symm.trans ht)
    · by_contra h
      have hsum : q.val+2 = n := by omega
      have hs := inserted_singleton_start hr q hq hqn
      have hb := ha.2 q 1 hs 1 (by omega)
      rw [cycAdd_assoc] at hb
      have hv : (cycAdd q 2).val = 0 := by rw [cycAdd_val, hsum]; simp
      have hp := ((inserted_false_iff q (cycAdd q 2) (by omega)).mp hb).2
      rw [hv] at hp
      omega
  · rintro ⟨hbefore, hafter⟩
    refine ⟨Or.inr ⟨⟨r, hrn⟩, ?_⟩, ?_⟩
    · apply (inserted_false_iff q _ (by omega)).mpr
      exact ⟨by intro he; have he' : r = q.val := congrArg Fin.val he; omega, by simp⟩
    · intro a t hs j hj
      by_cases ht0 : t = 0
      · subst t
        have hj0 : j = 0 := by omega
        subst j
        simpa [cycAdd_zero] using hs.2.2
      · rcases (inserted_start_pos_iff hr hrn q a hq hqn (by omega)).mp hs with
            ⟨ha0, htr⟩ | ⟨haq, ht1⟩
        · have hae : a = z := Fin.ext ha0
          rw [hae, htr, cycAdd_assoc]
          apply (inserted_false_iff q _ (by omega)).mpr
          have hjr : j ≤ r := by simpa [htr] using hj
          have hv : (cycAdd z (r+j)).val = r+j := by
            simp [z, cycAdd_val, Nat.mod_eq_of_lt (show r+j < n by omega)]
          exact ⟨by intro he; have := congrArg Fin.val he; omega, by omega⟩
        · rw [haq, ht1, cycAdd_assoc]
          apply (inserted_false_iff q _ (by omega)).mpr
          have hj1 : j ≤ 1 := by simpa [ht1] using hj
          have hv : (cycAdd q (1+j)).val = q.val+1+j := by
            rw [cycAdd_val, Nat.mod_eq_of_lt (by omega)]
            omega
          exact ⟨by intro he; have := congrArg Fin.val he; omega, by omega⟩

private theorem singleRun_flip_iff {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) (q : Fin n) :
    Admissible (CircularWords.flip (singleRun n r) q) ↔
      (q.val < r ∧ (q.val = 0 ∨ q.val+1 = r)) ∨
      (r ≤ q.val ∧ ((q.val = r ∨ q.val+1 = n) ∧ 2*(r+1) < n ∨
        (2*r < q.val ∧ q.val+2 < n))) := by
  by_cases hq : q.val < r
  · rw [singleRun_delete_iff hr hbig q hq]
    simp [hq, show ¬r ≤ q.val by omega]
  · have hqr : r ≤ q.val := by omega
    by_cases he : q.val = r
    · have hqe : q = ⟨r, by omega⟩ := Fin.ext he
      rw [hqe, insert_right_admissible_iff hr hbig]
      simp [show ¬r < r by omega, show ¬2*r < r by omega]
    · by_cases hl : q.val+1 = n
      · have hv : q.val = n-1 := by omega
        have hqe : q = ⟨n-1, by omega⟩ := Fin.ext hv
        rw [hqe, insert_left_admissible_iff hr hbig]
        have hn1 : n-1+1 = n := by omega
        simp [show ¬n-1 < r by omega, show r ≤ n-1 by omega, hn1,
          show ¬n-1+2 < n by omega]
      · have hqn : q.val+1 < n := by have := q.isLt; omega
        rw [insert_interior_admissible_iff hr q (by omega) hqn]
        simp [hq, hqr, he, hl]

private lemma singleRun_delete_count {n r : Nat} (hr : 0 < r) (hbig : 2*r < n) :
    (Finset.univ.filter (fun q : Fin n => q.val = 0 ∨ q.val+1 = r)).card = min r 2 := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨r-1, by omega⟩
  have he : Finset.univ.filter (fun q : Fin n => q.val = 0 ∨ q.val+1 = r) = {a,b} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    dsimp [a,b]
    omega
  rw [he]
  by_cases hr1 : r = 1
  · subst r; simp [a,b]
  · have hab : a ≠ b := by
      intro h
      have hv : 0 = r-1 := congrArg Fin.val h
      omega
    rw [Finset.card_pair hab, Nat.min_eq_right (by omega)]

private lemma singleRun_zero_flip_pred (r s : Nat) (hr : 0 < r)
    (q : Fin (2*r+1+s)) :
    (Admissible (CircularWords.flip (singleRun (2*r+1+s) r) q) ∧ r ≤ q.val) ↔
      2 ≤ s ∧ (q.val = r ∨ q.val = 2*r+s ∨
        (2*r < q.val ∧ q.val+2 < 2*r+1+s)) := by
  rw [singleRun_flip_iff hr (by omega) q]
  have := q.isLt
  omega

private def zeroInsertionIndex (r s : Nat) (hr : 0 < r) (hs : 2 ≤ s)
    (j : Fin s) : Fin (2*r+1+s) :=
  if j.val = 0 then ⟨r, by omega⟩
  else if j.val = 1 then ⟨2*r+s, by omega⟩
  else ⟨2*r+j.val-1, by have := j.isLt; omega⟩

private lemma zeroInsertionIndex_val (r s : Nat) (hr : 0 < r) (hs : 2 ≤ s) (j : Fin s) :
    (zeroInsertionIndex r s hr hs j).val =
      if j.val=0 then r else if j.val=1 then 2*r+s else 2*r+j.val-1 := by
  unfold zeroInsertionIndex
  split_ifs <;> rfl

private lemma zeroInsertionIndex_inj (r s : Nat) (hr : 0 < r) (hs : 2 ≤ s) :
    Function.Injective (zeroInsertionIndex r s hr hs) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [zeroInsertionIndex_val, zeroInsertionIndex_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega

private lemma singleRun_insert_count (r s : Nat) (hr : 0 < r) :
    (Finset.univ.filter (fun q : Fin (2*r+1+s) =>
      Admissible (CircularWords.flip (singleRun (2*r+1+s) r) q) ∧ r ≤ q.val)).card =
      if 2 ≤ s then s else 0 := by
  classical
  simp_rw [singleRun_zero_flip_pred r s hr]
  by_cases hs : 2 ≤ s
  · rw [if_pos hs]
    symm
    calc
      s = (Finset.univ : Finset (Fin s)).card := (Finset.card_fin s).symm
      _ = _ := by
        apply Finset.card_bij (fun j _ => zeroInsertionIndex r s hr hs j)
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hs, ?_⟩
          have hjlt := j.isLt
          rw [zeroInsertionIndex_val]
          split_ifs <;> omega
        · intro i hi j hj he
          exact zeroInsertionIndex_inj r s hr hs he
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rcases hq.2 with he | he | ⟨hb, ht⟩
          · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
            apply Fin.ext
            simp [zeroInsertionIndex, he]
          · refine ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
            apply Fin.ext
            simp [zeroInsertionIndex, he]
          · refine ⟨⟨q.val-2*r+1, by omega⟩, Finset.mem_univ _, ?_⟩
            apply Fin.ext
            rw [zeroInsertionIndex_val]
            have hk0 : q.val-2*r+1 ≠ 0 := by omega
            have hk1 : q.val-2*r+1 ≠ 1 := by omega
            rw [if_neg hk0, if_neg hk1]
            change 2*r+(q.val-2*r+1)-1 = q.val
            omega
  · simp [hs]

theorem singleRun_degree (r s : Nat) (hr : 0 < r) :
    degree (singleRun (2*r+1+s) r) = min r 2 + if 2 ≤ s then s else 0 := by
  classical
  let n := 2*r+1+s
  let W := Finset.univ.filter (fun q : Fin n => Admissible (CircularWords.flip (singleRun n r) q))
  have hsplit := Finset.card_filter_add_card_filter_not (s := W) (fun q => q.val < r)
  have hone : W.filter (fun q => q.val < r) =
      Finset.univ.filter (fun q : Fin n => q.val = 0 ∨ q.val+1 = r) := by
    ext q
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [singleRun_flip_iff hr (by dsimp [n]; omega) q]
    have := q.isLt
    dsimp [n] at *
    omega
  have hzero : W.filter (fun q => ¬q.val < r) =
      Finset.univ.filter (fun q : Fin n =>
        Admissible (CircularWords.flip (singleRun n r) q) ∧ r ≤ q.val) := by
    ext q
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [hone, hzero, singleRun_delete_count hr (by dsimp [n]; omega)] at hsplit
  rw [singleRun_insert_count r s hr] at hsplit
  exact hsplit.symm

private lemma rotate_single_raw {n : Nat} (w : Fin n → Bool) (i : Fin n) (r z : Nat)
    (he : linearize w i = rawWord [(r,z)]) : rotateWord w i = singleRun n r := by
  have hlen : n = r+z := by
    have h := congrArg List.length he
    simpa [linearize_length, rawWord_cons, rawWord] using h
  funext q
  have hv := linearize_get_optional w i q.val q.isLt
  rw [he, rawWord_cons] at hv
  change w (cycAdd i q.val) = decide (q.val < r)
  by_cases hq : q.val < r
  · simp [rawWord, List.getElem?_append, hq] at hv
    simp [hq,hv]
  · have hzq : q.val-r < z := by have := q.isLt; omega
    simp [rawWord, List.getElem?_append, hq,hzq] at hv
    simp [hq,hv]

theorem degree_raw_singleton {n : Nat} (w : Fin n → Bool) (i : Fin n) (r z : Nat)
    (hr : 0 < r) (hz : r < z) (he : linearize w i = rawWord [(r,z)]) :
    degree w = min r 2 + if 2 ≤ z-r-1 then z-r-1 else 0 := by
  have hlen : n = r+z := by
    have h := congrArg List.length he
    simpa [linearize_length, rawWord_cons, rawWord] using h
  have hns : n = 2*r+1+(z-r-1) := by omega
  rw [← rotateWord_degree w i, rotate_single_raw w i r z he]
  rw [hns]
  exact singleRun_degree r (z-r-1) hr

end
end SingleRunDegrees
