/- GID: D5/S3/Combinatorics/PatternMatchings/P13Correspondence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Correspondence
   mirror-E: none(waiver:actual-unbounded-scan-bijection)
   anchors: []
   utility: none
   digest: Normalized general-rank scans encode all P13-avoiding perfect matchings. -/

import D5.S3.Combinatorics.PatternMatchings.P13Orders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

open TripleAvoidingMatchingsDefs

/-- The complete active opener list at the cut t. -/
def QueueAt {n : ℕ} (m : Matching n) (t : ℕ) (q : List (Fin (2 * n))) : Prop :=
  ∀ x, x ∈ q ↔ x.val < t ∧ t ≤ (m.1 x).val

/-- The complete unscanned vertex suffix. -/
def VerticesAt {n : ℕ} (t : ℕ) (vs : List (Fin (2 * n))) : Prop :=
  ∀ x, x ∈ vs ↔ t ≤ x.val

private theorem head_at {n : ℕ} (v : Fin (2 * n)) (vs : List (Fin (2 * n)))
    (t : ℕ) (hv : (v :: vs).Pairwise (· < ·)) (he : VerticesAt t (v :: vs)) :
    v.val = t ∧ VerticesAt (t + 1) vs := by
  have hfirst := (List.pairwise_cons.mp hv).1
  have ht : t ≤ v.val := (he v).mp (by simp)
  have hvt : v.val = t := by
    by_contra hn
    have hbound : t < 2 * n := by have := v.isLt; omega
    let x : Fin (2 * n) := ⟨t, hbound⟩
    have hx := (he x).mpr (by rfl)
    rcases List.mem_cons.mp hx with hx | hx
    · have hh := congrArg Fin.val hx
      simp only [x] at hh
      omega
    · have hh := hfirst x hx
      change v.val < t at hh
      omega
  refine ⟨hvt, ?_⟩
  intro x
  constructor
  · intro hx
    have hh := hfirst x hx
    change v.val < x.val at hh
    omega
  · intro hx
    have hh := (he x).mpr (by omega)
    rcases List.mem_cons.mp hh with hh | hh
    · have hvx := congrArg Fin.val hh
      omega
    · exact hh

private theorem queue_update {n : ℕ} (m : Matching n) (v : Fin (2 * n))
    (t : ℕ) (q q' : List (Fin (2 * n))) (hv : v.val = t) (hq : QueueAt m t q)
    (he : ∀ x, x ∈ q' ↔ (x ∈ q ∧ x ≠ m.1 v) ∨ (x = v ∧ v < m.1 v)) :
    QueueAt m (t + 1) q' := by
  intro x
  rw [he, hq x]
  have hpartner : (m.1 x).val = t ↔ x = m.1 v := by
    constructor
    · intro h
      have he' : m.1 x = v := Fin.ext (by omega)
      have hh := congrArg m.1 he'
      simpa only [(m.2 x).1] using hh
    · intro h
      rw [h, (m.2 v).1, hv]
  have hvertex : x.val = t ↔ x = v := ⟨fun h => Fin.ext (by omega),
    fun h => by rw [h, hv]⟩
  constructor
  · rintro (⟨⟨hx, hm⟩, hn⟩ | ⟨hxv, ho⟩)
    · have hmne : (m.1 x).val ≠ t := fun h => hn (hpartner.mp h)
      omega
    · subst x
      change v.val < (m.1 v).val at ho
      omega
  · intro h
    by_cases hx : x.val < t
    · exact Or.inl ⟨⟨hx, by omega⟩, fun he' => by
        have hh := hpartner.mpr he'
        omega⟩
    · have he' : x = v := hvertex.mp (by omega)
      subst x
      exact Or.inr ⟨rfl, by change v.val < (m.1 v).val; omega⟩

private theorem queue_open {n : ℕ} (m : Matching n) (v : Fin (2 * n))
    (t : ℕ) (q : List (Fin (2 * n))) (hv : v.val = t) (hq : QueueAt m t q)
    (ho : v < m.1 v) : QueueAt m (t + 1) (q ++ [v]) := by
  apply queue_update m v t q _ hv hq
  intro x
  have hn : x ∈ q → x ≠ m.1 v := by
    intro hx he
    have hh := (hq x).mp hx
    rw [he] at hh
    change v.val < (m.1 v).val at ho
    omega
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro (hx | rfl)
    · exact Or.inl ⟨hx, hn hx⟩
    · exact Or.inr ⟨rfl, ho⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> simp [hx]

private theorem queue_close {n : ℕ} (m : Matching n) (v : Fin (2 * n))
    (t : ℕ) (q : List (Fin (2 * n))) (r : ℕ) (hr : r < q.length)
    (hv : v.val = t) (hq : QueueAt m t q) (hs : q.Nodup) (he : m.1 v = q[r])
    (hc : m.1 v < v) : QueueAt m (t + 1) (q.eraseIdx r) := by
  apply queue_update m v t q _ hv hq
  have hperm := List.getElem_cons_eraseIdx_perm hr
  have hn : q[r] ∉ q.eraseIdx r := (List.nodup_cons.mp (hperm.nodup_iff.mpr hs)).1
  intro x
  have hx : x ∈ q ↔ x = q[r] ∨ x ∈ q.eraseIdx r := by
    simpa only [List.mem_cons] using hperm.mem_iff.symm
  have hno : ¬ v < m.1 v := not_lt_of_ge hc.le
  simp only [hno, and_false, or_false]
  rw [he, hx]
  constructor
  · intro h
    exact ⟨Or.inr h, fun he' => hn (he' ▸ h)⟩
  · rintro ⟨h | h, hne⟩
    · exact (hne h).elim
    · exact h

/-- Scanning any actual matching is total, ordered, and selects only an active rank. -/
theorem encode_realizes {n : ℕ} (m : Matching n) :
    ∀ (vs q : List (Fin (2 * n))) (t : ℕ),
      vs.Pairwise (· < ·) → q.Pairwise (· < ·) →
      VerticesAt t vs → QueueAt m t q →
      Realizes m q vs (encodeFrom m q vs) := by
  intro vs
  induction vs with
  | nil =>
    intro q t hs hq hv ha
    have he : t = 2 * n ∨ 2 * n ≤ t := by
      by_contra hn
      have hb : t < 2 * n := by omega
      have hh := (hv ⟨t, hb⟩).mpr le_rfl
      simp at hh
    have hqe : q = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro x hx
      have hh := (ha x).mp hx
      have hb := (m.1 x).isLt
      omega)
    subst q
    exact Realizes.nil
  | cons v vs ih =>
    intro q t hs hq hv ha
    obtain ⟨hvt, hv'⟩ := head_at v vs t hs hv
    have hs' := (List.pairwise_cons.mp hs).2
    by_cases ho : v < m.1 v
    · have hq' : (q ++ [v]).Pairwise (· < ·) := by
        refine List.pairwise_append.mpr ⟨hq, by simp, ?_⟩
        intro x hx y hy
        have hh := (ha x).mp hx
        have hy' : y = v := by simpa using hy
        subst y
        change x.val < v.val
        omega
      have hi := ih (q ++ [v]) (t + 1) hs' hq' hv' (queue_open m v t q hvt ha ho)
      simpa only [encodeFrom, if_pos ho] using Realizes.opening ho hi
    · have hc : m.1 v < v := by have hn := (m.2 v).2; omega
      have hmem : m.1 v ∈ q := (ha (m.1 v)).mpr (by
        rw [(m.2 v).1]
        change (m.1 v).val < t ∧ t ≤ v.val
        constructor <;> omega)
      let r := q.idxOf (m.1 v)
      have hr : r < q.length := List.idxOf_lt_length_of_mem hmem
      have he : m.1 v = q[r] := (List.getElem_idxOf hr).symm
      have hn : q.Nodup := hq.imp (fun h => ne_of_lt h)
      have hi := ih (q.eraseIdx r) (t + 1) hs' (hq.sublist (List.eraseIdx_sublist _ _))
        hv' (queue_close m v t q r hr hvt ha hn he hc)
      simpa only [encodeFrom, if_neg ho] using Realizes.closing hr he hi

/-- The future-order law restricted to one closure. -/
def FutureAt {n : ℕ} (m : Matching n) (v : Fin (2 * n)) : Prop :=
  m.1 v < v → ∀ x y, x < y → y < v → v < m.1 x → v < m.1 y →
    (m.1 x < m.1 y ↔ x < m.1 v ∧ m.1 v < y)

private theorem closure_at {n : ℕ} (m : Matching n) (v : Fin (2 * n))
    (q : List (Fin (2 * n))) (r t : ℕ) (hr : r < q.length)
    (hv : v.val = t) (ha : QueueAt m t q) (hq : q.Pairwise (· < ·))
    (he : m.1 v = q[r]) (hc : m.1 v < v) :
    ClosureRespects q (fun x => (m.1 x).val) r ↔ FutureAt m v := by
  have mono : StrictMono q.get := List.pairwise_iff_get.mp hq
  have inj : Function.Injective m.1 :=
    Function.LeftInverse.injective (fun x => (m.2 x).1)
  have surv (x : Fin q.length) (hx : x.val ≠ r) :
      q.get x < v ∧ v < m.1 (q.get x) := by
    have hh := (ha (q.get x)).mp (List.get_mem ..)
    have hne : m.1 (q.get x) ≠ v := by
      intro hm
      have hh' := congrArg m.1 hm
      rw [(m.2 (q.get x)).1, he] at hh'
      have hx' : x = ⟨r, hr⟩ := mono.injective hh'
      exact hx (congrArg Fin.val hx')
    constructor <;> change _ < _ <;> omega
  constructor
  · intro h hclose x y hxy hyv hx hy
    have hxq : x ∈ q := (ha x).mpr (by change x.val < t ∧ t ≤ (m.1 x).val; omega)
    have hyq : y ∈ q := (ha y).mpr (by change y.val < t ∧ t ≤ (m.1 y).val; omega)
    let i : Fin q.length := ⟨q.idxOf x, List.idxOf_lt_length_of_mem hxq⟩
    let j : Fin q.length := ⟨q.idxOf y, List.idxOf_lt_length_of_mem hyq⟩
    have hi : q.get i = x := List.getElem_idxOf i.isLt
    have hj : q.get j = y := List.getElem_idxOf j.isLt
    have hir : i.val ≠ r := by
      intro h'
      have hh : x = m.1 v := by rw [← hi, he]; congr 1; exact Fin.ext h'
      rw [hh, (m.2 v).1] at hx
      exact lt_irrefl _ hx
    have hjr : j.val ≠ r := by
      intro h'
      have hh : y = m.1 v := by rw [← hj, he]; congr 1; exact Fin.ext h'
      rw [hh, (m.2 v).1] at hy
      exact lt_irrefl _ hy
    have hij : i < j := mono.lt_iff_lt.mp (by simpa only [hi, hj] using hxy)
    have hgetr : q.get ⟨r, hr⟩ = m.1 v := by
      simpa only [List.get_eq_getElem] using he.symm
    have hic : i.val < r ↔ x < m.1 v := by
      have hh := (mono.lt_iff_lt (a := i) (b := ⟨r, hr⟩)).symm
      change i.val < r ↔ q.get i < q.get ⟨r, hr⟩ at hh
      simpa only [hi, hgetr] using hh
    have hcj : r < j.val ↔ m.1 v < y := by
      have hh := (mono.lt_iff_lt (a := ⟨r, hr⟩) (b := j)).symm
      change r < j.val ↔ q.get ⟨r, hr⟩ < q.get j at hh
      simpa only [hj, hgetr] using hh
    have hh := closure_comparison q _ r h i j hir hjr
    change (m.1 (q.get i)).val < (m.1 (q.get j)).val ↔ _ at hh
    rw [hi, hj] at hh
    have hbefore : Before r i.val j.val ↔ i.val < r ∧ r < j.val := by
      unfold Before
      change i.val < j.val at hij
      omega
    exact hh.trans (hbefore.trans (and_congr hic hcj))
  · intro h x y hxr hyr hb
    obtain ⟨hxv, hx⟩ := surv x hxr
    obtain ⟨hyv, hy⟩ := surv y hyr
    have hne : m.1 (q.get x) ≠ m.1 (q.get y) := by
      intro hm
      have hxy := mono.injective (inj hm)
      have hh := congrArg Fin.val hxy
      unfold Before at hb
      omega
    rcases hb with hb | ⟨hyx, hsame⟩
    · have hxy : x < y := by change x.val < y.val; omega
      have hh := h hc _ _ (mono hxy) hyv hx hy
      apply hh.mpr
      rw [he]
      exact ⟨mono (show x < ⟨r, hr⟩ from hb.1),
        mono (show (⟨r, hr⟩ : Fin q.length) < y from by change r < y.val; omega)⟩
    · have hyx' : y < x := hyx
      have hh := h hc _ _ (mono hyx') hxv hy hx
      have hnot : ¬ (q.get y < m.1 v ∧ m.1 v < q.get x) := by
        rw [he]
        intro hsplit
        have h1 := mono.lt_iff_lt.mp hsplit.1
        have h2 := mono.lt_iff_lt.mp hsplit.2
        change y.val < r at h1
        change r < x.val at h2
        omega
      have hno := fun hlt => hnot (hh.mp hlt)
      change (m.1 (q.get x)).val < (m.1 (q.get y)).val
      omega

/-- Future-order laws at all remaining closure vertices. -/
def FutureSuffix {n : ℕ} (m : Matching n) (t : ℕ) : Prop :=
  ∀ v, t ≤ v.val → FutureAt m v

private theorem future_split {n : ℕ} (m : Matching n) (v : Fin (2 * n)) (t : ℕ)
    (hv : v.val = t) : FutureSuffix m t ↔ FutureAt m v ∧ FutureSuffix m (t + 1) := by
  constructor
  · intro h
    exact ⟨h v (by omega), fun x hx => h x (by omega)⟩
  · rintro ⟨hv', h⟩ x hx
    by_cases he : x.val = t
    · have hxe : x = v := Fin.ext (by omega)
      simpa only [hxe] using hv'
    · exact h x (by omega)

/-- The orders imposed by the full scan are precisely the source future-order
laws on its remaining vertices. The queue is the complete active set. -/
theorem ordered_run_iff {n : ℕ} (m : Matching n)
    {q vs : List (Fin (2 * n))} {w : List Step} (h : Realizes m q vs w)
    (hq : q.Pairwise (· < ·)) (hv : vs.Pairwise (· < ·)) :
    ∀ t, QueueAt m t q → VerticesAt t vs →
      (OrderedRun m q vs w ↔ FutureSuffix m t) := by
  revert hq hv
  induction h with
  | nil =>
    intro hq hv t ha he
    simp only [OrderedRun, true_iff, FutureSuffix]
    intro v hv
    have hh := (he v).mpr hv
    simp at hh
  | @opening q vs w v ho h ih =>
    intro hq hv t ha he
    obtain ⟨hvt, he'⟩ := head_at v vs t hv he
    obtain ⟨hvfirst, hvsort⟩ := List.pairwise_cons.mp hv
    have hq' : (q ++ [v]).Pairwise (· < ·) := by
      refine List.pairwise_append.mpr ⟨hq, by simp, ?_⟩
      intro x hx y hy
      have hh := (ha x).mp hx
      have hy' : y = v := by simpa using hy
      subst y
      change x.val < v.val
      omega
    change OrderedRun m (q ++ [v]) vs w ↔ FutureSuffix m t
    rw [ih hq' hvsort (t + 1) (queue_open m v t q hvt ha ho) he', future_split m v t hvt]
    have hf : FutureAt m v := by
      intro hc
      exact (not_lt_of_ge ho.le hc).elim
    exact (and_iff_right hf).symm
  | @closing q vs w v r hr hp h ih =>
    intro hq hv t ha he
    obtain ⟨hvt, he'⟩ := head_at v vs t hv he
    obtain ⟨hvfirst, hvsort⟩ := List.pairwise_cons.mp hv
    have hc : m.1 v < v := by
      have hh := (ha (q[r])).mp (List.getElem_mem hr)
      rw [← hp] at hh
      change (m.1 v).val < v.val
      omega
    have hn : q.Nodup := hq.imp (fun h => ne_of_lt h)
    have ha' := queue_close m v t q r hr hvt ha hn hp hc
    change (ClosureRespects q _ r ∧ OrderedRun m (q.eraseIdx r) vs w) ↔ FutureSuffix m t
    rw [ih (hq.sublist (List.eraseIdx_sublist _ _)) hvsort (t + 1) ha' he',
      future_split m v t hvt, closure_at m v q r t hr hvt ha hq hp hc]

private theorem finRange_sorted (N : ℕ) : (List.finRange N).Pairwise (· < ·) := by
  rw [← List.ofFn_id]
  exact List.pairwise_ofFn.mpr (fun i j hij => hij)

private theorem encode_length {n : ℕ} (m : Matching n)
    (vs : List (Fin (2 * n))) : ∀ q, (encodeFrom m q vs).length = vs.length := by
  induction vs with
  | nil => simp [encodeFrom]
  | cons v vs ih =>
    intro q
    unfold encodeFrom
    split_ifs <;> simp only [List.length_cons, ih]

/-- The full encoder of an avoiding matching is accepted by the local machine. -/
theorem encode_accepted {n : ℕ} (m : Matching n) (hm : Avoids m) :
    AcceptFrom (.S 0) 0 (encodeFrom m [] (List.finRange (2 * n))) := by
  have h := encode_realizes m (List.finRange (2 * n)) [] 0
    (finRange_sorted _) (by simp) (by simp [VerticesAt]) (by simp [QueueAt])
  apply (normalized_run m h (by simp) (finRange_sorted _) (by simp) (.S 0) 0 trivial rfl).mpr
  refine ⟨fun x => Fin.elim0 x, ?_⟩
  apply (ordered_run_iff m h (by simp) (finRange_sorted _) 0
    (by simp [QueueAt]) (by simp [VerticesAt])).mpr
  exact fun v _ hc x y hxy hyv hx hy => (future_order_iff m).mp hm v x y hc hxy hyv hx hy

/-- The actual matching decoded from any accepted scan avoids precisely P13. -/
theorem decode_avoids {n : ℕ} (w : Accepted n) : Avoids (decodeMatching w) := by
  have h := decode_realizes w
  have hn := (normalized_run (decodeMatching w) h (by simp) (finRange_sorted _)
    (by simp) (.S 0) 0 trivial rfl).mp w.2.2
  have hf := (ordered_run_iff (decodeMatching w) h (by simp) (finRange_sorted _) 0
    (by simp [QueueAt]) (by simp [VerticesAt])).mp hn.2
  exact (future_order_iff _).mpr (fun v x y hc hxy hyv hx hy =>
    hf v (by omega) hc x y hxy hyv hx hy)

/-- Two realizations of the same ranked scan agree at every queued and remaining endpoint. -/
theorem realizes_unique {n : ℕ} (m m' : Matching n)
    {q vs : List (Fin (2 * n))} {w : List Step} (h : Realizes m q vs w)
    (h' : Realizes m' q vs w) : ∀ x ∈ q ++ vs, m.1 x = m'.1 x := by
  revert h'
  induction h with
  | nil => intro h'; simp
  | @opening q vs w v ho h ih =>
    intro h'
    cases h' with
    | opening ho' h' =>
      intro x hx
      exact ih h' x (by simpa only [List.append_assoc, List.singleton_append] using hx)
  | @closing q vs w v r hr he h ih =>
    intro h'
    cases h' with
    | closing hr' he' h' =>
      intro x hx
      have ih' := ih h'
      by_cases hxv : x = v
      · subst x
        exact he.trans he'.symm
      · by_cases hxr : x = q[r]
        · subst x
          have hm : m.1 q[r] = v := by rw [← he]; exact (m.2 v).1
          have hm' : m'.1 q[r] = v := by rw [← he']; exact (m'.2 v).1
          exact hm.trans hm'.symm
        · apply ih' x
          rcases List.mem_append.mp hx with hx | hx
          · have hh := (List.getElem_cons_eraseIdx_perm hr).mem_iff.mpr hx
            have hx' : x ∈ q.eraseIdx r := by
              simpa only [List.mem_cons, hxr, false_or] using hh
            exact List.mem_append.mpr (Or.inl hx')
          · have hx' : x ∈ vs := by simpa only [List.mem_cons, hxv, false_or] using hx
            exact List.mem_append.mpr (Or.inr hx')

/-- The exhaustive bijection on actual perfect matchings of Fin(2n), for every n.
Pending openings remain distinct from the post-closure normalized base throughout. -/
noncomputable def matchingEquiv (n : ℕ) : {m : Matching n // Avoids m} ≃ Accepted n where
  toFun m := ⟨encodeFrom m.1 [] (List.finRange (2 * n)),
    by simpa using encode_length m.1 (List.finRange (2 * n)) [], encode_accepted m.1 m.2⟩
  invFun w := ⟨decodeMatching w, decode_avoids w⟩
  left_inv m := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have h := encode_realizes m.1 (List.finRange (2 * n)) [] 0
      (finRange_sorted _) (by simp) (by simp [VerticesAt]) (by simp [QueueAt])
    exact realizes_unique _ _ (decode_realizes _) h x (by simp)
  right_inv w := by
    apply Subtype.ext
    exact realizes_encode (decodeMatching w) (decode_realizes w) (by simp)
      (finRange_sorted _) (by simp)

end D5.S3.Combinatorics.PatternMatchings.P13
