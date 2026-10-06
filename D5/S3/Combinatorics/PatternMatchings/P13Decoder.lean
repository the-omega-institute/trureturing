/- GID: D5/S3/Combinatorics/PatternMatchings/P13Decoder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Decoder
   mirror-E: none(waiver:general-rank-endpoint-decoder)
   anchors: []
   utility: none
   digest: General-rank scans construct disjoint endpoint pairs covering all vertices. -/

import D5.S3.Combinatorics.PatternMatchings.P13Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

open TripleAvoidingMatchingsDefs
open TripleAvoidingMatchings (pairFunction pairFunction_spec)

/-- The ordered queue decoder allows every active rank; it tests no source pattern. -/
def decodePairs {α : Type} : List α → List α → List Step → Option (List (α × α))
  | [], [], [] => some []
  | q, v :: vs, .opening :: w => decodePairs (q ++ [v]) vs w
  | q, v :: vs, .closing r :: w =>
      if hr : r < q.length then
        (decodePairs (q.eraseIdx r) vs w).map ((q[r], v) :: ·)
      else none
  | _, _, _ => none

/-- Every locally accepted scan decodes, and its endpoints are exactly the
initial queue followed by the unscanned vertices, each with its multiplicity. -/
theorem decode_pairs {α : Type} (w : List Step) :
    ∀ (q vs : List α) (s : Base) (k : ℕ),
      s.Valid → q.length = s.size + k → vs.length = w.length → AcceptFrom s k w →
      ∃ p, decodePairs q vs w = some p ∧
        (p.flatMap fun e => [e.1, e.2]).Perm (q ++ vs) := by
  induction w with
  | nil =>
    intro q vs s k hs hq hv ha
    have hqe : q = [] := List.length_eq_zero_iff.mp (by
      simp only [AcceptFrom] at ha
      omega)
    have hve : vs = [] := List.length_eq_zero_iff.mp hv
    subst q
    subst vs
    exact ⟨[], rfl, .refl _⟩
  | cons a w ih =>
    intro q vs s k hs hq hv ha
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      have hv' : vs.length = w.length := by simpa using hv
      cases a with
      | opening =>
        obtain ⟨p, hp, hperm⟩ := ih (q ++ [v]) vs s (k + 1) hs
          (by simp only [List.length_append, List.length_singleton]; omega) hv' ha
        refine ⟨p, by simpa only [decodePairs] using hp, ?_⟩
        simpa only [List.append_assoc, List.singleton_append] using hperm
      | closing r =>
        obtain ⟨hr, ha'⟩ := ha
        have hrl : r < q.length := by have := hr.1; omega
        have ht := transition_spec s k r hs hr
        obtain ⟨p, hp, hperm⟩ := ih (q.eraseIdx r) vs (afterClose s k r) 0 ht.2.1
          (by have hh := List.length_eraseIdx_add_one hrl; omega) hv' ha'
        refine ⟨(q[r], v) :: p, by simp [decodePairs, hrl, hp], ?_⟩
        change (q[r] :: v :: p.flatMap (fun e => [e.1, e.2])).Perm (q ++ v :: vs)
        exact ((hperm.cons v).cons q[r]).trans
          (((List.perm_middle.symm).cons q[r]).trans
            ((List.getElem_cons_eraseIdx_perm hrl).append_right (v :: vs)))

/-- Every initially queued opener is paired with a future vertex. -/
private theorem queued {α : Type} (w : List Step) :
    ∀ (q vs : List α) (p : List (α × α)), decodePairs q vs w = some p →
      ∀ x ∈ q, ∃ b ∈ vs, (x, b) ∈ p := by
  induction w with
  | nil =>
    intro q vs p hp x hx
    cases q <;> cases vs <;> simp [decodePairs] at hp
    simp at hx
  | cons a w ih =>
    intro q vs p hp x hx
    cases vs with
    | nil => simp [decodePairs] at hp
    | cons v vs =>
      cases a with
      | opening =>
        simp only [decodePairs] at hp
        obtain ⟨b, hb, he⟩ := ih (q ++ [v]) vs p hp x (by simp [hx])
        exact ⟨b, by simp [hb], he⟩
      | closing r =>
        by_cases hr : r < q.length
        · cases hd : decodePairs (q.eraseIdx r) vs w with
          | none => simp [decodePairs, hr, hd] at hp
          | some p' =>
            simp only [decodePairs, dif_pos hr, hd, Option.map_some, Option.some.injEq] at hp
            subst p
            by_cases hxsel : x = q[r]
            · exact ⟨v, by simp, by simp [hxsel]⟩
            · have hx' : x ∈ q.eraseIdx r := by
                have hmem := (List.getElem_cons_eraseIdx_perm hr).mem_iff.mpr hx
                simpa only [List.mem_cons, hxsel, false_or] using hmem
              obtain ⟨b, hb, he⟩ := ih _ vs p' hd x hx'
              exact ⟨b, by simp [hb], by simp [he]⟩
        · simp [decodePairs, hr] at hp

/-- Pairs with distinct endpoints realize their two partner equations. -/
private theorem pair_mem {α : Type} [DecidableEq α] (p : List (α × α))
    (hn : (p.flatMap fun e => [e.1, e.2]).Nodup) :
    ∀ a b, (a, b) ∈ p → pairFunction p a = b ∧ pairFunction p b = a := by
  induction p with
  | nil => simp
  | cons e p ih =>
    rcases e with ⟨u, v⟩
    have hflat : (u :: v :: p.flatMap (fun e => [e.1, e.2])).Nodup := hn
    obtain ⟨hu, hv, htail⟩ := List.nodup_cons.mp hflat |>.imp_right List.nodup_cons.mp
    intro a b hab
    rcases List.mem_cons.mp hab with he | he
    · cases he
      simp_all [pairFunction]
    · obtain ⟨ha, hb⟩ := ih htail a b he
      have hma : a ∈ p.flatMap (fun e => [e.1, e.2]) :=
        List.mem_flatMap.mpr ⟨(a, b), he, by simp⟩
      have hmb : b ∈ p.flatMap (fun e => [e.1, e.2]) :=
        List.mem_flatMap.mpr ⟨(a, b), he, by simp⟩
      constructor <;> simp only [pairFunction] <;> split_ifs <;> subst_vars <;> simp_all

/-- Realization of a ranked scan by a partner map. No avoidance is assumed. -/
inductive Realizes {n : ℕ} (m : Matching n) :
    List (Fin (2 * n)) → List (Fin (2 * n)) → List Step → Prop
  | nil : Realizes m [] [] []
  | opening {q vs w v} : v < m.1 v → Realizes m (q ++ [v]) vs w →
      Realizes m q (v :: vs) (.opening :: w)
  | closing {q vs w v r} (hr : r < q.length) : m.1 v = q[r] →
      Realizes m (q.eraseIdx r) vs w → Realizes m q (v :: vs) (.closing r :: w)

/-- A deterministic encoder scans every vertex, recording the actual rank. -/
def encodeFrom {n : ℕ} (m : Matching n) :
    List (Fin (2 * n)) → List (Fin (2 * n)) → List Step
  | _, [] => []
  | q, v :: vs => if v < m.1 v then
      .opening :: encodeFrom m (q ++ [v]) vs
    else
      let r := q.idxOf (m.1 v)
      .closing r :: encodeFrom m (q.eraseIdx r) vs

/-- Decoding with the natural opener order realizes the resulting partner map. -/
theorem decoded_realizes {n : ℕ} (m : Matching n) (w : List Step) :
    ∀ (q vs : List (Fin (2 * n))) (p : List (Fin (2 * n) × Fin (2 * n))),
      q.Pairwise (· < ·) → vs.Pairwise (· < ·) →
      (∀ x ∈ q, ∀ v ∈ vs, x < v) → decodePairs q vs w = some p →
      (∀ a b, (a, b) ∈ p → m.1 a = b ∧ m.1 b = a) → Realizes m q vs w := by
  induction w with
  | nil =>
    intro q vs p hq hv hb hd hc
    cases q <;> cases vs <;> simp [decodePairs] at hd
    exact Realizes.nil
  | cons a w ih =>
    intro q vs p hq hv hb hd hc
    cases vs with
    | nil => simp [decodePairs] at hd
    | cons v vs =>
      obtain ⟨hvfirst, hvsort⟩ := List.pairwise_cons.mp hv
      cases a with
      | opening =>
        simp only [decodePairs] at hd
        obtain ⟨b, hb', he⟩ := queued w (q ++ [v]) vs p hd v (by simp)
        have ho : v < m.1 v := by rw [(hc v b he).1]; exact hvfirst b hb'
        refine Realizes.opening ho (ih (q ++ [v]) vs p ?_ hvsort ?_ hd hc)
        · exact List.pairwise_append.mpr ⟨hq, by simp, by
            intro x hx y hy
            have hy' : y = v := by simpa using hy
            subst y
            exact hb x hx v (by simp)⟩
        · intro x hx y hy
          rcases List.mem_append.mp hx with hx | hx
          · exact hb x hx y (by simp [hy])
          · have hx' : x = v := by simpa using hx
            subst x
            exact hvfirst y hy
      | closing r =>
        by_cases hr : r < q.length
        · cases hd' : decodePairs (q.eraseIdx r) vs w with
          | none => simp [decodePairs, hr, hd'] at hd
          | some p' =>
            simp only [decodePairs, dif_pos hr, hd', Option.map_some, Option.some.injEq] at hd
            subst p
            refine Realizes.closing hr (hc _ _ (by simp)).2
              (ih (q.eraseIdx r) vs p' (hq.sublist (List.eraseIdx_sublist _ _)) hvsort ?_
                hd' ?_)
            · intro x hx y hy
              exact hb x (List.mem_of_mem_eraseIdx hx) y (by simp [hy])
            · intro x y he
              exact hc x y (by simp [he])
        · simp [decodePairs, hr] at hd

/-- Realizing a scan in ordered endpoint lists recovers every recorded rank. -/
theorem realizes_encode {n : ℕ} (m : Matching n)
    {q vs : List (Fin (2 * n))} {w : List Step} (h : Realizes m q vs w)
    (hq : q.Pairwise (· < ·)) (hv : vs.Pairwise (· < ·))
    (hb : ∀ x ∈ q, ∀ v ∈ vs, x < v) : encodeFrom m q vs = w := by
  revert hq hv hb
  induction h with
  | nil => intro hq hv hb; rfl
  | @opening q vs w v ho h ih =>
    intro hq hv hb
    obtain ⟨hvfirst, hvsort⟩ := List.pairwise_cons.mp hv
    have hq' : (q ++ [v]).Pairwise (· < ·) :=
      List.pairwise_append.mpr ⟨hq, by simp, by
        intro x hx y hy
        have hy' : y = v := by simpa using hy
        subst y
        exact hb x hx v (by simp)⟩
    have hb' : ∀ x ∈ q ++ [v], ∀ y ∈ vs, x < y := by
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact hb x hx y (by simp [hy])
      · have hx' : x = v := by simpa using hx
        subst x
        exact hvfirst y hy
    simp only [encodeFrom, if_pos ho]
    rw [ih hq' hvsort hb']
  | @closing q vs w v r hr he h ih =>
    intro hq hv hb
    have hsel : q[r] < v := hb _ (List.getElem_mem hr) v (by simp)
    have hno : ¬ v < m.1 v := by rw [he]; exact not_lt_of_ge hsel.le
    have hidx : q.idxOf (m.1 v) = r := by
      rw [he]
      have hn : q.Nodup := hq.imp (fun hlt => ne_of_lt hlt)
      exact hn.idxOf_getElem r hr
    simp only [encodeFrom, if_neg hno, hidx]
    rw [ih (hq.sublist (List.eraseIdx_sublist _ _)) (List.pairwise_cons.mp hv).2
      (fun x hx y hy => hb x (List.mem_of_mem_eraseIdx hx) y (by simp [hy]))]

/-- Accepted scans construct an actual matching, including the empty scan. -/
noncomputable def decodeMatching {n : ℕ} (w : Accepted n) : Matching n := by
  classical
  have hex := decode_pairs w.1 [] (List.finRange (2 * n)) (.S 0) 0
    trivial rfl (by simpa using w.2.1.symm) w.2.2
  let p := Classical.choose hex
  have hp := Classical.choose_spec hex
  have hperm : (p.flatMap fun e => [e.1, e.2]).Perm (List.finRange (2 * n)) := by
    simpa using hp.2
  have hn := hperm.nodup_iff.mpr (List.nodup_finRange _)
  have hf := pairFunction_spec p hn
  exact ⟨pairFunction p, fun v => ⟨hf.1 v, fun h =>
    (hf.2 v).mp h (hperm.mem_iff.mpr (List.mem_finRange v))⟩⟩

/-- The matching constructed from an accepted scan realizes the entire scan. -/
theorem decode_realizes {n : ℕ} (w : Accepted n) :
    Realizes (decodeMatching w) [] (List.finRange (2 * n)) w.1 := by
  classical
  have hex := decode_pairs w.1 [] (List.finRange (2 * n)) (.S 0) 0
    trivial rfl (by simpa using w.2.1.symm) w.2.2
  let p := Classical.choose hex
  have hp := Classical.choose_spec hex
  have hn : (p.flatMap fun e => [e.1, e.2]).Nodup :=
    hp.2.nodup_iff.mpr (by simpa using List.nodup_finRange (2 * n))
  have hs : (List.finRange (2 * n)).Pairwise (· < ·) := by
    rw [← List.ofFn_id]
    exact List.pairwise_ofFn.mpr (fun i j hij => hij)
  exact decoded_realizes (decodeMatching w) w.1 [] _ p (by simp) hs (by simp)
    hp.1 (pair_mem p hn)

end D5.S3.Combinatorics.PatternMatchings.P13
