/- GID: D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact free-endpoint reduction of primitive graph games to complete matrices. -/
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierGraph

/-! The finite-horizon reduction of Meyerovitch–Young Question 6.1. -/

namespace MeyerovitchYoungQ61Complete

open Maths
open List

variable {V E W F K : Type*}

/-- A common positive length for connecting every ordered pair of vertices. -/
def ConnectsAt (G : EdgeGraph V E) (L : ℕ) : Prop :=
  ∀ s t, ∃ p : G.Walk s t, p.length = L

private def follows (G : EdgeGraph V E) (s : V) : List E → V → Prop
  | [], t => s = t
  | e :: es, t => G.source e = s ∧ follows G (G.target e) es t

private theorem follows_append (G : EdgeGraph V E) {s t u : V} {a b : List E}
    (ha : follows G s a t) (hb : follows G t b u) : follows G s (a ++ b) u := by
  induction a generalizing s with
  | nil => exact (show s = t from ha).symm ▸ hb
  | cons e a ih => exact ⟨ha.1, ih ha.2⟩

private theorem follows_edges (G : EdgeGraph V E) {s t : V} (p : G.Walk s t) :
    follows G s p.edges t := by
  induction p with
  | nil => rfl
  | concat p e he ih => exact follows_append G ih (show follows G _ [e] _ from ⟨he, rfl⟩)

private theorem walk_of_follows (G : EdgeGraph V E) {s t : V} {a : List E}
    (h : follows G s a t) : ∃ p : G.Walk s t, p.edges = a := by
  induction a generalizing s with
  | nil =>
    cases (show s = t from h)
    exact ⟨.nil, rfl⟩
  | cons e a ih =>
    obtain ⟨p, hp⟩ := ih h.2
    let q : G.Walk s (G.target e) := .concat .nil e h.1
    exact ⟨q.append p, by simp [q, EdgeGraph.Walk.edges, hp]⟩

/-- The free-start, free-finish edge words of the original graph. -/
def Legal (G : EdgeGraph V E) (a : List E) : Prop :=
  ∃ s t, ∃ p : G.Walk s t, p.edges = a

private theorem legal_iff_follows (G : EdgeGraph V E) (a : List E) :
    Legal G a ↔ ∃ s t, follows G s a t :=
  ⟨fun ⟨s, t, p, hp⟩ => ⟨s, t, hp ▸ follows_edges G p⟩,
    fun ⟨s, t, h⟩ => ⟨s, t, walk_of_follows G h⟩⟩

private theorem walk_length_le (G : EdgeGraph V E) {s t : V} (p : G.Walk s t)
    (n : ℕ) (hn : n ≤ p.length) : ∃ u, ∃ q : G.Walk s u, q.length = n := by
  induction p with
  | nil =>
    have : n = 0 := Nat.eq_zero_of_le_zero hn
    exact ⟨s, .nil, this.symm⟩
  | @concat t p e he ih =>
    by_cases h : n ≤ p.length
    · exact ih h
    · exact ⟨_, p.concat e he, by simp only [EdgeGraph.Walk.length_concat] at hn ⊢; omega⟩

private theorem walksFrom (G : EdgeGraph V E) (d : ℕ) (h : ConnectsAt G (d + 1)) :
    ∀ (n : ℕ) (s : V), ∃ t, ∃ p : G.Walk s t, p.length = n := by
  intro n
  induction n with
  | zero => exact fun s => ⟨s, .nil, rfl⟩
  | succ n ih =>
    intro s
    obtain ⟨t, p, hp⟩ := ih s
    obtain ⟨q, hq⟩ := h t t
    obtain ⟨u, r, hr⟩ := walk_length_le G q 1 (by omega)
    exact ⟨u, p.append r, by simp [hp, hr]⟩

open Classical in
private noncomputable def badFrom (G : EdgeGraph V E) (prev : E) : List E → ℕ
  | [] => 0
  | e :: es => (if G.target prev = G.source e then 0 else 1) + badFrom G e es

/-- Number of incompatible consecutive Alice edges. -/
noncomputable def badJoins (G : EdgeGraph V E) : List E → ℕ
  | [] => 0
  | e :: es => badFrom G e es

private def preceding (prev : E) (a : List E) : ℕ → E
  | 0 => prev
  | n + 1 => match a with
    | [] => prev
    | e :: es => preceding e es n

private theorem badFrom_drop (G : EdgeGraph V E) (prev : E) (a : List E) (n : ℕ) :
    badFrom G (preceding prev a n) (a.drop n) ≤ badFrom G prev a := by
  induction n generalizing prev a with
  | zero => simp [preceding]
  | succ n ih =>
    cases a with
    | nil => simp [badFrom]
    | cons e es =>
      exact (ih e es).trans (Nat.le_add_left ..)

private noncomputable def connector (G : EdgeGraph V E) {d : ℕ}
    (h : ConnectsAt G (d + 1)) (s t : V) : G.Walk s t :=
  Classical.choose (h s t)

private theorem connector_length (G : EdgeGraph V E) {d : ℕ}
    (h : ConnectsAt G (d + 1)) (s t : V) : (connector G h s t).length = d + 1 :=
  Classical.choose_spec (h s t)

private noncomputable def tailWalk (G : EdgeGraph V E) {d : ℕ}
    (h : ConnectsAt G (d + 1)) (s : V) (n : ℕ) :
    G.Walk s (Classical.choose (walksFrom G d h n s)) :=
  Classical.choose (Classical.choose_spec (walksFrom G d h n s))

private theorem tailWalk_length (G : EdgeGraph V E) {d : ℕ}
    (h : ConnectsAt G (d + 1)) (s : V) (n : ℕ) : (tailWalk G h s n).length = n :=
  Classical.choose_spec (Classical.choose_spec (walksFrom G d h n s))

private noncomputable def repairAfter (G : EdgeGraph V E) (d : ℕ)
    (h : ConnectsAt G (d + 1)) (prev : E) (a : List E) : List E := by
  classical
  exact match a with
  | [] => []
  | e :: es =>
    if G.target prev = G.source e then
      e :: repairAfter G d h e es
    else if d ≤ es.length then
      let last := preceding e es d
      (connector G h (G.target prev) (G.target last)).edges ++
        repairAfter G d h last (es.drop d)
    else (tailWalk G h (G.target prev) (es.length + 1)).edges
termination_by a.length
decreasing_by all_goals simp_wf

/-- Repair the word, copying a compatible edge and replacing a block
of length `d + 1` at an incompatible join. The final short block uses
a walk of exactly the remaining length. Connector choices are fixed. -/
private noncomputable def repair (G : EdgeGraph V E) (d : ℕ) (h : ConnectsAt G (d + 1)) :
    List E → List E
  | [] => []
  | e :: es => e :: repairAfter G d h e es

private theorem repairAfter_walk (G : EdgeGraph V E) (d : ℕ)
    (h : ConnectsAt G (d + 1)) (prev : E) (a : List E) :
    (repairAfter G d h prev a).length = a.length ∧
      ∃ t, follows G (G.target prev) (repairAfter G d h prev a) t := by
  classical
  rw [repairAfter.eq_def]
  split
  · exact ⟨rfl, _, rfl⟩
  · rename_i e es
    split
    · rename_i he
      obtain ⟨hlen, t, ht⟩ := repairAfter_walk G d h e es
      exact ⟨by simp [hlen], t, he.symm, ht⟩
    · split
      · rename_i hfull
        let last := preceding e es d
        obtain ⟨hlen, t, ht⟩ := repairAfter_walk G d h last (es.drop d)
        change (_ ++ repairAfter G d h last (es.drop d)).length = _ ∧
          ∃ t, follows G _ (_ ++ repairAfter G d h last (es.drop d)) t
        refine ⟨?_, t, follows_append G (follows_edges G (connector G h _ _)) ht⟩
        rw [List.length_append, EdgeGraph.Walk.edges_length, connector_length, hlen,
          List.length_drop, List.length_cons]
        omega
      · exact ⟨by simp [tailWalk_length], _, follows_edges G _⟩
termination_by a.length
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [List.length_cons]
  all_goals omega

private theorem repair_walk (G : EdgeGraph V E) [Nonempty V] (d : ℕ)
    (h : ConnectsAt G (d + 1)) (a : List E) :
    (repair G d h a).length = a.length ∧ Legal G (repair G d h a) := by
  cases a with
  | nil =>
    let s : V := Classical.choice inferInstance
    exact ⟨rfl, s, s, .nil, rfl⟩
  | cons e es =>
    obtain ⟨hlen, t, ht⟩ := repairAfter_walk G d h e es
    exact ⟨by simp [repair, hlen],
      (legal_iff_follows G _).2 ⟨G.source e, t, rfl, ht⟩⟩

variable [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Payoff against an edge word of the minimizing graph, paired in order. -/
private def wordCost (p : E → F → K) (a : List E) (b : List F) : K :=
  (List.zipWith p a b).sum

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem wordCost_append (p : E → F → K) {a a' : List E} {b b' : List F}
    (h : a.length = b.length) :
    wordCost p (a ++ a') (b ++ b') = wordCost p a b + wordCost p a' b' := by
  unfold wordCost
  rw [List.zipWith_append h, List.sum_append]

private theorem wordCost_change (p : E → F → K) {R : K}
    (hR : ∀ e e' f, p e f ≤ p e' f + R) {a a' : List E} (b : List F)
    (h : a.length = a'.length) (hb : a.length = b.length) :
    wordCost p a b ≤ wordCost p a' b + (a.length : K) * R := by
  induction a generalizing a' b with
  | nil => cases a' <;> cases b <;> simp_all [wordCost]
  | cons e es ih =>
    cases a' with
    | nil => simp at h
    | cons e' es' =>
      cases b with
      | nil => simp at hb
      | cons f fs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h hb
        have hind := ih fs h hb
        have hfirst := hR e e' f
        simp only [wordCost, List.zipWith_cons_cons, List.sum_cons, List.length_cons,
          Nat.cast_add, Nat.cast_one, add_mul, one_mul] at *
        linarith only [hind, hfirst]

private theorem repairAfter_cost (G : EdgeGraph V E) (d : ℕ)
    (h : ConnectsAt G (d + 1)) (p : E → F → K) {R : K} (hR₀ : 0 ≤ R)
    (hR : ∀ e e' f, p e f ≤ p e' f + R) (prev : E) (a : List E) (b : List F)
    (hb : a.length = b.length) :
    wordCost p a b ≤ wordCost p (repairAfter G d h prev a) b +
      ((d + 1 : ℕ) : K) * R * (badFrom G prev a : K) := by
  classical
  let bound : K := ((d + 1 : ℕ) : K) * R
  have hbound : 0 ≤ bound := mul_nonneg (Nat.cast_nonneg _) hR₀
  rw [repairAfter.eq_def]
  split
  · simp [wordCost, badFrom]
  · rename_i e es
    split
    · rename_i he
      cases b with
      | nil => simp at hb
      | cons f fs =>
        have hfs : es.length = fs.length := by simpa using hb
        have hind := repairAfter_cost G d h p hR₀ hR e es fs hfs
        simp only [wordCost, List.zipWith_cons_cons, List.sum_cons, badFrom,
          ite_eq_left he, zero_add] at hind ⊢
        linarith only [hind]
    · rename_i he
      split
      · rename_i hfull
        let last := preceding e es d
        let c := (connector G h (G.target prev) (G.target last)).edges
        have hc : c.length = d + 1 := by simp [c, connector_length]
        let l := d + 1
        have hla : l ≤ (e :: es).length := by simp [l, hfull]
        have hlb : l ≤ b.length := hla.trans hb.le
        have htake : ((e :: es).take l).length = l := by
          rw [List.length_take, Nat.min_eq_left hla]
        have htakeb : (b.take l).length = l := by
          simp [List.length_take, Nat.min_eq_left hlb]
        have hdrop : (es.drop d).length = (b.drop l).length := by
          simp only [List.length_cons] at hb
          simp only [List.length_drop, l]
          omega
        have hind := repairAfter_cost G d h p hR₀ hR last (es.drop d) (b.drop l) hdrop
        have hchg := wordCost_change p hR (b.take l) (htake.trans hc.symm)
          (htake.trans htakeb.symm)
        rw [htake] at hchg
        have hcount : (badFrom G last (es.drop d) : K) ≤ (badFrom G e es : K) := by
          exact_mod_cast badFrom_drop G e es d
        have hcount' := mul_le_mul_of_nonneg_left hcount hbound
        have hsplit : wordCost p (e :: es) b =
            wordCost p ((e :: es).take l) (b.take l) + wordCost p (es.drop d) (b.drop l) := by
          have hs := wordCost_append p (a' := (e :: es).drop l) (b' := b.drop l)
            (htake.trans htakeb.symm)
          rw [List.take_append_drop, List.take_append_drop] at hs
          exact hs
        change wordCost p (e :: es) b ≤
          wordCost p (c ++ repairAfter G d h last (es.drop d)) b +
            bound * (badFrom G prev (e :: es) : K)
        have hsplit' := wordCost_append p (a' := repairAfter G d h last (es.drop d))
          (b' := b.drop l) (hc.trans htakeb.symm)
        rw [List.take_append_drop] at hsplit'
        rw [hsplit, hsplit', badFrom, ite_eq_right he, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        change _ ≤ _ + (bound + bound * (badFrom G e es : K))
        change _ ≤ _ + bound * (badFrom G last (es.drop d) : K) at hind
        change _ ≤ _ + bound at hchg
        linarith only [hind, hchg, hcount']
      · rename_i hshort
        let c := (tailWalk G h (G.target prev) (es.length + 1)).edges
        have hc : (e :: es).length = c.length := by simp [c, tailWalk_length]
        have hchg := wordCost_change p hR b hc hb
        have hlen : ((e :: es).length : K) ≤ ((d + 1 : ℕ) : K) := by
          exact_mod_cast (show (e :: es).length ≤ d + 1 by simp; omega)
        have hchg' := mul_le_mul_of_nonneg_right hlen hR₀
        have hcount : (1 : K) ≤ (badFrom G prev (e :: es) : K) := by
          exact_mod_cast (show 1 ≤ badFrom G prev (e :: es) by simp [badFrom, he])
        have hcount' := mul_le_mul_of_nonneg_left hcount hbound
        rw [mul_one] at hcount'
        change wordCost p (e :: es) b ≤ wordCost p c b + bound * _
        change _ ≤ bound at hchg'
        linarith only [hchg, hchg', hcount']
termination_by a.length
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [List.length_cons, List.length_drop]
  all_goals omega

/-- The deterministic repair loses at most one connector-length times
the payoff oscillation per incompatible join, against the very same Bob word. -/
private theorem repair_cost (G : EdgeGraph V E) (d : ℕ) (h : ConnectsAt G (d + 1))
    (p : E → F → K) {R : K} (hR₀ : 0 ≤ R) (hR : ∀ e e' f, p e f ≤ p e' f + R)
    (a : List E) (b : List F) (hb : a.length = b.length) :
    wordCost p a b ≤ wordCost p (repair G d h a) b +
      ((d + 1 : ℕ) : K) * R * (badJoins G a : K) := by
  cases a with
  | nil => simp [repair, wordCost, badJoins]
  | cons e es =>
    cases b with
    | nil => simp at hb
    | cons f fs =>
      have hind := repairAfter_cost G d h p hR₀ hR e es fs (by simpa using hb)
      simp only [repair, wordCost, List.zipWith_cons_cons, List.sum_cons, badJoins] at hind ⊢
      linarith only [hind]


private theorem badFrom_eq_zero_iff (G : EdgeGraph V E) (prev : E) (a : List E) :
    badFrom G prev a = 0 ↔ ∃ t, follows G (G.target prev) a t := by
  induction a generalizing prev with
  | nil => simp [badFrom, follows]
  | cons e es ih =>
    by_cases he : G.target prev = G.source e
    · simpa [badFrom, follows, he] using ih e
    · have hs : G.source e ≠ G.target prev := Ne.symm he
      simp [badFrom, follows, he, hs]

private theorem badJoins_eq_zero_iff (G : EdgeGraph V E) [Nonempty V] (a : List E) :
    badJoins G a = 0 ↔ Legal G a := by
  rw [legal_iff_follows]
  cases a with
  | nil =>
    exact ⟨fun _ => let v : V := Classical.choice inferInstance; ⟨v, v, rfl⟩, fun _ => rfl⟩
  | cons e es =>
    change badFrom G e es = 0 ↔ ∃ s t, G.source e = s ∧ follows G (G.target e) es t
    rw [badFrom_eq_zero_iff]
    exact ⟨fun ⟨t, ht⟩ => ⟨_, t, rfl, ht⟩, fun ⟨_, t, _, ht⟩ => ⟨t, ht⟩⟩

/-- Bob remembers a freely chosen Alice vertex on each end of each edge. -/
private def liftGraph (Y : EdgeGraph W F) (V : Type*) : EdgeGraph (W × V) (F × V × V) where
  source f := (Y.source f.1, f.2.1)
  target f := (Y.target f.1, f.2.2)

open Classical in
private noncomputable def entryCharge (X : EdgeGraph V E) (C : K) (u : V) : List E → K
  | [] => 0
  | e :: _ => if u = X.source e then 0 else C

open Classical in
private noncomputable def exitCharge (X : EdgeGraph V E) (H : K) (v : V) (e : E) : K :=
  if v = X.target e then 0 else H

/-- Pay the original score, subtract a charge for an incompatible entry,
and add a larger charge for a noncanonical exit. -/
private noncomputable def liftPayoff (X : EdgeGraph V E) (p : E → F → K) (C H : K)
    (e : E) (f : F × V × V) : K :=
  p e f.1 - entryCharge X C f.2.1 [e] + exitCharge X H f.2.2 e

open Classical in
/-- The free initial register contributes this common boundary charge.
The empty word incurs no charge. -/
noncomputable def boundary (V : Type*) (C : K) (n : ℕ) : K :=
  if n = 0 ∨ Subsingleton V then 0 else C

omit [IsStrictOrderedRing K] in
private theorem entry_le_boundary (X : EdgeGraph V E) {C : K} (hC : 0 ≤ C)
    (u : V) (a : List E) : entryCharge X C u a ≤ boundary V C a.length := by
  cases a with
  | nil => simp [entryCharge, boundary]
  | cons e es =>
    by_cases hv : Subsingleton V
    · simp [entryCharge, boundary, hv, @Subsingleton.elim V hv u (X.source e)]
    · simp only [entryCharge, boundary, List.length_cons, Nat.succ_ne_zero,
        false_or, hv, ite_false]
      split <;> simp_all

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem entry_eq_boundary (X : EdgeGraph V E) [Nonempty V] (C : K) (a : List E) :
    ∃ u, entryCharge X C u a = boundary V C a.length := by
  cases a with
  | nil => exact ⟨Classical.choice inferInstance, by simp [entryCharge, boundary]⟩
  | cons e es =>
    by_cases hv : Subsingleton V
    · exact ⟨X.source e, by simp [entryCharge, boundary, hv]⟩
    · have h : ∃ u, u ≠ X.source e := by
        by_contra! h
        exact hv ⟨fun x y => (h x).trans (h y).symm⟩
      obtain ⟨u, hu⟩ := h
      exact ⟨u, by simp [entryCharge, boundary, hv, hu]⟩

private theorem joinCharge_cons (X : EdgeGraph V E) (C : K) (e : E) (a : List E) :
    C * (badJoins X (e :: a) : K) =
      C * (badJoins X a : K) + entryCharge X C (X.target e) a := by
  cases a with
  | nil => simp [badJoins, badFrom, entryCharge]
  | cons f fs =>
    simp only [badJoins, badFrom, entryCharge, Nat.cast_add, mul_add]
    split <;> simp [add_comm]

private theorem entry_le_exit_add_entry (X : EdgeGraph V E) {C H : K}
    (hC : 0 ≤ C) (hCH : C ≤ H) (v : V) (e : E) (a : List E) :
    entryCharge X C v a ≤ exitCharge X H v e + entryCharge X C (X.target e) a := by
  by_cases hv : v = X.target e
  · simp [hv, exitCharge]
  · rw [exitCharge, ite_eq_right hv]
    cases a with
    | nil => simpa [entryCharge] using hC.trans hCH
    | cons f fs =>
      simp only [entryCharge]
      split <;> split <;> linarith only [hC, hCH]

private theorem follows_project (Y : EdgeGraph W F) {s t : W × V}
    {b : List (F × V × V)} (hb : follows (liftGraph Y V) s b t) :
    follows Y s.1 (b.map Prod.fst) t.1 := by
  induction b generalizing s with
  | nil => exact congrArg Prod.fst hb
  | cons f fs ih => exact ⟨congrArg Prod.fst hb.1, ih hb.2⟩

private theorem lifted_cost_lower (X : EdgeGraph V E) (Y : EdgeGraph W F)
    (p : E → F → K) {C H : K} (hC : 0 ≤ C) (hCH : C ≤ H)
    (a : List E) (b : List (F × V × V)) (hlen : a.length = b.length)
    (s t : W × V) (hb : follows (liftGraph Y V) s b t) :
    wordCost p a (b.map Prod.fst) - C * (badJoins X a : K) - entryCharge X C s.2 a ≤
      wordCost (liftPayoff X p C H) a b := by
  induction a generalizing s b with
  | nil => simp [wordCost, badJoins, entryCharge]
  | cons e es ih =>
    cases b with
    | nil => simp at hlen
    | cons f fs =>
      have hs : f.2.1 = s.2 := congrArg Prod.snd hb.1
      have hi := ih fs (by simpa using hlen) _ hb.2
      dsimp only [liftGraph] at hi
      have htrade := entry_le_exit_add_entry X hC hCH f.2.2 e es
      rw [joinCharge_cons]
      change p e f.1 + wordCost p es (fs.map Prod.fst) -
        (C * (badJoins X es : K) + entryCharge X C (X.target e) es) -
        entryCharge X C s.2 [e] ≤
        p e f.1 - entryCharge X C f.2.1 [e] + exitCharge X H f.2.2 e +
          wordCost (liftPayoff X p C H) es fs
      rw [hs]
      linarith only [hi, htrade]

private def canonicalLift (X : EdgeGraph V E) (u : V) : List E → List F → List (F × V × V)
  | e :: es, f :: fs => (f, u, X.target e) :: canonicalLift X (X.target e) es fs
  | _, _ => []

private theorem canonicalLift_spec (X : EdgeGraph V E) (Y : EdgeGraph W F)
    (p : E → F → K) (C H : K) (a : List E) (b : List F) (hlen : a.length = b.length)
    (s t : W) (hb : follows Y s b t) (u : V) :
    let c := canonicalLift X u a b
    c.length = a.length ∧ (∃ v, follows (liftGraph Y V) (s, u) c (t, v)) ∧
      wordCost (liftPayoff X p C H) a c =
        wordCost p a b - C * (badJoins X a : K) - entryCharge X C u a := by
  induction a generalizing b s u with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, ⟨u, Prod.ext hb rfl⟩, by simp [wordCost, badJoins, entryCharge]⟩
    | cons f fs => simp at hlen
  | cons e es ih =>
    cases b with
    | nil => simp at hlen
    | cons f fs =>
      obtain ⟨hc, ⟨v, hv⟩, hcost⟩ := ih fs (by simpa using hlen) _ hb.2 (X.target e)
      refine ⟨by simp [canonicalLift, hc], ⟨v, Prod.ext hb.1 rfl, hv⟩, ?_⟩
      rw [joinCharge_cons]
      change p e f - entryCharge X C u [e] + exitCharge X H (X.target e) e +
        wordCost (liftPayoff X p C H) es (canonicalLift X (X.target e) es fs) = _
      change wordCost (liftPayoff X p C H) es (canonicalLift X (X.target e) es fs) = _ at hcost
      rw [hcost]
      simp only [exitCharge, eq_self, ite_true, add_zero]
      change _ = p e f + wordCost p es fs -
        (C * (badJoins X es : K) + entryCharge X C (X.target e) es) - entryCharge X C u [e]
      ring

private def IsMinimum (Y : EdgeGraph W F) (p : E → F → K) (a : List E) (m : K) : Prop :=
  (∃ b, Legal Y b ∧ b.length = a.length ∧ wordCost p a b = m) ∧
    ∀ b, Legal Y b → b.length = a.length → m ≤ wordCost p a b

omit [IsStrictOrderedRing K] in
private theorem exists_minimum (Y : EdgeGraph W F) [Nonempty W] [Finite F] (d : ℕ)
    (hY : ConnectsAt Y (d + 1)) (p : E → F → K) (a : List E) :
    ∃ m, IsMinimum Y p a m := by
  classical
  let paths : Set (List F) := {b | Legal Y b ∧ b.length = a.length}
  have hfinite : paths.Finite :=
    (List.finite_length_le F a.length).subset (fun b hb => (show b.length = _ from hb.2).le)
  obtain ⟨s⟩ := ‹Nonempty W›
  obtain ⟨t, q, hq⟩ := walksFrom Y d hY a.length s
  have hnonempty : paths.Nonempty := ⟨q.edges, ⟨s, t, q, rfl⟩, by simpa using hq⟩
  obtain ⟨b, hb, hbmin⟩ := paths.exists_min_image (wordCost p a) hfinite hnonempty
  exact ⟨_, ⟨b, hb.1, hb.2, rfl⟩, fun b' hb' hl => hbmin b' ⟨hb', hl⟩⟩

omit [IsStrictOrderedRing K] in
private theorem minimum_unique {Y : EdgeGraph W F} {p : E → F → K} {a : List E} {m m' : K}
    (h : IsMinimum Y p a m) (h' : IsMinimum Y p a m') : m = m' := by
  obtain ⟨b, hb, hl, rfl⟩ := h.1
  obtain ⟨b', hb', hl', rfl⟩ := h'.1
  exact le_antisymm (h.2 b' hb' hl') (h'.2 b hb hl)

/-- The worst payoff over all original Bob walks of the specified length. -/
noncomputable def freeMinimum (Y : EdgeGraph W F) [Nonempty W] [Finite F] (d : ℕ)
    (hY : ConnectsAt Y (d + 1)) (p : E → F → K) (a : List E) : K :=
  Classical.choose (exists_minimum Y d hY p a)

omit [IsStrictOrderedRing K] in
private theorem freeMinimum_spec (Y : EdgeGraph W F) [Nonempty W] [Finite F] (d : ℕ)
    (hY : ConnectsAt Y (d + 1)) (p : E → F → K) (a : List E) :
    IsMinimum Y p a (freeMinimum Y d hY p a) :=
  Classical.choose_spec (exists_minimum Y d hY p a)

private theorem lifted_minimum (X : EdgeGraph V E) [Nonempty V] (Y : EdgeGraph W F)
    (p : E → F → K) {C H m : K} (hC : 0 ≤ C) (hCH : C ≤ H) (a : List E)
    (hm : IsMinimum Y p a m) :
    IsMinimum (liftGraph Y V) (liftPayoff X p C H) a
      (m - C * (badJoins X a : K) - boundary V C a.length) := by
  constructor
  · obtain ⟨b, hb, hlen, hcost⟩ := hm.1
    obtain ⟨s, t, hp⟩ := (legal_iff_follows Y b).1 hb
    obtain ⟨u, hu⟩ := entry_eq_boundary X C a
    obtain ⟨hc, ⟨v, hv⟩, hc'⟩ := canonicalLift_spec X Y p C H a b hlen.symm s t hp u
    exact ⟨_, (legal_iff_follows _ _).2 ⟨(s, u), (t, v), hv⟩, hc,
      hc'.trans (by rw [hcost, hu])⟩
  · intro b hb hlen
    obtain ⟨s, t, hs⟩ := (legal_iff_follows _ _).1 hb
    have hproject := (legal_iff_follows Y _).2 ⟨_, _, follows_project Y hs⟩
    have hbase := hm.2 _ hproject (by simpa using hlen)
    have hentry := entry_le_boundary X hC s.2 a
    have hcost := lifted_cost_lower X Y p hC hCH a b hlen.symm s t hs
    linarith only [hbase, hentry, hcost]

private theorem lift_connectsAt (Y : EdgeGraph W F) (V : Type*) (d : ℕ)
    (hY : ConnectsAt Y (d + 1)) : ConnectsAt (liftGraph Y V) (d + 1) := by
  intro s t
  obtain ⟨p, hp⟩ := hY s.1 t.1
  have lift_nonempty {i j : W} (q : Y.Walk i j) (hq : 0 < q.length) (u v : V) :
      ∃ r : (liftGraph Y V).Walk (i, u) (j, v), r.length = q.length := by
    induction q generalizing v with
    | nil => simp at hq
    | @concat j q f hf ih =>
      by_cases hn : 0 < q.length
      · obtain ⟨r, hr⟩ := ih hn u
        exact ⟨r.concat (f, u, v) (Prod.ext hf rfl), by simp [hr]⟩
      · cases q with
        | nil => exact ⟨.concat .nil (f, u, v) (Prod.ext hf rfl), rfl⟩
        | concat => simp at hn
  obtain ⟨r, hr⟩ := lift_nonempty p (by omega) s.2 t.2
  exact ⟨r, hr.trans hp⟩

/-- The actual lifted minimum equals the original free-endpoint minimum
minus the incompatible-join charge and the exact common boundary charge. -/
private theorem lifted_freeMinimum (X : EdgeGraph V E) [Finite V] [Nonempty V]
    (Y : EdgeGraph W F) [Nonempty W] [Finite F] (d : ℕ) (hY : ConnectsAt Y (d + 1))
    (p : E → F → K) {C H : K} (hC : 0 ≤ C) (hCH : C ≤ H) (a : List E) :
    freeMinimum (liftGraph Y V) d (lift_connectsAt Y V d hY) (liftPayoff X p C H) a =
      freeMinimum Y d hY p a - C * (badJoins X a : K) - boundary V C a.length :=
  minimum_unique (freeMinimum_spec _ d _ _ a)
    (lifted_minimum X Y p hC hCH a (freeMinimum_spec Y d hY p a))

private theorem minimum_repair (X : EdgeGraph V E) [Nonempty V] (Y : EdgeGraph W F)
    [Nonempty W] [Finite F] (d dY : ℕ) (hX : ConnectsAt X (d + 1))
    (hY : ConnectsAt Y (dY + 1)) (p : E → F → K) {R : K} (hR₀ : 0 ≤ R)
    (hR : ∀ e e' f, p e f ≤ p e' f + R) (a : List E) :
    freeMinimum Y dY hY p a ≤ freeMinimum Y dY hY p (repair X d hX a) +
      ((d + 1 : ℕ) : K) * R * (badJoins X a : K) := by
  obtain ⟨b, hb, hlen, hcost⟩ := (freeMinimum_spec Y dY hY p (repair X d hX a)).1
  have hlen' := hlen.trans (repair_walk X d hX a).1
  have hle := (freeMinimum_spec Y dY hY p a).2 b hb hlen'
  have hrep := repair_cost X d hX p hR₀ hR a b hlen'.symm
  rw [hcost] at hrep
  exact hle.trans hrep

/-- The corrected lifted payoff agrees with the original score on legal
words, and any illegal word is strictly beaten by its same-length repair. -/
private theorem lifted_repair_strict (X : EdgeGraph V E) [Finite V] [Nonempty V]
    (Y : EdgeGraph W F) [Nonempty W] [Finite F] (d dY : ℕ)
    (hX : ConnectsAt X (d + 1)) (hY : ConnectsAt Y (dY + 1)) (p : E → F → K)
    {R C H : K} (hR₀ : 0 ≤ R) (hR : ∀ e e' f, p e f ≤ p e' f + R)
    (hC : ((d + 1 : ℕ) : K) * R < C) (hCH : C ≤ H) (a : List E) :
    let corrected := fun w : List E =>
      freeMinimum (liftGraph Y V) dY (lift_connectsAt Y V dY hY) (liftPayoff X p C H) w +
        boundary V C w.length
    (Legal X a → corrected a = freeMinimum Y dY hY p a) ∧
    (¬ Legal X a → corrected a < corrected (repair X d hX a)) := by
  have hC₀ : 0 ≤ C := (mul_nonneg (Nat.cast_nonneg _) hR₀).trans hC.le
  have hlegal (w : List E) (hw : Legal X w) :
      freeMinimum (liftGraph Y V) dY (lift_connectsAt Y V dY hY) (liftPayoff X p C H) w +
        boundary V C w.length = freeMinimum Y dY hY p w := by
    rw [lifted_freeMinimum X Y dY hY p hC₀ hCH, (badJoins_eq_zero_iff X w).2 hw]
    simp
  refine ⟨hlegal a, fun ha => ?_⟩
  dsimp only
  rw [lifted_freeMinimum X Y dY hY p hC₀ hCH, hlegal _ (repair_walk X d hX a).2]
  have hk : 0 < (badJoins X a : K) := by
    exact_mod_cast Nat.pos_of_ne_zero ((badJoins_eq_zero_iff X a).not.mpr ha)
  have hp := mul_lt_mul_of_pos_right hC hk
  have hr := minimum_repair X Y d dY hX hY p hR₀ hR a
  linarith only [hp, hr]

/-! Completing the lifted Bob graph. -/

private def completeGraph (W : Type*) : EdgeGraph W (W × W) := ⟨Prod.fst, Prod.snd⟩

private theorem complete_connects (W : Type*) : ConnectsAt (completeGraph W) 1 :=
  fun i j => ⟨.concat .nil (i, j) rfl, rfl⟩

private def parallelEdges (Y : EdgeGraph W F) (i j : W) : Set F :=
  {f | Y.source f = i ∧ Y.target f = j}

omit [CommRing K] [IsStrictOrderedRing K] in
private theorem exists_parallel_min (Y : EdgeGraph W F) [Finite F] (q : F → K)
    {i j : W} (h : (parallelEdges Y i j).Nonempty) :
    ∃ f ∈ parallelEdges Y i j, ∀ f' ∈ parallelEdges Y i j, q f ≤ q f' :=
  (parallelEdges Y i j).exists_min_image q (Set.toFinite _) h

/-- One complete min-plus matrix per Alice edge. Existing entries are the
minimum over the corresponding parallel Bob edges. Missing entries cost J. -/
private noncomputable def completeMatrices (Y : EdgeGraph W F) [Finite F] (q : E → F → K)
    (J : K) (e : E) : Matrix W W K := by
  classical
  exact fun i j => if h : (parallelEdges Y i j).Nonempty then
    q e (Classical.choose (exists_parallel_min Y (q e) h)) else J

omit [IsStrictOrderedRing K] in
private theorem complete_existing (Y : EdgeGraph W F) [Finite F] (q : E → F → K)
    (J : K) (e : E) {i j : W} (h : (parallelEdges Y i j).Nonempty) :
    ∃ f ∈ parallelEdges Y i j,
      completeMatrices Y q J e i j = q e f ∧
      ∀ f' ∈ parallelEdges Y i j, q e f ≤ q e f' := by
  classical
  obtain ⟨hf, hmin⟩ := Classical.choose_spec (exists_parallel_min Y (q e) h)
  exact ⟨_, hf, by simp [completeMatrices, h], hmin⟩

private def matrixCost (A : E → Matrix W W K) (e : E) (f : W × W) : K :=
  A e f.1 f.2

/-- Free-endpoint readout of a min-plus product. Expanding the product
takes the minimum of the entry sums over complete vertex walks. -/
noncomputable def matrixMinimum (A : E → Matrix W W K) [Finite W] [Nonempty W] (a : List E) : K :=
  freeMinimum (completeGraph W) 0 (complete_connects W) (matrixCost A) a

private theorem follows_complete (Y : EdgeGraph W F) {i j : W} {b : List F}
    (hb : follows Y i b j) :
    follows (completeGraph W) i (b.map fun f => (Y.source f, Y.target f)) j := by
  induction b generalizing i with
  | nil => exact hb
  | cons f fs ih => exact ⟨hb.1, ih hb.2⟩

private theorem complete_cost_le (Y : EdgeGraph W F) [Finite F] (q : E → F → K)
    (J : K) (a : List E) (b : List F) :
    wordCost (matrixCost (completeMatrices Y q J)) a
      (b.map fun f => (Y.source f, Y.target f)) ≤ wordCost q a b := by
  induction a generalizing b with
  | nil => rfl
  | cons e es ih =>
    cases b with
    | nil => rfl
    | cons f fs =>
      obtain ⟨_, _, heq, hmin⟩ := complete_existing Y q J e
        (show (parallelEdges Y (Y.source f) (Y.target f)).Nonempty from ⟨f, rfl, rfl⟩)
      apply add_le_add _ (ih fs)
      exact heq.le.trans (hmin f ⟨rfl, rfl⟩)

private theorem complete_realized (Y : EdgeGraph W F) [Finite F] (q : E → F → K)
    (J : K) (a : List E) {b : List (W × W)} (hlen : b.length = a.length)
    (hreal : ∀ f ∈ b, (parallelEdges Y f.1 f.2).Nonempty)
    {i j : W} (hb : follows (completeGraph W) i b j) :
    ∃ c, c.length = a.length ∧ follows Y i c j ∧
      wordCost q a c = wordCost (matrixCost (completeMatrices Y q J)) a b := by
  induction a generalizing b i with
  | nil =>
    have hnil : b = [] := List.length_eq_zero_iff.mp hlen
    subst b
    exact ⟨[], rfl, hb, rfl⟩
  | cons e es ih =>
    cases b with
    | nil => simp at hlen
    | cons f fs =>
      obtain ⟨g, hg, heq, _⟩ := complete_existing Y q J e (hreal f (List.mem_cons_self ..))
      obtain ⟨c, hc, hcwalk, hcost⟩ := ih (by simpa using hlen)
        (fun x hx => hreal x (List.mem_cons_of_mem _ hx)) hb.2
      refine ⟨g :: c, by simp [hc], ⟨hg.1.trans hb.1, hg.2.symm ▸ hcwalk⟩, ?_⟩
      change q e g + wordCost q es c =
        completeMatrices Y q J e f.1 f.2 + wordCost (matrixCost (completeMatrices Y q J)) es fs
      rw [heq, hcost]

private theorem wordCost_le_mul (q : E → F → K) (hi : K)
    (hhi : ∀ e f, q e f ≤ hi) (a : List E) (b : List F) (hlen : a.length = b.length) :
    wordCost q a b ≤ (b.length : K) * hi := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [wordCost]
  | cons e es ih =>
    cases b with
    | nil => simp at hlen
    | cons f fs =>
      have ht := ih fs (by simpa using hlen)
      have hh := hhi e f
      change q e f + wordCost q es fs ≤ _
      rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith only [ht, hh]

private theorem mul_le_wordCost (q : E → F → K) (lo : K)
    (hlo : ∀ e f, lo ≤ q e f) (a : List E) (b : List F) (hlen : a.length = b.length) :
    (b.length : K) * lo ≤ wordCost q a b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [wordCost]
  | cons e es ih =>
    cases b with
    | nil => simp at hlen
    | cons f fs =>
      have ht := ih fs (by simpa using hlen)
      have hh := hlo e f
      change _ ≤ q e f + wordCost q es fs
      rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith only [ht, hh]

private theorem missing_cost_lower (Y : EdgeGraph W F) [Finite F] (q : E → F → K)
    {lo J : K} (hlo : ∀ e f, lo ≤ q e f) (hJ : lo ≤ J)
    (a : List E) (b : List (W × W)) (hlen : a.length = b.length)
    (hmissing : ∃ f ∈ b, ¬ (parallelEdges Y f.1 f.2).Nonempty) :
    J + ((b.length - 1 : ℕ) : K) * lo ≤ wordCost (matrixCost (completeMatrices Y q J)) a b := by
  classical
  let cost := matrixCost (completeMatrices Y q J)
  have hall : ∀ e f, lo ≤ cost e f := by
    intro e f
    by_cases hf : (parallelEdges Y f.1 f.2).Nonempty
    · obtain ⟨g, _, hg, _⟩ := complete_existing Y q J e hf
      exact (hlo e g).trans hg.ge
    · simpa [cost, matrixCost, completeMatrices, hf] using hJ
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons e es ih =>
    cases b with
    | nil => simp at hlen
    | cons f fs =>
      have hlen' : es.length = fs.length := by simpa using hlen
      by_cases hf : (parallelEdges Y f.1 f.2).Nonempty
      · have ht : ∃ g ∈ fs, ¬ (parallelEdges Y g.1 g.2).Nonempty := by
          obtain ⟨g, hg, hg'⟩ := hmissing
          rcases List.mem_cons.mp hg with rfl | hg
          · exact (hg' hf).elim
          · exact ⟨g, hg, hg'⟩
        have hfs : 0 < fs.length := List.length_pos_iff.mpr (by rintro rfl; simp at ht)
        have hlo' := hall e f
        have hind := ih fs hlen' ht
        change J + (fs.length : K) * lo ≤ cost e f + wordCost cost es fs
        conv_lhs => rw [show fs.length = fs.length - 1 + 1 by omega, Nat.cast_add, Nat.cast_one,
          add_mul, one_mul]
        linarith only [hlo', hind]
      · have heq : cost e f = J := by simp [cost, matrixCost, completeMatrices, hf]
        change J + (fs.length : K) * lo ≤ cost e f + wordCost cost es fs
        rw [heq]
        exact add_le_add_right (mul_le_wordCost cost lo hall es fs hlen') J

private theorem follows_split (G : EdgeGraph V E) {s t : V} {a b : List E}
    (h : follows G s (a ++ b) t) : ∃ u, follows G s a u ∧ follows G u b t := by
  induction a generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons e es ih =>
    obtain ⟨u, hu, hu'⟩ := ih h.2
    exact ⟨u, ⟨h.1, hu⟩, hu'⟩

private theorem window_with (b : List F) {f : F} (hf : f ∈ b)
    {L : ℕ} (hL : 0 < L) (hb : L ≤ b.length) :
    ∃ u v w, b = u ++ v ++ w ∧ v.length = L ∧ f ∈ v := by
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hf
  let i := min k (b.length - L)
  have hi : i ≤ k := min_le_left _ _
  have hiv : k - i < L := by
    dsimp [i]
    omega
  have hiL : L ≤ (b.drop i).length := by
    simp only [List.length_drop]
    dsimp [i]
    omega
  let v := (b.drop i).take L
  have hv : v.length = L := by dsimp only [v]; rw [List.length_take, Nat.min_eq_left hiL]
  refine ⟨b.take i, v, (b.drop i).drop L, ?_, hv, ?_⟩
  · rw [List.append_assoc]
    simp [v]
  · have h : k - i < v.length := by omega
    apply List.mem_iff_getElem.mpr
    refine ⟨k - i, h, ?_⟩
    simpa [v, Nat.add_sub_of_le hi, Nat.add_comm (k - i) i] using he

private theorem complete_best_has_no_missing (Y : EdgeGraph W F) [Finite W] [Nonempty W]
    [Finite F] (d : ℕ) (hY : ConnectsAt Y (d + 1)) (q : E → F → K)
    {lo hi J : K} (hlo : ∀ e f, lo ≤ q e f) (hhi : ∀ e f, q e f ≤ hi)
    (hlohi : lo ≤ hi) (hJ : hi + (d : K) * (hi - lo) < J)
    (a : List E) (b : List (W × W)) (hb : Legal (completeGraph W) b)
    (hlen : b.length = a.length)
    (hbest : ∀ c, Legal (completeGraph W) c → c.length = a.length →
      wordCost (matrixCost (completeMatrices Y q J)) a b ≤
        wordCost (matrixCost (completeMatrices Y q J)) a c) :
    ∀ f ∈ b, (parallelEdges Y f.1 f.2).Nonempty := by
  classical
  intro f hf
  by_contra hmissing
  let cost := matrixCost (completeMatrices Y q J)
  have hjlo : lo ≤ J := by
    have hn := mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hlohi)
    linarith only [hJ, hlohi, hn]
  have beats {n : ℕ} (hn : 0 < n) (hnd : n ≤ d + 1) :
      (n : K) * hi < J + ((n - 1 : ℕ) : K) * lo := by
    have hcast : ((n - 1 : ℕ) : K) + 1 = (n : K) := by
      exact_mod_cast (show n - 1 + 1 = n by omega)
    have hcast' : ((n - 1 : ℕ) : K) ≤ (d : K) := by
      exact_mod_cast (show n - 1 ≤ d by omega)
    have hmul := mul_le_mul_of_nonneg_right hcast' (sub_nonneg.mpr hlohi)
    have heq : (n : K) * hi = (((n - 1 : ℕ) : K) + 1) * hi := by rw [hcast]
    linarith only [hJ, hmul, heq]
  by_cases hlong : d + 1 ≤ b.length
  · obtain ⟨u, v, w, he, hv, hfv⟩ := window_with b hf (by omega) hlong
    obtain ⟨i, j, hpath⟩ := (legal_iff_follows _ _).1 hb
    rw [he] at hpath hlen
    obtain ⟨t, huv, hw⟩ := follows_split _ hpath
    obtain ⟨s, hu, hvpath⟩ := follows_split _ huv
    obtain ⟨r, hr⟩ := hY s t
    let r' := r.edges.map fun g => (Y.source g, Y.target g)
    have hr' : r'.length = v.length := by simp [r', hr, hv]
    have hclegal : Legal (completeGraph W) (u ++ r' ++ w) :=
      (legal_iff_follows _ _).2 ⟨i, j, follows_append _ (follows_append _ hu
        (follows_complete Y (follows_edges Y r))) hw⟩
    have hc := hbest (u ++ r' ++ w) hclegal (by simpa [hr'] using hlen)
    let x := a.take u.length
    let y := (a.drop u.length).take v.length
    let z := (a.drop u.length).drop v.length
    have ha : a = x ++ y ++ z := by rw [List.append_assoc]; simp [x, y, z]
    simp only [List.length_append] at hlen
    have hx : x.length = u.length := by simp [x, List.length_take]; omega
    have hy : y.length = v.length := by simp [y, List.length_take, List.length_drop]; omega
    have huvlen : (x ++ y).length = (u ++ v).length := by simp [hx, hy]
    have hur := (wordCost_append cost hx (a' := y) (b' := r'))
    have huvr : (x ++ y).length = (u ++ r').length := by simp [hx, hy, hr']
    have hbest' : wordCost cost y v ≤ wordCost cost y r' := by
      change wordCost cost a b ≤ wordCost cost a (u ++ r' ++ w) at hc
      rw [ha, he, wordCost_append cost huvlen, wordCost_append cost huvr,
        wordCost_append cost hx, hur] at hc
      linarith only [hc]
    have hmin := missing_cost_lower Y q hlo hjlo y v hy ⟨f, hfv, hmissing⟩
    have hreal := complete_cost_le Y q J y r.edges
    have hmax := wordCost_le_mul q hi hhi y r.edges (by simpa [hr, hv] using hy)
    have ht := beats (n := v.length) (by omega) (by omega)
    have hreal' : wordCost cost y r' ≤ (v.length : K) * hi :=
      hreal.trans (by simpa [hr, hv] using hmax)
    exact (not_lt_of_ge ((hmin.trans hbest').trans hreal')) ht
  · obtain ⟨s⟩ := ‹Nonempty W›
    obtain ⟨t, r, hr⟩ := walksFrom Y d hY a.length s
    let r' := r.edges.map fun g => (Y.source g, Y.target g)
    have hclegal : Legal (completeGraph W) r' :=
      (legal_iff_follows _ _).2 ⟨s, t, follows_complete Y (follows_edges Y r)⟩
    have hc : wordCost cost a b ≤ wordCost cost a r' :=
      hbest r' hclegal (by simp [r', hr])
    have hlenr : a.length = r.edges.length := by simp [hr]
    have hreal := (complete_cost_le Y q J a r.edges).trans
      (wordCost_le_mul q hi hhi a r.edges hlenr)
    have hreal' : wordCost cost a r' ≤ (b.length : K) * hi := by simpa [hr, hlen] using hreal
    have hmin := missing_cost_lower Y q hlo hjlo a b hlen.symm ⟨f, hf, hmissing⟩
    have hpos := List.length_pos_of_mem hf
    exact (not_lt_of_ge ((hmin.trans hc).trans hreal')) (beats hpos (by omega))

/-- A high missing-entry cost preserves the free-endpoint minimum at every
horizon, including horizons shorter than the common connector length. -/
private theorem matrixMinimum_eq (Y : EdgeGraph W F) [Finite W] [Nonempty W] [Finite F]
    (d : ℕ) (hY : ConnectsAt Y (d + 1)) (q : E → F → K)
    {lo hi J : K} (hlo : ∀ e f, lo ≤ q e f) (hhi : ∀ e f, q e f ≤ hi)
    (hlohi : lo ≤ hi) (hJ : hi + (d : K) * (hi - lo) < J) (a : List E) :
    matrixMinimum (completeMatrices Y q J) a = freeMinimum Y d hY q a := by
  let cost := matrixCost (completeMatrices Y q J)
  have hm := freeMinimum_spec (completeGraph W) 0 (complete_connects W) cost a
  change IsMinimum (completeGraph W) cost a (matrixMinimum (completeMatrices Y q J) a) at hm
  have hn := freeMinimum_spec Y d hY q a
  apply le_antisymm
  · obtain ⟨b, hb, hlen, hcost⟩ := hn.1
    obtain ⟨i, j, hp⟩ := (legal_iff_follows _ _).1 hb
    have hlegal := (legal_iff_follows _ _).2 ⟨i, j, follows_complete Y hp⟩
    have h := (hm.2 _ hlegal (by simpa using hlen)).trans (complete_cost_le Y q J a b)
    exact h.trans_eq hcost
  · obtain ⟨b, hb, hlen, hcost⟩ := hm.1
    have hreal := complete_best_has_no_missing Y d hY q hlo hhi hlohi hJ a b hb hlen
      (fun c hc hc' => hcost.symm ▸ hm.2 c hc hc')
    obtain ⟨i, j, hp⟩ := (legal_iff_follows _ _).1 hb
    obtain ⟨c, hc, hcwalk, heq⟩ := complete_realized Y q J a hlen hreal hp
    exact (hn.2 c ((legal_iff_follows _ _).2 ⟨i, j, hcwalk⟩) hc).trans_eq (heq.trans hcost)

/-! Maximizing the corrected matrix score. -/

private theorem edge_nonempty (G : EdgeGraph V E) [Nonempty V] (d : ℕ)
    (hG : ConnectsAt G (d + 1)) : Nonempty E := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨p, hp⟩ := hG v v
  have h : p.edges ≠ [] := by
    intro he
    have hh := p.edges_length
    simp [he, hp] at hh
  exact ⟨p.edges.head h⟩

omit [CommRing K] [IsStrictOrderedRing K] in
private theorem payoff_bounds [Finite E] [Finite F] [Nonempty E] [Nonempty F]
    (p : E → F → K) : ∃ lo hi, lo ≤ hi ∧ ∀ e f, lo ≤ p e f ∧ p e f ≤ hi := by
  classical
  let cost : E × F → K := fun x => p x.1 x.2
  let s : Set (E × F) := Set.univ
  have hfin : s.Finite := Set.toFinite _
  have hne : s.Nonempty := Set.univ_nonempty
  obtain ⟨x, _, hx⟩ := s.exists_min_image cost hfin hne
  obtain ⟨y, hy, hmax⟩ := s.exists_max_image cost hfin hne
  exact ⟨cost x, cost y, hx y hy,
    fun e f => ⟨hx (e, f) (Set.mem_univ _), hmax (e, f) (Set.mem_univ _)⟩⟩

/-- For every primitive finite graph game there is one complete matrix per
Alice edge, indexed by the product of the two vertex sets, and one charge C.
At each horizon the corrected complete-matrix maximum is the original
free-endpoint maximin. The maximizing words are exactly the original
maximizing walks. -/
theorem finite_horizon_reduction (X : EdgeGraph V E) [Finite V] [Nonempty V] [Finite E]
    (Y : EdgeGraph W F) [Finite W] [Nonempty W] [Finite F] (dX dY : ℕ)
    (hX : ConnectsAt X (dX + 1)) (hY : ConnectsAt Y (dY + 1)) (p : E → F → K) :
    ∃ (A : E → Matrix (W × V) (W × V) K) (C : K), 0 < C ∧
      (∀ a : List E, matrixMinimum A a + boundary V C a.length =
        freeMinimum Y dY hY p a - C * (badJoins X a : K)) ∧
      ∀ n, ∃ m : K,
        IsGreatest {v | ∃ a : List E, a.length = n ∧ Legal X a ∧
          freeMinimum Y dY hY p a = v} m ∧
        IsGreatest {v | ∃ a : List E, a.length = n ∧ matrixMinimum A a = v}
          (m - boundary V C n) ∧
        ∀ a : List E, a.length = n →
          (matrixMinimum A a + boundary V C n = m ↔
            Legal X a ∧ freeMinimum Y dY hY p a = m) := by
  classical
  let _ : Nonempty E := edge_nonempty X dX hX
  let _ : Nonempty F := edge_nonempty Y dY hY
  obtain ⟨pmin, pmax, hpp, hp⟩ := payoff_bounds p
  let R := pmax - pmin
  have hR : 0 ≤ R := sub_nonneg.mpr hpp
  have hosc (e e' : E) (f : F) : p e f ≤ p e' f + R := by
    have h1 := (hp e f).2
    have h2 := (hp e' f).1
    dsimp [R]
    linarith only [h1, h2]
  let C : K := ((dX + 1 : ℕ) : K) * R + 1
  have hC : ((dX + 1 : ℕ) : K) * R < C := lt_add_of_pos_right _ zero_lt_one
  have hCpos : 0 < C := (mul_nonneg (Nat.cast_nonneg _) hR).trans_lt hC
  let H := C + 1
  have hCH : C ≤ H := le_of_lt (lt_add_of_pos_right _ zero_lt_one)
  let q := liftPayoff X p C H
  let B := liftGraph Y V
  have hb := lift_connectsAt Y V dY hY
  obtain ⟨lo, hi, hlohi, hq⟩ := payoff_bounds q
  let J := hi + (dY : K) * (hi - lo) + 1
  have hJ : hi + (dY : K) * (hi - lo) < J := lt_add_of_pos_right _ zero_lt_one
  let A := completeMatrices B q J
  have hmatrix (a : List E) : matrixMinimum A a = freeMinimum B dY hb q a :=
    matrixMinimum_eq B dY hb q (fun e f => (hq e f).1) (fun e f => (hq e f).2) hlohi hJ a
  refine ⟨A, C, hCpos, ?_, fun n => ?_⟩
  · intro a
    rw [hmatrix, lifted_freeMinimum X Y dY hY p hCpos.le hCH]
    exact sub_add_cancel _ _
  let paths : Set (List E) := {a | Legal X a ∧ a.length = n}
  have hfin : paths.Finite :=
    (List.finite_length_le E n).subset (fun _ ha => ha.2.le)
  obtain ⟨s⟩ := ‹Nonempty V›
  obtain ⟨t, w, hw⟩ := walksFrom X dX hX n s
  have hne : paths.Nonempty := ⟨w.edges, ⟨s, t, w, rfl⟩, by simpa using hw⟩
  obtain ⟨best, hbest, hopt⟩ := paths.exists_max_image (freeMinimum Y dY hY p) hfin hne
  let m := freeMinimum Y dY hY p best
  have hscore (a : List E) (ha : a.length = n) :
      matrixMinimum A a + boundary V C n ≤ m ∧
        (matrixMinimum A a + boundary V C n = m ↔ Legal X a ∧ freeMinimum Y dY hY p a = m) := by
    obtain ⟨heq, hstrict⟩ := lifted_repair_strict X Y dX dY hX hY p hR hosc hC hCH a
    dsimp only at heq hstrict
    by_cases hlegal : Legal X a
    · rw [hmatrix, ← ha, heq hlegal]
      exact ⟨hopt a ⟨hlegal, ha⟩, by simp [hlegal]⟩
    · obtain ⟨hlen, hwalk⟩ := repair_walk X dX hX a
      have heq' := (lifted_repair_strict X Y dX dY hX hY p hR hosc hC hCH
        (repair X dX hX a)).1 hwalk
      have hlt : matrixMinimum A a + boundary V C n < m := by
        rw [hmatrix, ← ha]
        exact (hstrict hlegal).trans_le (heq'.trans_le (hopt _ ⟨hwalk, hlen.trans ha⟩))
      exact ⟨hlt.le, by simp [hlt.ne, hlegal]⟩
  refine ⟨m, ⟨⟨best, hbest.2, hbest.1, rfl⟩, ?_⟩,
    ⟨⟨best, hbest.2, eq_sub_of_add_eq ((hscore best hbest.2).2.2 ⟨hbest.1, rfl⟩)⟩, ?_⟩,
    fun a ha => (hscore a ha).2⟩
  · rintro v ⟨a, ha, hlegal, rfl⟩
    exact hopt a ⟨hlegal, ha⟩
  · rintro v ⟨a, ha, rfl⟩
    exact (le_sub_iff_add_le).2 (hscore a ha).1

end MeyerovitchYoungQ61Complete
