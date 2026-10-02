/- GID: D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Neutral gaps give exact legal-word histograms and terminal label fibers. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S3.Combinatorics.ArrowWilfGapData
import Mathlib.Data.Bool.Count
import Mathlib.Data.Vector.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.WindowHistogramLegalCount

open LiteralWindowEnd (Window bits first last triple flatten run endable nonzero execution)
open D5.S3.Arith.ZeckendorfFutureKernel (legal)
open D5.S3.Combinatorics.ArrowWilfGapData (Gaps)
open scoped BigOperators

/-- A gap contains no neutral input window. -/
def Free (g : List Window) : Prop := ∀ b ∈ g, b ≠ .zero ∧ b ≠ .middle

/-- The three exponents of a legal gap; the central exponent is zero or one. -/
structure Gap where
  x : ℕ
  z : Bool
  y : ℕ
  deriving DecidableEq

def gap (q : Gap) : List Window :=
  List.replicate q.x .low ++ (if q.z then [.ends] else []) ++
    List.replicate q.y .high

/-- The first gap, followed by each neutral letter and its following gap. -/
abbrev Cuts := List Window × List (Bool × List Window)

def join (p : Cuts) : List Window :=
  p.1 ++ p.2.flatMap (fun dg => triple false dg.1 false :: dg.2)

def gaps (p : Cuts) : List (List Window) := p.1 :: p.2.map Prod.snd

def Clean (p : Cuts) : Prop := ∀ g ∈ gaps p, Free g

/-- Split at actual neutral input positions, retaining every empty gap. -/
def split : List Window → Cuts
  | [] => ([], [])
  | b :: w =>
      let p := split w
      match b with
      | .zero => ([], (false, p.1) :: p.2)
      | .middle => ([], (true, p.1) :: p.2)
      | b => (b :: p.1, p.2)

private theorem gap_language (w : List Window) (hw : Free w) :
    (legal false (flatten w) ↔ ∃ q : Gap, gap q = w) ∧
    (legal true (flatten w) ↔ ∃ n : ℕ, w = List.replicate n .high) := by
  have highs (n : ℕ) (s : Bool) : legal s (flatten (List.replicate n .high)) := by
    induction n generalizing s with
    | zero => simp [flatten, legal]
    | succ n ih => simpa [List.replicate_succ, flatten, bits, legal] using ih true
  have normal (q : Gap) : legal false (flatten (gap q)) := by
    rcases q with ⟨a, z, b⟩
    induction a with
    | zero =>
      cases z
      · simpa [gap] using highs b false
      · simpa [gap, flatten, bits, legal] using highs b true
    | succ a ih => simpa [gap, List.replicate_succ, flatten, bits, legal] using ih
  have forward : ∀ w : List Window, Free w →
      (legal false (flatten w) → ∃ q : Gap, gap q = w) ∧
      (legal true (flatten w) → ∃ n : ℕ, w = List.replicate n .high) := by
    intro v
    induction v with
    | nil => intro _; exact ⟨fun _ => ⟨⟨0, false, 0⟩, rfl⟩, fun _ => ⟨0, rfl⟩⟩
    | cons d v ih =>
      intro hv
      have ht : Free v := fun b hb => hv b (List.mem_cons_of_mem d hb)
      obtain ⟨ihf, iht⟩ := ih ht
      cases d with
      | zero => exact (hv .zero (by simp)).1 rfl |>.elim
      | middle => exact (hv .middle (by simp)).2 rfl |>.elim
      | low =>
        constructor
        · intro h
          obtain ⟨q, hq⟩ := ihf (by simpa [flatten, bits, legal] using h)
          exact ⟨⟨q.x + 1, q.z, q.y⟩,
            by simpa [gap, List.replicate_succ] using congrArg (List.cons .low) hq⟩
        · simp [flatten, bits, legal]
      | ends =>
        constructor
        · intro h
          obtain ⟨n, hn⟩ := iht (by simpa [flatten, bits, legal] using h)
          exact ⟨⟨0, true, n⟩, by simp [gap, hn]⟩
        · simp [flatten, bits, legal]
      | high =>
        constructor
        · intro h
          obtain ⟨n, hn⟩ := iht (by simpa [flatten, bits, legal] using h)
          exact ⟨⟨0, false, n + 1⟩, by simp [gap, List.replicate_succ, hn]⟩
        · intro h
          obtain ⟨n, hn⟩ := iht (by simpa [flatten, bits, legal] using h)
          exact ⟨n + 1, by simp [List.replicate_succ, hn]⟩
  exact ⟨⟨(forward w hw).1, fun ⟨q, hq⟩ => hq ▸ normal q⟩,
    ⟨(forward w hw).2, fun ⟨n, hn⟩ => hn ▸ highs n true⟩⟩

private theorem split_properties (w : List Window) :
    join (split w) = w ∧ Clean (split w) ∧
    (split w).2.length = w.count .zero + w.count .middle ∧
    (∀ s : Bool, legal s (flatten w) ↔
      legal s (flatten (split w).1) ∧
        ∀ dg ∈ (split w).2, legal false (flatten dg.2)) := by
  induction w with
  | nil => simp [split, join, Clean, gaps, Free, flatten, legal]
  | cons d w ih =>
    obtain ⟨he, hc, hn, hl⟩ := ih
    rcases hp : split w with ⟨g, ds⟩
    simp only [hp, join, Clean, gaps, List.mem_cons, List.mem_map,
      forall_eq_or_imp, Prod.forall, exists_and_right, exists_eq_right] at he hc hn hl
    cases d <;>
      simp_all [split, join, Clean, gaps, Free, triple, flatten, bits, legal,
        List.count_cons, List.mem_map, List.flatMap_cons, List.cons_append]
    all_goals first | exact hc.2 | exact ⟨hc.2, by omega⟩

private theorem split_inverse (p : Cuts) (hp : Clean p) : split (join p) = p := by
  have split_prefix (g : List Window) (hg : Free g) (w : List Window) :
      split (g ++ w) = (g ++ (split w).1, (split w).2) := by
    induction g with
    | nil => simp
    | cons d g ih =>
      have hd := hg d (by simp)
      have ht : Free g := fun b hb => hg b (List.mem_cons_of_mem d hb)
      cases d <;> simp_all [split, List.cons_append]
  rcases p with ⟨g, ds⟩
  simp only [Clean, gaps, List.mem_cons, forall_eq_or_imp] at hp
  rw [join, split_prefix g hp.1]
  induction ds with
  | nil => simp [split]
  | cons dg ds ih =>
    rcases dg with ⟨d, h⟩
    have hh : Free h := hp.2 h (by simp)
    have ht : ∀ v ∈ ds.map Prod.snd, Free v := by
      intro v hv
      exact hp.2 v (by simp [hv])
    have hi := ih ⟨hp.1, ht⟩
    cases d <;> simp_all [List.flatMap_cons, triple, split, split_prefix h hh]

/-- Neutral positions determine a unique decomposition, and each legal gap
has unique low/end/high exponents. -/
private theorem decomposition :
    (∀ w : List Window, ∃! p : Cuts, Clean p ∧ join p = w) ∧
    (∀ w : List Window, (split w).2.length = w.count .zero + w.count .middle) ∧
    (∀ w : List Window, legal false (flatten w) ↔
      ∀ g ∈ gaps (split w), ∃! q : Gap, gap q = g) := by
  have injective : Function.Injective gap := by
    intro p q h
    have hx : (gap p).count .low = (gap q).count .low := congrArg (List.count .low) h
    have hy : (gap p).count .high = (gap q).count .high := congrArg (List.count .high) h
    have hz : (gap p).count .ends = (gap q).count .ends := congrArg (List.count .ends) h
    rcases p with ⟨a, z, b⟩
    rcases q with ⟨a', z', b'⟩
    cases z <;> cases z' <;>
      simp [gap, List.count_replicate] at hx hy hz <;> simp_all
  refine ⟨?_, ?_, ?_⟩
  · intro w
    refine ⟨split w, ⟨(split_properties w).2.1, (split_properties w).1⟩, ?_⟩
    intro p hp
    rw [← split_inverse p hp.1, hp.2]
  · intro w
    exact (split_properties w).2.2.1
  · intro w
    rw [(split_properties w).2.2.2 false]
    have characterize (g : List Window) (hg : Free g) :
        legal false (flatten g) ↔ ∃! q : Gap, gap q = g := by
      rw [(gap_language g hg).1]
      exact ⟨fun ⟨q, hq⟩ => ⟨q, hq, fun p hp => injective (hp.trans hq.symm)⟩,
        fun ⟨q, hq, _⟩ => ⟨q, hq⟩⟩
    have hc := (split_properties w).2.1
    unfold Clean at hc
    constructor
    · rintro ⟨hg, ht⟩ g h
      apply (characterize g (hc g h)).mp
      rcases List.mem_cons.mp h with he | h
      · simpa [he] using hg
      · obtain ⟨dg, hdg, rfl⟩ := List.mem_map.mp h
        exact ht dg hdg
    · intro h
      refine ⟨(characterize _ (hc _ (by simp [gaps]))).mpr (h _ (by simp [gaps])), ?_⟩
      intro dg hdg
      have hg : dg.2 ∈ gaps (split w) :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨dg, hdg, rfl⟩)
      exact (characterize dg.2 (hc _ hg)).mpr (h _ hg)




/-- Canonical legal gaps together with the ordered neutral letters. -/
abbrev Code := Gap × List (Bool × Gap)

def codeCuts (p : Code) : Cuts := (gap p.1, p.2.map fun dg => (dg.1, gap dg.2))
def codeWord (p : Code) : List Window := join (codeCuts p)
def readGap (g : List Window) : Gap :=
  ⟨g.count .low, decide (g.count .ends = 1), g.count .high⟩
def readCode (p : Cuts) : Code :=
  (readGap p.1, p.2.map fun dg => (dg.1, readGap dg.2))
def terminalGap (p : Code) : Gap := p.2.foldl (fun _ dg => dg.2) p.1

private theorem code_language :
    (∀ w : List Window, legal false (flatten w) ↔ ∃! p : Code, codeWord p = w) ∧
    (∀ p : Code, readCode (split (codeWord p)) = p ∧ legal false (flatten (codeWord p))) := by
  have reading (q : Gap) : readGap (gap q) = q := by
    rcases q with ⟨a, z, b⟩
    cases z <;> simp [readGap, gap, List.count_replicate]
  have clean (p : Code) : Clean (codeCuts p) := by
    rcases p with ⟨g, ds⟩
    simp only [Clean, gaps, codeCuts, List.map_map]
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · intro b hb
      cases b <;> simp_all [gap, List.mem_append, List.mem_replicate]
    · obtain ⟨dg, _, rfl⟩ := List.mem_map.mp hh
      intro b hb
      cases b <;> simp_all [gap, List.mem_append, List.mem_replicate]
  have inverse (p : Code) : readCode (split (codeWord p)) = p := by
    rw [codeWord, split_inverse _ (clean p)]
    rcases p with ⟨g, ds⟩
    simp [readCode, codeCuts, List.map_map, Function.comp_def, reading]
  have legal_code (p : Code) : legal false (flatten (codeWord p)) := by
    rw [(decomposition).2.2, codeWord, split_inverse _ (clean p)]
    intro g hg
    simp only [gaps, codeCuts, List.map_map, List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨dg, _, rfl⟩
    · exact ⟨p.1, rfl, fun q hq => by simpa [reading] using congrArg readGap hq⟩
    · exact ⟨dg.2, rfl, fun q hq => by simpa [reading] using congrArg readGap hq⟩
  refine ⟨?_, fun p => ⟨inverse p, legal_code p⟩⟩
  intro w
  constructor
  · intro hw
    have hs := split_properties w
    have restore (g : List Window) (hg : Free g) (hl : legal false (flatten g)) :
        gap (readGap g) = g := by
      obtain ⟨q, hq⟩ := (gap_language g hg).1.mp hl
      rw [← hq, reading]
    have hl := hs.2.2.2 false |>.mp hw
    have rebuilt : codeCuts (readCode (split w)) = split w := by
      apply Prod.ext
      · exact restore _ (hs.2.1 _ (by simp [Clean, gaps])) hl.1
      · simp only [codeCuts, readCode, List.map_map, Function.comp_def]
        conv_rhs => rw [← List.map_id (split w).2]
        apply List.map_congr_left
        intro dg hdg
        have hg : dg.2 ∈ gaps (split w) :=
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨dg, hdg, rfl⟩)
        simp only [restore _ (hs.2.1 _ hg) (hl.2 _ hdg), Prod.eta, id_eq]
    refine ⟨readCode (split w), ?_, ?_⟩
    · change join (codeCuts (readCode (split w))) = w
      rw [rebuilt, hs.1]
    · intro p hp
      rw [← inverse p, hp]
  · rintro ⟨p, hp, _⟩
    simpa [← hp] using legal_code p

/-- The five letter multiplicities read directly from a canonical code. -/
def inventory (p : Code) : Window → ℕ
  | .low => p.1.x + (p.2.map fun dg => dg.2.x).sum
  | .high => p.1.y + (p.2.map fun dg => dg.2.y).sum
  | .ends => (if p.1.z then 1 else 0) + (p.2.map fun dg => if dg.2.z then 1 else 0).sum
  | .zero => (p.2.map Prod.fst).count false
  | .middle => (p.2.map Prod.fst).count true

/-- The fiber consists of literal words, without quotienting or identifying positions. -/
def HistogramWords (h : Window → ℕ) :=
  {w : List Window // legal false (flatten w) ∧ ∀ f, w.count f = h f}

def HistogramCodes (h : Window → ℕ) := {p : Code // ∀ f, inventory p f = h f}

/-- An exact last-window fiber inside a literal-word histogram. -/
def EndpointWords (h : Window → ℕ) (f : Window) :=
  {w : HistogramWords h // w.val.getLast? = some f}

/-- Positive End acceptance with a zero initial seam and zero initial flag. -/
def PositiveEndpointWords (h : Window → ℕ) (f : Window) :=
  {w : EndpointWords h f // endable (run (some (false, false)) w.val.val) = true}

private theorem histogram_encoding (h : Window → ℕ) :
    (∀ p : Code, ∀ f, (codeWord p).count f = inventory p f) ∧
    (∃ e : HistogramCodes h ≃ HistogramWords h,
      ∀ p, (e p).val = codeWord p.val) := by
  have counts (p : Code) (f : Window) : (codeWord p).count f = inventory p f := by
    rcases p with ⟨g, ds⟩
    induction ds generalizing g with
    | nil => cases f <;> cases hz : g.z <;>
        simp [codeWord, codeCuts, join, inventory, gap, hz, List.count_replicate]
    | cons dg ds ih =>
      rcases dg with ⟨d, q⟩
      have he : codeWord (g, (d, q) :: ds) = gap g ++ triple false d false :: codeWord (q, ds) := by
        simp [codeWord, codeCuts, join, List.flatMap_cons]
      rw [he, List.count_append, List.count_cons, ih q]
      cases f <;> cases d <;> cases hz : g.z <;>
        simp [inventory, gap, triple, hz, List.count_replicate, List.count_cons,
          Nat.add_assoc]
  let e : HistogramCodes h ≃ HistogramWords h :=
    { toFun := fun p => ⟨codeWord p.val, (code_language.2 p.val).2,
        fun f => (counts p.val f).trans (p.property f)⟩
      invFun := fun w => ⟨readCode (split w.val), by
        obtain ⟨p, hp, _⟩ := (code_language.1 w.val).mp w.property.1
        have hr : readCode (split w.val) = p := by
          rw [← hp, (code_language.2 p).1]
        intro f
        rw [hr, ← counts p f, hp]
        exact w.property.2 f⟩
      left_inv := fun p => Subtype.ext (code_language.2 p.val).1
      right_inv := fun w => by
        apply Subtype.ext
        obtain ⟨p, hp, _⟩ := (code_language.1 w.val).mp w.property.1
        change codeWord (readCode (split w.val)) = w.val
        rw [← hp, (code_language.2 p).1] }
  exact ⟨counts, e, fun _ => rfl⟩

def rawCode {t : ℕ} (q : (Fin t → Bool) × (Fin (t + 1) → Gap)) : Code :=
  (q.2 0, List.ofFn fun i => (q.1 i, q.2 i.succ))

def histogram (a b c r s : ℕ) : LiteralWindowEnd.Window → ℕ
  | .low => a | .high => b | .ends => c | .zero => r | .middle => s
abbrev Factors (a b c r s : ℕ) :=
  {R : Finset (Fin (r + s)) // R.card = r} ×
  {Z : Finset (Fin (r + s + 1)) // Z.card = c} × Gaps (r + s + 1) a × Gaps (r + s + 1) b

def factorRaw {a b c r s : ℕ} (p : Factors a b c r s) :
    (Fin (r + s) → Bool) × (Fin (r + s + 1) → Gap) :=
  (fun i => decide (i ∉ p.1.val), fun i =>
    ⟨p.2.2.1.val i, decide (i ∈ p.2.1.val), p.2.2.2.val i⟩)


private theorem histogram_count (a b c r s : ℕ) :
    (∃ e : Factors a b c r s ≃ HistogramWords (histogram a b c r s),
      ∀ p, (e p).val = codeWord (rawCode (factorRaw p))) ∧
    Finite (HistogramWords (histogram a b c r s)) ∧
    Nat.card (HistogramWords (histogram a b c r s)) =
      (r + s).choose r * (r + s + 1).choose c *
        (r + s + 1).multichoose a * (r + s + 1).multichoose b := by
  let rawEquiv (t : ℕ) :
      {p : Code // p.2.length = t} ≃ (Fin t → Bool) × (Fin (t + 1) → Gap) := by
    let e : {p : Code // p.2.length = t} ≃ (Fin t → Bool) × (Fin (t + 1) → Gap) :=
      { toFun := fun p =>
          let v : List.Vector (Bool × Gap) t := ⟨p.val.2, p.property⟩
          (fun i => (v.get i).1, Fin.cons p.val.1 (fun i => (v.get i).2))
        invFun := fun q => ⟨rawCode q, by simp [rawCode]⟩
        left_inv := fun p => by
          apply Subtype.ext
          dsimp [rawCode]
          apply Prod.ext
          · simp
          · have hv := congrArg List.Vector.toList
              (List.Vector.ofFn_get (⟨p.val.2, p.property⟩ : List.Vector (Bool × Gap) t))
            simpa [List.Vector.toList_ofFn] using hv
        right_inv := fun q => by
          apply Prod.ext
          · funext i
            change ((List.ofFn fun j => (q.1 j, q.2 j.succ)).get
              ⟨i.val, by simpa using i.isLt⟩).1 = q.1 i
            rw [List.get_ofFn]
            congr 1
          · funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [rawCode]
            · change ((List.ofFn fun j => (q.1 j, q.2 j.succ)).get
                ⟨j.val, by simpa using j.isLt⟩).2 = q.2 j.succ
              rw [List.get_ofFn]
              congr 1 }
    exact e
  let factorEquiv (a b c r s : ℕ) :
      {q : (Fin (r + s) → Bool) × (Fin (r + s + 1) → Gap) //
        ∀ f, inventory (rawCode q) f = histogram a b c r s f} ≃ Factors a b c r s := by
    have counts {n : ℕ} (d : Fin n → Bool) (f : Bool) :
        (List.ofFn d).count f = ∑ i, if d i = f then 1 else 0 := by
      calc
        _ = ((List.ofFn d).flatMap fun x => [x]).count f := by simp
        _ = ((List.ofFn d).map fun x => if x = f then 1 else 0).sum := by
          rw [List.count_flatMap]
          simp [Function.comp_def, List.count_singleton]
        _ = _ := by simp [List.map_ofFn, List.sum_ofFn, Function.comp_def]
    have totals (q : (Fin (r + s) → Bool) × (Fin (r + s + 1) → Gap)) :
        inventory (rawCode q) .low = ∑ i, (q.2 i).x ∧
        inventory (rawCode q) .high = ∑ i, (q.2 i).y ∧
        inventory (rawCode q) .ends = ∑ i, if (q.2 i).z then 1 else 0 := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [rawCode, inventory, List.map_ofFn, List.sum_ofFn, Function.comp_def]
          using (Fin.sum_univ_succ (fun i => (q.2 i).x)).symm
      · simpa only [rawCode, inventory, List.map_ofFn, List.sum_ofFn, Function.comp_def]
          using (Fin.sum_univ_succ (fun i => (q.2 i).y)).symm
      · simp only [rawCode, inventory, List.map_ofFn, List.sum_ofFn, Function.comp_def]
        rw [Fin.sum_univ_succ]
        apply congrArg₂ Nat.add
        · by_cases hz : (q.2 0).z = true <;> simp [hz]
        · apply Finset.sum_congr rfl
          intro i _
          by_cases hz : (q.2 i.succ).z = true <;> simp [hz]
    let e : {q : (Fin (r + s) → Bool) × (Fin (r + s + 1) → Gap) //
        ∀ f, inventory (rawCode q) f = histogram a b c r s f} ≃ Factors a b c r s :=
      { toFun := fun q =>
          (⟨Finset.univ.filter (fun i => q.val.1 i = false), by
            have h := q.property .zero
            simpa [inventory, rawCode, List.map_ofFn, counts, Finset.sum_boole, histogram] using h⟩,
          ⟨Finset.univ.filter (fun i => (q.val.2 i).z = true), by
            have h := (totals q.val).2.2.symm.trans (q.property .ends)
            simpa [Finset.sum_boole, histogram] using h⟩,
          ⟨Finsupp.equivFunOnFinite.symm (fun i => (q.val.2 i).x), by
            simp only [Finset.mem_finsuppAntidiag]
            exact ⟨(totals q.val).1.symm.trans (q.property .low), Finset.subset_univ _⟩⟩,
          ⟨Finsupp.equivFunOnFinite.symm (fun i => (q.val.2 i).y), by
            simp only [Finset.mem_finsuppAntidiag]
            exact ⟨(totals q.val).2.1.symm.trans (q.property .high), Finset.subset_univ _⟩⟩)
        invFun := fun p => ⟨factorRaw p, by
          intro f
          have hx := (Finset.mem_finsuppAntidiag.mp p.2.2.1.property).1
          have hy := (Finset.mem_finsuppAntidiag.mp p.2.2.2.property).1
          cases f with
          | low => simpa [histogram, factorRaw] using (totals (factorRaw p)).1.trans hx
          | high => simpa [histogram, factorRaw] using (totals (factorRaw p)).2.1.trans hy
          | ends =>
            rw [(totals (factorRaw p)).2.2]
            simpa [histogram, factorRaw, Finset.sum_boole] using p.2.1.property
          | zero => simpa [histogram, inventory, rawCode, factorRaw, List.map_ofFn,
              counts, Finset.sum_boole] using p.1.property
          | middle =>
            have hn := List.count_false_add_count_true (List.ofFn (factorRaw p).1)
            have hz : (List.ofFn (factorRaw p).1).count false = r := by
              simpa [factorRaw, counts, Finset.sum_boole] using p.1.property
            simp only [List.length_ofFn] at hn
            have ht : (List.ofFn (factorRaw p).1).count true = s := by omega
            simpa [inventory, rawCode, List.map_ofFn, histogram, Function.comp_def] using ht⟩
        left_inv := fun q => by
          apply Subtype.ext
          apply Prod.ext
          · funext i
            dsimp [factorRaw]
            cases hi : q.val.1 i <;> simp [hi]
          · funext i
            cases hgi : q.val.2 i with
            | mk x z y => cases z <;> simp [factorRaw, hgi]
        right_inv := fun p => by
          apply Prod.ext
          · apply Subtype.ext; ext i; simp [factorRaw]
          · apply Prod.ext
            · apply Subtype.ext; ext i; simp [factorRaw]
            · apply Prod.ext <;> apply Subtype.ext <;> ext i <;> rfl }
    exact e
  let codesRawEquiv (a b c r s : ℕ) :
      HistogramCodes (histogram a b c r s) ≃
        {q : (Fin (r + s) → Bool) × (Fin (r + s + 1) → Gap) //
          ∀ f, inventory (rawCode q) f = histogram a b c r s f} := by
    have length (p : HistogramCodes (histogram a b c r s)) : p.val.2.length = r + s := by
      calc
        _ = (p.val.2.map Prod.fst).length := by simp
        _ = (p.val.2.map Prod.fst).count false + (p.val.2.map Prod.fst).count true :=
          (List.count_false_add_count_true _).symm
        _ = r + s := by
          change inventory p.val .zero + inventory p.val .middle = r + s
          rw [p.property .zero, p.property .middle]
          rfl
    let e := rawEquiv (r + s)
    exact
      { toFun := fun p => ⟨e ⟨p.val, length p⟩, by
          have hr := congrArg Subtype.val (e.symm_apply_apply ⟨p.val, length p⟩)
          change rawCode (e ⟨p.val, length p⟩) = p.val at hr
          rw [hr]
          exact p.property⟩
        invFun := fun q => ⟨rawCode q.val, q.property⟩
        left_inv := fun p => by
          apply Subtype.ext
          have hr := congrArg (fun q : {p : Code // p.2.length = r + s} => q.val)
            (e.symm_apply_apply ⟨p.val, length p⟩)
          change rawCode (e ⟨p.val, length p⟩) = p.val at hr
          exact hr
        right_inv := fun q => by
          apply Subtype.ext
          exact e.apply_symm_apply q.val }
  obtain ⟨words, hw⟩ := (histogram_encoding (histogram a b c r s)).2
  let e := ((codesRawEquiv a b c r s).trans (factorEquiv a b c r s)).symm.trans words
  refine ⟨⟨e, ?_⟩, Finite.of_equiv _ e, ?_⟩
  · intro p
    change (words _).val = codeWord (rawCode (factorRaw p))
    exact hw _
  · classical
    rw [Nat.card_congr e.symm]
    have cg (n k : ℕ) : Nat.card (Gaps n k) = n.multichoose k := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      simpa using Finset.card_finsuppAntidiag_nat_eq_multichoose
        (s := (Finset.univ : Finset (Fin n))) k
    simp only [Factors, Nat.card_prod, cg]
    simp [Nat.card_eq_fintype_card, Fintype.card_finset_len, Nat.mul_assoc]

example (q : Option (Bool × Bool)) (w : List Window) :
    run q w = w.foldl LiteralWindowEnd.step q := by
  rfl

/-- Unique neutral-position decomposition and a reversible canonical code
that counts every histogram and retains exact terminal constraints and labels. -/
theorem result :
    (∀ w : List Window, ∃! p : Cuts, Clean p ∧ join p = w) ∧
    (∀ w : List Window, (split w).2.length = w.count .zero + w.count .middle) ∧
    (∀ w : List Window, legal false (flatten w) ↔
      ∀ g ∈ gaps (split w), ∃! q : Gap, gap q = g) ∧
    (∀ w : List Window, legal false (flatten w) ↔ ∃! p : Code, codeWord p = w) ∧
    (∀ p : Code, (codeWord p).getLast? = some .low ↔
      0 < (terminalGap p).x ∧ (terminalGap p).z = false ∧ (terminalGap p).y = 0) ∧
    (∀ p : Code, (codeWord p).getLast? = some .ends ↔
      (terminalGap p).z = true ∧ (terminalGap p).y = 0) ∧
    (∀ p : Code, ∀ f, (codeWord p).count f = inventory p f) ∧
    (∀ h : Window → ℕ, ∃ e : HistogramCodes h ≃ HistogramWords h,
      ∀ p, (e p).val = codeWord p.val) ∧
    (∀ a b c r s : ℕ,
      (∃ e : Factors a b c r s ≃ HistogramWords (histogram a b c r s),
        ∀ p, (e p).val = codeWord (rawCode (factorRaw p))) ∧
      Finite (HistogramWords (histogram a b c r s)) ∧
      Nat.card (HistogramWords (histogram a b c r s)) =
        (r + s).choose r * (r + s + 1).choose c *
          (r + s + 1).multichoose a * (r + s + 1).multichoose b) ∧
    (∀ a b c r s : ℕ, 0 < a + b + c + r + s →
      (∑ f : Window, Nat.card (EndpointWords (histogram a b c r s) f)) =
        Nat.card (HistogramWords (histogram a b c r s))) ∧
    (Nat.card (HistogramWords (histogram 0 0 0 0 0)) = 1 ∧
      ∀ w : HistogramWords (histogram 0 0 0 0 0), w.val = []) ∧
    (∀ h : Window → ℕ, ∀ f : Window, h f = 0 → IsEmpty (EndpointWords h f)) ∧
    (∀ a b c r s : ℕ, r + s + 1 < c → IsEmpty (HistogramWords (histogram a b c r s))) ∧
    (∀ h : Window → ℕ, ∀ f : Window,
      Nat.card (PositiveEndpointWords h f) =
        if f = .zero then 0 else Nat.card (EndpointWords h f)) := by
  have terminal_shapes (p : Code) :
      ((codeWord p).getLast? = some .low ↔
        0 < (terminalGap p).x ∧ (terminalGap p).z = false ∧ (terminalGap p).y = 0) ∧
      ((codeWord p).getLast? = some .ends ↔
        (terminalGap p).z = true ∧ (terminalGap p).y = 0) := by
    have final (g : Gap) (ds : List (Bool × Gap)) (f : Window)
        (hf : f = .low ∨ f = .ends) :
        (codeWord (g, ds)).getLast? = some f ↔
          (gap (terminalGap (g, ds))).getLast? = some f := by
      induction ds generalizing g with
      | nil => simp [codeWord, codeCuts, join, terminalGap]
      | cons dg ds ih =>
        rcases dg with ⟨d, h⟩
        have he : codeWord (g, (d, h) :: ds) = gap g ++ triple false d false :: codeWord (h, ds) := by
          simp [codeWord, codeCuts, join, List.flatMap_cons, List.append_assoc]
        rw [he, List.getLast?_append_of_ne_nil _ (by simp)]
        have hn : triple false d false ≠ f := by
          rcases hf with rfl | rfl <;> cases d <;> simp [triple]
        have ht : (triple false d false :: codeWord (h, ds)).getLast? = some f ↔
            (codeWord (h, ds)).getLast? = some f := by
          cases codeWord (h, ds) <;> simp [hn]
        rw [ht, ih h]
        rfl
    rw [final p.1 p.2 .low (Or.inl rfl), final p.1 p.2 .ends (Or.inr rfl)]
    generalize terminalGap p = q
    rcases q with ⟨a, z, b⟩
    cases z <;>
      simp only [gap, Bool.false_eq_true, ↓reduceIte,
        List.getLast?_append, List.getLast?_replicate, List.getLast?_singleton,
        List.getLast?_nil]
    all_goals by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      simp [ha, hb, Nat.pos_iff_ne_zero]
  refine ⟨decomposition.1, decomposition.2.1, decomposition.2.2, code_language.1,
    fun p => (terminal_shapes p).1, fun p => (terminal_shapes p).2,
    (histogram_encoding (fun _ => 0)).1,
    (fun h => (histogram_encoding h).2), histogram_count, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c r s hn
    classical
    letI : Finite (HistogramWords (histogram a b c r s)) := (histogram_count a b c r s).2.1
    have nonempty (w : HistogramWords (histogram a b c r s)) : w.val ≠ [] := by
      intro he
      have hx := w.property.2 .low
      have hy := w.property.2 .high
      have hz := w.property.2 .ends
      have hu := w.property.2 .zero
      have hv := w.property.2 .middle
      simp [he, histogram] at hx hy hz hu hv
      omega
    letI : IsEmpty {w : HistogramWords (histogram a b c r s) // w.val.getLast? = none} :=
      ⟨fun w => nonempty w.val (List.getLast?_eq_none_iff.mp w.property)⟩
    have total : Nat.card (HistogramWords (histogram a b c r s)) =
        Nat.card {w : HistogramWords (histogram a b c r s) // w.val.getLast? = none} +
          ∑ f : Window, Nat.card (EndpointWords (histogram a b c r s) f) := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv
        (fun w : HistogramWords (histogram a b c r s) => w.val.getLast?)),
        Nat.card_sigma, Fintype.sum_option]
      rfl
    have h0 : Nat.card {w : HistogramWords (histogram a b c r s) //
        w.val.getLast? = none} = 0 := Nat.card_of_isEmpty
    rw [h0, zero_add] at total
    exact total.symm
  · refine ⟨?_, ?_⟩
    · simpa using (histogram_count 0 0 0 0 0).2.2
    · intro w
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro f hf
      have hp := List.count_pos_iff.mpr hf
      rw [w.property.2 f] at hp
      cases f <;> simp [histogram] at hp
  · intro h f hf
    refine ⟨fun w => ?_⟩
    have hp := List.count_pos_iff.mpr (List.mem_of_getLast? w.property)
    rw [w.val.property.2 f, hf] at hp
    exact Nat.not_lt_zero _ hp
  · intro a b c r s hc
    letI : Finite (HistogramWords (histogram a b c r s)) := (histogram_count a b c r s).2.1
    letI : Fintype (HistogramWords (histogram a b c r s)) := Fintype.ofFinite _
    apply Fintype.card_eq_zero_iff.mp
    rw [← Nat.card_eq_fintype_card, (histogram_count a b c r s).2.2,
      Nat.choose_eq_zero_of_lt hc]
    simp

  · intro h f
    have terminal (w : EndpointWords h f) :
        endable (run (some (false, false)) w.val.val) = nonzero f := by
      rw [(execution false false w.val.val).1.mpr w.val.property.1]
      obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp w.property
      simp [endable, hu, List.foldl_append]
    by_cases hf : f = .zero
    · subst f
      letI : IsEmpty (PositiveEndpointWords h .zero) := ⟨fun w => by
        have hp := w.property
        rw [terminal w.val] at hp
        simp [nonzero] at hp⟩
      simp
    · rw [if_neg hf]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun w : EndpointWords h f => by
        rw [terminal w]
        simp [nonzero, hf]))


end D5.S3.Arith.FibonacciAtomic.WindowHistogramLegalCount
