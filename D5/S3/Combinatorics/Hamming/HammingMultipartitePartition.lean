/- GID: D5/S3/Combinatorics/Hamming/HammingMultipartitePartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/HammingMultipartitePartition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All-direction maximal full-line partitions of mixed-alphabet Hamming graphs. -/

/-
proof_shape: Vertex, graph, line: definition
proof_shape: result: content
admission_basis: open-problem-resolution (https://github.com/the-omega-institute/trureturing/issues/13221)
Source: Nasra Daher Ahmed and Ravi Kunjwal, Characterizing unitaries via quasi-process functions,
  arXiv:2610.00579v1, Conjecture V.1. The source attributes the binary case to Erde,
  arXiv:2404.03950; the binary case is not claimed as new.
Original Lean implementation by OpenAI Codex (GPT-6), licensed under Apache-2.0.
Direct library reuse: Fin.init_snoc, Fin.snoc, Fin.lastCases, Function.update_of_ne,
  SimpleGraph.isMaximalClique_iff, and the pinned Mathlib finite-function instances.
The private seed and induction are consumed by result; no finite-instance theorem is public.
Utility none: the delivered theorem is universal in dimension and every alphabet size;
  the finite seed is internal to its induction, not an independent computed contribution.
Direct frozen project dependencies: none.
No source prose or third-party proof code is copied.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Hamming.HammingMultipartitePartition

/-- Vertices with independently chosen coordinate alphabet sizes. -/
abbrev Vertex {n : ℕ} (d : Fin n → ℕ) := (i : Fin n) → Fin (d i)

/-- Two vertices are adjacent exactly when they differ in one coordinate. -/
def graph {n : ℕ} (d : Fin n → ℕ) : SimpleGraph (Vertex d) where
  Adj x y := ∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j
  symm := ⟨by
    rintro x y ⟨i, hne, heq⟩
    exact ⟨i, hne.symm, fun j hj => (heq j hj).symm⟩⟩
  loopless := ⟨by
    rintro x ⟨i, hi, _⟩
    exact hi rfl⟩

/-- A full line varies freely in its direction and fixes all other coordinates. -/
def line {n : ℕ} {d : Fin n → ℕ} (i : Fin n) (x : Vertex d) : Set (Vertex d) :=
  {y | ∀ j, j ≠ i → y j = x j}

private abbrev Cube (n : ℕ) := Fin n → Bool

private def flip {n : ℕ} (x : Cube n) (i : Fin n) : Cube n :=
  Function.update x i (!(x i))

private structure Selector (n : ℕ) where
  z : Fin n
  choose : Cube n → Fin n
  stable : ∀ x, choose (flip x (choose x)) = choose x
  onto : ∀ i, ∃ x, choose x = i
  a : Cube n
  b : Cube n
  at_a : choose a = z
  at_b : choose b = z
  a_zero : a z = false
  b_zero : b z = false
  distinct : a ≠ b

private def seed : Selector 4 where
  z := 0
  choose x := if x 1 && x 2 then 0 else if x 0 && !(x 2) then 1
    else if !(x 0) && !(x 1) then 2 else 3
  a := fun i => decide (i = 1 ∨ i = 2)
  b := fun i => decide (i ≠ 0)
  stable := by decide
  onto := by decide
  at_a := by decide
  at_b := by decide
  a_zero := by decide
  b_zero := by decide
  distinct := by decide

private def orbit {n : ℕ} (s : Selector n) (x : Cube n) : Prop :=
  x = s.a ∨ x = flip s.a s.z

private theorem orbit_choose {n : ℕ} (s : Selector n) {x : Cube n} (h : orbit s x) :
    s.choose x = s.z := by
  rcases h with h | h
  · simpa [h] using s.at_a
  · rw [h, ← s.at_a]
    exact s.stable s.a

private theorem orbit_flip {n : ℕ} (s : Selector n) (x : Cube n) :
    orbit s (flip x (s.choose x)) ↔ orbit s x := by
  have hinv (y : Cube n) : flip (flip y s.z) s.z = y := by
    funext j
    by_cases h : j = s.z
    · subst j; simp [flip]
    · simp [flip, h]
  constructor
  · intro h
    have hc := orbit_choose s h
    have hcx : s.choose x = s.z := (s.stable x).symm.trans hc
    rcases h with h | h
    · right
      have := congrArg (fun t => flip t s.z) h
      simpa [hcx, hinv] using this
    · left
      have := congrArg (fun t => flip t s.z) h
      simpa [hcx, hinv] using this
  · intro h
    have hc := orbit_choose s h
    rw [hc]
    rcases h with h | h
    · right; rw [h]
    · left; rw [h, hinv]

private theorem b_outside {n : ℕ} (s : Selector n) : ¬ orbit s s.b := by
  rintro (h | h)
  · exact s.distinct h.symm
  · have hz := congr_fun h s.z
    simp [flip, s.a_zero, s.b_zero] at hz

private noncomputable def step {n : ℕ} (s : Selector n) : Selector (n + 1) := by
  classical
  let c : Cube (n + 1) → Fin (n + 1) := fun x =>
    if orbit s (Fin.init x) then Fin.last n else (s.choose (Fin.init x)).castSucc
  refine
    { z := s.z.castSucc
      choose := c
      a := Fin.snoc s.b false
      b := Fin.snoc s.b true
      stable := ?_
      onto := ?_
      at_a := ?_
      at_b := ?_
      a_zero := ?_
      b_zero := ?_
      distinct := ?_ }
  · intro x
    by_cases h : orbit s (Fin.init x)
    · have hi : Fin.init (flip x (Fin.last n)) = Fin.init x := by
        funext i
        simp [Fin.init, flip]
      simp [c, h, hi]
    · have hi : Fin.init (flip x (s.choose (Fin.init x)).castSucc) =
          flip (Fin.init x) (s.choose (Fin.init x)) := by
        funext j
        by_cases hj : j = s.choose (Fin.init x)
        · subst j; simp [Fin.init, flip]
        · simp [Fin.init, flip, hj]
      have ho : ¬ orbit s (flip (Fin.init x) (s.choose (Fin.init x))) :=
        fun hh => h ((orbit_flip s (Fin.init x)).mp hh)
      simp [c, h, hi, ho, s.stable]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨Fin.snoc s.a false, by simp [c, orbit]⟩
    · by_cases hj : j = s.z
      · exact ⟨Fin.snoc s.b false, by simp [c, b_outside s, s.at_b, hj]⟩
      · obtain ⟨x, hx⟩ := s.onto j
        have ho : ¬ orbit s x := fun hh => hj (hx.symm.trans (orbit_choose s hh))
        exact ⟨Fin.snoc x false, by simp [c, ho, hx]⟩
  · simp [c, b_outside s, s.at_b]
  · simp [c, b_outside s, s.at_b]
  · simp [s.b_zero]
  · simp [s.b_zero]
  · simp

private theorem selector_exists (n : ℕ) (hn : 4 ≤ n) : Nonempty (Selector n) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨seed⟩
  | succ n hn ih =>
      obtain ⟨s⟩ := ih
      exact ⟨step s⟩

private def binary {n : ℕ} {d : Fin n → ℕ} (x : Vertex d) : Cube n :=
  fun i => decide ((x i).val ≠ 0)

private theorem choice_constant {n : ℕ} {d : Fin n → ℕ} (s : Selector n)
    (x y : Vertex d) (h : y ∈ line (s.choose (binary x)) x) :
    s.choose (binary y) = s.choose (binary x) := by
  let i := s.choose (binary x)
  have hoff : ∀ j, j ≠ i → binary y j = binary x j := by
    intro j hj
    simp only [binary]
    rw [h j hj]
  by_cases hi : binary y i = binary x i
  · have he : binary y = binary x := by
      funext j
      by_cases hj : j = i
      · simpa [hj] using hi
      · exact hoff j hj
    rw [he]
  · have he : binary y = flip (binary x) i := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [flip, Function.update_self]
        cases hx : binary x i <;> cases hy : binary y i <;> simp_all
      · rw [show flip (binary x) i j = binary x j from
          by simpa only [flip] using
            Function.update_of_ne hj (!(binary x i)) (binary x), hoff j hj]
    rw [he]
    exact s.stable (binary x)

private theorem selected_line_constant {n : ℕ} {d : Fin n → ℕ} (s : Selector n)
    (x y : Vertex d) (h : y ∈ line (s.choose (binary x)) x) :
    line (s.choose (binary y)) y = line (s.choose (binary x)) x := by
  rw [choice_constant s x y h]
  ext z
  constructor
  · intro hz j hj
    exact (hz j hj).trans (h j hj)
  · intro hz j hj
    exact (hz j hj).trans (h j hj).symm

private theorem line_clique {n : ℕ} {d : Fin n → ℕ} (i : Fin n) (x : Vertex d) :
    (graph d).IsClique (line i x) := by
  intro y hy z hz hne
  refine ⟨i, ?_, fun j hj => (hy j hj).trans (hz j hj).symm⟩
  intro hi
  apply hne
  funext j
  by_cases hj : j = i
  · subst j; exact hi
  · exact (hy j hj).trans (hz j hj).symm

private theorem line_maximal {n : ℕ} {d : Fin n → ℕ} (hd : ∀ i, 2 ≤ d i)
    (i : Fin n) (x : Vertex d) : Maximal (graph d).IsClique (line i x) := by
  classical
  refine SimpleGraph.isMaximalClique_iff.mpr ⟨line_clique i x, ?_⟩
  intro S hS hsub z hz
  by_contra hout
  change ¬ (∀ j, j ≠ i → z j = x j) at hout
  push Not at hout
  obtain ⟨j, hji, hzx⟩ := hout
  have hv : ∃ v : Fin (d i), v ≠ z i := by
    let zero : Fin (d i) := ⟨0, by have := hd i; omega⟩
    let one : Fin (d i) := ⟨1, by have := hd i; omega⟩
    by_cases h : z i = zero
    · refine ⟨one, ?_⟩
      rw [h]
      exact fun he => by have := congrArg Fin.val he; simp [one, zero] at this
    · exact ⟨zero, fun he => h he.symm⟩
  obtain ⟨v, hv⟩ := hv
  let y : Vertex d := Function.update x i v
  have hy : y ∈ line i x := fun k hk => Function.update_of_ne hk v x
  have hiy : y i ≠ z i := by simpa [y] using hv
  have hjy : y j ≠ z j := by
    rw [show y j = x j from hy j hji]
    exact hzx.symm
  have hyz : y ≠ z := fun he => hiy (congr_fun he i)
  obtain ⟨k, _, heq⟩ := hS (hsub hy) hz hyz
  by_cases hik : i = k
  · exact hjy (heq j (by simpa [← hik] using hji))
  · exact hiy (heq i hik)

private theorem binary_onto {n : ℕ} {d : Fin n → ℕ} (hd : ∀ i, 2 ≤ d i)
    (b : Cube n) : ∃ x : Vertex d, binary x = b := by
  let x : Vertex d := fun i =>
    if b i then ⟨1, by have := hd i; omega⟩ else ⟨0, by have := hd i; omega⟩
  refine ⟨x, ?_⟩
  funext i
  cases h : b i <;> simp [binary, x, h]

/-- Ahmed–Kunjwal Conjecture V.1: all mixed alphabets of size at least two in
at least four dimensions admit a partition into nonempty full coordinate lines,
each inclusion-maximal as a Hamming clique, with every coordinate direction used. -/
theorem result (n : ℕ) (hn : 4 ≤ n) (d : Fin n → ℕ) (hd : ∀ i, 2 ≤ d i) :
    ∃ P : Set (Set (Vertex d)),
      (∀ S ∈ P, S.Nonempty ∧ (∃ i x, S = line i x) ∧ Maximal (graph d).IsClique S) ∧
      (∀ x : Vertex d, ∃! S, S ∈ P ∧ x ∈ S) ∧
      (∀ i : Fin n, ∃ x : Vertex d, line i x ∈ P) := by
  classical
  obtain ⟨s⟩ := selector_exists n hn
  let L : Vertex d → Set (Vertex d) := fun x => line (s.choose (binary x)) x
  refine ⟨Set.range L, ?_, ?_, ?_⟩
  · rintro S ⟨x, rfl⟩
    exact ⟨⟨x, fun _ _ => rfl⟩, ⟨s.choose (binary x), x, rfl⟩,
      line_maximal hd (s.choose (binary x)) x⟩
  · intro x
    refine ⟨L x, ⟨⟨x, rfl⟩, fun _ _ => rfl⟩, ?_⟩
    rintro S ⟨⟨y, rfl⟩, hxy⟩
    exact (selected_line_constant s y x hxy).symm
  · intro i
    obtain ⟨b, hb⟩ := s.onto i
    obtain ⟨x, hx⟩ := binary_onto hd b
    refine ⟨x, ⟨x, ?_⟩⟩
    simp [L, hx, hb]

end D5.S3.Combinatorics.Hamming.HammingMultipartitePartition
