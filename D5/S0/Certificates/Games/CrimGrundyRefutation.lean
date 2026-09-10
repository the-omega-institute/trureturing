/- GID: D5/S0/Certificates/Games/CrimGrundyRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/CrimGrundyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Games/CrimGrundyRefutation.claim; result=D5/S0/Certificates/Games/CrimGrundyRefutation.result; claim=D5/S0/Certificates/Games/CrimGrundyRefutation.claim
   digest: Refutes printed Conjecture 3 of arXiv:2606.16828v1 at r=7 and k=5. -/

/- proof_shape: content
   escape_witness: The CRIM row/conjugate-row move graph, cell-count descent,
     and a complete locally checked SG certificate connected to well-founded evaluation.
   admission_basis: escape-witness
   Direct frozen dependencies: none. -/

import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.SplitIfs
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
namespace D5.S0.Certificates.Games.CrimGrundyRefutation
/-!
The paper represents partitions as decreasing lists of positive parts (page 4).
Row deletion and conjugate-row-conjugate column deletion are exactly section 3
(page 8). The definitions below extend to arbitrary natural lists to keep proofs
of cell-count descent independent of ordering. Zero entries cannot be deleted
as rows; conjugation discards zero column heights. On positive decreasing lists,
these are precisely the paper's moves, including removal of vanishing rows.
The empty list has no moves and therefore has Grundy value zero.

The claim is only the r ≥ 7 formula printed in Conjecture 3 (page 18), with
rectair parameters from section 2.2 (page 5). It makes no assertion about other
results, the authors' intended statement, or any corrected formula.

The source conjecture is literature-attested. A prior reader calculation by
Shivam Patel, posted 2026-08-20, is explicitly unverified at
https://mathdb.com/p/375372/the-sprague-grundy-conjecture-for-near-square-rectairs.
It is recorded as prior work, not used as a computational premise; no priority
or verdict about that posting is claimed. The certificate below was generated
by the two implementations recorded in docs/reports/crim-grundy-0910.
-/

/-- Row lengths; paper positions have positive entries in decreasing order. -/
abbrev Position := List ℕ

/-- Remove any positive row, preserving the order of all remaining rows. -/
def rowMoves (p : Position) : List Position :=
  List.rec [] (fun n tail rest => (if n = 0 then [] else [tail]) ++ rest.map (n :: ·)) p

/-- Number of cells in column j, with columns numbered from zero. -/
def height (p : Position) : ℕ → ℕ :=
  List.rec (fun _ => 0) (fun n _ rest j => (if j < n then 1 else 0) + rest j) p

/-- Conjugation lists the positive column heights in increasing column order. -/
def conjugate (p : Position) : Position :=
  ((List.range p.sum).map (height p)).filter (· != 0)

/-- All CRIM moves: row deletion, or conjugate-row-conjugate column deletion. -/
def moves (p : Position) : List Position :=
  rowMoves p ++ (rowMoves (conjugate p)).map conjugate

private def row_decreases (p q : Position) (h : q ∈ rowMoves p) : q.sum < p.sum := by
  induction p generalizing q with
  | nil => simp [rowMoves] at h
  | cons n p ih =>
    simp only [rowMoves, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨s, hs, rfl⟩
    · split_ifs at h with hn
      · simp at h
      · simp only [List.mem_singleton] at h
        subst q
        simp only [List.sum_cons]
        omega
    · simpa using Nat.add_lt_add_left (ih s hs) n

private def sum_indicator (w n : ℕ) (h : n ≤ w) :
    ((List.range w).map (fun j => if j < n then 1 else 0)).sum = n := by
  induction w with
  | zero =>
    have : n = 0 := by omega
    subst n
    simp
  | succ w ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    by_cases hn : n ≤ w
    · rw [ih hn, if_neg (by omega)]
      omega
    · have : n = w + 1 := by omega
      subst n
      have he : ((List.range w).map (fun j => if j < w + 1 then 1 else 0)) =
          (List.range w).map (fun _ => 1) := by
        apply List.map_congr_left
        intro j hj
        simp only [List.mem_range] at hj
        simp [show j < w + 1 by omega]
      rw [he]
      simp

private def sum_heights (p : Position) (w : ℕ) (h : ∀ n ∈ p, n ≤ w) :
    ((List.range w).map (height p)).sum = p.sum := by
  induction p with
  | nil => simp [height]
  | cons n p ih =>
    change ((List.range w).map (fun j => (if j < n then 1 else 0) + height p j)).sum =
      n + p.sum
    rw [List.sum_map_add, sum_indicator w n (h n (by simp)),
      ih (fun x hx => h x (by simp [hx]))]

private def sum_nonzero (p : Position) : (p.filter (· != 0)).sum = p.sum := by
  induction p with
  | nil => rfl
  | cons n p ih =>
    by_cases hn : n = 0 <;> simp [hn, ih]

private def conjugate_sum (p : Position) : (conjugate p).sum = p.sum := by
  rw [conjugate, sum_nonzero]
  exact sum_heights p p.sum (fun n hn => List.single_le_sum (fun x _ => Nat.zero_le x) n hn)

private def move_decreases (p q : Position) (h : q ∈ moves p) : q.sum < p.sum := by
  simp only [moves, List.mem_append, List.mem_map] at h
  rcases h with h | ⟨s, hs, rfl⟩
  · exact row_decreases p q h
  · simpa [conjugate_sum] using row_decreases (conjugate p) s hs

private def missing_nonempty (s : Finset ℕ) :
    (Finset.range (s.card + 1) \ s).Nonempty := by
  apply Finset.sdiff_nonempty.mpr
  intro h
  have := Finset.card_le_card h
  simp only [Finset.card_range] at this
  omega

/-- Least natural number absent from a finite set, using Mathlib finite minima. -/
def mex (s : Finset ℕ) : ℕ :=
  (Finset.range (s.card + 1) \ s).min' (missing_nonempty s)

private def mex_spec (s : Finset ℕ) :
    mex s ∉ s ∧ ∀ n < mex s, n ∈ s := by
  have hm := Finset.min'_mem _ (missing_nonempty s)
  change mex s ∈ Finset.range (s.card + 1) \ s at hm
  rcases Finset.mem_sdiff.mp hm with ⟨hr, hs⟩
  refine ⟨hs, fun n hn => ?_⟩
  by_contra hns
  have hmem : n ∈ Finset.range (s.card + 1) \ s := by
    simp only [Finset.mem_sdiff, Finset.mem_range] at *
    exact ⟨by omega, hns⟩
  have := Finset.min'_le _ n hmem
  change mex s ≤ n at this
  omega

/-- Sprague–Grundy evaluation by well-founded recursion on the total cell count. -/
def grundy : Position → ℕ :=
  (measure List.sum).wf.fix fun p rec =>
    mex ((moves p).attach.map (fun q => rec q.val (move_decreases p q.val q.property))).toFinset

private def grundy_eq (p : Position) :
    grundy p = mex ((moves p).map grundy).toFinset := by
  rw [grundy, WellFounded.fix_eq]
  simp
private def mex_unique (s : Finset ℕ) (n : ℕ)
    (hn : n ∉ s) (hbelow : ∀ m < n, m ∈ s) : mex s = n := by
  obtain ⟨hmissing, hsmall⟩ := mex_spec s
  rcases lt_trichotomy (mex s) n with h | h | h
  · exact False.elim (hmissing (hbelow _ h))
  · exact h
  · exact False.elim (hn (hsmall _ h))

private inductive Certificate where
  | empty
  | branch (position : Position) (candidate : ℕ) (left right : Certificate)

private def domain : Certificate → List Position
  | .empty => []
  | .branch p _ left right => domain left ++ p :: domain right

private def lookup (p : Position) : Certificate → Option ℕ
  | .empty => none
  | .branch q n left right =>
    if p = q then some n else
      if compare p q = .lt then lookup p left else lookup p right

-- Soundness of successful lookup needs no assumption about tree ordering.
private def lookup_mem (c : Certificate) (p : Position)
    (h : (lookup p c).isSome = true) : p ∈ domain c := by
  induction c with
  | empty => simp [lookup] at h
  | branch q n left right ihl ihr =>
    simp only [lookup] at h
    split_ifs at h with hp hlt
    · simp [domain, hp]
    · simp [domain, ihl h]
    · simp [domain, ihr h]

private def value (c : Certificate) (p : Position) := (lookup p c).getD 0

private def check (c : Certificate) (p : Position) : Bool :=
  let options := moves p
  let used := options.map (value c)
  options.all (fun q => (lookup q c).isSome) &&
    !used.contains (value c p) &&
    (List.range (value c p)).all (fun n => used.contains n)

private def certificate_correct (c : Certificate)
    (hc : (domain c).all (check c) = true) (p : Position) (hp : p ∈ domain c) :
    grundy p = value c p := by
  induction p using (measure List.sum).wf.induction with
  | h p ih =>
    have hcheck := List.all_eq_true.mp hc p hp
    simp only [check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
      Bool.not_eq_true', Bool.eq_false_iff, List.mem_range] at hcheck
    obtain ⟨⟨hclosed, hmissing⟩, hbelow⟩ := hcheck
    rw [grundy_eq]
    have he : (moves p).map grundy = (moves p).map (value c) := by
      apply List.map_congr_left
      intro q hq
      exact ih q (move_decreases p q hq) (lookup_mem c q (hclosed q hq))
    rw [he]
    apply mex_unique
    · simpa using hmissing
    · intro n hn
      simpa using hbelow n hn


/-- The rectair [c^(r-k), c-1, ..., c-k]; the claim supplies its valid range. -/
def rectair (r c k : ℕ) : Position :=
  List.replicate (r - k) c ++ (List.range k).map (fun i => c - (i + 1))

/-- Exactly the r ≥ 7 formula of printed Conjecture 3, using the actual CRIM evaluator. -/
def claim : Prop :=
  ∀ r k : ℕ, 7 ≤ r → k < min r (r - 1) →
    grundy (rectair r (r - 1) k) = if k = r - 2 ∧ r % 2 = 1 then 3 else 1

-- Candidate values only: every entry is checked against all actual moves below.
-- Balanced by lexicographic position order; all entries remain candidate data.
private def certificate : Certificate :=
  .branch [4, 4, 4, 3, 2, 2, 1] 3
    (.branch [3, 3, 3, 3, 3, 1] 1
      (.branch [3, 2, 2, 1, 1, 1] 2
        (.branch [2, 2, 2, 1, 1, 1] 0
          (.branch [2, 1, 1, 1] 0
            (.branch [1, 1, 1, 1, 1] 1
              (.branch [1, 1] 2
                (.branch [1] 1
                  (.branch [] 0 .empty .empty) .empty)
                (.branch [1, 1, 1, 1] 2
                  (.branch [1, 1, 1] 1 .empty .empty) .empty))
              (.branch [2] 2
                (.branch [1, 1, 1, 1, 1, 1, 1] 1
                  (.branch [1, 1, 1, 1, 1, 1] 2 .empty .empty) .empty)
                (.branch [2, 1, 1] 3
                  (.branch [2, 1] 0 .empty .empty) .empty)))
            (.branch [2, 2, 1, 1, 1] 3
              (.branch [2, 2] 0
                (.branch [2, 1, 1, 1, 1, 1] 0
                  (.branch [2, 1, 1, 1, 1] 3 .empty .empty) .empty)
                (.branch [2, 2, 1, 1] 0
                  (.branch [2, 2, 1] 3 .empty .empty) .empty))
              (.branch [2, 2, 2] 2
                (.branch [2, 2, 1, 1, 1, 1, 1] 3
                  (.branch [2, 2, 1, 1, 1, 1] 0 .empty .empty) .empty)
                (.branch [2, 2, 2, 1, 1] 2
                  (.branch [2, 2, 2, 1] 0 .empty .empty) .empty))))
          (.branch [3, 1] 3
            (.branch [2, 2, 2, 2, 2] 2
              (.branch [2, 2, 2, 2, 1] 3
                (.branch [2, 2, 2, 2] 0
                  (.branch [2, 2, 2, 1, 1, 1, 1] 2 .empty .empty) .empty)
                (.branch [2, 2, 2, 2, 1, 1, 1] 3
                  (.branch [2, 2, 2, 2, 1, 1] 0 .empty .empty) .empty))
              (.branch [2, 2, 2, 2, 2, 2] 0
                (.branch [2, 2, 2, 2, 2, 1, 1] 2
                  (.branch [2, 2, 2, 2, 2, 1] 0 .empty .empty) .empty)
                (.branch [3] 1
                  (.branch [2, 2, 2, 2, 2, 2, 1] 3 .empty .empty) .empty)))
            (.branch [3, 2, 1, 1] 2
              (.branch [3, 1, 1, 1, 1] 0
                (.branch [3, 1, 1, 1] 3
                  (.branch [3, 1, 1] 0 .empty .empty) .empty)
                (.branch [3, 2, 1] 1
                  (.branch [3, 2] 3 .empty .empty) .empty))
              (.branch [3, 2, 2] 1
                (.branch [3, 2, 1, 1, 1, 1] 2
                  (.branch [3, 2, 1, 1, 1] 1 .empty .empty) .empty)
                (.branch [3, 2, 2, 1, 1] 1
                  (.branch [3, 2, 2, 1] 2 .empty .empty) .empty)))))
        (.branch [3, 3, 2, 2, 2, 2, 1] 1
          (.branch [3, 3, 2, 1] 2
            (.branch [3, 3] 2
              (.branch [3, 2, 2, 2, 1, 1] 3
                (.branch [3, 2, 2, 2, 1] 1
                  (.branch [3, 2, 2, 2] 3 .empty .empty) .empty)
                (.branch [3, 2, 2, 2, 2, 1] 2
                  (.branch [3, 2, 2, 2, 2] 1 .empty .empty) .empty))
              (.branch [3, 3, 1, 1, 1] 1
                (.branch [3, 3, 1, 1] 2
                  (.branch [3, 3, 1] 1 .empty .empty) .empty)
                (.branch [3, 3, 2] 0
                  (.branch [3, 3, 1, 1, 1, 1] 2 .empty .empty) .empty)))
            (.branch [3, 3, 2, 2, 1, 1] 2
              (.branch [3, 3, 2, 1, 1, 1, 1] 0
                (.branch [3, 3, 2, 1, 1, 1] 2
                  (.branch [3, 3, 2, 1, 1] 0 .empty .empty) .empty)
                (.branch [3, 3, 2, 2, 1] 1
                  (.branch [3, 3, 2, 2] 2 .empty .empty) .empty))
              (.branch [3, 3, 2, 2, 2, 1] 2
                (.branch [3, 3, 2, 2, 2] 0
                  (.branch [3, 3, 2, 2, 1, 1, 1] 1 .empty .empty) .empty)
                (.branch [3, 3, 2, 2, 2, 2] 2
                  (.branch [3, 3, 2, 2, 2, 1, 1] 0 .empty .empty) .empty))))
          (.branch [3, 3, 3, 2, 2, 2] 1
            (.branch [3, 3, 3, 2, 1] 4
              (.branch [3, 3, 3, 1, 1] 0
                (.branch [3, 3, 3, 1] 3
                  (.branch [3, 3, 3] 0 .empty .empty) .empty)
                (.branch [3, 3, 3, 2] 1
                  (.branch [3, 3, 3, 1, 1, 1] 3 .empty .empty) .empty))
              (.branch [3, 3, 3, 2, 2] 0
                (.branch [3, 3, 3, 2, 1, 1, 1] 4
                  (.branch [3, 3, 3, 2, 1, 1] 1 .empty .empty) .empty)
                (.branch [3, 3, 3, 2, 2, 1, 1] 0
                  (.branch [3, 3, 3, 2, 2, 1] 3 .empty .empty) .empty)))
            (.branch [3, 3, 3, 3, 2, 1] 1
              (.branch [3, 3, 3, 3, 1] 2
                (.branch [3, 3, 3, 3] 1
                  (.branch [3, 3, 3, 2, 2, 2, 1] 4 .empty .empty) .empty)
                (.branch [3, 3, 3, 3, 2] 0
                  (.branch [3, 3, 3, 3, 1, 1] 1 .empty .empty) .empty))
              (.branch [3, 3, 3, 3, 2, 2, 1] 2
                (.branch [3, 3, 3, 3, 2, 2] 1
                  (.branch [3, 3, 3, 3, 2, 1, 1] 0 .empty .empty) .empty)
                (.branch [3, 3, 3, 3, 3] 0 .empty .empty))))))
      (.branch [4, 4, 2, 1, 1] 2
        (.branch [4, 3, 2, 2] 0
          (.branch [4, 2, 2, 1] 1
            (.branch [4, 1, 1, 1] 0
              (.branch [4] 2
                (.branch [3, 3, 3, 3, 3, 2, 1] 4
                  (.branch [3, 3, 3, 3, 3, 2] 1 .empty .empty) .empty)
                (.branch [4, 1, 1] 3
                  (.branch [4, 1] 0 .empty .empty) .empty))
              (.branch [4, 2, 1, 1] 0
                (.branch [4, 2, 1] 2
                  (.branch [4, 2] 0 .empty .empty) .empty)
                (.branch [4, 2, 2] 2
                  (.branch [4, 2, 1, 1, 1] 2 .empty .empty) .empty)))
            (.branch [4, 3, 1, 1] 1
              (.branch [4, 2, 2, 2, 1] 2
                (.branch [4, 2, 2, 2] 0
                  (.branch [4, 2, 2, 1, 1] 2 .empty .empty) .empty)
                (.branch [4, 3, 1] 2
                  (.branch [4, 3] 0 .empty .empty) .empty))
              (.branch [4, 3, 2, 1] 0
                (.branch [4, 3, 2] 2
                  (.branch [4, 3, 1, 1, 1] 2 .empty .empty) .empty)
                (.branch [4, 3, 2, 1, 1, 1] 0
                  (.branch [4, 3, 2, 1, 1] 3 .empty .empty) .empty))))
          (.branch [4, 3, 3, 2, 2, 1] 0
            (.branch [4, 3, 3, 1] 0
              (.branch [4, 3, 2, 2, 2] 2
                (.branch [4, 3, 2, 2, 1, 1] 0
                  (.branch [4, 3, 2, 2, 1] 3 .empty .empty) .empty)
                (.branch [4, 3, 3] 3
                  (.branch [4, 3, 2, 2, 2, 1] 0 .empty .empty) .empty))
              (.branch [4, 3, 3, 2, 1] 3
                (.branch [4, 3, 3, 2] 4
                  (.branch [4, 3, 3, 1, 1] 3 .empty .empty) .empty)
                (.branch [4, 3, 3, 2, 2] 3
                  (.branch [4, 3, 3, 2, 1, 1] 4 .empty .empty) .empty)))
            (.branch [4, 4, 1] 3
              (.branch [4, 3, 3, 3, 2] 3
                (.branch [4, 3, 3, 3, 1] 4
                  (.branch [4, 3, 3, 3] 2 .empty .empty) .empty)
                (.branch [4, 4] 0
                  (.branch [4, 3, 3, 3, 2, 1] 0 .empty .empty) .empty))
              (.branch [4, 4, 2] 2
                (.branch [4, 4, 1, 1, 1] 3
                  (.branch [4, 4, 1, 1] 0 .empty .empty) .empty)
                (.branch [4, 4, 2, 1] 0 .empty .empty)))))
        (.branch [4, 4, 3, 3, 2, 1] 0
          (.branch [4, 4, 3, 2, 1] 3
            (.branch [4, 4, 2, 2, 2, 1] 0
              (.branch [4, 4, 2, 2, 1] 3
                (.branch [4, 4, 2, 2] 0
                  (.branch [4, 4, 2, 1, 1, 1] 0 .empty .empty) .empty)
                (.branch [4, 4, 2, 2, 2] 2
                  (.branch [4, 4, 2, 2, 1, 1] 0 .empty .empty) .empty))
              (.branch [4, 4, 3, 1, 1] 2
                (.branch [4, 4, 3, 1] 4
                  (.branch [4, 4, 3] 1 .empty .empty) .empty)
                (.branch [4, 4, 3, 2] 0
                  (.branch [4, 4, 3, 1, 1, 1] 1 .empty .empty) .empty)))
            (.branch [4, 4, 3, 2, 2, 2] 0
              (.branch [4, 4, 3, 2, 2] 1
                (.branch [4, 4, 3, 2, 1, 1, 1] 3
                  (.branch [4, 4, 3, 2, 1, 1] 0 .empty .empty) .empty)
                (.branch [4, 4, 3, 2, 2, 1, 1] 1
                  (.branch [4, 4, 3, 2, 2, 1] 4 .empty .empty) .empty))
              (.branch [4, 4, 3, 3, 1] 3
                (.branch [4, 4, 3, 3] 0
                  (.branch [4, 4, 3, 2, 2, 2, 1] 3 .empty .empty) .empty)
                (.branch [4, 4, 3, 3, 2] 2
                  (.branch [4, 4, 3, 3, 1, 1] 0 .empty .empty) .empty))))
          (.branch [4, 4, 4, 2, 1] 1
            (.branch [4, 4, 3, 3, 3, 2] 0
              (.branch [4, 4, 3, 3, 2, 2, 1] 3
                (.branch [4, 4, 3, 3, 2, 2] 0
                  (.branch [4, 4, 3, 3, 2, 1, 1] 2 .empty .empty) .empty)
                (.branch [4, 4, 3, 3, 3, 1] 5
                  (.branch [4, 4, 3, 3, 3] 1 .empty .empty) .empty))
              (.branch [4, 4, 4, 1] 2
                (.branch [4, 4, 4] 1
                  (.branch [4, 4, 3, 3, 3, 2, 1] 3 .empty .empty) .empty)
                (.branch [4, 4, 4, 2] 0
                  (.branch [4, 4, 4, 1, 1] 1 .empty .empty) .empty)))
            (.branch [4, 4, 4, 3, 1, 1] 0
              (.branch [4, 4, 4, 2, 2, 1] 2
                (.branch [4, 4, 4, 2, 2] 1
                  (.branch [4, 4, 4, 2, 1, 1] 0 .empty .empty) .empty)
                (.branch [4, 4, 4, 3, 1] 3
                  (.branch [4, 4, 4, 3] 0 .empty .empty) .empty))
              (.branch [4, 4, 4, 3, 2, 1, 1] 1
                (.branch [4, 4, 4, 3, 2, 1] 0
                  (.branch [4, 4, 4, 3, 2] 1 .empty .empty) .empty)
                (.branch [4, 4, 4, 3, 2, 2] 0 .empty .empty)))))))
    (.branch [5, 5, 4, 3, 2, 2] 1
      (.branch [5, 4, 3, 2, 2, 1] 2
        (.branch [5, 3, 2] 0
          (.branch [4, 4, 4, 4, 3, 2, 1] 3
            (.branch [4, 4, 4, 4, 1] 3
              (.branch [4, 4, 4, 3, 3, 2] 0
                (.branch [4, 4, 4, 3, 3, 1] 2
                  (.branch [4, 4, 4, 3, 3] 1 .empty .empty) .empty)
                (.branch [4, 4, 4, 4] 0
                  (.branch [4, 4, 4, 3, 3, 2, 1] 1 .empty .empty) .empty))
              (.branch [4, 4, 4, 4, 3] 1
                (.branch [4, 4, 4, 4, 2, 1] 0
                  (.branch [4, 4, 4, 4, 2] 1 .empty .empty) .empty)
                (.branch [4, 4, 4, 4, 3, 2] 0
                  (.branch [4, 4, 4, 4, 3, 1] 2 .empty .empty) .empty)))
            (.branch [5, 2, 1, 1] 2
              (.branch [5, 1, 1] 0
                (.branch [5, 1] 3
                  (.branch [5] 1 .empty .empty) .empty)
                (.branch [5, 2, 1] 1
                  (.branch [5, 2] 3 .empty .empty) .empty))
              (.branch [5, 3] 2
                (.branch [5, 2, 2, 1] 2
                  (.branch [5, 2, 2] 1 .empty .empty) .empty)
                (.branch [5, 3, 1, 1] 2
                  (.branch [5, 3, 1] 1 .empty .empty) .empty))))
          (.branch [5, 4, 2] 1
            (.branch [5, 3, 3, 1] 3
              (.branch [5, 3, 2, 2] 2
                (.branch [5, 3, 2, 1, 1] 0
                  (.branch [5, 3, 2, 1] 3 .empty .empty) .empty)
                (.branch [5, 3, 3] 0
                  (.branch [5, 3, 2, 2, 1] 1 .empty .empty) .empty))
              (.branch [5, 4] 3
                (.branch [5, 3, 3, 2, 1] 0
                  (.branch [5, 3, 3, 2] 2 .empty .empty) .empty)
                (.branch [5, 4, 1, 1] 2
                  (.branch [5, 4, 1] 1 .empty .empty) .empty)))
            (.branch [5, 4, 3, 1] 3
              (.branch [5, 4, 2, 2] 3
                (.branch [5, 4, 2, 1, 1] 1
                  (.branch [5, 4, 2, 1] 3 .empty .empty) .empty)
                (.branch [5, 4, 3] 4
                  (.branch [5, 4, 2, 2, 1] 0 .empty .empty) .empty))
              (.branch [5, 4, 3, 2, 1] 1
                (.branch [5, 4, 3, 2] 3
                  (.branch [5, 4, 3, 1, 1] 0 .empty .empty) .empty)
                (.branch [5, 4, 3, 2, 2] 4
                  (.branch [5, 4, 3, 2, 1, 1] 2 .empty .empty) .empty)))))
        (.branch [5, 5, 3, 2] 1
          (.branch [5, 4, 4, 3, 2, 1] 5
            (.branch [5, 4, 4, 1] 4
              (.branch [5, 4, 3, 3, 2] 0
                (.branch [5, 4, 3, 3, 1] 2
                  (.branch [5, 4, 3, 3] 1 .empty .empty) .empty)
                (.branch [5, 4, 4] 2
                  (.branch [5, 4, 3, 3, 2, 1] 4 .empty .empty) .empty))
              (.branch [5, 4, 4, 3] 3
                (.branch [5, 4, 4, 2, 1] 2
                  (.branch [5, 4, 4, 2] 3 .empty .empty) .empty)
                (.branch [5, 4, 4, 3, 2] 2
                  (.branch [5, 4, 4, 3, 1] 0 .empty .empty) .empty)))
            (.branch [5, 5, 2, 1, 1] 0
              (.branch [5, 5, 1, 1] 2
                (.branch [5, 5, 1] 1
                  (.branch [5, 5] 2 .empty .empty) .empty)
                (.branch [5, 5, 2, 1] 2
                  (.branch [5, 5, 2] 0 .empty .empty) .empty))
              (.branch [5, 5, 3] 0
                (.branch [5, 5, 2, 2, 1] 1
                  (.branch [5, 5, 2, 2] 2 .empty .empty) .empty)
                (.branch [5, 5, 3, 1, 1] 0
                  (.branch [5, 5, 3, 1] 3 .empty .empty) .empty))))
          (.branch [5, 5, 4, 2] 2
            (.branch [5, 5, 3, 3, 1] 2
              (.branch [5, 5, 3, 2, 2] 0
                (.branch [5, 5, 3, 2, 1, 1] 1
                  (.branch [5, 5, 3, 2, 1] 4 .empty .empty) .empty)
                (.branch [5, 5, 3, 3] 1
                  (.branch [5, 5, 3, 2, 2, 1] 3 .empty .empty) .empty))
              (.branch [5, 5, 4] 0
                (.branch [5, 5, 3, 3, 2, 1] 1
                  (.branch [5, 5, 3, 3, 2] 0 .empty .empty) .empty)
                (.branch [5, 5, 4, 1, 1] 0
                  (.branch [5, 5, 4, 1] 3 .empty .empty) .empty)))
            (.branch [5, 5, 4, 3, 1] 2
              (.branch [5, 5, 4, 2, 2] 0
                (.branch [5, 5, 4, 2, 1, 1] 2
                  (.branch [5, 5, 4, 2, 1] 0 .empty .empty) .empty)
                (.branch [5, 5, 4, 3] 1
                  (.branch [5, 5, 4, 2, 2, 1] 3 .empty .empty) .empty))
              (.branch [5, 5, 4, 3, 2, 1] 5
                (.branch [5, 5, 4, 3, 2] 0
                  (.branch [5, 5, 4, 3, 1, 1] 1 .empty .empty) .empty)
                (.branch [5, 5, 4, 3, 2, 1, 1] 0 .empty .empty))))))
      (.branch [6, 5, 1] 2
        (.branch [5, 5, 5, 4, 2] 0
          (.branch [5, 5, 4, 4, 3, 2] 1
            (.branch [5, 5, 4, 4] 1
              (.branch [5, 5, 4, 3, 3, 1] 3
                (.branch [5, 5, 4, 3, 3] 0
                  (.branch [5, 5, 4, 3, 2, 2, 1] 4 .empty .empty) .empty)
                (.branch [5, 5, 4, 3, 3, 2, 1] 0
                  (.branch [5, 5, 4, 3, 3, 2] 1 .empty .empty) .empty))
              (.branch [5, 5, 4, 4, 2, 1] 1
                (.branch [5, 5, 4, 4, 2] 0
                  (.branch [5, 5, 4, 4, 1] 2 .empty .empty) .empty)
                (.branch [5, 5, 4, 4, 3, 1] 1
                  (.branch [5, 5, 4, 4, 3] 0 .empty .empty) .empty)))
            (.branch [5, 5, 5, 3] 1
              (.branch [5, 5, 5, 1] 3
                (.branch [5, 5, 5] 0
                  (.branch [5, 5, 4, 4, 3, 2, 1] 4 .empty .empty) .empty)
                (.branch [5, 5, 5, 2, 1] 0
                  (.branch [5, 5, 5, 2] 1 .empty .empty) .empty))
              (.branch [5, 5, 5, 3, 2, 1] 3
                (.branch [5, 5, 5, 3, 2] 0
                  (.branch [5, 5, 5, 3, 1] 2 .empty .empty) .empty)
                (.branch [5, 5, 5, 4, 1] 2
                  (.branch [5, 5, 5, 4] 1 .empty .empty) .empty))))
          (.branch [6, 3, 2] 2
            (.branch [6] 2
              (.branch [5, 5, 5, 4, 3, 1] 3
                (.branch [5, 5, 5, 4, 3] 0
                  (.branch [5, 5, 5, 4, 2, 1] 1 .empty .empty) .empty)
                (.branch [5, 5, 5, 4, 3, 2, 1] 2
                  (.branch [5, 5, 5, 4, 3, 2] 1 .empty .empty) .empty))
              (.branch [6, 2, 1] 2
                (.branch [6, 2] 0
                  (.branch [6, 1] 0 .empty .empty) .empty)
                (.branch [6, 3, 1] 2
                  (.branch [6, 3] 0 .empty .empty) .empty)))
            (.branch [6, 4, 3] 1
              (.branch [6, 4, 1] 3
                (.branch [6, 4] 0
                  (.branch [6, 3, 2, 1] 0 .empty .empty) .empty)
                (.branch [6, 4, 2, 1] 0
                  (.branch [6, 4, 2] 2 .empty .empty) .empty))
              (.branch [6, 4, 3, 2, 1] 2
                (.branch [6, 4, 3, 2] 0
                  (.branch [6, 4, 3, 1] 4 .empty .empty) .empty)
                (.branch [6, 5] 0 .empty .empty)))))
        (.branch [6, 6, 4, 1] 2
          (.branch [6, 5, 4, 3, 1] 5
            (.branch [6, 5, 3, 2, 1] 2
              (.branch [6, 5, 3] 3
                (.branch [6, 5, 2, 1] 0
                  (.branch [6, 5, 2] 2 .empty .empty) .empty)
                (.branch [6, 5, 3, 2] 4
                  (.branch [6, 5, 3, 1] 0 .empty .empty) .empty))
              (.branch [6, 5, 4, 2] 0
                (.branch [6, 5, 4, 1] 0
                  (.branch [6, 5, 4] 1 .empty .empty) .empty)
                (.branch [6, 5, 4, 3] 0
                  (.branch [6, 5, 4, 2, 1] 4 .empty .empty) .empty)))
            (.branch [6, 6, 2, 1] 0
              (.branch [6, 6] 0
                (.branch [6, 5, 4, 3, 2, 1] 0
                  (.branch [6, 5, 4, 3, 2] 5 .empty .empty) .empty)
                (.branch [6, 6, 2] 2
                  (.branch [6, 6, 1] 3 .empty .empty) .empty))
              (.branch [6, 6, 3, 2] 0
                (.branch [6, 6, 3, 1] 4
                  (.branch [6, 6, 3] 1 .empty .empty) .empty)
                (.branch [6, 6, 4] 1
                  (.branch [6, 6, 3, 2, 1] 3 .empty .empty) .empty))))
          (.branch [6, 6, 5, 3, 1] 1
            (.branch [6, 6, 4, 3, 2, 1] 0
              (.branch [6, 6, 4, 3] 0
                (.branch [6, 6, 4, 2, 1] 1
                  (.branch [6, 6, 4, 2] 0 .empty .empty) .empty)
                (.branch [6, 6, 4, 3, 2] 1
                  (.branch [6, 6, 4, 3, 1] 3 .empty .empty) .empty))
              (.branch [6, 6, 5, 2] 0
                (.branch [6, 6, 5, 1] 4
                  (.branch [6, 6, 5] 1 .empty .empty) .empty)
                (.branch [6, 6, 5, 3] 0
                  (.branch [6, 6, 5, 2, 1] 1 .empty .empty) .empty)))
            (.branch [6, 6, 5, 4, 2, 1] 0
              (.branch [6, 6, 5, 4] 0
                (.branch [6, 6, 5, 3, 2, 1] 4
                  (.branch [6, 6, 5, 3, 2] 1 .empty .empty) .empty)
                (.branch [6, 6, 5, 4, 2] 1
                  (.branch [6, 6, 5, 4, 1] 3 .empty .empty) .empty))
              (.branch [6, 6, 5, 4, 3, 2] 0
                (.branch [6, 6, 5, 4, 3, 1] 2
                  (.branch [6, 6, 5, 4, 3] 1 .empty .empty) .empty)
                (.branch [6, 6, 5, 4, 3, 2, 1] 1 .empty .empty)))))))

set_option maxHeartbeats 4000000 in
-- Checks all 377 positions against their complete CRIM option lists.
/-- The full CRIM recursion gives G(R^5_{7,6}) = 1, contradicting the printed value 3. -/
theorem result : ¬ claim := by
  have checked : (domain certificate).all (check certificate) = true := by
    -- Keep each state's kernel reduction separate, then combine all checks.
    conv => lhs; arg 1; reduce
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have actual : grundy (rectair 7 6 5) = 1 := by
    calc
      _ = value certificate (rectair 7 6 5) :=
        certificate_correct certificate checked _ (by decide +kernel)
      _ = 1 := by decide +kernel
  intro h
  have predicted : grundy (rectair 7 6 5) = 3 := h 7 5 (by decide) (by decide)
  omega

#print axioms claim
#print axioms result

end D5.S0.Certificates.Games.CrimGrundyRefutation
