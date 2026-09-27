/- GID: D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.claim; result=D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.result; claim=D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.claim
   digest: Mi-Xu-Yang Conjecture 5.2 fails at n=3 for the permutation 132. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9318)
   Direct frozen dependencies: none (pinned Mathlib only) -/

import Mathlib.Data.List.Sublists

namespace D5.S1.Words.Patterns.MiXuYangPartiallyRestrictedStackMaximalSortRefutation

private def samePattern (u sigma : List Nat) : Bool :=
  u.length == sigma.length &&
    (List.range u.length).all (fun i =>
      (List.range u.length).all (fun j =>
        decide (u[i]! < u[j]! ↔ sigma[i]! < sigma[j]!)))

private def containsBool (pi sigma : List Nat) : Bool :=
  pi.sublists.any fun u => samePattern u sigma

/-- `π` contains `σ`: some subsequence of `π` is order-isomorphic to `σ` (page 2). -/
def Contains (pi sigma : List Nat) : Prop :=
  containsBool pi sigma = true

private instance decidableContains (pi sigma : List Nat) : Decidable (Contains pi sigma) := by
  unfold Contains
  infer_instance

/-- `(T, k)`-avoiding: `T` is read as the set of its distinct members
(page 1: "`k` distinct permutations from `T`"), of which `w` contains at most `k`. -/
def TkAvoiding (T : List (List Nat)) (k : Nat) (w : List Nat) : Prop :=
  (T.dedup.filter fun sigma => containsBool w sigma).length ≤ k

private instance decidableTkAvoiding (T : List (List Nat)) (k : Nat) (w : List Nat) :
    Decidable (TkAvoiding T k w) := by
  unfold TkAvoiding
  infer_instance

/-- On an empty stack, `pushInput` pushes unconditionally: for pattern families of length at
least two the resulting singleton is `(T, k)`-avoiding, while for a `T` containing a length-one
pattern the paper's algorithm leaves the empty-stack pop case undefined. -/
private def pushInput (T : List (List Nat)) (k x : Nat) :
    List Nat → List Nat × List Nat
  | [] => ([], [x])
  | stack@(a :: rest) =>
      if TkAvoiding T k (x :: stack) then
        ([], x :: stack)
      else
        let r := pushInput T k x rest
        (a :: r.1, r.2)

/-- The `s_{(T,k)}` stack algorithm of page 1: stack listed top-first; push the next
input if the stack stays `(T, k)`-avoiding, otherwise pop the top to the output and
retry; flush the stack top-first at the end. For families whose patterns all have length at
least two this is the page-1 machine, covering `s` and `t`; with a length-one pattern, the paper
does not define a failed singleton push because there is no stack element to pop. -/
def stackRun (T : List (List Nat)) (k : Nat) (stack input : List Nat) : List Nat :=
  match input with
  | [] => stack
  | x :: xs =>
      let r := pushInput T k x stack
      r.1 ++ stackRun T k r.2 xs

/-- West's `s`: the stack avoids `21` read top-to-bottom, i.e. the instance
`s_{({21},0)}` (page 1). -/
def s (pi : List Nat) : List Nat :=
  stackRun [[2, 1]] 0 [] pi

/-- `t := s_{({12,21},1)}` (page 2). -/
def t (pi : List Nat) : List Nat :=
  stackRun [[1, 2], [2, 1]] 1 [] pi

/-- `π` takes exactly `j` sorts by `s ∘ t` (page 6: `m_{(s∘t)}(π) = j`):
the `j`-th iterate is `id_n` and no earlier iterate is. -/
def TakesSorts (pi : List Nat) (j : Nat) : Prop :=
  (fun w => s (t w))^[j] pi = List.range' 1 pi.length ∧
    ∀ i < j, (fun w => s (t w))^[i] pi ≠ List.range' 1 pi.length

private instance decidableTakesSorts (pi : List Nat) (j : Nat) : Decidable (TakesSorts pi j) := by
  unfold TakesSorts
  infer_instance

/-- `π = 2σ1n` with `σ ∈ Av_{n−3}(213)` (page 7). -/
def LemmaForm (n : Nat) (pi : List Nat) : Prop :=
  ∃ sigma : List Nat,
    pi = 2 :: sigma ++ [1, n] ∧
      sigma.Perm (List.range' 3 (n - 3)) ∧
        ¬ Contains sigma [2, 1, 3]

/-- Conjecture 5.2 as printed, for every `n ≥ 3` and every `π ∈ S_n`. -/
def claim : Prop :=
  ∀ n : Nat, 3 ≤ n → ∀ pi : List Nat,
    pi.Perm (List.range' 1 n) →
      (TakesSorts pi (2 * n - 5) ↔ LemmaForm n pi)

example : TkAvoiding [[2, 1], [2, 1]] 1 [2, 1] := by decide +kernel
example : ¬ TkAvoiding [[1, 2], [2, 1]] 1 [2, 3, 1] := by decide +kernel
example : TkAvoiding [[1, 2], [2, 1]] 1 [3, 1] := by decide +kernel

example : t [1, 2, 3] = [3, 2, 1] := by decide +kernel
example : t [1, 3, 2] = [3, 2, 1] := by decide +kernel
example : t [2, 1, 3] = [1, 3, 2] := by decide +kernel
example : t [2, 3, 1] = [3, 1, 2] := by decide +kernel
example : t [3, 1, 2] = [1, 2, 3] := by decide +kernel
example : t [3, 2, 1] = [1, 2, 3] := by decide +kernel

example : s [1, 2, 3] = [1, 2, 3] := by decide +kernel
example : s [1, 3, 2] = [1, 2, 3] := by decide +kernel
example : s [2, 1, 3] = [1, 2, 3] := by decide +kernel
example : s [2, 3, 1] = [2, 1, 3] := by decide +kernel
example : s [3, 1, 2] = [1, 2, 3] := by decide +kernel
example : s [3, 2, 1] = [1, 2, 3] := by decide +kernel

example : 3 ≤ (3 : Nat) ∧ [1, 3, 2].Perm (List.range' 1 3) := by decide +kernel
example : TakesSorts [1, 3, 2] 1 := by decide +kernel

/-- The conjecture is false: `132` takes one sort and is not of the form `2σ13`. -/
theorem result : ¬ claim := by
  intro h
  have sorts : TakesSorts [1, 3, 2] 1 := by decide +kernel
  have form : LemmaForm 3 [1, 3, 2] :=
    (h 3 (by decide) [1, 3, 2] (by decide +kernel)).mp sorts
  rcases form with ⟨sigma, hsigma, -⟩
  simp at hsigma

#print axioms result

end D5.S1.Words.Patterns.MiXuYangPartiallyRestrictedStackMaximalSortRefutation
