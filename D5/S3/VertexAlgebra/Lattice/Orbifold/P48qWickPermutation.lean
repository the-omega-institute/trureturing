/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qWickPermutation
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Permutation invariance of first-oscillator Wick sums by occurrence. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qArbitraryWickRecursion

/-!
Permutation invariance of the finite first-oscillator Wick recursion.
The occurrence sums use the labelled-remainder argument of
`LatticeHalfFockFiniteCorrection.correctionWord_matching` directly on list positions.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qArbitraryWickRecursion

variable {I M : Type*} [AddCommMonoid M]

private def sumErase (word : List I) (f : I → List I → M) : M :=
  ∑ j : Fin word.length, f (word.get j) (word.eraseIdx j)

private theorem sumErase_cons (a : I) (tail : List I) (f : I → List I → M) :
    sumErase (a :: tail) f = f a tail + sumErase tail (fun b rest => f b (a :: rest)) := by
  unfold sumErase
  exact Fin.sum_univ_succ (fun j : Fin (tail.length + 1) =>
    f ((a :: tail).get j) ((a :: tail).eraseIdx j))

private theorem sumErase_add (word : List I) (f g : I → List I → M) :
    sumErase word (fun a rest => f a rest + g a rest) = sumErase word f + sumErase word g :=
  Finset.sum_add_distrib

private theorem sumErase_perm {left right : List I} (h : left.Perm right)
    (f : I → List I → M)
    (hf : ∀ a {xs ys : List I}, xs.Perm ys → xs.length < left.length → f a xs = f a ys) :
    sumErase left f = sumErase right f := by
  induction h generalizing f with
  | nil => rfl
  | @cons a xs ys h ih =>
    rw [sumErase_cons, sumErase_cons, hf a h (by simp)]
    congr 1
    apply ih
    intro b rest other hp hlen
    exact hf b (hp.cons a) (Nat.succ_lt_succ hlen)
  | swap a b tail =>
    simp only [sumErase_cons]
    have rest :
        sumErase tail (fun c xs => f c (b :: a :: xs)) =
          sumErase tail (fun c xs => f c (a :: b :: xs)) := by
      unfold sumErase
      apply Finset.sum_congr rfl
      intro j _
      have hlen := List.length_eraseIdx_add_one j.isLt
      exact hf _ (List.Perm.swap a b _) (by simp only [List.length_cons]; omega)
    rw [rest, add_left_comm]
  | trans h₁ _ ih₁ ih₂ =>
    apply (ih₁ f hf).trans (ih₂ f ?_)
    intro a xs ys hp hlen
    apply hf a hp
    rwa [h₁.length_eq]

/-- Choose two distinct positions in either order, leaving the same remainder. -/
private theorem sumErase_twice_swap (word : List I) (f : I → I → List I → M) :
    sumErase word (fun a rest => sumErase rest (fun b xs => f a b xs)) =
      sumErase word (fun b rest => sumErase rest (fun a xs => f a b xs)) := by
  induction word generalizing f with
  | nil => rfl
  | cons c tail ih =>
    simp only [sumErase_cons, sumErase_add]
    rw [ih (fun a b xs => f a b (c :: xs)), add_left_comm]

variable [Module ℂ M]

private theorem smul_sumErase (c : ℂ) (word : List I) (f : I → List I → M) :
    c • sumErase word f = sumErase word (fun a rest => c • f a rest) :=
  Finset.smul_sum

variable (A : Matrix I I ℂ) (μ : I → ℂ) (normal : List I → M)

private theorem normalWick_cons_sumErase (pre : List I) (a : I) (pending : List I) :
    normalWick A μ normal (a :: pending) pre =
      normalWick A μ normal pending (pre ++ [a]) +
        μ a • normalWick A μ normal pending pre +
        sumErase pending (fun b rest => A a b • normalWick A μ normal rest pre) :=
  normalWick_step A μ normal pre a pending

private theorem normalWick_prefix_perm
    (hN : ∀ {xs ys : List I}, xs.Perm ys → normal xs = normal ys)
    (word : List I) {pre other : List I} (h : pre.Perm other) :
    normalWick A μ normal word pre = normalWick A μ normal word other := by
  cases word with
  | nil => simpa only [normalWick_nil] using hN h
  | cons a tail =>
    rw [normalWick_step, normalWick_step,
      normalWick_prefix_perm hN tail (h.append_right [a]),
      normalWick_prefix_perm hN tail h]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [normalWick_prefix_perm hN (tail.eraseIdx j) h]
termination_by word.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private theorem normalWick_swap_heads
    (hA : ∀ a b, A a b = A b a)
    (hN : ∀ {xs ys : List I}, xs.Perm ys → normal xs = normal ys)
    (a b : I) (tail pre : List I) :
    normalWick A μ normal (a :: b :: tail) pre =
      normalWick A μ normal (b :: a :: tail) pre := by
  have prefixPerm : ((pre ++ [a]) ++ [b]).Perm ((pre ++ [b]) ++ [a]) := by
    simpa only [List.append_assoc, List.singleton_append] using
      (List.Perm.swap b a []).append_left pre
  have doublePair :
      sumErase tail (fun x rest => sumErase rest
          (fun y xs => (A a x * A b y) • normalWick A μ normal xs pre)) =
        sumErase tail (fun y rest => sumErase rest
          (fun x xs => (A b y * A a x) • normalWick A μ normal xs pre)) := by
    rw [sumErase_twice_swap tail (fun x y xs => (A a x * A b y) •
      normalWick A μ normal xs pre)]
    simp only [mul_comm (A a _) (A b _)]
  simp only [normalWick_cons_sumErase, sumErase_cons, smul_add, sumErase_add, smul_sumErase,
    smul_smul]
  rw [normalWick_prefix_perm A μ normal hN tail prefixPerm, hA a b, mul_comm (μ a) (μ b),
    doublePair]
  simp only [mul_comm (A _ _) (μ _)]
  abel

/-- The existing finite Wick recursion is invariant under permutation of its pending word.
The prefix is arbitrary and each occurrence contributes its own indexed partner term. -/
theorem normalWick_perm
    (hA : ∀ a b, A a b = A b a)
    (hN : ∀ {xs ys : List I}, xs.Perm ys → normal xs = normal ys)
    {left right : List I} (h : left.Perm right) (pre : List I) :
    normalWick A μ normal left pre = normalWick A μ normal right pre := by
  suffices bounded : ∀ (n : ℕ) {xs ys : List I}, xs.Perm ys → xs.length ≤ n →
      ∀ pendingPrefix : List I,
        normalWick A μ normal xs pendingPrefix = normalWick A μ normal ys pendingPrefix by
    exact bounded left.length h le_rfl pre
  intro n
  induction n with
  | zero =>
    intro xs ys hp hlen pendingPrefix
    have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    have hy : ys = [] := List.length_eq_zero_iff.mp (hp.length_eq.symm.trans
      (Nat.eq_zero_of_le_zero hlen))
    rw [hx, hy]
  | succ n ih =>
    intro xs ys hp hlen pendingPrefix
    induction hp with
    | nil => rfl
    | @cons a xs ys hp _ =>
      have htail : xs.length ≤ n := Nat.le_of_succ_le_succ hlen
      rw [normalWick_cons_sumErase, normalWick_cons_sumErase,
        ih hp htail (pendingPrefix ++ [a]), ih hp htail pendingPrefix]
      congr 1
      apply sumErase_perm hp
      intro b rest other hrest hsize
      rw [ih hrest ((Nat.le_of_lt hsize).trans htail) pendingPrefix]
    | swap a b tail => exact normalWick_swap_heads A μ normal hA hN b a tail pendingPrefix
    | trans hp₁ _ ih₁ ih₂ =>
      exact (ih₁ hlen).trans (ih₂ (hp₁.length_eq ▸ hlen))

#print axioms normalWick_perm

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qArbitraryWickRecursion
