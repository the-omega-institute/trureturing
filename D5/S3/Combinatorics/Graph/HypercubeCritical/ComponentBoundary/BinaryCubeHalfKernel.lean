/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: In even cube dimension the binary adjacency kernel is determined by one half. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import Mathlib.Data.ZMod.Basic

/-! In characteristic two the commuting coordinate involutions have vanishing
cross terms. The odd-dimensional adjacency is an involution and the
kernel in the next even dimension is its graph. This supplies exact
half-cube transport for the binary singleton syndrome in the Q9 fold. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip)

/-- Sum of coordinate flips on binary-valued cube functions. -/
def adjacency {n : ℕ} (f : Q n → ZMod 2) (x : Q n) : ZMod 2 :=
  ∑ i : Fin n, f (flip x i)

private theorem adjacency_add {n : ℕ} (f g : Q n → ZMod 2) :
    adjacency (f + g) = adjacency f + adjacency g := by
  funext x
  simp only [adjacency, Pi.add_apply, Finset.sum_add_distrib]

private theorem adjacency_cons {n : ℕ} (f : Q (n + 1) → ZMod 2) (b : Bool) (x : Q n) :
    adjacency f (Fin.cons b x) = f (Fin.cons (!b) x) +
      adjacency (fun y => f (Fin.cons b y)) x := by
  simp only [adjacency, Fin.sum_univ_succ, BalancedCriticalSpectrum.flip, Fin.cons_zero,
    Fin.update_cons_zero, Fin.cons_succ, ← Fin.cons_update]

/-- Over the binary field, the square of the cube adjacency is dimension
times the identity, in every dimension. -/
theorem adjacency_square {n : ℕ} (f : Q n → ZMod 2) :
    adjacency (adjacency f) = (n : ZMod 2) • f := by
  induction n with
  | zero =>
    funext x
    simp [adjacency]
  | succ n ih =>
    funext z
    rw [← Fin.cons_self_tail z]
    let b := z 0
    let x := Fin.tail z
    change adjacency (adjacency f) (Fin.cons b x) = (↑(n + 1) : ZMod 2) * f (Fin.cons b x)
    rw [adjacency_cons, adjacency_cons]
    simp only [Bool.not_not]
    have hfun : (fun y => adjacency f (Fin.cons b y)) =
        (fun y => f (Fin.cons (!b) y)) + adjacency (fun y => f (Fin.cons b y)) := by
      funext y
      exact adjacency_cons f b y
    rw [hfun, adjacency_add, Pi.add_apply, ih]
    change f (Fin.cons b x) + adjacency (fun y => f (Fin.cons (!b) y)) x +
      (adjacency (fun y => f (Fin.cons (!b) y)) x + (n : ZMod 2) * f (Fin.cons b x)) = _
    have hz : ∀ a : ZMod 2, a + a = 0 := by decide
    rw [Nat.cast_succ]
    calc
      _ = f (Fin.cons b x) + (adjacency (fun y => f (Fin.cons (!b) y)) x +
          adjacency (fun y => f (Fin.cons (!b) y)) x) + (n : ZMod 2) * f (Fin.cons b x) := by ring
      _ = _ := by rw [hz, add_zero]; ring

/-- An odd-dimensional binary adjacency is its own inverse. -/
theorem adjacency_involutive {n : ℕ} (hn : Odd n) :
    Function.Involutive (@adjacency n) := by
  intro f
  obtain ⟨k, hk⟩ := hn
  have hc : (n : ZMod 2) = 1 := by
    rw [hk]
    push_cast
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul, zero_add]
  rw [adjacency_square, hc, one_smul]

/-- In even dimension, a function is in the binary adjacency kernel if and
only if its upper half is the odd-dimensional adjacency of its lower half.
This reconstructs the entire word from one half with no search. -/
theorem adjacency_eq_zero_iff_half {n : ℕ} (hn : Odd n) (f : Q (n + 1) → ZMod 2) :
    adjacency f = 0 ↔
      (fun x => f (Fin.cons true x)) = adjacency (fun x => f (Fin.cons false x)) := by
  constructor
  · intro h
    funext x
    have he := congrFun h (Fin.cons false x)
    rw [adjacency_cons] at he
    change f (Fin.cons true x) + adjacency (fun y => f (Fin.cons false y)) x = 0 at he
    have hz : ∀ a : ZMod 2, -a = a := by decide
    exact (eq_neg_of_add_eq_zero_left he).trans (hz _)
  · intro h
    funext z
    rw [← Fin.cons_self_tail z, adjacency_cons]
    cases hb : z 0
    · change f (Fin.cons true (Fin.tail z)) +
        adjacency (fun y => f (Fin.cons false y)) (Fin.tail z) = 0
      rw [congrFun h]
      exact (show ∀ a : ZMod 2, a + a = 0 from by decide) _
    · change f (Fin.cons false (Fin.tail z)) +
        adjacency (fun y => f (Fin.cons true y)) (Fin.tail z) = 0
      rw [h, adjacency_involutive hn]
      exact (show ∀ a : ZMod 2, a + a = 0 from by decide) _

/-- The fixed and residual words of a binary kernel satisfy an affine
half-cube equation. The known word contributes a fixed syndrome, so the
missing upper half is forced by the lower residual word. -/
theorem adjacency_add_eq_zero_iff_affine_half {n : ℕ} (hn : Odd n)
    (fixed residual : Q (n + 1) → ZMod 2) :
    adjacency (fixed + residual) = 0 ↔
      (fun x => residual (Fin.cons true x)) =
        adjacency (fun x => residual (Fin.cons false x)) +
        ((fun x => fixed (Fin.cons true x)) +
          adjacency (fun x => fixed (Fin.cons false x))) := by
  rw [adjacency_eq_zero_iff_half hn]
  have hfun : (fun x => (fixed + residual) (Fin.cons false x)) =
      (fun x => fixed (Fin.cons false x)) + (fun x => residual (Fin.cons false x)) := rfl
  rw [hfun, adjacency_add]
  have hchar : ∀ a : ZMod 2, a + a = 0 := by decide
  constructor
  · intro h
    funext x
    have he := congrFun h x
    change fixed (Fin.cons true x) + residual (Fin.cons true x) =
      adjacency (fun y => fixed (Fin.cons false y)) x +
        adjacency (fun y => residual (Fin.cons false y)) x at he
    change residual (Fin.cons true x) = _ + (_ + _)
    calc
      _ = fixed (Fin.cons true x) + (fixed (Fin.cons true x) + residual (Fin.cons true x)) := by
        rw [← add_assoc, hchar, zero_add]
      _ = _ := by rw [he]; ring
  · intro h
    funext x
    have he := congrFun h x
    change residual (Fin.cons true x) =
      adjacency (fun y => residual (Fin.cons false y)) x +
        (fixed (Fin.cons true x) + adjacency (fun y => fixed (Fin.cons false y)) x) at he
    change fixed (Fin.cons true x) + residual (Fin.cons true x) = _ + _
    rw [he]
    calc
      _ = (fixed (Fin.cons true x) + fixed (Fin.cons true x)) +
          (adjacency (fun y => fixed (Fin.cons false y)) x +
            adjacency (fun y => residual (Fin.cons false y)) x) := by ring
      _ = _ := by rw [hchar, zero_add]

/-- Flattening the first two axes of a binary kernel word gives four
sections. The sum of the two adjacent sections equals the adjacency of the
given section. This keeps track of the square symmetry of the two axes. -/
theorem adjacency_two_sections_eq {n : ℕ} {f : Q (n + 2) → ZMod 2}
    (hf : adjacency f = 0) (a b : Bool) :
    adjacency (fun x : Q n => f (Fin.cons a (Fin.cons b x))) =
      (fun x : Q n => f (Fin.cons (!a) (Fin.cons b x))) +
      (fun x : Q n => f (Fin.cons a (Fin.cons (!b) x))) := by
  funext x
  have hz := congrFun hf (Fin.cons a (Fin.cons b x))
  rw [adjacency_cons, adjacency_cons] at hz
  change f (Fin.cons (!a) (Fin.cons b x)) +
    (f (Fin.cons a (Fin.cons (!b) x)) +
      adjacency (fun y : Q n => f (Fin.cons a (Fin.cons b y))) x) = 0 at hz
  change adjacency (fun y : Q n => f (Fin.cons a (Fin.cons b y))) x =
    f (Fin.cons (!a) (Fin.cons b x)) + f (Fin.cons a (Fin.cons (!b) x))
  have hneg : ∀ k : ZMod 2, -k = k := by decide
  exact (eq_neg_of_add_eq_zero_right (by simpa only [add_assoc] using hz)).trans (hneg _)

/-- Each sum of opposite sections of a binary kernel word is a kernel word
on the cube with those two axes removed. -/
theorem adjacency_opposite_sections_zero {n : ℕ} {f : Q (n + 2) → ZMod 2}
    (hf : adjacency f = 0) (a b : Bool) :
    adjacency ((fun x : Q n => f (Fin.cons a (Fin.cons b x))) +
      (fun x : Q n => f (Fin.cons (!a) (Fin.cons (!b) x)))) = 0 := by
  rw [adjacency_add, adjacency_two_sections_eq hf a b,
    adjacency_two_sections_eq hf (!a) (!b)]
  simp only [Bool.not_not]
  funext x
  simp only [Pi.add_apply, Pi.zero_apply]
  have hchar : ∀ k : ZMod 2, k + k = 0 := by decide
  rw [add_comm (f (Fin.cons a (Fin.cons (!b) x))) (f (Fin.cons (!a) (Fin.cons b x)))]
  exact hchar _

#print axioms adjacency_square
#print axioms adjacency_eq_zero_iff_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel
