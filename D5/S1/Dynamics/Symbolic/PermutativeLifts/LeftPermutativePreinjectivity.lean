/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-difference preinjectivity for two-sided codes whose local rule is injective in its left endpoint. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity

/-! The finite-difference argument only needs one endpoint permutation. -/

/-!
proof_shape:
  LeftPermutative: definition; consumer: left_preinjective_code.
  left_preinjective_code: content;
    escape_witness: the finite-disagreement maximum coordinate and the resulting equal right tail;
    admission_basis: escape-witness.
Direct frozen dependencies: D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity;
dependency state statement_id: sha256:9fb67b695eed10da02cbe201890996cd808067c2899dda05c098dd6219f74b07;
module statement_id: sha256:71cad9352171405fd2521f247dc327e2136a38b957ec9a6111d98f7f23e1dab4;
statement_ids: LeftPermutative=sha256:bc20e82d9f7dcac3b49a79ed3c07de4011a5af5568f39d778e311ac2543b3f7d,
  left_preinjective_code=sha256:11cd3ae50edbea5353fe96657409293ef95d1c56d5b0e99869071977b542108e;
unfinished Reg audit: https://github.com/the-omega-institute/trureturing/issues/25915;
utility: none; the result is an unbounded symbolic theorem over arbitrary alphabets,
window lengths, and integer configurations, with no bounded enumeration or certified instance.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.LeftPermutativePreinjectivity

open Function
open BipermutativeLift
open BipermutativePreinjectivity
open SymbolicDynamics.FullShift

variable {A : Type*} {k : ℕ}
variable {h : (Fin (k + 2) → A) → A}

/-- A local rule is left-permutative when its left endpoint determines the output injectively
for every fixed right-hand tail. -/
structure LeftPermutative (h : (Fin (k + 2) → A) → A) : Prop where
  left : ∀ v : Prefix A k, Bijective (fun a : A => h (Fin.cons a v))

private def tailAt (m : ℤ) (z : ℤ → A) : Prefix A k :=
  fun j => z (m + ((j : ℕ) + 1))

private theorem window_eq_cons_tail (m : ℤ) (z : ℤ → A) :
    window z m = Fin.cons (z m) (tailAt (k := k) m z) := by
  ext j
  cases j using Fin.cases with
  | zero => simp [window]
  | succ j =>
    simp only [window, Fin.cons_succ, Fin.val_succ, tailAt]
    norm_num

private theorem finite_difference_preinjective (lh : LeftPermutative h)
    {x y : ℤ → A} (hfin : FiniteDifference x y)
    (hcode : code h x = code h y) : x = y := by
  by_contra hxy
  have hsne : ({i : ℤ | x i ≠ y i} : Set ℤ).Nonempty := by
    by_contra hs
    apply hxy
    funext i
    by_contra hne
    exact hs ⟨i, hne⟩
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image
    ({i : ℤ | x i ≠ y i} : Set ℤ) id hfin hsne
  let tx : Prefix A k := tailAt m x
  let ty : Prefix A k := tailAt m y
  have htail : tx = ty := by
    funext j
    by_contra hne
    have hmem : m + ((j : ℕ) + 1) ∈ ({i : ℤ | x i ≠ y i} : Set ℤ) := by
      simpa [tx, ty, tailAt] using hne
    have hle := hmax _ hmem
    have hle' : m + ((j : ℕ) + 1) ≤ m := by simpa using hle
    have hlt : m < m + ((j : ℕ) + 1) := by omega
    exact (not_lt_of_ge hle') hlt
  have hwindow : window x m = Fin.cons (x m) ty := by
    rw [window_eq_cons_tail]
    simpa only [tx] using congrArg
      (fun t : Prefix A k => Fin.cons (n := k + 1) (α := fun _ => A) (x m) t) htail
  have hwindow' : window y m = Fin.cons (y m) ty := by
    rw [window_eq_cons_tail]
  have hcode_m : h (Fin.cons (x m) ty) = h (Fin.cons (y m) ty) := by
    rw [← hwindow, ← hwindow']
    exact congrFun hcode m
  have hxy_m : x m = y m := (lh.left ty).injective hcode_m
  exact hm hxy_m

/-- Left-permutative two-sided codes are preinjective on every finite-difference fibre. -/
theorem left_preinjective_code (lh : LeftPermutative h) : Preinjective h := by
  intro x y hfin hcode
  exact finite_difference_preinjective lh hfin hcode

end D5.S1.Dynamics.Symbolic.PermutativeLifts.LeftPermutativePreinjectivity
