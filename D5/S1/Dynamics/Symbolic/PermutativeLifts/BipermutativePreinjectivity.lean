/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-difference preinjectivity for bipermutative two-sided codes. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift

/-! Finite-difference preinjectivity. -/

/-!
proof_shape:
  FiniteDifference: definition; consumers: Preinjective, finite_difference_preinjective.
  Preinjective: definition; consumer: preinjective_code.
  tailAt: definition; bind-only organization;
    consumers: window_eq_cons_tail, finite_difference_preinjective.
  window_eq_cons_tail: bind-only; escape_witness: none;
    consumer: finite_difference_preinjective.
  finite_difference_preinjective: content;
    escape_witness: the finite-disagreement maximum coordinate and the resulting equal right tail;
    consumer: preinjective_code.
  preinjective_code: content; escape_witness: finite_difference_preinjective;
    admission_basis: escape-witness.
Direct frozen dependencies: D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift;
statement_id: sha256:43228dc3658ae4dbde29cdff50c2612a33ba40ab4ebe31528f930f6afb333c80.
utility: none; the theorem is an unbounded symbolic statement over arbitrary
alphabets, window lengths, and integer configurations, with no bounded enumeration,
checker, numeric reduction, or certified instance.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity

open Function
open BipermutativeLift
open SymbolicDynamics.FullShift

variable {A : Type*} {k : ℕ}
variable {h : (Fin (k + 2) → A) → A}

/-- Two configurations differ only on a finite set of integer coordinates. -/
def FiniteDifference (x y : ℤ → A) : Prop :=
  Set.Finite {i : ℤ | x i ≠ y i}

/-- The finite-difference preinjectivity predicate for a two-sided code. -/
def Preinjective (h : (Fin (k + 2) → A) → A) : Prop :=
  ∀ ⦃x y : ℤ → A⦄, FiniteDifference x y → code h x = code h y → x = y

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

private theorem finite_difference_preinjective (bh : Bipermutative h)
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
    have hlt : m < m + ((j : ℕ) + 1) := by
      omega
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
  have hxy_m : x m = y m := (bh.left ty).injective hcode_m
  exact hm hxy_m

/-- A bipermutative code is preinjective on every finite-difference fibre. -/
theorem preinjective_code (bh : Bipermutative h) : Preinjective h := by
  intro x y hfin hcode
  exact finite_difference_preinjective bh hfin hcode


end D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity
