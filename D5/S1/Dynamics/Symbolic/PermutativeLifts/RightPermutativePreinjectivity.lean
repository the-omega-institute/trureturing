/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-difference preinjectivity for two-sided codes whose local rule is injective in its right endpoint. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.LeftPermutativePreinjectivity

/-! The dual finite-difference argument only needs one endpoint permutation. -/

/-!
proof_shape:
  RightPermutative: definition; consumer: right_preinjective_code.
  right_preinjective_code: content;
    escape_witness: the finite-disagreement minimum coordinate and the resulting equal left window prefix;
    admission_basis: escape-witness.
Direct frozen dependencies: D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity;
dependency state statement_id: sha256:71cad9352171405fd2521f247dc327e2136a38b957ec9a6111d98f7f23e1dab4;
module statement_id: sha256:5944dfcfd286d7df157bb7e3946b2426fe9417a908c9d078776561de1a6a0aed;
statement_ids: RightPermutative=sha256:e51b16c11e932488d60f32102e142490da534e2b0f8400964a444c82e2b31dd2,
  right_preinjective_code=sha256:328ed72cf6e65d05f380532474ca1eecec82426ab690ca6c3a6d4d33d1b5f392;
unfinished Reg audit: https://github.com/the-omega-institute/trureturing/issues/25962
  (template enrollment, source reconstruction, actual-positive law, and whole-family sensitivity remain unperformed);
utility: none; the result is an unbounded symbolic theorem over arbitrary alphabets,
window lengths, and integer configurations, with no bounded enumeration or certified instance.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.RightPermutativePreinjectivity

open Function
open BipermutativeLift
open BipermutativePreinjectivity
open SymbolicDynamics.FullShift

variable {A : Type*} {k : ℕ}
variable {h : (Fin (k + 2) → A) → A}

/-- A local rule is right-permutative when its right endpoint determines the output injectively
for every fixed left-hand prefix. -/
structure RightPermutative (h : (Fin (k + 2) → A) → A) : Prop where
  right : ∀ u : Prefix A k, Bijective (fun b : A => h (Fin.snoc u b))

private def headAt (m : ℤ) (z : ℤ → A) : Prefix A k :=
  fun j => z (m - ((k + 1 : ℕ) : ℤ) + (j : ℕ))

private theorem window_eq_head_snoc (m : ℤ) (z : ℤ → A) :
    window z (m - (k + 1 : ℕ)) = Fin.snoc (headAt (k := k) m z) (z m) := by
  ext j
  cases j using Fin.lastCases with
  | last => simp [window]
  | cast j => simp [window, headAt]

private theorem finite_difference_preinjective (rh : RightPermutative h)
    {x y : ℤ → A} (hfin : FiniteDifference x y)
    (hcode : code h x = code h y) : x = y := by
  by_contra hxy
  have hsne : ({i : ℤ | x i ≠ y i} : Set ℤ).Nonempty := by
    by_contra hs
    apply hxy
    funext i
    by_contra hne
    exact hs ⟨i, hne⟩
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image
    ({i : ℤ | x i ≠ y i} : Set ℤ) id hfin hsne
  let tx : Prefix A k := headAt m x
  let ty : Prefix A k := headAt m y
  have hhead : tx = ty := by
    funext j
    by_contra hne
    have hmem : m - ((k + 1 : ℕ) : ℤ) + (j : ℕ) ∈
        ({i : ℤ | x i ≠ y i} : Set ℤ) := by
      simpa [tx, ty, headAt] using hne
    have hle := hmin _ hmem
    have hlt : m - ((k + 1 : ℕ) : ℤ) + (j : ℕ) < m := by omega
    exact (not_lt_of_ge hle) hlt
  have hwindow : window x (m - (k + 1 : ℕ)) = Fin.snoc tx (x m) := by
    rw [window_eq_head_snoc]
  have hwindow' : window y (m - (k + 1 : ℕ)) = Fin.snoc tx (y m) := by
    rw [window_eq_head_snoc]
    simpa only [ty] using congrArg
      (fun t : Prefix A k => Fin.snoc (α := fun _ => A) t (y m)) hhead.symm
  have hcode_m : h (Fin.snoc tx (x m)) = h (Fin.snoc tx (y m)) := by
    rw [← hwindow, ← hwindow']
    exact congrFun hcode (m - (k + 1 : ℕ))
  have hxy_m : x m = y m := (rh.right tx).injective hcode_m
  exact hm hxy_m

/-- Right-permutative two-sided codes are preinjective on every finite-difference fibre. -/
theorem right_preinjective_code (rh : RightPermutative h) : Preinjective h := by
  intro x y hfin hcode
  exact finite_difference_preinjective rh hfin hcode

end D5.S1.Dynamics.Symbolic.PermutativeLifts.RightPermutativePreinjectivity
