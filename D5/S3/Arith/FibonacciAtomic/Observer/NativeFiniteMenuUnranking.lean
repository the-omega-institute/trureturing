/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuUnranking
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: All-menu native representatives invert original ranks with bounded tree height. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking

open GenealogicalFiberTransport (Source decompose)
open ActualTreeReadoutAcquisition (Address)
open ActualImageAddressCertificate (height)
open NativeFiniteMenuCode

private def unrankAux : Nat → Menu → Nat → Source
  | 0, _, _ => .of true
  | h + 1, S, i =>
    if S = [] then .of true else
    if i < N S then
      if branch : i < N (child false S) * N (child true S) then
        let digits := (finProdFinEquiv (m := N (child false S))
          (n := N (child true S))).symm ⟨i, branch⟩
        .mul (unrankAux h (child false S) digits.1.val)
          (unrankAux h (child true S) digits.2.val)
      else if i = N (child false S) * N (child true S) then .of true else .of false
    else .of true

/-- Reverse the original branch-first rank by a finite menu-depth recursion.
All invalid natural indices return alpha. -/
def unrank (S : Menu) (i : Nat) : Source :=
  unrankAux (S.toFinset.sup List.length + 1) S i

private theorem aux_height (h : Nat) (S : Menu) (i : Nat) :
    height (unrankAux h S i) ≤ h := by
  induction h generalizing S i with
  | zero => simp [unrankAux, height, decompose, BinaryTree.height]
  | succ h ih =>
    rw [unrankAux]
    split
    · simp [height, decompose, BinaryTree.height]
    · split
      · split
        · change max (height (unrankAux h _ _)) (height (unrankAux h _ _)) + 1 ≤ h + 1
          exact Nat.add_le_add_right (max_le (ih _ _) (ih _ _)) 1
        · split <;> simp [height, decompose, BinaryTree.height]
      · simp [height, decompose, BinaryTree.height]

private theorem aux_correct (h : Nat) (S : Menu) (i : Nat)
    (depth : ∀ q ∈ S, q.length < h) (valid : i < N S) :
    code S (unrankAux h S i) = i := by
  induction h generalizing S i with
  | zero =>
    have hs : S = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      have := depth q hq
      omega
    subst S
    have g := (original_code_grammar []).1 rfl
    rw [g.1] at valid
    simpa [unrankAux, g.2, show i = 0 by omega]
  | succ h ih =>
    by_cases hs : S = []
    · subst S
      have g := (original_code_grammar []).1 rfl
      rw [g.1] at valid
      simpa [unrankAux, g.2, show i = 0 by omega]
    · have g := (original_code_grammar S).2.1 hs
      have childDepth (b : Bool) : ∀ q ∈ child b S, q.length < h := by
        intro q hq
        have hd := depth (b :: q) ((mem_child b S q).mp hq)
        simp only [List.length_cons] at hd
        omega
      rw [unrankAux]
      simp only [hs, ↓reduceIte, valid, ↓reduceDIte]
      split
      · rename_i branch
        let digits := (finProdFinEquiv (m := N (child false S))
          (n := N (child true S))).symm ⟨i, branch⟩
        rw [g.2.1, ih _ _ (childDepth false) digits.1.isLt,
          ih _ _ (childDepth true) digits.2.isLt]
        have ranked := congrArg Fin.val
          ((finProdFinEquiv (m := N (child false S)) (n := N (child true S))).apply_symm_apply
            ⟨i, branch⟩)
        simpa only [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm] using ranked
      · rename_i branch
        split
        · rename_i alpha
          exact g.2.2.1.trans alpha.symm
        · rename_i alpha
          have hn := g.1
          have he : eta S = true := by
            by_contra he
            simp only [he, ↓reduceIte] at hn
            omega
          simp only [g.2.2.2, he, ↓reduceIte]
          rw [he] at hn
          simp only [↓reduceIte] at hn
          omega

/-- Every original numerical label has one actual native representative, with
an alpha default and the original leaf-zero, branch-max height bound. -/
theorem original_menu_unranking (S : Menu) (i : Nat) :
    (N S ≤ i → unrank S i = .of true) ∧
    (S = [] → unrank S i = .of true ∧ height (unrank S i) = 0) ∧
    (i < N S → code S (unrank S i) = i) ∧
    (S ≠ [] → height (unrank S i) ≤ 1 + S.toFinset.sup List.length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro invalid
    simp only [unrank, unrankAux]
    split
    · rfl
    · simp [show ¬ i < N S by omega]
  · rintro rfl
    simp [unrank, unrankAux, height, decompose, BinaryTree.height]
  · intro valid
    apply aux_correct _ S i _ valid
    intro q hq
    exact Nat.lt_succ_of_le (Finset.le_sup (List.mem_toFinset.mpr hq))
  · intro _
    simpa only [unrank, Nat.add_comm] using aux_height (S.toFinset.sup List.length + 1) S i

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking
