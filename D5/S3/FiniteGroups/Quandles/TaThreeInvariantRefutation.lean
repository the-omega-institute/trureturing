/- GID: D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.claim; result=D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.result; claim=D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.claim
   digest: Full three-invariant counterexample to Ta Problem 11.6. -/

/- admission_basis: open-problem-resolution (#25997).
   proof_shape: content; escape_witness: labelBlockEquiv, used through
   whole_good_card and both complete numerical counts on the live path.
   Escape audit of good_counts is unfinished under the linked issue; no
   declared_validated Reg mirror is claimed. The designated result is exempt.
   The central-label characterization is attributed to Ta Theorem 6.7, with
   our z equal to the inverse of the source's zeta. -/

import D5.S3.FiniteGroups.Quandles.BlockCounting
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! A full counterexample to Ta Problem 11.6. The group laws come from
Mathlib semidirect products; all finite certificate obligations are checked
by kernel reduction, and the complete central-label bijection supplies
exhaustiveness of the good-map counts. -/

namespace D5.S3.FiniteGroups.Quandles.TaThreeInvariantRefutation

open D5.S3.FiniteGroups.Quandles
open BlockCounting

set_option maxRecDepth 10000

private abbrev N := Multiplicative (ZMod 16)
private abbrev H := Multiplicative (ZMod 4)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private def generator (t : Bool) : MulAut N where
  toFun x := Multiplicative.ofAdd ((if t then 7 else 5 : ZMod 16) * x.toAdd)
  invFun x := Multiplicative.ofAdd ((if t then 7 else 13 : ZMod 16) * x.toAdd)
  left_inv := by
    have h : ∀ (t : Bool) (x : N),
        Multiplicative.ofAdd ((if t then 7 else 13 : ZMod 16) *
          ((if t then 7 else 5 : ZMod 16) * x.toAdd)) = x := by decide
    exact h t
  right_inv := by
    have h : ∀ (t : Bool) (x : N),
        Multiplicative.ofAdd ((if t then 7 else 5 : ZMod 16) *
          ((if t then 7 else 13 : ZMod 16) * x.toAdd)) = x := by decide
    exact h t
  map_mul' := by
    intro x y
    cases t <;> exact congrArg Multiplicative.ofAdd (mul_add _ _ _)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private def action (t : Bool) : H →* MulAut N where
  toFun j := generator t ^ j.toAdd.val
  map_one' := rfl
  map_mul' := by
    intro j k
    ext x
    have h : ∀ (t : Bool) (j k : H) (x : N),
        (generator t ^ (j * k).toAdd.val) x =
          ((generator t ^ j.toAdd.val) * (generator t ^ k.toAdd.val)) x := by
      intro t j k
      fin_cases t <;> fin_cases j <;> fin_cases k <;> decide
    exact h t j k x

/-- The native Mathlib semidirect products, with r=5 for false and r=7 for true. -/
abbrev Gr (t : Bool) := N ⋊[action t] H

instance (t : Bool) : Group (Gr t) := inferInstanceAs (Group (N ⋊[action t] H))
instance (t : Bool) : DecidableEq (Gr t) := inferInstanceAs (DecidableEq (N ⋊[action t] H))
instance (t : Bool) : Fintype (Gr t) :=
  Fintype.ofEquiv (N × H) SemidirectProduct.equivProd.symm

private def elt (t : Bool) (i : ZMod 16) (j : ZMod 4) : Gr t :=
  ⟨Multiplicative.ofAdd i, Multiplicative.ofAdd j⟩

private def size5 (b : Fin 10) : ℕ := if b.val = 0 then 4 else 2
private def size7 (b : Fin 7) : ℕ := if b.val < 4 then 4 else 2

private def codeTable5 : Fin 64 → Sigma (fun b : Fin 10 => Fin (size5 b)) :=
  ![⟨0, ⟨0, by decide⟩⟩,
    ⟨1, ⟨0, by decide⟩⟩,
    ⟨7, ⟨0, by decide⟩⟩,
    ⟨1, ⟨1, by decide⟩⟩,
    ⟨2, ⟨0, by decide⟩⟩,
    ⟨3, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨8, ⟨0, by decide⟩⟩,
    ⟨6, ⟨0, by decide⟩⟩,
    ⟨9, ⟨0, by decide⟩⟩,
    ⟨6, ⟨1, by decide⟩⟩,
    ⟨2, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨1, by decide⟩⟩,
    ⟨0, ⟨1, by decide⟩⟩,
    ⟨1, ⟨0, by decide⟩⟩,
    ⟨7, ⟨1, by decide⟩⟩,
    ⟨1, ⟨1, by decide⟩⟩,
    ⟨2, ⟨0, by decide⟩⟩,
    ⟨3, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨8, ⟨1, by decide⟩⟩,
    ⟨6, ⟨0, by decide⟩⟩,
    ⟨9, ⟨1, by decide⟩⟩,
    ⟨6, ⟨1, by decide⟩⟩,
    ⟨2, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨1, by decide⟩⟩,
    ⟨0, ⟨2, by decide⟩⟩,
    ⟨1, ⟨0, by decide⟩⟩,
    ⟨7, ⟨0, by decide⟩⟩,
    ⟨1, ⟨1, by decide⟩⟩,
    ⟨2, ⟨0, by decide⟩⟩,
    ⟨3, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨8, ⟨0, by decide⟩⟩,
    ⟨6, ⟨0, by decide⟩⟩,
    ⟨9, ⟨0, by decide⟩⟩,
    ⟨6, ⟨1, by decide⟩⟩,
    ⟨2, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨1, by decide⟩⟩,
    ⟨0, ⟨3, by decide⟩⟩,
    ⟨1, ⟨0, by decide⟩⟩,
    ⟨7, ⟨1, by decide⟩⟩,
    ⟨1, ⟨1, by decide⟩⟩,
    ⟨2, ⟨0, by decide⟩⟩,
    ⟨3, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨8, ⟨1, by decide⟩⟩,
    ⟨6, ⟨0, by decide⟩⟩,
    ⟨9, ⟨1, by decide⟩⟩,
    ⟨6, ⟨1, by decide⟩⟩,
    ⟨2, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨1, by decide⟩⟩]

private def code5 (x : Gr false) : Sigma (fun b : Fin 10 => Fin (size5 b)) :=
  codeTable5 ⟨x.left.toAdd.val * 4 + x.right.toAdd.val, by
    have h := x.left.toAdd.val_lt; have k := x.right.toAdd.val_lt; omega⟩

private def reprTable5 : Fin 10 → Fin 4 → Gr false :=
  ![![elt false 0 0, elt false 4 0, elt false 8 0, elt false 12 0],
    ![elt false 0 1, elt false 0 3, elt false 0 1, elt false 0 1],
    ![elt false 1 0, elt false 3 0, elt false 1 0, elt false 1 0],
    ![elt false 1 1, elt false 3 3, elt false 1 1, elt false 1 1],
    ![elt false 1 2, elt false 3 2, elt false 1 2, elt false 1 2],
    ![elt false 1 3, elt false 3 1, elt false 1 3, elt false 1 3],
    ![elt false 2 1, elt false 2 3, elt false 2 1, elt false 2 1],
    ![elt false 0 2, elt false 4 2, elt false 0 2, elt false 0 2],
    ![elt false 2 0, elt false 6 0, elt false 2 0, elt false 2 0],
    ![elt false 2 2, elt false 6 2, elt false 2 2, elt false 2 2]]

private def repr5 (c : Sigma (fun b : Fin 10 => Fin (size5 b))) : Gr false :=
  reprTable5 c.1 ⟨c.2.val % 4, Nat.mod_lt _ (by decide)⟩

private def cen5 : Fin 4 → Gr false :=
  ![elt false 0 0, elt false 4 0, elt false 8 0, elt false 12 0]

private def destTable5 : Fin 10 → Fin 4 → Fin 4 → ℕ :=
  ![![![0, 1, 2, 3],
    ![3, 0, 1, 2],
    ![2, 3, 0, 1],
    ![1, 2, 3, 0]],
    ![![1, 1, 1, 1],
    ![0, 0, 0, 0],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]],
    ![![1, 1, 1, 1],
    ![0, 0, 0, 0],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]],
    ![![1, 1, 1, 1],
    ![0, 0, 0, 0],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]],
    ![![1, 1, 1, 1],
    ![0, 0, 0, 0],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]],
    ![![1, 1, 1, 1],
    ![0, 0, 0, 0],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]],
    ![![1, 1, 1, 1],
    ![0, 0, 0, 0],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]],
    ![![0, 1, 0, 1],
    ![1, 0, 1, 0],
    ![0, 1, 0, 1],
    ![0, 1, 0, 1]],
    ![![1, 0, 1, 0],
    ![0, 1, 0, 1],
    ![1, 0, 1, 0],
    ![1, 0, 1, 0]],
    ![![1, 0, 1, 0],
    ![0, 1, 0, 1],
    ![1, 0, 1, 0],
    ![1, 0, 1, 0]]]

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private def dest5 (b : Fin 10) (i : Fin (size5 b)) (z : Fin 4) : Fin (size5 b) :=
  ⟨destTable5 b ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ z, by
    have h : ∀ (b : Fin 10) (i : Fin (size5 b)) (z : Fin 4),
        destTable5 b ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ z < size5 b := by decide
    exact h b i z⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private noncomputable def center5 : Fin 4 ≃ Subgroup.center (Gr false) := by
  have hmem : ∀ z, cen5 z ∈ Subgroup.center (Gr false) := by
    intro z
    fin_cases z <;> decide
  refine Equiv.ofBijective (fun z => ⟨cen5 z, hmem z⟩) ⟨?_, ?_⟩
  · intro z w h
    have hinj : Function.Injective cen5 := by decide
    exact hinj (congrArg Subtype.val h)
  · intro x
    have hsur : ∀ x : Gr false, x ∈ Subgroup.center (Gr false) → ∃ z, cen5 z = x := by
      rintro ⟨i, j⟩
      change Fin 16 at i
      change Fin 4 at j
      fin_cases i <;> fin_cases j <;> decide
    obtain ⟨z, hz⟩ := hsur x.val x.property
    exact ⟨z, Subtype.ext hz⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private noncomputable def data5 : Data (Gr false) (Fin 10) (Fin 4) (fun b => Fin (size5 b)) where
  code := code5
  repr := repr5
  code_repr := by decide
  code_conj := by
    rintro ⟨i, j⟩
    change Fin 16 at i
    change Fin 4 at j
    fin_cases i <;> fin_cases j <;> decide
  repr_conj := by
    rintro ⟨i, j⟩
    change Fin 16 at i
    change Fin 4 at j
    fin_cases i <;> fin_cases j <;> decide
  center := center5
  dest := dest5
  code_twist := by
    rintro ⟨i, j⟩
    change Fin 16 at i
    change Fin 4 at j
    fin_cases i <;> fin_cases j <;> decide

private def codeTable7 : Fin 64 → Sigma (fun b : Fin 7 => Fin (size7 b)) :=
  ![⟨0, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨0, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨1, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨1, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨2, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨2, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨3, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨6, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨6, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨3, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨2, ⟨2, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨2, ⟨3, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨1, ⟨0, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨1, ⟨1, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨0, ⟨2, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨0, ⟨3, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨1, ⟨2, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨1, ⟨3, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨2, ⟨2, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨2, ⟨3, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨2, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨3, ⟨3, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨6, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨6, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨3, ⟨2, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨3, ⟨3, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩,
    ⟨2, ⟨0, by decide⟩⟩,
    ⟨4, ⟨0, by decide⟩⟩,
    ⟨2, ⟨1, by decide⟩⟩,
    ⟨4, ⟨1, by decide⟩⟩,
    ⟨1, ⟨2, by decide⟩⟩,
    ⟨5, ⟨0, by decide⟩⟩,
    ⟨1, ⟨3, by decide⟩⟩,
    ⟨5, ⟨1, by decide⟩⟩]

private def code7 (x : Gr true) : Sigma (fun b : Fin 7 => Fin (size7 b)) :=
  codeTable7 ⟨x.left.toAdd.val * 4 + x.right.toAdd.val, by
    have h := x.left.toAdd.val_lt; have k := x.right.toAdd.val_lt; omega⟩

private def reprTable7 : Fin 7 → Fin 4 → Gr true :=
  ![![elt true 0 0, elt true 0 2, elt true 8 0, elt true 8 2],
    ![elt true 1 0, elt true 1 2, elt true 9 0, elt true 9 2],
    ![elt true 2 0, elt true 2 2, elt true 6 0, elt true 6 2],
    ![elt true 3 0, elt true 3 2, elt true 11 0, elt true 11 2],
    ![elt true 0 1, elt true 0 3, elt true 0 1, elt true 0 1],
    ![elt true 1 1, elt true 1 3, elt true 1 1, elt true 1 1],
    ![elt true 4 0, elt true 4 2, elt true 4 0, elt true 4 0]]

private def repr7 (c : Sigma (fun b : Fin 7 => Fin (size7 b))) : Gr true :=
  reprTable7 c.1 ⟨c.2.val % 4, Nat.mod_lt _ (by decide)⟩

private def cen7 : Fin 4 → Gr true :=
  ![elt true 0 0, elt true 0 2, elt true 8 0, elt true 8 2]

private def destTable7 : Fin 7 → Fin 4 → Fin 4 → ℕ :=
  ![![![0, 1, 2, 3],
    ![1, 0, 3, 2],
    ![2, 3, 0, 1],
    ![3, 2, 1, 0]],
    ![![2, 3, 0, 1],
    ![3, 2, 1, 0],
    ![0, 1, 2, 3],
    ![1, 0, 3, 2]],
    ![![0, 1, 2, 3],
    ![1, 0, 3, 2],
    ![2, 3, 0, 1],
    ![3, 2, 1, 0]],
    ![![2, 3, 0, 1],
    ![3, 2, 1, 0],
    ![0, 1, 2, 3],
    ![1, 0, 3, 2]],
    ![![1, 0, 1, 0],
    ![0, 1, 0, 1],
    ![1, 0, 1, 0],
    ![1, 0, 1, 0]],
    ![![1, 0, 1, 0],
    ![0, 1, 0, 1],
    ![1, 0, 1, 0],
    ![1, 0, 1, 0]],
    ![![0, 1, 0, 1],
    ![1, 0, 1, 0],
    ![0, 1, 0, 1],
    ![0, 1, 0, 1]]]

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private def dest7 (b : Fin 7) (i : Fin (size7 b)) (z : Fin 4) : Fin (size7 b) :=
  ⟨destTable7 b ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ z, by
    have h : ∀ (b : Fin 7) (i : Fin (size7 b)) (z : Fin 4),
        destTable7 b ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ z < size7 b := by decide
    exact h b i z⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private noncomputable def center7 : Fin 4 ≃ Subgroup.center (Gr true) := by
  have hmem : ∀ z, cen7 z ∈ Subgroup.center (Gr true) := by
    intro z
    fin_cases z <;> decide
  refine Equiv.ofBijective (fun z => ⟨cen7 z, hmem z⟩) ⟨?_, ?_⟩
  · intro z w h
    have hinj : Function.Injective cen7 := by decide
    exact hinj (congrArg Subtype.val h)
  · intro x
    have hsur : ∀ x : Gr true, x ∈ Subgroup.center (Gr true) → ∃ z, cen7 z = x := by
      rintro ⟨i, j⟩
      change Fin 16 at i
      change Fin 4 at j
      fin_cases i <;> fin_cases j <;> decide
    obtain ⟨z, hz⟩ := hsur x.val x.property
    exact ⟨z, Subtype.ext hz⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private noncomputable def data7 : Data (Gr true) (Fin 7) (Fin 4) (fun b => Fin (size7 b)) where
  code := code7
  repr := repr7
  code_repr := by decide
  code_conj := by
    rintro ⟨i, j⟩
    change Fin 16 at i
    change Fin 4 at j
    fin_cases i <;> fin_cases j <;> decide
  repr_conj := by
    rintro ⟨i, j⟩
    change Fin 16 at i
    change Fin 4 at j
    fin_cases i <;> fin_cases j <;> decide
  center := center7
  dest := dest7
  code_twist := by
    rintro ⟨i, j⟩
    change Fin 16 at i
    change Fin 4 at j
    fin_cases i <;> fin_cases j <;> decide

private def count5 (b : Fin 10) : ℕ := if b.val = 0 then 10 else if b.val < 7 then 4 else 6
private def count7 (b : Fin 7) : ℕ := if b.val < 4 then 10 else 6

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private theorem local_counts5 : ∀ b : Fin 10,
    Fintype.card (Local dest5 b) = count5 b := by
  intro b
  fin_cases b <;> decide

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
private theorem local_counts7 : ∀ b : Fin 7,
    Fintype.card (Local dest7 b) = count7 b := by
  intro b
  fin_cases b <;> decide

/-- Cardinality of all good maps of the whole conjugation quandle, using
exactly the existing repository definition. -/
noncomputable def goodCount (G : Type*) [Group G] [Fintype G] [DecidableEq G] : ℕ :=
  Nat.card (D5.S3.FiniteGroups.Quandles.ConjugationSubquandle.Good
    (Finset.univ : Finset G) (by intro x _ y _; exact Finset.mem_univ _))

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete finite certificate for this declaration.
/-- The two complete counts; every local label assignment is counted, and
the general bijection proves that every good map is obtained exactly once. -/
theorem good_counts : goodCount (Gr false) = 8847360 ∧ goodCount (Gr true) = 2160000 := by
  constructor
  · change Nat.card _ = _
    rw [whole_good_card data5]
    have h : ∀ b : Fin 10, Nat.card (Local data5.dest b) = count5 b := by
      intro b
      rw [Nat.card_eq_fintype_card]
      exact local_counts5 b
    simp_rw [h]
    decide
  · change Nat.card _ = _
    rw [whole_good_card data7]
    have h : ∀ b : Fin 7, Nat.card (Local data7.dest b) = count7 b := by
      intro b
      rw [Nat.card_eq_fintype_card]
      exact local_counts7 b
    simp_rw [h]
    decide

/-- The three-invariant determination assertion of Ta, Problem 11.6, for
finite nonabelian groups. Equality is of counts of maps, not isomorphism types. -/
def claim : Prop :=
  ∀ (G K : Type) [Group G] [Group K] [Fintype G] [Fintype K]
    [DecidableEq G] [DecidableEq K],
    (∃ x y : G, x * y ≠ y * x) → (∃ x y : K, x * y ≠ y * x) →
    Nat.card G = Nat.card K →
    Nat.card (Subgroup.center G) = Nat.card (Subgroup.center K) →
    Nat.card (ConjClasses G) = Nat.card (ConjClasses K) →
    goodCount G = goodCount K

/-- Both groups have invariant triple (64,4,22), but their complete counts
are different, refuting the original universal determination assertion. -/
theorem result : ¬ claim := by
  intro h
  have hn5 : ∃ x y : Gr false, x * y ≠ y * x := by
    exact ⟨elt false 1 0, elt false 0 1, by decide⟩
  have hn7 : ∃ x y : Gr true, x * y ≠ y * x := by
    exact ⟨elt true 1 0, elt true 0 1, by decide⟩
  have ho5 : Nat.card (Gr false) = 64 := by rw [Nat.card_eq_fintype_card]; decide
  have ho7 : Nat.card (Gr true) = 64 := by rw [Nat.card_eq_fintype_card]; decide
  have hz5 : Nat.card (Subgroup.center (Gr false)) = 4 := by
    rw [← Nat.card_congr center5]; simp
  have hz7 : Nat.card (Subgroup.center (Gr true)) = 4 := by
    rw [← Nat.card_congr center7]; simp
  have hk5 : Nat.card (ConjClasses (Gr false)) = 22 := by
    rw [Nat.card_congr (classEquiv data5), Nat.card_eq_fintype_card]
    decide
  have hk7 : Nat.card (ConjClasses (Gr true)) = 22 := by
    rw [Nat.card_congr (classEquiv data7), Nat.card_eq_fintype_card]
    decide
  have he := h (Gr false) (Gr true) hn5 hn7 (ho5.trans ho7.symm)
    (hz5.trans hz7.symm) (hk5.trans hk7.symm)
  rw [good_counts.1, good_counts.2] at he
  norm_num at he

#print axioms result

end D5.S3.FiniteGroups.Quandles.TaThreeInvariantRefutation
