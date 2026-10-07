/- GID: D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.claim; result=D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.result; claim=D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.claim
   digest: A length-3 involution count refutes Class 69 equidistribution. -/

/-
proof_shape: R: definitional data; box: definitional data; IsOccurrence: definitional data;
  occ: definitional data; claim: definitional data; result: bind-only (finite evaluation by decide)
escape_witness: none
admission_basis: open-problem-resolution (#12885; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.MeshPattern.Class69InvolutionRefutation

/-- The four shaded-cell sets in Fang--Fu--Kitaev--Li--Su--Sun, Class 69. -/
def R : Fin 4 → Finset (ℕ × ℕ) := fun a =>
  match a.1 with
  | 0 => {(1, 2), (1, 1), (2, 1), (0, 0)}
  | 1 => {(2, 2), (0, 1), (1, 1), (1, 0)}
  | 2 => {(0, 2), (1, 1), (2, 1), (1, 0)}
  | _ => {(1, 2), (0, 1), (1, 1), (2, 0)}

/-- The box containing a third point relative to two selected points. -/
def box {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j r : Fin n) : ℕ × ℕ :=
  ((if i < r then 1 else 0) + (if j < r then 1 else 0),
    (if σ i < σ r then 1 else 0) + (if σ j < σ r then 1 else 0))

/-- A pair is an occurrence of a shaded length-2 mesh pattern. -/
def IsOccurrence {n : ℕ} (R : Finset (ℕ × ℕ)) (σ : Equiv.Perm (Fin n))
    (i j : Fin n) : Prop :=
  i < j ∧ σ i < σ j ∧ ∀ r, r ≠ i → r ≠ j → box σ i j r ∉ R

/-- The number of occurrences of a shaded length-2 mesh pattern. -/
def occ {n : ℕ} (R : Finset (ℕ × ℕ)) (σ : Equiv.Perm (Fin n)) : ℕ :=
  by
    letI : DecidablePred (fun p : Fin n × Fin n => IsOccurrence R σ p.1 p.2) :=
      fun p => by
        unfold IsOccurrence
        infer_instance
    exact (((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).filter
      fun p : Fin n × Fin n => IsOccurrence R σ p.1 p.2).card

/-- Fang--Fu--Kitaev--Li--Su--Sun, arXiv:2606.14367v1, Conjecture 1: the four Class 69
length-2 mesh patterns are equidistributed on involutions. -/
def claim : Prop :=
  ∀ n k : ℕ, ∀ a b : Fin 4,
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      fun σ => σ * σ = 1 ∧ occ (R a) σ = k).card =
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        fun σ => σ * σ = 1 ∧ occ (R b) σ = k).card

/-- The conjecture fails for n = 3, k = 0, and patterns R 0 and R 2. -/
theorem result : ¬ claim := by
  intro h
  unfold claim at h
  have heq := h 3 0 0 2
  let permTable : Fin 6 → Equiv.Perm (Fin 3) := fun i =>
    match i.1 with
    | 0 => 1
    | 1 => Equiv.swap 0 1
    | 2 => Equiv.swap 1 2
    | 3 => Equiv.swap 0 1 * Equiv.swap 1 2
    | 4 => Equiv.swap 1 2 * Equiv.swap 0 1
    | _ => Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1
  have hbij : Function.Bijective permTable := by
    decide +kernel
  let permEquiv : Fin 6 ≃ Equiv.Perm (Fin 3) := Equiv.ofBijective permTable hbij
  have hcard0 :
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => σ * σ = 1 ∧ occ (R 0) σ = 0).card =
        (Finset.univ.filter fun i : Fin 6 => permTable i * permTable i = 1 ∧
          occ (R 0) (permTable i) = 0).card := by
    symm
    apply Finset.card_equiv permEquiv
    intro i
    simp [permEquiv]
  have hcard2 :
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => σ * σ = 1 ∧ occ (R 2) σ = 0).card =
        (Finset.univ.filter fun i : Fin 6 => permTable i * permTable i = 1 ∧
          occ (R 2) (permTable i) = 0).card := by
    symm
    apply Finset.card_equiv permEquiv
    intro i
    simp [permEquiv]
  rw [hcard0, hcard2] at heq
  have hne :
      (Finset.univ.filter fun i : Fin 6 => permTable i * permTable i = 1 ∧
        occ (R 0) (permTable i) = 0).card ≠
        (Finset.univ.filter fun i : Fin 6 => permTable i * permTable i = 1 ∧
          occ (R 2) (permTable i) = 0).card := by
    decide +kernel
  exact hne heq

end D5.S3.Combinatorics.MeshPattern.Class69InvolutionRefutation
