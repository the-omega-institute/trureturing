/- GID: D5/S3/StatisticalMechanics/FccPointGroupShells
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/FccPointGroupShells
   mirror-E: none(waiver:noncomputational-symbolic-identity)
   anchors: []
   utility: none
   digest: Signed permutation orbits on contact graph shells of the face centered cubic lattice. -/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-! Point-group orbit counting in the face centered cubic contact graph. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.StatisticalMechanics.FccPointGroupShells

/-- The even-sum integer lattice in three dimensions. -/
abbrev L := {x : Fin 3 → ℤ // (∑ i, x i) % 2 = 0}

/-- The twelve contact steps: two coordinates change by a unit and the third is fixed. -/
def contactGraph : SimpleGraph L where
  Adj x y :=
    (|(y.1 0 - x.1 0)| = 1 ∧ |(y.1 1 - x.1 1)| = 1 ∧ y.1 2 = x.1 2) ∨
    (|(y.1 0 - x.1 0)| = 1 ∧ y.1 1 = x.1 1 ∧ |(y.1 2 - x.1 2)| = 1) ∨
    (y.1 0 = x.1 0 ∧ |(y.1 1 - x.1 1)| = 1 ∧ |(y.1 2 - x.1 2)| = 1)
  symm := ⟨by
    intro x y h
    simpa only [abs_sub_comm, eq_comm] using h⟩
  loopless := ⟨by intro x h; simp at h⟩

/-- The origin of the lattice. -/
def origin : L := ⟨0, by simp⟩

/-- Genuine shortest-walk distance in the contact graph. -/
def d (x : L) : ℕ := contactGraph.dist origin x

/-- All signed coordinate permutations, represented faithfully as permutations of integer triples. -/
def W : Subgroup (Equiv.Perm (Fin 3 → ℤ)) where
  carrier := {w | ∃ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ x i, w x i = s i * x (p i)}
  one_mem' := ⟨1, fun _ => 1, fun _ => Or.inl rfl, by intros; simp⟩
  mul_mem' := by
    rintro w v ⟨p, s, hs, hw⟩ ⟨q, t, ht, hv⟩
    refine ⟨p.trans q, fun i => s i * t (p i), ?_, ?_⟩
    · intro i
      rcases hs i with h | h <;> rcases ht (p i) with h' | h' <;> simp [h, h']
    · intro x i
      change w (v x) i = _
      rw [hw, hv]
      simp [mul_assoc]
  inv_mem' := by
    rintro w ⟨p, s, hs, hw⟩
    refine ⟨p.symm, fun i => s (p.symm i), fun i => hs _, ?_⟩
    intro x i
    have h := hw (w.symm x) (p.symm i)
    simp only [Equiv.apply_symm_apply] at h
    change w.symm x i = _
    rcases hs (p.symm i) with he | he <;> simp_all

private def norm (x : Fin 3 → ℤ) (i : Fin 3) : ℕ := (x i).natAbs

private lemma norm_signed (w : W) : ∃ p : Equiv.Perm (Fin 3),
    ∀ x, norm (w.1 x) = norm x ∘ p := by
  obtain ⟨p, s, hs, hw⟩ := w.2
  refine ⟨p, fun x => funext fun i => ?_⟩
  dsimp only [norm, Function.comp_apply]
  rw [hw]
  rcases hs i with h | h <;> simp [h]

private lemma parity_norm (x : Fin 3 → ℤ) :
    (∑ i, x i) % 2 = ((∑ i, norm x i : ℕ) : ℤ) % 2 := by
  simp only [Fin.sum_univ_three, Nat.cast_add, norm, Int.natCast_natAbs]
  rcases le_total 0 (x 0) with h0 | h0 <;>
    rcases le_total 0 (x 1) with h1 | h1 <;>
      rcases le_total 0 (x 2) with h2 | h2 <;>
        simp only [abs_of_nonneg, abs_of_nonpos, h0, h1, h2] <;> omega

private lemma signed_preserves (w : W) (x : L) : (∑ i, w.1 x.1 i) % 2 = 0 := by
  obtain ⟨p, hp⟩ := norm_signed w
  rw [parity_norm, hp]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp, ← parity_norm]
  exact x.2

/-- The literal signed permutation action restricted to the lattice. -/
instance latticeAction : MulAction W L where
  smul w x := ⟨w.1 x.1, signed_preserves w x⟩
  one_smul x := Subtype.ext (by rfl)
  mul_smul w v x := Subtype.ext (by rfl)

/-- The radius-n shell, including the origin shell at n=0. -/
def Shell (n : ℕ) := {x : L // d x = n}

/-- Number of signed permutation orbits on the shell, using the restricted orbit relation. -/
def A (n : ℕ) : ℕ :=
  Nat.card (Quotient ((MulAction.orbitRel W L).comap (Subtype.val : Shell n → L)))

private def potential (x : Fin 3 → ℤ) : ℕ :=
  max (Finset.univ.sup (norm x)) ((∑ i, norm x i) / 2)

private lemma potential_signed (w : W) (x : Fin 3 → ℤ) :
    potential (w.1 x) = potential x := by
  obtain ⟨p, hp⟩ := norm_signed w
  dsimp only [potential]
  rw [hp]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp]
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := norm x) (Finset.mem_univ (p i))
  · apply Finset.sup_le
    intro i _
    simpa using Finset.le_sup (f := norm x ∘ p) (Finset.mem_univ (p.symm i))

private def signed (p : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) : W :=
  ⟨{ toFun := fun x i => s i * x (p i)
     invFun := fun x i => s (p.symm i) * x (p.symm i)
     left_inv := by
       intro x; funext i
       change s (p.symm i) * (s (p.symm i) * x (p (p.symm i))) = x i
       rcases hs (p.symm i) with h | h <;> simp [h]
     right_inv := by
       intro x; funext i
       change s i * (s (p.symm (p i)) * x (p.symm (p i))) = x i
       rcases hs i with h | h <;> simp [h] }, p, s, hs, by intros; rfl⟩

private def canonical (x : Fin 3 → ℤ) : Fin 3 → ℕ :=
  norm x ∘ Tuple.sort (norm x)

private lemma canonical_mono (x : Fin 3 → ℤ) : Monotone (canonical x) :=
  Tuple.monotone_sort _

private lemma canonical_signed (w : W) (x : Fin 3 → ℤ) :
    canonical (w.1 x) = canonical x := by
  obtain ⟨p, hp⟩ := norm_signed w
  dsimp only [canonical]
  rw [hp]
  exact Tuple.comp_perm_comp_sort_eq_comp_sort

private lemma to_canonical (x : Fin 3 → ℤ) :
    ∃ w : W, w.1 x = fun i => (canonical x i : ℤ) := by
  let p := Tuple.sort (norm x)
  let s : Fin 3 → ℤ := fun i => if 0 ≤ x (p i) then 1 else -1
  have hs : ∀ i, s i = 1 ∨ s i = -1 := by intro i; dsimp [s]; split <;> simp
  refine ⟨signed p s hs, ?_⟩
  funext i
  change s i * x (p i) = (x (p i)).natAbs
  rw [Int.natCast_natAbs]
  dsimp only [s]
  split <;> simp_all [abs_of_nonneg, abs_of_neg]

end D5.S3.StatisticalMechanics.FccPointGroupShells
