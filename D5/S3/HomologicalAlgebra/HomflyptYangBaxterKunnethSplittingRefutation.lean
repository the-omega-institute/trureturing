/- GID: D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.claim; result=D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.result; claim=D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.claim
   digest: The HOMFLYPT Yang-Baxter Künneth subcomplex has no chain retraction for two letters. -/

/-
proof_shape: result: bind-only (finite boundary normalization and the linear retraction contradiction).
escape_witness: none.
admission_basis: open-problem-resolution (#11622; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
noncomputable section
namespace D5.S3.HomologicalAlgebra.HomflyptYangBaxterKunnethSplittingRefutation

def normalizedR (m : ℕ) (a b : Fin m) : (Fin m × Fin m) →₀ Polynomial ℤ :=
  if a ≥ b then Finsupp.single (b, a) 1
  else Finsupp.single (a, b) (1-Polynomial.X) + Finsupp.single (b, a) Polynomial.X

def leftMove {m n : ℕ} (w : (Fin (n+1) → Fin m)) (i : Fin (n+1)) : (Fin n → Fin m) →₀ Polynomial ℤ :=
  match i with
  | ⟨0, _⟩ => Finsupp.single (Matrix.vecTail w) 1
  | ⟨k+1, h⟩ =>
      let j : Fin n := ⟨k, Nat.lt_of_succ_lt_succ h⟩
      let jp : Fin (n+1) := j.castSucc
      let jq : Fin (n+1) := j.succ
      Finsupp.linearCombination (Polynomial ℤ) (fun ab =>
        leftMove (Function.update (Function.update w j.castSucc ab.1) j.succ ab.2) j.castSucc) (normalizedR m (w jp) (w jq))

def rightMove {m n : ℕ} (w : (Fin (n+1) → Fin m)) (i : Fin (n+1)) : (Fin n → Fin m) →₀ Polynomial ℤ :=
  match i with
  | ⟨0, _⟩ => Finsupp.single (Fin.init w) 1
  | ⟨k+1, h⟩ =>
      let j : Fin n := (⟨k, Nat.lt_of_succ_lt_succ h⟩ : Fin n).rev
      let jp : Fin (n+1) := j.castSucc
      let jq : Fin (n+1) := j.succ
      let next : Fin (n+1) := ⟨k, by omega⟩
      Finsupp.linearCombination (Polynomial ℤ) (fun ab =>
        rightMove (Function.update (Function.update w j.castSucc ab.1) j.succ ab.2) next) (normalizedR m (w jp) (w jq))

/-- The left face moves position i to the left wall and deletes the first letter. -/
def leftFace (m n : ℕ) (i : Fin (n+1)) : ((Fin (n+1) → Fin m) →₀ Polynomial ℤ) →ₗ[Polynomial ℤ] ((Fin n → Fin m) →₀ Polynomial ℤ) :=
  Finsupp.linearCombination (Polynomial ℤ) (fun w => leftMove w i)

/-- The right face moves position i to the right wall and deletes the last letter. -/
def rightFace (m n : ℕ) (i : Fin (n+1)) : ((Fin (n+1) → Fin m) →₀ Polynomial ℤ) →ₗ[Polynomial ℤ] ((Fin n → Fin m) →₀ Polynomial ℤ) :=
  Finsupp.linearCombination (Polynomial ℤ) (fun w => rightMove w i.rev)

/-- The alternating difference of the two faces, with the paper's one-based signs. -/
def differential : (m n : ℕ) → ((Fin n → Fin m) →₀ Polynomial ℤ) →ₗ[Polynomial ℤ] ((Fin (n-1) → Fin m) →₀ Polynomial ℤ)
  | _, 0 => 0
  | m, n+1 => ∑ i : Fin (n+1), ((-1 : Polynomial ℤ) ^ (i.val+1)) •
      (leftFace m n i - rightFace m n i)

/-- Definition 5.4 permits every cutoff, including the two empty blocks. -/
def blockWord (m : ℕ) (A B : Finset (Fin m)) (n : ℕ) (w : Fin n → Fin m) : Prop :=
  ∃ i : Fin (n+1), (∀ j : Fin n, j.val < i.val → w j ∈ A) ∧
    (∀ j : Fin n, i.val ≤ j.val → w j ∈ B)

/-- A linear retraction in every degree, commuting with the boundary after inclusion.
The second equality is the chain-map equality for the restricted differential, expressed
in the ambient module through its injective subtype map. -/
def splits (m : ℕ) (A B : Finset (Fin m)) : Prop :=
  ∃ p : ∀ n, ((Fin n → Fin m) →₀ Polynomial ℤ) →ₗ[Polynomial ℤ] (Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin n → Fin m | blockWord m A B n w}),
    (∀ n, (p n).comp ((Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin n → Fin m | blockWord m A B n w})).subtype = LinearMap.id) ∧
    (∀ n (c : (Fin (n+1) → Fin m) →₀ Polynomial ℤ),
      (p n (differential m (n+1) c) : (Fin n → Fin m) →₀ Polynomial ℤ) =
        differential m (n+1) (p (n+1) c : (Fin (n+1) → Fin m) →₀ Polynomial ℤ))

/-- Conjecture 5.6, universally quantified over the ordered decompositions. -/
def claim : Prop :=
  ∀ (m : ℕ) (A B : Finset (Fin m)), A ∪ B = Finset.univ →
    (∀ a ∈ A, ∀ b ∈ B, b ≤ a) → splits m A B

set_option maxHeartbeats 4000000 in
/-- The two-letter ordered decomposition contradicts the asserted chain splitting. -/
theorem result : ¬ claim := by
  classical
  intro h
  let A : Finset (Fin 2) := {1}
  let B : Finset (Fin 2) := {0}
  obtain ⟨p, hp, hc⟩ := h 2 A B (by decide) (by decide)
  let t : Polynomial ℤ := Polynomial.X
  let u : Fin 4 → Fin 2 := ![1,1,1,0]
  let v : Fin 4 → Fin 2 := ![1,0,0,0]
  let e : (Fin 4 → Fin 2) →₀ Polynomial ℤ := Finsupp.single u 1 - Finsupp.single v 1
  let q : Polynomial ℤ := t^3 * (t^2-1)
  let c : (Fin 5 → Fin 2) →₀ Polynomial ℤ :=
    (t * (t+1)) • Finsupp.single ![(0 : Fin 2),0,0,0,1] (1 : Polynomial ℤ) +
    (t^3+t^2+t+1) • Finsupp.single ![(0 : Fin 2),0,0,1,0] (1 : Polynomial ℤ) +
    t • Finsupp.single ![(0 : Fin 2),0,1,0,1] (1 : Polynomial ℤ) -
    t • Finsupp.single ![(0 : Fin 2),1,0,0,1] (1 : Polynomial ℤ) +
    t^3 • Finsupp.single ![(0 : Fin 2),1,1,0,0] (1 : Polynomial ℤ) +
    t^2 • Finsupp.single ![(0 : Fin 2),1,1,1,0] (1 : Polynomial ℤ)
  have hd : differential 2 5 c = q • e := by
    simp only [c, map_add, map_sub, map_smul, differential,
      leftFace, rightFace,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    apply Finsupp.ext
    intro w
    simp [leftMove.eq_def, rightMove.eq_def, normalizedR,
      Finsupp.linearCombination_single, Fin.rev, e, q]
    fin_cases w <;> simp +decide [Finsupp.single_apply, Matrix.vecTail, u, v]
    all_goals ring
  have hu : blockWord 2 A B 4 u := by
    refine ⟨3, ?_, ?_⟩ <;> intro j hj <;> fin_cases j <;> simp_all [A, B, u]
  have hv : blockWord 2 A B 4 v := by
    refine ⟨1, ?_, ?_⟩ <;> intro j hj <;> fin_cases j <;> simp_all [A, B, v]
  have he : e ∈ (Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin 4 → Fin 2 | blockWord 2 A B 4 w}) :=
    ((Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin 4 → Fin 2 | blockWord 2 A B 4 w})).sub_mem
      (Finsupp.single_mem_supported (Polynomial ℤ) 1 hu)
      (Finsupp.single_mem_supported (Polynomial ℤ) 1 hv)
  have hqe : q • e ∈ (Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin 4 → Fin 2 | blockWord 2 A B 4 w}) :=
    ((Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin 4 → Fin 2 | blockWord 2 A B 4 w})).smul_mem q he
  have hz : ∀ x : (Fin 5 → Fin 2) →₀ Polynomial ℤ, x ∈ (Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin 5 → Fin 2 | blockWord 2 A B 5 w}) → differential 2 5 x = 0 := by
    intro x hx
    rw [Finsupp.supported_eq_span_single] at hx
    apply Submodule.span_induction (p := fun x _ => differential 2 5 x = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨w, ⟨i, hA, hB⟩, rfl⟩
      have hw : w = fun j => if j.val < i.val then 1 else 0 := by
        funext j
        by_cases hj : j.val < i.val
        · have hjA := hA j hj
          simpa [A, hj] using hjA
        · have hjB := hB j (by omega)
          simpa [B, hj] using hjB
      rw [hw]
      fin_cases i <;>
        simp only [differential, leftFace, rightFace, Fin.sum_univ_succ, Fin.sum_univ_zero]
      all_goals
        simp [Finsupp.linearCombination_single, leftMove.eq_def, rightMove.eq_def,
          normalizedR, Fin.rev]
        apply Finsupp.ext
        intro z
        fin_cases z <;> simp +decide [Finsupp.single_apply, Matrix.vecTail]
    · exact map_zero _
    · intro x y _ _ hx hy
      simp [map_add, hx, hy]
    · intro a x _ hx
      simp [map_smul, hx]
  have hfixed : (p 4 (q • e) : (Fin 4 → Fin 2) →₀ Polynomial ℤ) = q • e := by
    let z : (Finsupp.supported (Polynomial ℤ) (Polynomial ℤ) {w : Fin 4 → Fin 2 | blockWord 2 A B 4 w}) := ⟨q • e, hqe⟩
    have hh := LinearMap.congr_fun (hp 4) z
    exact congrArg Subtype.val hh
  have hzero : q • e = 0 := by
    rw [← hfixed, ← hd, hc 4 c]
    exact hz _ (p 5 c).property
  have hq : q = 0 := by
    have hh := congrArg (fun x : (Fin 4 → Fin 2) →₀ Polynomial ℤ => x u) hzero
    simpa +decide [e, u, v, Finsupp.single_apply, q] using hh
  have hcoeff := congrArg (fun a : Polynomial ℤ => a.coeff 5) hq
  have hpoly : q = t^5-t^3 := by dsimp [q]; ring
  rw [hpoly] at hcoeff
  norm_num [t] at hcoeff

end D5.S3.HomologicalAlgebra.HomflyptYangBaxterKunnethSplittingRefutation
