/- GID: D5/S3/Arith/SumFreeCodeDimensionRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/SumFreeCodeDimensionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/SumFreeCodeDimensionRefutation.claim; result=D5/S3/Arith/SumFreeCodeDimensionRefutation.result; claim=D5/S3/Arith/SumFreeCodeDimensionRefutation.claim
   digest: Two first-order sum-free maps on the ternary plane yield codes of dimensions five and four. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.SumFreeCodeDimensionRefutation

open scoped BigOperators

private instance ternaryPrime : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The coordinate space over the field with three elements. -/
abbrev V (n : ℕ) := Fin n → ZMod 3

/-- The sum on every injectively parametrized affine s-plane is nonzero. -/
def SumFree {n : ℕ} (s : ℕ) (f : V n → V n) : Prop :=
  ∀ (a : V n) (u : Fin s → V n), LinearIndependent (ZMod 3) u →
    (∑ c : Fin s → ZMod 3, f (a + ∑ i, c i • u i)) ≠ 0

/-- Reduced exponent vectors of total degree at most 2s - 1. -/
abbrev Monomials (n s : ℕ) :=
  {e : Fin n → Fin 3 // ∑ i, (e i).val ≤ 2 * s - 1}

/-- Reed–Muller evaluation rows followed by the coordinate rows of f. -/
def parityMatrix (n s : ℕ) (f : V n → V n) :
    Matrix (Monomials n s ⊕ Fin n) (V n) (ZMod 3) :=
  fun r x => match r with
  | .inl e => ∏ i, x i ^ (e.val i).val
  | .inr i => f x i

/-- The parity-check map defining C_s(f), with one coordinate per row. -/
def parityCheck (n s : ℕ) (f : V n → V n) :
    (V n → ZMod 3) →ₗ[ZMod 3] ((Monomials n s ⊕ Fin n) → ZMod 3) :=
  (parityMatrix n s f).mulVecLin

/-- The dimension of the code C_s(f), literally the kernel dimension. -/
noncomputable def codeDim (n s : ℕ) (f : V n → V n) : ℕ :=
  Module.finrank (ZMod 3) (LinearMap.ker (parityCheck n s f))

/-- Dimension independence at every admissible n and s over the ternary field. -/
def claim : Prop :=
  ∀ n s : ℕ, 2 ≤ n → 1 ≤ s → s ≤ n - 1 →
    ∀ f g : V n → V n, SumFree s f → SumFree s g →
      codeDim n s f = codeDim n s g

private def f (x : V 2) : V 2 := ![x 0 ^ 2 + x 1 ^ 2, 0]
private def g (x : V 2) : V 2 := ![x 0 ^ 2, x 1 ^ 2]

private theorem witnesses_sumFree : SumFree 1 f ∧ SumFree 1 g := by
  have hf : ∀ (a : V 2) (u : Fin 1 → V 2), u 0 ≠ 0 →
      (∑ c : Fin 1 → ZMod 3, f (a + ∑ i, c i • u i)) ≠ 0 := by decide
  have hg : ∀ (a : V 2) (u : Fin 1 → V 2), u 0 ≠ 0 →
      (∑ c : Fin 1 → ZMod 3, g (a + ∑ i, c i • u i)) ≠ 0 := by decide
  constructor
  · intro a u hu
    exact hf a u (linearIndependent_unique_iff.mp hu)
  · intro a u hu
    exact hg a u (linearIndependent_unique_iff.mp hu)

private def compactF : Matrix (Fin 4) (V 2) (ZMod 3) :=
  ![fun _ => 1, fun x => x 0, fun x => x 1, fun x => x 0 ^ 2 + x 1 ^ 2]

private def compactG : Matrix (Fin 5) (V 2) (ZMod 3) :=
  ![fun _ => 1, fun x => x 0, fun x => x 1, fun x => x 0 ^ 2, fun x => x 1 ^ 2]

/-- Repeated and zero rows do not change the kernel. -/
private theorem ker_eq_compact (k : ℕ) (h : V 2 → V 2)
    (C : Matrix (Fin k) (V 2) (ZMod 3))
    (rows : ∀ r, parityMatrix 2 1 h r = 0 ∨
      ∃ i, parityMatrix 2 1 h r = C i)
    (cover : ∀ i, ∃ r, parityMatrix 2 1 h r = C i) :
    LinearMap.ker (parityCheck 2 1 h) = LinearMap.ker C.mulVecLin := by
  ext w
  change (parityMatrix 2 1 h).mulVec w = 0 ↔ C.mulVec w = 0
  constructor
  · intro hw
    funext i
    obtain ⟨r, hr⟩ := cover i
    have hi := congrFun hw r
    change (∑ x, parityMatrix 2 1 h r x * w x) = 0 at hi
    change (∑ x, C i x * w x) = 0
    rw [hr] at hi
    exact hi
  · intro hw
    funext r
    change (∑ x, parityMatrix 2 1 h r x * w x) = 0
    rcases rows r with hz | ⟨i, hi⟩
    · simp [hz]
    · rw [hi]
      exact congrFun hw i

private def rightF : Matrix (V 2) (Fin 4) (ZMod 3) := fun x =>
  if x = ![0, 0] then ![1, 0, 0, 2] else
  if x = ![0, 1] then ![0, 1, 2, 2] else
  if x = ![0, 2] then ![0, 1, 1, 2] else
  if x = ![1, 0] then ![0, 1, 0, 0] else 0

private def rightG : Matrix (V 2) (Fin 5) (ZMod 3) := fun x =>
  if x = ![0, 0] then ![1, 0, 0, 2, 2] else
  if x = ![0, 1] then ![0, 0, 2, 0, 2] else
  if x = ![0, 2] then ![0, 0, 1, 0, 2] else
  if x = ![1, 0] then ![0, 2, 0, 2, 0] else
  if x = ![2, 0] then ![0, 1, 0, 2, 0] else 0

private theorem compact_nullity (k : ℕ)
    (C : Matrix (Fin k) (V 2) (ZMod 3))
    (B : Matrix (V 2) (Fin k) (ZMod 3)) (hCB : C * B = 1) :
    k + Module.finrank (ZMod 3) (LinearMap.ker C.mulVecLin) = 9 := by
  have hs : Function.Surjective C.mulVecLin := by
    intro y
    refine ⟨B.mulVec y, ?_⟩
    change C.mulVec (B.mulVec y) = y
    rw [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
  have hr := LinearMap.range_eq_top.mpr hs
  have hd := C.mulVecLin.finrank_range_add_finrank_ker
  rw [hr, finrank_top] at hd
  simpa [Module.finrank_pi, Fintype.card_fin, V, Fintype.card_fun,
    ZMod.card] using hd

private theorem witness_dimensions : codeDim 2 1 f = 5 ∧ codeDim 2 1 g = 4 := by
  have hfk := ker_eq_compact 4 f compactF (by
    unfold Monomials parityMatrix compactF f
    decide) (by
    unfold Monomials parityMatrix compactF f
    decide)
  have hgk := ker_eq_compact 5 g compactG (by
    unfold Monomials parityMatrix compactG g
    decide) (by
    unfold Monomials parityMatrix compactG g
    decide)
  have hf := compact_nullity 4 compactF rightF (by decide)
  have hg := compact_nullity 5 compactG rightG (by decide)
  unfold codeDim
  rw [hfk, hgk]
  omega

/-- The two admissible functions have unequal kernel dimensions. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hf, hg⟩ := witnesses_sumFree
  have he := h 2 1 (by decide) (by decide) (by decide) f g hf hg
  obtain ⟨hdf, hdg⟩ := witness_dimensions
  rw [hdf, hdg] at he
  exact (by decide : (5 : ℕ) ≠ 4) he

end D5.S3.Arith.SumFreeCodeDimensionRefutation
