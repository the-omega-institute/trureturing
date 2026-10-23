/- GID: D5/S3/Arith/SumFreeCodeMinimumWeightRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/SumFreeCodeMinimumWeightRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.claim; result=D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result; claim=D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.claim
   digest: The original sum-free parity kernels have attained minimum nonzero weights five and four. -/

module

public import D5.S3.Arith.SumFreeCodeDimensionRefutation
import all D5.S3.Arith.SumFreeCodeDimensionRefutation
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.ENat.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Arith.SumFreeCodeMinimumWeightRefutation

open scoped BigOperators

open SumFreeCodeDimensionRefutation (g witnesses_sumFree ker_eq_compact compactG rightG)

/-- The coordinate space over an arbitrary finite field. -/
abbrev V (K : Type) (n : ℕ) := Fin n → K

/-- Independent directions parametrize every affine s-plane without repetitions. -/
def SumFree (K : Type) [Field K] [Fintype K] {n : ℕ}
    (s : ℕ) (f : V K n → V K n) : Prop :=
  ∀ (a : V K n) (u : Fin s → V K n), LinearIndependent K u →
    (∑ c : Fin s → K, f (a + ∑ i, c i • u i)) ≠ 0

/-- All reduced monomials in the source Reed–Muller degree range. -/
abbrev Monomials (K : Type) [Fintype K] (n s : ℕ) :=
  {e : Fin n → Fin (Fintype.card K) //
    ∑ i, (e i).val ≤ s * (Fintype.card K - 1) - 1}

/-- The original monomial rows together with all function-coordinate rows. -/
def parityMatrix (K : Type) [Field K] [Fintype K] (n s : ℕ)
    (f : V K n → V K n) : Matrix (Monomials K n s ⊕ Fin n) (V K n) K :=
  fun r x => match r with
  | .inl e => ∏ i, x i ^ (e.val i).val
  | .inr i => f x i

/-- The original code C_s(f) is the kernel of this linear map. -/
def parityCheck (K : Type) [Field K] [Fintype K] (n s : ℕ)
    (f : V K n → V K n) :
    (V K n → K) →ₗ[K] ((Monomials K n s ⊕ Fin n) → K) :=
  (parityMatrix K n s f).mulVecLin

/-- The least nonzero Hamming weight; the zero code has value infinity. -/
noncomputable def minimumWeight (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (n s : ℕ) (f : V K n → V K n) : ℕ∞ :=
  sInf {d | ∃ w : V K n → K,
    w ≠ 0 ∧ parityCheck K n s f w = 0 ∧ (hammingNorm w : ℕ∞) = d}

/-- Minimum-weight independence for every finite field and every source parameter. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K],
    ∀ n s : ℕ, 2 ≤ n → 1 ≤ s → s ≤ n - 1 →
      ∀ f g : V K n → V K n, SumFree K s f → SumFree K s g →
        minimumWeight K n s f = minimumWeight K n s g

/-- Squaring in the quadratic extension, written in ternary coordinates. -/
def F (x : SumFreeCodeDimensionRefutation.V 2) : SumFreeCodeDimensionRefutation.V 2 :=
  ![x 0 ^ 2 - x 1 ^ 2, 2 * x 0 * x 1]

-- Kernel reduction checks the finite matrices and all 81 free-coordinate choices.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The finite certificates are reduced without native evaluation or added axioms.
/-- The full source minimum-weight assertion is false. -/
theorem result : ¬ claim := by
  -- Inline the instance so the closed finite propositions are reducible by decide.
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro h
  have hf : SumFreeCodeDimensionRefutation.SumFree 1 F := by
    have hc : ∀ (a : SumFreeCodeDimensionRefutation.V 2)
        (u : Fin 1 → SumFreeCodeDimensionRefutation.V 2), u 0 ≠ 0 →
        (∑ c : Fin 1 → ZMod 3, F (a + ∑ i, c i • u i)) ≠ 0 := by decide
    intro a u hu
    exact hc a u (linearIndependent_unique_iff.mp hu)
  have hg : SumFreeCodeDimensionRefutation.SumFree 1 g := witnesses_sumFree.2
  have bridge : ∀ f : SumFreeCodeDimensionRefutation.V 2 → SumFreeCodeDimensionRefutation.V 2,
      parityCheck (ZMod 3) 2 1 f = SumFreeCodeDimensionRefutation.parityCheck 2 1 f := by
    intro f
    ext w r
    cases r <;> rfl
  let CF : Matrix (Fin 5) (SumFreeCodeDimensionRefutation.V 2) (ZMod 3) :=
    ![fun _ => 1, fun x => x 0, fun x => x 1, fun x => F x 0, fun x => F x 1]
  have kerF := ker_eq_compact 5 F CF (by
    unfold SumFreeCodeDimensionRefutation.Monomials
      SumFreeCodeDimensionRefutation.parityMatrix F
    dsimp [CF]
    decide) (by
    unfold SumFreeCodeDimensionRefutation.Monomials
      SumFreeCodeDimensionRefutation.parityMatrix F
    dsimp [CF]
    decide)
  have kerG := ker_eq_compact 5 g compactG (by
    unfold SumFreeCodeDimensionRefutation.Monomials
      SumFreeCodeDimensionRefutation.parityMatrix compactG g
    decide) (by
    unfold SumFreeCodeDimensionRefutation.Monomials
      SumFreeCodeDimensionRefutation.parityMatrix compactG g
    decide)
  let EF : Matrix (SumFreeCodeDimensionRefutation.V 2) (Fin 4) (ZMod 3) := fun x =>
    if x = ![0, 0] then ![2, 2, 1, 2] else
    if x = ![0, 1] then ![2, 1, 2, 2] else
    if x = ![0, 2] then ![2, 1, 1, 0] else
    if x = ![1, 0] then ![1, 1, 0, 2] else
    if x = ![1, 1] then ![1, 0, 1, 2] else
    if x = ![1, 2] then ![1, 0, 0, 0] else
    if x = ![2, 0] then ![0, 1, 0, 0] else
    if x = ![2, 1] then ![0, 0, 1, 0] else ![0, 0, 0, 1]
  let EG : Matrix (SumFreeCodeDimensionRefutation.V 2) (Fin 4) (ZMod 3) := fun x =>
    if x = ![0, 0] then ![1, 1, 1, 1] else
    if x = ![0, 1] then ![2, 0, 2, 0] else
    if x = ![0, 2] then ![0, 2, 0, 2] else
    if x = ![1, 0] then ![2, 2, 0, 0] else
    if x = ![1, 1] then ![1, 0, 0, 0] else
    if x = ![1, 2] then ![0, 1, 0, 0] else
    if x = ![2, 0] then ![0, 0, 2, 2] else
    if x = ![2, 1] then ![0, 0, 1, 0] else ![0, 0, 0, 1]
  let SF : Matrix (SumFreeCodeDimensionRefutation.V 2) (Fin 5) (ZMod 3) := fun x =>
    if x = ![0, 0] then ![1, 1, 0, 1, 2] else
    if x = ![0, 1] then ![0, 2, 2, 1, 1] else
    if x = ![0, 2] then ![0, 2, 1, 1, 0] else
    if x = ![1, 0] then ![0, 1, 0, 0, 1] else
    if x = ![1, 1] then ![0, 0, 0, 0, 2] else 0
  let PF : Matrix (Fin 4) (SumFreeCodeDimensionRefutation.V 2) (ZMod 3) := fun i x =>
    if x = ![![1, 2], ![2, 0], ![2, 1], ![2, 2]] i then 1 else 0
  let PG : Matrix (Fin 4) (SumFreeCodeDimensionRefutation.V 2) (ZMod 3) := fun i x =>
    if x = ![![1, 1], ![1, 2], ![2, 1], ![2, 2]] i then 1 else 0
  have certF : (1 : Matrix (SumFreeCodeDimensionRefutation.V 2)
      (SumFreeCodeDimensionRefutation.V 2) (ZMod 3)) = EF * PF + SF * CF := by decide
  have certG : (1 : Matrix (SumFreeCodeDimensionRefutation.V 2)
      (SumFreeCodeDimensionRefutation.V 2) (ZMod 3)) = EG * PG + rightG * compactG := by decide
  have lowF : ∀ a : Fin 4 → ZMod 3,
      EF.mulVec a ≠ 0 → 5 ≤ hammingNorm (EF.mulVec a) := by decide
  have lowG : ∀ a : Fin 4 → ZMod 3,
      EG.mulVec a ≠ 0 → 4 ≤ hammingNorm (EG.mulVec a) := by decide
  have lowerF : ∀ w : SumFreeCodeDimensionRefutation.V 2 → ZMod 3,
      SumFreeCodeDimensionRefutation.parityCheck 2 1 F w = 0 →
      w ≠ 0 → 5 ≤ hammingNorm w := by
    intro w hk hw
    have hc : CF.mulVec w = 0 := by
      have hm : w ∈ LinearMap.ker (SumFreeCodeDimensionRefutation.parityCheck 2 1 F) := hk
      rw [kerF] at hm
      exact hm
    have rep : w = EF.mulVec (PF.mulVec w) := by
      calc
        w = (1 : Matrix _ _ (ZMod 3)).mulVec w := (Matrix.one_mulVec w).symm
        _ = (EF * PF + SF * CF).mulVec w := by rw [certF]
        _ = EF.mulVec (PF.mulVec w) := by
          rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc]
          simp
    rw [rep] at hw ⊢
    exact lowF (PF.mulVec w) hw
  have lowerG : ∀ w : SumFreeCodeDimensionRefutation.V 2 → ZMod 3,
      SumFreeCodeDimensionRefutation.parityCheck 2 1 g w = 0 →
      w ≠ 0 → 4 ≤ hammingNorm w := by
    intro w hk hw
    have hc : compactG.mulVec w = 0 := by
      have hm : w ∈ LinearMap.ker (SumFreeCodeDimensionRefutation.parityCheck 2 1 g) := hk
      rw [kerG] at hm
      exact hm
    have rep : w = EG.mulVec (PG.mulVec w) := by
      calc
        w = (1 : Matrix _ _ (ZMod 3)).mulVec w := (Matrix.one_mulVec w).symm
        _ = (EG * PG + rightG * compactG).mulVec w := by rw [certG]
        _ = EG.mulVec (PG.mulVec w) := by
          rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc]
          simp
    rw [rep] at hw ⊢
    exact lowG (PG.mulVec w) hw
  let wf : SumFreeCodeDimensionRefutation.V 2 → ZMod 3 := fun x =>
    if x = ![0, 2] ∨ x = ![1, 2] ∨ x = ![2, 0] ∨ x = ![2, 1] then 1 else
    if x = ![2, 2] then 2 else 0
  let wg : SumFreeCodeDimensionRefutation.V 2 → ZMod 3 := fun x =>
    if x = ![0, 0] ∨ x = ![1, 1] then 1 else
    if x = ![0, 1] ∨ x = ![1, 0] then 2 else 0
  have attainF : wf ≠ 0 ∧ SumFreeCodeDimensionRefutation.parityCheck 2 1 F wf = 0 ∧
      hammingNorm wf = 5 := by decide
  have attainG : wg ≠ 0 ∧ SumFreeCodeDimensionRefutation.parityCheck 2 1 g wg = 0 ∧
      hammingNorm wg = 4 := by decide
  have minima : minimumWeight (ZMod 3) 2 1 F = 5 ∧
      minimumWeight (ZMod 3) 2 1 g = 4 := by
    constructor
    · apply le_antisymm
      · apply sInf_le
        exact ⟨wf, attainF.1, by rw [bridge]; exact attainF.2.1,
          by rw [attainF.2.2]; rfl⟩
      · apply le_sInf
        rintro d ⟨w, hw, hk, rfl⟩
        rw [bridge] at hk
        exact_mod_cast lowerF w hk hw
    · apply le_antisymm
      · apply sInf_le
        exact ⟨wg, attainG.1, by rw [bridge]; exact attainG.2.1,
          by rw [attainG.2.2]; rfl⟩
      · apply le_sInf
        rintro d ⟨w, hw, hk, rfl⟩
        rw [bridge] at hk
        exact_mod_cast lowerG w hk hw
  have he := h (ZMod 3) 2 1 (by decide) (by decide) (by decide) F g hf hg
  rw [minima.1, minima.2] at he
  exact (by decide : (5 : ℕ∞) ≠ 4) he

end D5.S3.Arith.SumFreeCodeMinimumWeightRefutation
