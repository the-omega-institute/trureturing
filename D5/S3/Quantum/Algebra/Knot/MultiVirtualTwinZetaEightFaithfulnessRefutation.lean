/- GID: D5/S3/Quantum/Algebra/Knot/MultiVirtualTwinZetaEightFaithfulnessRefutation
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/Knot/MultiVirtualTwinZetaEightFaithfulnessRefutation.claim; result=D5/S3/Quantum/Algebra/Knot/MultiVirtualTwinZetaEightFaithfulnessRefutation.result; claim=D5/S3/Quantum/Algebra/Knot/MultiVirtualTwinZetaEightFaithfulnessRefutation.claim
   digest: Three virtual colors give a nontrivial commutator killed by every zeta8 image. -/
/-
result
proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#26876; Refuted)
Direct frozen dependencies: none.

Private theorem classifications (all bind-only; escape_witness none;
Direct frozen dependencies none):
color_relators -> detector; swaps_square -> detector;
kernelWord_ne_one -> zeta_not_injective; rho_pair_diagonal -> zeta_kernel;
zeta_kernel -> zeta_not_injective; zeta_not_injective -> result.
The proofs use PresentedGroup.toGroup, Equiv.swap_mul_self,
Matrix.commute_diagonal, map_commutatorElement and normalization.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The generator inclusions and their carrier are inlined, preserving the
preregistered expressions without forwarding declarations.
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.Knot.MultiVirtualTwinZetaEightFaithfulnessRefutation

def Equations (k n : ℕ) :
    Set (FreeGroup (Fin (n - 1) ⊕ (Fin (n - 1) × Fin k)) × FreeGroup (Fin (n - 1) ⊕ (Fin (n - 1) × Fin k))) :=
  { p |
    (∃ i : Fin (n - 1), p = (FreeGroup.of (Sum.inl i) ^ 2, 1)) ∨
    (∃ i j : Fin (n - 1), (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) ∧ p = (FreeGroup.of (Sum.inl i) * FreeGroup.of (Sum.inl j), FreeGroup.of (Sum.inl j) * FreeGroup.of (Sum.inl i))) ∨
    (∃ (i : Fin (n - 1)) (alpha : Fin k), p = (FreeGroup.of (Sum.inr (i, alpha)) ^ 2, 1)) ∨
    (∃ (i j : Fin (n - 1)) (alpha beta : Fin k), (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) ∧
      p = (FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, beta)), FreeGroup.of (Sum.inr (j, beta)) * FreeGroup.of (Sum.inr (i, alpha)))) ∨
    (∃ (i j : Fin (n - 1)) (alpha : Fin k), (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) ∧
      p = (FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inl j), FreeGroup.of (Sum.inl j) * FreeGroup.of (Sum.inr (i, alpha)))) ∨
    (∃ (i j : Fin (n - 1)) (alpha : Fin k), i.val + 1 = j.val ∧
      p = (FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, alpha)) * FreeGroup.of (Sum.inr (i, alpha)),
        FreeGroup.of (Sum.inr (j, alpha)) * FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, alpha)))) ∨
    (∃ (i j : Fin (n - 1)) (alpha beta : Fin k),
      i.val + 1 = j.val ∧ alpha.val < beta.val ∧
      p = (FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, beta)) * FreeGroup.of (Sum.inr (i, beta)),
        FreeGroup.of (Sum.inr (j, beta)) * FreeGroup.of (Sum.inr (i, beta)) * FreeGroup.of (Sum.inr (j, alpha)))) ∨
    (∃ (i j : Fin (n - 1)) (alpha beta : Fin k),
      i.val + 1 = j.val ∧ alpha.val < beta.val ∧
      p = (FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, alpha)) * FreeGroup.of (Sum.inr (i, beta)),
        FreeGroup.of (Sum.inr (j, beta)) * FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, alpha)))) ∨
    (∃ (i j : Fin (n - 1)) (alpha : Fin k), i.val + 1 = j.val ∧
      p = (FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, alpha)) * FreeGroup.of (Sum.inl i),
        FreeGroup.of (Sum.inl j) * FreeGroup.of (Sum.inr (i, alpha)) * FreeGroup.of (Sum.inr (j, alpha)))) }

/-- Each equation L=R contributes the group relator L*R^{-1}. -/
def relators (k n : ℕ) : Set (FreeGroup (Fin (n - 1) ⊕ (Fin (n - 1) × Fin k))) :=
  { w | ∃ p ∈ Equations k n, w = p.1 * p.2⁻¹ }

/-- The source group M_kVT_n as a quotient by precisely (11)-(19). -/
abbrev MultiVirtualTwin (k n : ℕ) := PresentedGroup (relators k n)

/-- The zeta_8 block on s_i, from Theorem 4.1(8). -/
def sBlock (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-a, -(a ^ 2 - 1) / b; b, a]

/-- The zeta_8 block on rho_i^alpha, from Theorem 4.1(8). -/
def rhoBlock (y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1 / y; y, 0]

/-- I_i, the given 2 by 2 block, and I_(n-i-2), using zero-based i. -/
def localBlock {n : ℕ} (i : Fin (n - 1)) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun row col =>
    if row.val = i.val ∧ col.val = i.val then B 0 0
    else if row.val = i.val ∧ col.val = i.val + 1 then B 0 1
    else if row.val = i.val + 1 ∧ col.val = i.val then B 1 0
    else if row.val = i.val + 1 ∧ col.val = i.val + 1 then B 1 1
    else if row = col then 1 else 0

/-- Literal generator matrices, including the identity outside the local block. -/
def generatorMatrix {k n : ℕ} (a b : ℂ) (y : Fin k → ℂ) :
    (Fin (n - 1) ⊕ (Fin (n - 1) × Fin k)) → Matrix (Fin n) (Fin n) ℂ
  | Sum.inl i => localBlock i (sBlock a b)
  | Sum.inr (i, alpha) => localBlock i (rhoBlock (y alpha))

/-- A representation is zeta_8 exactly when it has the prescribed generator images. -/
def IsZetaEight {k n : ℕ} (a b : ℂ) (y : Fin k → ℂ)
    (f : MultiVirtualTwin k n →* Matrix.GeneralLinearGroup (Fin n) ℂ) : Prop :=
  ∀ g : Fin (n - 1) ⊕ (Fin (n - 1) × Fin k),
    (f (PresentedGroup.of g) : Matrix (Fin n) (Fin n) ℂ) = generatorMatrix a b y g

/-- Question 4.3, affirmative universal reading. Existence prevents a vacuous
faithfulness assertion about the representation prescribed by the source. -/
def claim : Prop :=
  ∀ (k n : ℕ), 1 ≤ k → 3 ≤ n →
    ∀ (a b : ℂ) (y : Fin k → ℂ),
      a ≠ 0 → a ≠ 1 → a ≠ -1 → b ≠ 0 → (∀ alpha : Fin k, y alpha ≠ 0) →
        (∃ f : MultiVirtualTwin k n →* Matrix.GeneralLinearGroup (Fin n) ℂ,
          IsZetaEight a b y f) ∧
        ∀ f : MultiVirtualTwin k n →* Matrix.GeneralLinearGroup (Fin n) ℂ,
          IsZetaEight a b y f → Function.Injective f

end D5.S3.Quantum.Algebra.Knot.MultiVirtualTwinZetaEightFaithfulnessRefutation

namespace D5.S3.Quantum.Algebra.Knot.MultiVirtualTwinZetaEightFaithfulnessRefutation

open scoped commutatorElement

private theorem color_relators {k : ℕ} {G : Type*} [Group G]
    (u : Fin k → G) (hu : ∀ alpha, u alpha * u alpha = 1) :
    ∀ w ∈ relators k 3, FreeGroup.lift (Sum.elim (fun _ => 1) (u ∘ Prod.snd)) w = 1 := by
  intro w hw
  obtain ⟨p, hp, rfl⟩ := hw
  suffices he : FreeGroup.lift (Sum.elim (fun _ => 1) (u ∘ Prod.snd)) p.1 =
      FreeGroup.lift (Sum.elim (fun _ => 1) (u ∘ Prod.snd)) p.2 by
    simp only [map_mul, map_inv, he, mul_inv_cancel]
  rcases hp with h | h | h | h | h | h | h | h | h
  · obtain ⟨i, rfl⟩ := h
    simp
  · obtain ⟨i, j, hfar, _⟩ := h
    rcases hfar with hf | hf <;> have hi := i.isLt <;> have hj := j.isLt <;> omega
  · obtain ⟨i, alpha, rfl⟩ := h
    simpa [pow_two] using hu alpha
  · obtain ⟨i, j, alpha, beta, hfar, _⟩ := h
    rcases hfar with hf | hf <;> have hi := i.isLt <;> have hj := j.isLt <;> omega
  · obtain ⟨i, j, alpha, hfar, _⟩ := h
    rcases hfar with hf | hf <;> have hi := i.isLt <;> have hj := j.isLt <;> omega
  · obtain ⟨i, j, alpha, _, rfl⟩ := h
    simp
  · obtain ⟨i, j, alpha, beta, _, _, rfl⟩ := h
    simp only [Nat.add_one_sub_one, map_mul, FreeGroup.lift_apply_of,
      Sum.elim_inr, Function.comp_apply, mul_assoc, hu]
    rw [← mul_assoc, hu, one_mul, mul_one]
  · obtain ⟨i, j, alpha, beta, _, _, rfl⟩ := h
    simp only [Nat.add_one_sub_one, map_mul, FreeGroup.lift_apply_of,
      Sum.elim_inr, Function.comp_apply, mul_assoc, hu]
    rw [← mul_assoc, hu, one_mul, mul_one]
  · obtain ⟨i, j, alpha, _, rfl⟩ := h
    simp

private def swaps : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 2 3]

private theorem swaps_square (alpha : Fin 3) : swaps alpha * swaps alpha = 1 := by
  fin_cases alpha <;> exact Equiv.swap_mul_self _ _

private def detector : MultiVirtualTwin 3 3 →* Equiv.Perm (Fin 4) :=
  PresentedGroup.toGroup (color_relators swaps swaps_square)

private def kernelWord : MultiVirtualTwin 3 3 := ⁅(PresentedGroup.of (Sum.inr (0, 0)) *
      PresentedGroup.of (Sum.inr (0, 1)) : MultiVirtualTwin 3 3),
    PresentedGroup.of (Sum.inr (0, 0)) * PresentedGroup.of (Sum.inr (0, 2))⁆

private theorem kernelWord_ne_one : kernelWord ≠ 1 := by
  intro h
  have hh := congrArg (fun t => detector t 0) h
  have hc : detector kernelWord 0 ≠ detector 1 0 := by
    exact not_eq_of_beq_eq_false rfl
  exact hc hh

private theorem rho_pair_diagonal (x z : ℂ) :
    localBlock (n := 3) 0 (rhoBlock x) * localBlock (n := 3) 0 (rhoBlock z) =
      Matrix.diagonal ![z / x, x / z, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, localBlock, rhoBlock,
      Matrix.diagonal, div_eq_mul_inv, mul_comm]

private theorem zeta_kernel (a b : ℂ) (y : Fin 3 → ℂ)
    (f : MultiVirtualTwin 3 3 →* Matrix.GeneralLinearGroup (Fin 3) ℂ)
    (hf : IsZetaEight a b y f) : f kernelWord = 1 := by
  let r (alpha : Fin 3) : MultiVirtualTwin 3 3 := PresentedGroup.of (Sum.inr (0, alpha))
  have hr (alpha : Fin 3) : (f (r alpha) : Matrix (Fin 3) (Fin 3) ℂ) =
      localBlock 0 (rhoBlock (y alpha)) := hf (Sum.inr (0, alpha))
  have hp : ((f (r 0 * r 1)) : Matrix (Fin 3) (Fin 3) ℂ) =
      Matrix.diagonal ![y 1 / y 0, y 0 / y 1, 1] := by
    simpa only [map_mul, Matrix.GeneralLinearGroup.coe_mul, hr] using
      rho_pair_diagonal (y 0) (y 1)
  have hq : ((f (r 0 * r 2)) : Matrix (Fin 3) (Fin 3) ℂ) =
      Matrix.diagonal ![y 2 / y 0, y 0 / y 2, 1] := by
    simpa only [map_mul, Matrix.GeneralLinearGroup.coe_mul, hr] using
      rho_pair_diagonal (y 0) (y 2)
  have hc : Commute (f (r 0 * r 1)) (f (r 0 * r 2)) := by
    apply Units.ext
    change (f (r 0 * r 1) : Matrix (Fin 3) (Fin 3) ℂ) *
        (f (r 0 * r 2) : Matrix (Fin 3) (Fin 3) ℂ) =
      (f (r 0 * r 2) : Matrix (Fin 3) (Fin 3) ℂ) *
        (f (r 0 * r 1) : Matrix (Fin 3) (Fin 3) ℂ)
    rw [hp, hq]
    exact (Matrix.commute_diagonal _ _).eq
  exact (map_commutatorElement f _ _).trans
    (commutatorElement_eq_one_iff_commute.mpr hc)

private theorem zeta_not_injective (a b : ℂ) (y : Fin 3 → ℂ)
    (f : MultiVirtualTwin 3 3 →* Matrix.GeneralLinearGroup (Fin 3) ℂ)
    (hf : IsZetaEight a b y f) : ¬ Function.Injective f := by
  intro hi
  exact kernelWord_ne_one (hi ((zeta_kernel a b y f hf).trans (map_one f).symm))

theorem result : ¬ claim := by
  intro h
  obtain ⟨⟨f, hf⟩, hi⟩ := h 3 3 (by norm_num) (by norm_num) 2 1 (fun _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by intro alpha; norm_num)
  exact zeta_not_injective 2 1 (fun _ => 1) f hf (hi f hf)

end D5.S3.Quantum.Algebra.Knot.MultiVirtualTwinZetaEightFaithfulnessRefutation
