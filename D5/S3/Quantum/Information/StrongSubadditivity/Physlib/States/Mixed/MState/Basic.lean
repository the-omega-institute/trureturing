/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/States/Mixed/MState/Basic
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/States/Mixed/MState.lean.
Changes: D5 import paths, bounded modules, local supplier elaboration options,
and omission of the unused real-power lemma and its Rpow dependency.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/
module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.ContinuousLinearMap
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.LinearEquiv
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Misc
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ClassicalInfo.Distribution
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.States.Pure.Braket

public import Mathlib.Logic.Equiv.Basic

/-!
Finite dimensional quantum mixed states, ρ.

The same comments apply as in `Braket`:

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.

Important definitions:
 * `instMixable`: the `Mixable` instance allowing convex combinations of `MState`s
 * `ofClassical`: Mixed states representing classical distributions
 * `purity`: The purity `Tr[ρ^2]` of a state
 * `spectrum`: The spectrum of the matrix
 * `uniform`: The maximally mixed state
 * `mix`: The total state corresponding to an ensemble
 * `average`: Averages a function over an ensemble, with appropriate weights
-/

@[expose] public section

set_option relaxedAutoImplicit true

noncomputable section

open BigOperators
open ComplexConjugate
open HermitianMat
open scoped Matrix ComplexOrder

/-- A **mixed quantum state** is a PSD matrix with trace 1.

We don't `extend (M : HermitianMat d ℂ)` because that gives an annoying thing where
`M` is actually a `Subtype`, which means `ρ.M.foo` notation doesn't work. -/
@[ext]
structure MState (d : Type*) [Fintype d] [DecidableEq d] where
  M : HermitianMat d ℂ
  nonneg : 0 ≤ M
  tr : M.trace = 1

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

variable (ψ φ : Ket d)
variable (ρ σ : MState d)

namespace MState

attribute [coe] MState.M
instance instCoe : Coe (MState d) (HermitianMat d ℂ) := ⟨MState.M⟩

attribute [simp] MState.tr

/-- The underlying `Matrix` in an MState. Prefer `MState.M` for the `HermitianMat`. -/
def m (ρ : MState d) : Matrix d d ℂ := ρ.M.mat

@[simp]
lemma mat_M : ρ.M.mat = ρ.m := by
  rfl

lemma pos (ρ : MState d) : 0 < ρ.M := by
  apply ρ.nonneg.lt_of_ne'
  intro h
  have := ρ.tr
  simp [h] at this

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `MState.M`: it is always positive (`0 < ρ.M`).
Note: we must not call `whnfR` on `e` because `MState.M` is a structure
projection (reducible), so `whnfR` would reduce it and destroy the pattern. -/
@[positivity MState.M _]
meta def evalMStateM : PositivityExt where eval {_u _α} _zα _pα? e :=
  match _pα? with | none => pure .none | some _ => do
  let ρ := e.appArg!
  pure (.positive (← mkAppM ``MState.pos #[ρ]))

--TODO: There should be a bunch of places where we can use `positivity` to prove things,
-- that are currently proved manually.
example (ρ : MState d) : 0 < ρ.M := by positivity

--XXX These are methods that directly reference the matrix, "m" or ".val".
-- We'd like to remove these (where possible) so that mostly go through HermitianMat
-- where possible.
lemma psd : ρ.m.PosSemidef :=
  HermitianMat.zero_le_iff.mp ρ.nonneg


/-- Every mixed state is Hermitian. -/
theorem Hermitian : ρ.m.IsHermitian :=
  ρ.M.H

@[simp]
lemma tr' : ρ.m.trace = 1 := by
  rw [MState.m.eq_def, ← HermitianMat.trace_eq_trace_rc, ρ.tr]
  simp

lemma ext_m {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  rw [MState.mk.injEq]
  ext1
  exact h

/-- The map from mixed states to their matrices is injective -/
theorem m_inj : (MState.m (d := d)).Injective :=
  fun _ _ h ↦ by ext1; ext1; exact h

lemma M_Injective : Function.Injective (MState.M (d := d)) := by
  intro _ _
  exact MState.ext

variable (d) in
/-- The matrices corresponding to MStates are `Convex ℝ` -/
theorem convex : Convex ℝ (Set.range (MState.M (d := d))) := by
  simp only [Convex, Set.mem_range, StarConvex,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro x y a b ha hb hab
  replace hab : a + b = (1 : ℂ) := by norm_cast
  have := HermitianMat.convex_cone x.nonneg y.nonneg ha hb
  exact ⟨⟨_, this, by simpa using mod_cast hab⟩, rfl⟩

instance instMixable : Mixable (HermitianMat d ℂ) (MState d) where
  to_U := MState.M
  to_U_inj := MState.ext
  mkT {u} := fun h ↦
    ⟨⟨u, h.casesOn fun t ht ↦ ht ▸ t.nonneg,
      h.casesOn fun t ht ↦ ht ▸ t.tr⟩, rfl⟩
  convex := convex d

include ρ in
/-- An MState is a witness that d is nonempty. -/
lemma nonempty : Nonempty d := by
  by_contra h
  simpa [HermitianMat.trace_eq_re_trace, not_nonempty_iff.mp h] using ρ.tr

-- Could have used properties of ρ.spectrum
lemma eigenvalue_nonneg : ∀ i, 0 ≤ ρ.Hermitian.eigenvalues i := by
  rw [← Matrix.PosSemidef.nonneg_iff_eigenvalue_nonneg ρ.Hermitian]
  exact ρ.nonneg

set_option backward.isDefEq.respectTransparency false in
-- Could have used properties of ρ.spectrum
lemma eigenvalue_le_one : ∀ i, ρ.Hermitian.eigenvalues i ≤ 1 := by
  intro i
  convert! Finset.single_le_sum (fun y _ ↦ ρ.psd.eigenvalues_nonneg y) (Finset.mem_univ i)
  rw [ρ.M.sum_eigenvalues_eq_trace, ρ.tr]

lemma le_one : ρ.M ≤ 1 := by
  open MatrixOrder in
  suffices h : ρ.m ≤ (1 : ℝ) • 1 by
    rw [one_smul] at h
    exact h
  rw [← Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff ρ.Hermitian]
  exact eigenvalue_le_one ρ

open scoped RealInnerProductSpace InnerProductSpace

/-- The inner product of two MState's, as a real number between 0 and 1. -/
scoped instance : Inner Prob (MState d) where
  inner := fun ρ σ ↦ ⟨⟪ρ.M, σ.M⟫,
    inner_ge_zero ρ.nonneg σ.nonneg,
    (inner_le_mul_trace ρ.nonneg σ.nonneg).trans (by simp)⟩

lemma inner_def : ⟪ρ, σ⟫_Prob = ⟨⟪ρ.M, σ.M⟫,
    inner_ge_zero ρ.nonneg σ.nonneg,
    (inner_le_mul_trace ρ.nonneg σ.nonneg).trans (by simp)⟩ := by
  rfl

lemma val_inner : (⟪ρ, σ⟫_Prob : ℝ) = ⟪ρ.M, σ.M⟫ := by
  rfl

section exp_val

def exp_val_ℂ (T : Matrix d d ℂ) : ℂ :=
  (T * ρ.m).trace

--TODO: Bundle as a ContinuousLinearMap.
/-- The **expectation value** of an operator on a quantum state. -/
def exp_val (T : HermitianMat d ℂ) : ℝ :=
  ⟪ρ.M, T⟫

lemma exp_val_nonneg {T : HermitianMat d ℂ} (h : 0 ≤ T) : 0 ≤ ρ.exp_val T :=
  inner_ge_zero ρ.nonneg h

--TODO: Positivity extension for `MState.exp_val`. (Use the `inner` extension that we need
-- to write first.)

@[simp]
lemma exp_val_zero : ρ.exp_val 0 = 0 := by
  simp [MState.exp_val]

@[simp]
lemma exp_val_one : ρ.exp_val 1 = 1 := by
  simp [MState.exp_val]

lemma exp_val_le_one {T : HermitianMat d ℂ} (h : T ≤ 1) : ρ.exp_val T ≤ 1 := by
  have hmono := inner_mono ρ.nonneg h
  rwa [inner_one ρ.M, ρ.tr] at hmono

lemma exp_val_prob {T : HermitianMat d ℂ} (h : 0 ≤ T ∧ T ≤ 1) :
    0 ≤ ρ.exp_val T ∧ ρ.exp_val T ≤ 1 :=
  ⟨ρ.exp_val_nonneg h.1, ρ.exp_val_le_one h.2⟩

lemma exp_val_sub (A B : HermitianMat d ℂ) :
    ρ.exp_val (A - B) = ρ.exp_val A - ρ.exp_val B := by
  simp [exp_val, inner_sub_right]

/-- If a PSD observable `A` has expectation value of 0 on a state `ρ`, it must entirely contain the
support of `ρ` in its kernel. -/
theorem exp_val_eq_zero_iff {A : HermitianMat d ℂ} (hA₁ : 0 ≤ A) :
    ρ.exp_val A = 0 ↔ ρ.M.support ≤ A.ker := by
  exact inner_zero_iff ρ.nonneg hA₁

/-- If an observable `A` has expectation value of 1 on a state `ρ`, it must entirely contain the
support of `ρ` in its 1-eigenspace. -/
theorem exp_val_eq_one_iff {A : HermitianMat d ℂ} (hA₂ : A ≤ 1) :
    ρ.exp_val A = 1 ↔ ρ.M.support ≤ (1 - A).ker := by
  rw [← exp_val_eq_zero_iff ρ (A := 1 - A) (HermitianMat.zero_le_iff.mpr hA₂)]
  rw [exp_val_sub, exp_val_one]
  rw [sub_eq_zero, eq_comm]

lemma exp_val_add (A B : HermitianMat d ℂ) :
    ρ.exp_val (A + B) = ρ.exp_val A + ρ.exp_val B := by
  simp [exp_val, inner_add_right]

@[simp]
lemma exp_val_smul (r : ℝ) (A : HermitianMat d ℂ) :
    ρ.exp_val (r • A) = r * ρ.exp_val A := by
  simp [MState.exp_val]

@[gcongr]
lemma exp_val_le_exp_val (ρ : MState d) {A B : HermitianMat d ℂ} (h : A ≤ B) :
    ρ.exp_val A ≤ ρ.exp_val B := by
  simp only [MState.exp_val]
  refine inner_mono ρ.nonneg h

end exp_val

section pure

set_option backward.isDefEq.respectTransparency false in
/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  M := {
    val := Matrix.vecMulVec ψ (ψ : Bra d)
    property := (Matrix.PosSemidef.outer_self_conj ψ).1
  }
  nonneg := HermitianMat.zero_le_iff.mpr (.outer_self_conj ψ)
  tr := by
    have h₁ (x) : ψ x * conj (ψ x) = Complex.normSq (ψ x) := by
      rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    simp [HermitianMat.trace_eq_re_trace, Matrix.trace, Matrix.vecMulVec_apply, Bra.eq_conj, h₁]
    exact ψ.normalized

set_option backward.isDefEq.respectTransparency false in
lemma pure_inner : ⟪pure ψ, pure φ⟫_Prob = ‖Braket.dot ψ φ‖^2 := by
  simp [MState.inner_def, HermitianMat.inner_def, pure, Matrix.vecMulVec_mul_vecMulVec,
    Braket.dot_eq_dotProduct, Matrix.trace_smul]
  rw [show ((ψ : d → ℂ) ⬝ᵥ ((φ : Bra d) : d → ℂ)) =
      conj (((ψ : Bra d) : d → ℂ) ⬝ᵥ (φ : d → ℂ)) from by
    change (ψ : d → ℂ) ⬝ᵥ star (φ : d → ℂ) =
      conj (((ψ : Bra d) : d → ℂ) ⬝ᵥ (φ : d → ℂ))
    rw [Matrix.dotProduct_star (ψ : d → ℂ) (φ : d → ℂ)]
    congr 1
    exact dotProduct_comm (φ : d → ℂ) (star (ψ : d → ℂ))]
  simpa [Complex.normSq_apply] using
    Complex.normSq_eq_norm_sq (((ψ : Bra d) : d → ℂ) ⬝ᵥ (φ : d → ℂ))

@[simp]
lemma pure_apply {i j : d} : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma pure_mul_self : (pure ψ).m * (pure ψ).m = (pure ψ : Matrix d d ℂ) := by
  dsimp [pure, MState.m]
  simp [Matrix.vecMulVec_mul_vecMulVec, ← Braket.dot_eq_dotProduct]

/-- The purity of a state is Tr[ρ^2]. This is a `Prob`, because it is always
between zero and one. -/
def purity (ρ : MState d) : Prob := ⟪ρ, ρ⟫_Prob

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum (ρ : MState d) : ProbDistribution d :=
  ProbDistribution.mk'
    (ρ.M.H.eigenvalues ·)
    (ρ.psd.eigenvalues_nonneg ·)
    (by rw [sum_eigenvalues_eq_trace, ρ.tr])

/-- The spectrum of a pure state is (1,0,0,...), i.e. a constant distribution. -/
theorem spectrum_pure_eq_constant :
    ∃ i, (pure ψ).spectrum = ProbDistribution.constant i := by
  let ρ := pure ψ
  -- Prove 1 is in the spectrum of pure ψ by exhibiting an eigenvector with value 1.
  have : ∃i, (pure ψ).spectrum i = 1 := by
    simp [spectrum, ProbDistribution.mk']
    have hEig : ∃i, (pure ψ).M.H.eigenvalues i = 1 := by
      -- Prove ψ is an eigenvector of ρ = pure ψ
      have hv : ρ.M *ᵥ ψ = ψ := by
        ext
        simp_rw [ρ, pure, Matrix.mulVec, mat, Matrix.vecMulVec_apply, dotProduct,
        Bra.apply', Ket.apply, mul_assoc, ← Finset.mul_sum, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_sum, ← Ket.apply, ψ.normalized, Complex.ofReal_one, mul_one]
      let U : Matrix.unitaryGroup d ℂ := star ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
      let w : d → ℂ := U *ᵥ ψ
      -- Prove w = U ψ is an eigenvector of the diagonalized matrix of ρ = pure ψ
      have hDiag : Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) *ᵥ w = w := by
        simp_rw [← Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary,
        eq_comm, Unitary.conjStarAlgAut_apply,
        ← Matrix.mulVec_mulVec, w, U, Matrix.mulVec_mulVec] -- Uses spectral theorem
        simp_all
        rw [←Matrix.mulVec_mulVec, hv]
      -- Prove w = U ψ is nonzero by contradiction
      have hwNonZero : ∃j, w j ≠ 0 := by
        by_contra hwZero
        simp at hwZero
        rw [←funext_iff] at hwZero
        -- If w is zero, then ψ is zero, since U is invertible
        have hψZero : ∀x, ψ x = 0 := by
          apply congr_fun
          -- Prove U is invertible
          have hUdetNonZero : (U : Matrix d d ℂ).det ≠ 0 := by
            by_contra hDetZero
            obtain ⟨u, huUni⟩ := U
            have h0uni: 0 ∈ unitary ℂ := by
              rw [←hDetZero]
              simp
              exact Matrix.det_of_mem_unitary huUni
            rw [Unitary.mem_iff] at h0uni
            simp_all
          exact Matrix.eq_zero_of_mulVec_eq_zero hUdetNonZero hwZero
        -- Reach an contradiction that ψ has norm 0
        have hψn := Ket.normalized ψ
        have hnormZero : ∀ x : d, Complex.normSq (ψ x) = 0 := fun x => by
          rw [hψZero x, Complex.normSq_zero]
        have hsumZero : ∑ x : d, Complex.normSq (ψ x) = 0 := by
          apply Finset.sum_eq_zero
          intros x _
          exact hnormZero x
        simp_all
      obtain ⟨j, hwNonZero'⟩ := hwNonZero
      have hDiagj := congr_fun hDiag j
      rw [Matrix.mulVec_diagonal, mul_eq_right₀ hwNonZero'] at hDiagj
      use j
      simp_all
    obtain ⟨i, hEig'⟩ := hEig
    use i
    ext
    exact hEig'
  --If 1 is in a distribution, the distribution is a constant.
  obtain ⟨i, hi⟩ := this
  use i
  exact ProbDistribution.constant_of_exists_one hi

set_option backward.isDefEq.respectTransparency false in
/-- If the spectrum of a mixed state is (1,0,0...) i.e. a constant distribution, it is
 a pure state. -/
theorem pure_of_constant_spectrum (h : ∃ i, ρ.spectrum = ProbDistribution.constant i) :
    ∃ ψ, ρ = pure ψ := by
  obtain ⟨i, h'⟩ := h
  -- Translate assumption to eigenvalues being (1,0,0,...)
  have hEig : ρ.M.H.eigenvalues = fun x => if x = i then 1 else 0 := by
    ext x
    simp [spectrum, ProbDistribution.constant, ProbDistribution.mk'] at h'
    rw [Subtype.mk.injEq] at h'
    have h'x := congr_fun h' x
    rw [if_congr (Eq.comm) (Eq.refl 1) (Eq.refl 0)]
    rw [Prob.ext_iff] at h'x
    dsimp at h'x
    rw [h'x]
    split_ifs
    case pos => rfl
    case neg => rfl
  -- Choose the eigenvector v of ρ with eigenvalue 1 to make ψ
  let ⟨u, huUni⟩ := ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
  let D : Matrix d d ℂ := Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) -- Diagonal matrix of ρ
  let v : EuclideanSpace ℂ d := ρ.M.H.eigenvectorBasis i
  -- Prove v is normalized
  have hUvNorm : ∑ x, ‖v x‖^2 = 1 := by
    have hinnerv : Inner.inner ℂ v v = 1 := by
      have := ρ.M.H.eigenvectorBasis.orthonormal
      rw [orthonormal_iff_ite] at this
      convert this i i
      simp
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.mul_conj'] at hinnerv
    rw [← Fintype.sum_equiv (Equiv.refl d) _ (fun x => (Complex.ofReal ‖v x‖) ^ 2) (fun x => Complex.ofReal_pow ‖v x‖ 2)] at hinnerv
    rw [← Complex.ofReal_sum Finset.univ (fun x => ‖v x‖ ^ 2), Complex.ofReal_eq_one] at hinnerv
    exact hinnerv
  let ψ : Ket d := ⟨v, hUvNorm⟩ -- Construct ψ
  use ψ
  ext j k
  -- Use spectral theorem to prove that ρ = pure ψ
  rw [Matrix.IsHermitian.spectral_theorem ρ.M.H, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  simp [ψ, v, hEig]
  have hsum : ∀ x ∈ Finset.univ, x ∉ ({i} : Finset d) → (ρ.M.H.eigenvectorBasis x j) * (↑(if x = i then 1 else 0) : ℝ) * (starRingEnd ℂ) (ρ.Hermitian.eigenvectorBasis x k) = 0 := by
    intros x hx hxnoti
    rw [Finset.mem_singleton] at hxnoti
    rw [ite_eq_right hxnoti, Complex.ofReal_zero]
    ring
  simp_rw [←Finset.sum_subset (Finset.subset_univ {i}) hsum, Finset.sum_singleton, reduceIte, Complex.ofReal_one, mul_one]
  rfl

/-- A state ρ is pure iff its spectrum is (1,0,0,...) i.e. a constant distribution. -/
theorem pure_iff_constant_spectrum : (∃ ψ, ρ = pure ψ) ↔
    ∃ i, ρ.spectrum = ProbDistribution.constant i :=
  ⟨fun h ↦ h.rec fun ψ h₂ ↦ h₂ ▸ spectrum_pure_eq_constant ψ,
  pure_of_constant_spectrum ρ⟩

set_option backward.isDefEq.respectTransparency false in
lemma pure_iff_purity_one : (∃ ψ, ρ = pure ψ) ↔ ρ.purity = 1 := by
  --purity = exp(-Collision entropy)
  --purity eq 1 iff collision entropy is zero
  --entropy is zero iff distribution is constant
  --distribution is constant iff pure
  constructor <;> intro h;
  · obtain ⟨w, rfl⟩ := h
    dsimp [purity, inner]
    have := pure_mul_self w
    aesop;
  · -- A state is pure iff its spectrum is constant.
    apply (pure_iff_constant_spectrum ρ).mpr
    have h_eigenvalues : ∑ i, (ρ.spectrum i).val ^ 2 = 1 := by
      -- By definition of purity, we know that the sum of the squares of the eigenvalues is equal to the trace of ρ squared.
      have h_trace_sq : ∑ i, (ρ.spectrum i).val ^ 2 = ρ.purity := by
        have h_eigenvalues : ∑ i, (ρ.M.H.eigenvalues i) ^ 2 = (ρ.M.mat * ρ.M.mat).trace := by
          have := Matrix.IsHermitian.spectral_theorem ρ.M.H;
          conv_rhs => rw [ this ];
          simp [ Matrix.trace_mul_comm, Matrix.mul_assoc ];
          exact Finset.sum_congr rfl fun _ _ => by ring;
        convert! congr_arg Complex.re h_eigenvalues using 1;
      simp_all only [Set.Icc.coe_one]
    -- Each eigenvalue satisfies `λᵢ (1 - λᵢ) ≥ 0`, and these terms sum to
    -- `∑ λᵢ - ∑ λᵢ² = 1 - 1 = 0`, so every `λᵢ` is `0` or `1`.
    have hbin : ∀ i, (ρ.spectrum i).val = 0 ∨ (ρ.spectrum i).val = 1 := by
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ (ρ.spectrum i).val * (1 - (ρ.spectrum i).val) :=
        fun i _ => mul_nonneg (ρ.spectrum i).2.1 (by linarith [(ρ.spectrum i).2.2])
      have hz : ∑ i, (ρ.spectrum i).val * (1 - (ρ.spectrum i).val) = 0 := by
        have e : ∑ i, (ρ.spectrum i).val * (1 - (ρ.spectrum i).val)
            = (∑ i, (ρ.spectrum i : ℝ)) - ∑ i, (ρ.spectrum i).val ^ 2 := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [e, h_eigenvalues, ρ.spectrum.normalized]; norm_num
      exact fun i => (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i
        (Finset.mem_univ i))).imp id fun h => by linarith
    -- Since `∑ λᵢ = 1`, not all eigenvalues vanish, so one of them equals `1`.
    obtain ⟨i, hi⟩ : ∃ i, (ρ.spectrum i).val = 1 := by
      by_contra hcon
      simp only [not_exists] at hcon
      simpa [fun i => (hbin i).resolve_right (hcon i)] using ρ.spectrum.normalized
    exact ⟨i, ProbDistribution.constant_of_exists_one (Subtype.ext hi)⟩

set_option backward.isDefEq.respectTransparency false in
--TODO: Would be better if there was an `MState.eigenstate` or similar (maybe extending
-- a similar thing for `HermitianMat`) and then this could be an equality with that, as
-- an explicit formula, instead of this `Exists`.
lemma spectralDecomposition (ρ : MState d) :
    ∃ (ψs : d → Ket d), ρ.M = ∑ i, (ρ.spectrum i : ℝ) • (MState.pure (ψs i)).M := by
  use (fun i ↦ ⟨(ρ.M.H.eigenvectorUnitary · i), Matrix.unitaryGroup_row_norm _ i⟩)
  ext i j
  nth_rw 1 [ρ.M.H.spectral_theorem]
  --TODO Cleanup
  simp only [Complex.coe_algebraMap, spectrum, ProbDistribution.mk',
    ProbDistribution.funlike_apply, pure, Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [HermitianMat.mat_finset_sum]
  simp only [Unitary.conjStarAlgAut_apply]
  rw [Finset.sum_apply, Finset.sum_apply, Matrix.mul_apply]
  congr!
  simp only [Matrix.mul_diagonal, Matrix.IsHermitian.eigenvectorUnitary_apply,
    mul_comm, Matrix.star_apply, RCLike.star_def]
  simp only [Function.comp_apply, mat_M, mat_apply, HermitianMat.smul_apply, Complex.real_smul]
  rw [mul_assoc]
  rfl

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  M := ρ₁.M ⊗ₖ ρ₂.M
  nonneg := HermitianMat.zero_le_iff.mpr (ρ₁.psd.PosSemidef_kronecker ρ₂.psd)
  tr := by simp

infixl:100 " ⊗ᴹ " => MState.prod

lemma prod_inner_prod (ξ1 ψ1 : MState d₁) (ξ2 ψ2 : MState d₂) :
    ⟪ξ1 ⊗ᴹ ξ2, ψ1 ⊗ᴹ ψ2⟫_Prob = ⟪ξ1, ψ1⟫_Prob * ⟪ξ2, ψ2⟫_Prob := by
  ext1
  simp only [inner_def, Prob.coe_mul, ← Complex.ofReal_inj]
  --Lots of this should actually be facts about HermitianMat first
  simp only [prod, Complex.ofReal_mul]
  simp only [← RCLike.ofReal_eq_complex_ofReal, inner_eq_trace_rc]
  simp only [kronecker, ← Matrix.trace_kronecker]
  simp only [mat_M, mat_mk, Matrix.mul_kronecker_mul]

/-- The product of pure states is a pure product state , `Ket.prod`. -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ᵠ ψ₂) = (pure ψ₁) ⊗ᴹ (pure ψ₂) := by
  ext : 3
  simp [Ket.prod, Ket.apply, prod, -mat_apply]
  ac_rfl

end prod

set_option backward.isDefEq.respectTransparency false in
/-- A representation of a classical distribution as a quantum state, diagonal in the given basis. -/
def ofClassical (dist : ProbDistribution d) : MState d where
  M := diagonal ℂ (fun x ↦ dist x)
  nonneg := by simp [zero_le_iff, diagonal, Matrix.posSemidef_diagonal_iff]
  tr := by simp [trace_diagonal]

@[simp]
lemma coe_ofClassical (dist : ProbDistribution d) :
    (ofClassical dist).M = diagonal ℂ (dist ·) := by
  rfl

/-- The maximally mixed state. -/
def uniform [Nonempty d] : MState d :=
  ofClassical ProbDistribution.uniform

/-- There is exactly one state on a dimension-1 system. -/
--note that this still takes (and uses) the `Fintype d` and `DecidableEq d` instances on `MState d`.
--Even though instances for those can be derived from `Unique d`, we want this `Unique` instance to
--apply on `@MState d ?x ?y` for _any_ x and y.
instance instUnique [Unique d] : Unique (MState d) where
  default := @uniform _ _ _ _
  uniq := by
    intro ρ
    ext
    have h₁ := ρ.tr
    have h₂ := (@uniform _ _ _ _ : MState d).tr
    simp [Matrix.trace, Unique.eq_default, -MState.tr, HermitianMat.trace_eq_re_trace] at h₁ h₂ ⊢
    apply Complex.ext
    · exact h₁.trans h₂.symm
    · rw [complex_im_eq_zero, complex_im_eq_zero]

/-- There exists a mixed state for every nonempty `d`.
Here, the maximally mixed one is chosen. -/
instance instInhabited [Nonempty d] : Inhabited (MState d) where
  default := uniform

lemma default_eq [Nonempty d] : (default : MState d) = uniform := rfl

@[simp]
lemma M_default [Unique d] : (default : MState d).M = 1 := by
  simp [default_eq, uniform]
  rfl

section ptrace

/-- Partial tracing out the left half of a system. -/
@[simps]
def traceLeft (ρ : MState (d₁ × d₂)) : MState d₂ where
  M := ρ.M.traceLeft
  nonneg := zero_le_iff.mpr ρ.psd.traceLeft
  tr := by simp [trace]

/-- Partial tracing out the right half of a system. -/
@[simps]
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁ where
  M := ρ.M.traceRight
  nonneg := zero_le_iff.mpr ρ.psd.traceRight
  tr := by simp [trace]

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
@[simp]
theorem traceLeft_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).traceLeft = ρ₂ := by
  ext1
  simp [prod]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
@[simp]
theorem traceRight_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ᴹ ρ₂).traceRight = ρ₁ := by
  ext1
  simp [prod]

end ptrace


end MState
