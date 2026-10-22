/- GID: D5/S3/Quantum/Codes/QuditStabilizerProductVector
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Uniform qudit Pauli words, their commutation form, and the product-vector obstruction. -/

import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import D5.S3.Quantum.Algebra.WeylPhaseArithmetic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.ByContra

/-!
# Pauli words and product vectors

Finite tensor products of Weyl matrices act on qudit configuration spaces. Scalar exclusion,
finite averaging, and commuting endomorphisms control their common fixed vectors.
-/

section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylPhaseArithmetic

namespace D5.S3.Quantum.Codes.QuditStabilizerProductVector

noncomputable section

structure PauliWord (N p : ℕ) where
  phase : ZMod p
  x : Fin N → ZMod p
  z : Fin N → ZMod p

private def localSymplectic {p : ℕ} (x z x' z' : ZMod p) : ZMod p :=
  z * x' - x * z'

private def localPauli (p : ℕ) [NeZero p] (x z : ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  shiftMatrix p ^ x.val * clockMatrix p ^ z.val

def pauliWordOperator {N p : ℕ} [NeZero p] (w : PauliWord N p) :
    Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ :=
  (windowRoot p ^ w.phase.val) • Matrix.of (fun u v =>
    ∏ n, localPauli p (w.x n) (w.z n) (u n) (v n))

private def wordMul {N p : ℕ} (a b : PauliWord N p) : PauliWord N p :=
  { phase := a.phase + b.phase
    x := a.x + b.x
    z := a.z + b.z }

def commutationVector {N p : ℕ} (a b : PauliWord N p) : Fin N → ZMod p :=
  fun n => localSymplectic (a.x n) (a.z n) (b.x n) (b.z n)

private theorem coordinate_product_mul {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (A B : ι → Matrix α α ℂ) :
    Matrix.of (fun u v : ι → α => ∏ n, A n (u n) (v n)) *
        Matrix.of (fun u v : ι → α => ∏ n, B n (u n) (v n)) =
      Matrix.of (fun u v : ι → α => ∏ n, (A n * B n) (u n) (v n)) := by
  ext u v
  change (∑ w : ι → α, (∏ n, A n (u n) (w n)) * (∏ n, B n (w n) (v n))) =
    ∏ n, ∑ a, A n (u n) a * B n a (v n)
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w hw
  exact (Finset.prod_mul_distrib).symm

private theorem phase_sum {ι : Type*} {p : ℕ} [NeZero p]
    (s : Finset ι) (f : ι → ZMod p) :
    windowRoot p ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, windowRoot p ^ (f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, windowRoot_pow_val_add, ih]

private theorem coordinate_product_one {ι α : Type*} [Fintype ι]
    [DecidableEq α] :
    Matrix.of (fun u v : ι → α => ∏ n, (1 : Matrix α α ℂ) (u n) (v n)) = 1 := by
  ext u v
  simp only [Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole]
  simp only [funext_iff]

private theorem scalar_word_operator {N p : ℕ} [NeZero p] (r : ZMod p) :
    pauliWordOperator (⟨r, 0, 0⟩ : PauliWord N p) =
      Matrix.scalar (Fin N → ZMod p) (windowRoot p ^ r.val) := by
  classical
  dsimp only [pauliWordOperator]
  simp only [Pi.zero_apply, localPauli, ZMod.val_zero, pow_zero, mul_one]
  rw [coordinate_product_one]
  ext u v
  by_cases huv : u = v <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, huv]

private theorem pauli_word_mul {N p : ℕ} [NeZero p] (a b : PauliWord N p) :
    pauliWordOperator a * pauliWordOperator b =
      windowRoot p ^ (∑ n, a.z n * b.x n).val •
        pauliWordOperator (wordMul a b) := by
  simp only [wordMul, pauliWordOperator, Matrix.smul_mul, Matrix.mul_smul,
    coordinate_product_mul, smul_smul]
  ext u v
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    windowRoot_pow_val_add, Pi.add_apply]
  have hprod :
      (∏ n, (localPauli p (a.x n) (a.z n) * localPauli p (b.x n) (b.z n)) (u n) (v n)) =
        (∏ n, windowRoot p ^ (a.z n * b.x n).val) *
          ∏ n, localPauli p (a.x n + b.x n) (a.z n + b.z n) (u n) (v n) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro n hn
    exact congrArg (fun A : Matrix (ZMod p) (ZMod p) ℂ => A (u n) (v n))
      (displacement_mul (a.x n) (a.z n) (b.x n) (b.z n))
  rw [hprod, ← phase_sum]
  ring

private theorem pauli_word_product {N p : ℕ} [NeZero p] (a b : PauliWord N p) :
    ∃ c : PauliWord N p, pauliWordOperator a * pauliWordOperator b =
      pauliWordOperator c := by
  refine ⟨⟨a.phase + b.phase + ∑ n, a.z n * b.x n, a.x + b.x, a.z + b.z⟩, ?_⟩
  rw [pauli_word_mul]
  ext u v
  simp only [wordMul, pauliWordOperator, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, windowRoot_pow_val_add]
  ring

private instance {N p : ℕ} [NeZero p] : Finite (PauliWord N p) :=
  Finite.of_injective (fun w : PauliWord N p => (w.phase, w.x, w.z)) (by
    intro a b h
    cases a
    cases b
    simpa only [Prod.mk.injEq, PauliWord.mk.injEq] using h)

private theorem pauli_word_isUnit {N p : ℕ} [NeZero p] (w : PauliWord N p) :
    IsUnit (pauliWordOperator w) := by
  classical
  have hX : IsUnit (shiftMatrix p) :=
    isUnit_iff_exists_inv'.mpr ⟨star (shiftMatrix p), (window_unitary (M := p)).1⟩
  have hZ : IsUnit (clockMatrix p) :=
    isUnit_iff_exists_inv'.mpr ⟨star (clockMatrix p), (window_unitary (M := p)).2⟩
  have hlocal (n : Fin N) : IsUnit (localPauli p (w.x n) (w.z n)) :=
    (hX.pow _).mul (hZ.pow _)
  let U (n : Fin N) := (hlocal n).unit
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨(windowRoot p ^ w.phase.val)⁻¹ •
    Matrix.of (fun u v : Fin N → ZMod p =>
      ∏ n, ((↑((U n)⁻¹)) : Matrix (ZMod p) (ZMod p) ℂ) (u n) (v n)), ?_⟩
  rw [pauliWordOperator, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ ((windowRoot_isPrimitiveRoot p).ne_zero (NeZero.ne p))),
    one_smul, coordinate_product_mul]
  have hinv (n : Fin N) :
      (↑((U n)⁻¹) : Matrix (ZMod p) (ZMod p) ℂ) *
        localPauli p (w.x n) (w.z n) = 1 := (hlocal n).val_inv_mul
  simp_rw [hinv]
  exact coordinate_product_one

private theorem exists_common_eigenvector {ι V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (s : Finset ι) (f : ι → Module.End ℂ V) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∃ χ : ι → ℂ, ∃ v : V, v ≠ 0 ∧ ∀ i ∈ s, f i v = χ i • v := by
  classical
  induction s using Finset.induction_on generalizing V with
  | empty =>
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨0, v, hv, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨μ, hμ⟩ := (f i).exists_eigenvalue
    letI : Nontrivial ((f i).eigenspace μ) := Submodule.nontrivial_iff_ne_bot.mpr hμ
    have hpres (j : ι) : ∀ v ∈ (f i).eigenspace μ, f j v ∈ (f i).eigenspace μ :=
      Module.End.mapsTo_genEigenspace_of_comm (hcomm i j) μ 1
    let g (j : ι) : Module.End ℂ ((f i).eigenspace μ) := (f j).restrict (hpres j)
    have hg : ∀ j l, Commute (g j) (g l) := by
      intro j l
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact congrArg (fun T : Module.End ℂ V => T v.1) (hcomm j l).eq
    obtain ⟨χ, v, hv, hχ⟩ := ih g hg
    refine ⟨fun j => if j = i then μ else χ j, v.1,
      fun hz => hv (Subtype.ext hz), ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa using Module.End.mem_eigenspace_iff.mp v.2
    · have hjs := Finset.mem_of_mem_insert_of_ne hj hji
      simpa [hji, g] using congrArg Subtype.val (hχ j hjs)

private theorem product_fixed_vector {ι α β : Type*} [Finite ι] [Fintype α] [Fintype β]
    (A : ι → Matrix α α ℂ) (B : ι → Matrix β β ℂ) (c : ι → ℂ)
    (hcomm : ∀ i j, Commute (B i) (B j))
    (hV : ∃ ψ : (α × β) → ℂ, ψ ≠ 0 ∧
      ∀ i, (c i • Matrix.kronecker (A i) (B i)).mulVec ψ = ψ) :
    ∃ a : α → ℂ, ∃ b : β → ℂ,
      (fun x : α × β => a x.1 * b x.2) ≠ 0 ∧
      ∀ i, (c i • Matrix.kronecker (A i) (B i)).mulVec
        (fun x : α × β => a x.1 * b x.2) = (fun x : α × β => a x.1 * b x.2) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let T (i : ι) := c i • Matrix.kronecker (A i) (B i)
  let L (i : ι) : Module.End ℂ ((α × β) → ℂ) :=
    (Matrix.kronecker (1 : Matrix α α ℂ) (B i)).mulVecLin
  let W : Submodule ℂ ((α × β) → ℂ) :=
    { carrier := {ψ | ∀ i, (T i).mulVec ψ = ψ}
      zero_mem' := by intro i; simp
      add_mem' := by
        intro ψ φ hψ hφ i
        rw [Matrix.mulVec_add, hψ i, hφ i]
      smul_mem' := by
        intro z ψ hψ i
        rw [Matrix.mulVec_smul, hψ i] }
  have hcommT (i j : ι) :
      Commute (Matrix.kronecker (1 : Matrix α α ℂ) (B i)) (T j) := by
    change _ * _ = _ * _
    dsimp only [T, Matrix.kronecker]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, one_mul, mul_one, (hcomm i j).eq]
  have hpres (i : ι) : ∀ ψ ∈ W, L i ψ ∈ W := by
    intro ψ hψ j
    change (T j).mulVec ((Matrix.kronecker (1 : Matrix α α ℂ) (B i)).mulVec ψ) = _
    rw [Matrix.mulVec_mulVec, ← (hcommT i j).eq, ← Matrix.mulVec_mulVec, hψ j]
    rfl
  have hleftcomm (i j : ι) : Commute (L i) (L j) := by
    change (L i).comp (L j) = (L j).comp (L i)
    dsimp only [L, Matrix.kronecker]
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, (hcomm i j).eq]
  obtain ⟨ψ, hψ, hψfix⟩ := hV
  have hψmem : ψ ∈ W := hψfix
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr (by
    intro heq
    exact hψ (by simpa only [heq, Submodule.mem_bot] using hψmem))
  let f (i : ι) : Module.End ℂ W := (L i).restrict (hpres i)
  have hfcomm : ∀ i j, Commute (f i) (f j) := by
    intro i j
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun F : Module.End ℂ ((α × β) → ℂ) => F v.1) (hleftcomm i j).eq
  obtain ⟨χ, w, hw, hχ⟩ := exists_common_eigenvector Finset.univ f hfcomm
  have hw0 : w.1 ≠ 0 := fun hz => hw (Subtype.ext hz)
  obtain ⟨xy, hxy⟩ := Function.ne_iff.mp hw0
  have hleft (i : ι) :
      (Matrix.kronecker (1 : Matrix α α ℂ) (B i)).mulVec w.1 = χ i • w.1 :=
    congrArg Subtype.val (hχ i (Finset.mem_univ i))
  have hright (i : ι) :
      (c i * χ i) • (Matrix.kronecker (A i) (1 : Matrix β β ℂ)).mulVec w.1 = w.1 := by
    have hfactor :
        Matrix.kronecker (A i) (1 : Matrix β β ℂ) *
            Matrix.kronecker (1 : Matrix α α ℂ) (B i) = Matrix.kronecker (A i) (B i) := by
      dsimp only [Matrix.kronecker]
      rw [← Matrix.mul_kronecker_mul, one_mul, mul_one]
    calc
      _ = (c i • (Matrix.kronecker (A i) (1 : Matrix β β ℂ) *
          Matrix.kronecker (1 : Matrix α α ℂ) (B i))).mulVec w.1 := by
        rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hleft,
          Matrix.mulVec_smul, smul_smul]
      _ = (T i).mulVec w.1 := by rw [hfactor]
      _ = w.1 := w.2 i
  let a (x : α) := w.1 (x, xy.2)
  let b (y : β) := w.1 (xy.1, y)
  have ha (i : ι) (x : α) : (c i * χ i) * (A i).mulVec a x = a x := by
    have hh := congrFun (hright i) (x, xy.2)
    simpa [a, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul] using hh
  have hb (i : ι) (y : β) : (B i).mulVec b y = χ i * b y := by
    have hh := congrFun (hleft i) (xy.1, y)
    simpa [b, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul] using hh
  refine ⟨a, b, ?_, ?_⟩
  · intro hz
    apply mul_ne_zero hxy hxy
    exact congrFun hz xy
  · intro i
    funext x
    have hprod : (T i).mulVec (fun x : α × β => a x.1 * b x.2) x =
        c i * ((A i).mulVec a x.1 * (B i).mulVec b x.2) := by
      change (∑ uv : α × β,
        (c i * (A i x.1 uv.1 * B i x.2 uv.2)) * (a uv.1 * b uv.2)) =
          c i * ((∑ u, A i x.1 u * a u) * ∑ v, B i x.2 v * b v)
      rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      ring
    rw [hprod, hb]
    calc
      c i * ((A i).mulVec a x.1 * (χ i * b x.2)) =
          ((c i * χ i) * (A i).mulVec a x.1) * b x.2 := by ring
      _ = a x.1 * b x.2 := by rw [ha]

private theorem local_pauli_commutation {p : ℕ} [NeZero p]
    (x z x' z' : ZMod p) :
    localPauli p x z * localPauli p x' z' =
      windowRoot p ^ (localSymplectic x z x' z').val •
        (localPauli p x' z' * localPauli p x z) := by
  change displacement p x z * displacement p x' z' =
    windowRoot p ^ (z * x' - x * z').val •
      (displacement p x' z' * displacement p x z)
  rw [displacement_mul, displacement_mul, smul_smul, ← windowRoot_pow_val_add]
  rw [show z * x' - x * z' + z' * x = z * x' by ring,
    add_comm x' x, add_comm z' z]

private theorem coordinate_product_commutation {ι : Type*} {p : ℕ}
    [Fintype ι] [DecidableEq ι] [NeZero p] (x z x' z' : ι → ZMod p) :
    Matrix.of (fun u v : ι → ZMod p => ∏ n, localPauli p (x n) (z n) (u n) (v n)) *
        Matrix.of (fun u v : ι → ZMod p => ∏ n, localPauli p (x' n) (z' n) (u n) (v n)) =
      windowRoot p ^ (∑ n, localSymplectic (x n) (z n) (x' n) (z' n)).val •
        (Matrix.of (fun u v : ι → ZMod p =>
            ∏ n, localPauli p (x' n) (z' n) (u n) (v n)) *
          Matrix.of (fun u v : ι → ZMod p =>
            ∏ n, localPauli p (x n) (z n) (u n) (v n))) := by
  rw [coordinate_product_mul, coordinate_product_mul]
  ext u v
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [phase_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro n hn
  exact congrArg (fun A : Matrix (ZMod p) (ZMod p) ℂ => A (u n) (v n))
    (local_pauli_commutation (x n) (z n) (x' n) (z' n))

private theorem pauli_word_commutation {N p : ℕ} [NeZero p]
    (a b : PauliWord N p) :
    pauliWordOperator a * pauliWordOperator b =
      windowRoot p ^ (∑ n, commutationVector a b n).val •
        (pauliWordOperator b * pauliWordOperator a) := by
  simp only [pauliWordOperator, Matrix.smul_mul, Matrix.mul_smul,
    coordinate_product_mul, smul_smul]
  ext u v
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have hprod :
      (∏ n, (localPauli p (a.x n) (a.z n) * localPauli p (b.x n) (b.z n)) (u n) (v n)) =
        (∏ n, windowRoot p ^ (commutationVector a b n).val) *
          ∏ n, (localPauli p (b.x n) (b.z n) * localPauli p (a.x n) (a.z n))
            (u n) (v n) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro n hn
    exact congrArg (fun A : Matrix (ZMod p) (ZMod p) ℂ => A (u n) (v n))
      (local_pauli_commutation (a.x n) (a.z n) (b.x n) (b.z n))
  rw [hprod, ← phase_sum]
  dsimp only [commutationVector]
  ring

private theorem pauli_word_trace_zero {N p : ℕ} [NeZero p]
    (w : PauliWord N p) (h : ∃ n, w.x n ≠ 0 ∨ w.z n ≠ 0) :
    Matrix.trace (pauliWordOperator w) = 0 := by
  obtain ⟨n, hn⟩ := h
  rw [pauliWordOperator, Matrix.trace_smul]
  suffices Matrix.trace (Matrix.of (fun u v : Fin N → ZMod p =>
      ∏ j, localPauli p (w.x j) (w.z j) (u j) (v j))) = 0 by simp [this]
  change (∑ u : Fin N → ZMod p, ∏ j,
    localPauli p (w.x j) (w.z j) (u j) (u j)) = 0
  rw [← Fintype.prod_sum (fun (j : Fin N) (a : ZMod p) =>
    localPauli p (w.x j) (w.z j) a a)]
  apply Finset.prod_eq_zero (Finset.mem_univ n)
  exact D5.S3.Quantum.Algebra.WeylDisplacementTrace.displacement_trace_eq_zero
    (w.x n) (w.z n) (by tauto)

theorem common_fixed_subspace_nontrivial {N p : ℕ} [NeZero p]
    (S : Finset (PauliWord N p))
    (hscalar : ∀ A ∈ Submonoid.closure (pauliWordOperator '' (S : Set (PauliWord N p))),
      ∀ c : ℂ, A = Matrix.scalar (Fin N → ZMod p) c → c = 1) :
    ∃ ψ : (Fin N → ZMod p) → ℂ, ψ ≠ 0 ∧
      ∀ a ∈ S, (pauliWordOperator a).mulVec ψ = ψ := by
  classical
  let T := Submonoid.closure (pauliWordOperator '' (S : Set (PauliWord N p)))
  let C : Submonoid (Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ) :=
    { carrier := Set.range pauliWordOperator
      one_mem' := ⟨⟨0, 0, 0⟩, by rw [scalar_word_operator]; simp⟩
      mul_mem' := by
        rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
        obtain ⟨c, hc⟩ := pauli_word_product a b
        exact ⟨c, hc.symm⟩ }
  have hTC : T ≤ C := Submonoid.closure_le.mpr (by
    rintro A ⟨a, ha, rfl⟩
    exact ⟨a, rfl⟩)
  have hfinite : (T : Set (Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ)).Finite :=
    (Set.finite_range pauliWordOperator).subset hTC
  letI : Fintype T := hfinite.fintype
  have htrace (A : T) (hne : A ≠ 1) : Matrix.trace A.1 = 0 := by
    obtain ⟨w, hw⟩ := hTC A.2
    rw [← hw]
    apply pauli_word_trace_zero
    by_contra hn
    have hz : ∀ n, w.x n = 0 ∧ w.z n = 0 := by
      simpa only [not_exists, not_or, not_not] using hn
    have hx0 : w.x = 0 := funext (fun n => (hz n).1)
    have hz0 : w.z = 0 := funext (fun n => (hz n).2)
    have hop : pauliWordOperator w =
        Matrix.scalar (Fin N → ZMod p) (windowRoot p ^ w.phase.val) := by
      cases w with
      | mk r x z =>
        dsimp only at hx0 hz0
        subst x
        subst z
        exact scalar_word_operator r
    have hphase := hscalar A.1 A.2 _ (hw.symm.trans hop)
    apply hne
    apply Subtype.ext
    rw [← hw, hop, hphase]
    simp
  let M : Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ := ∑ A : T, A.1
  have htraceM : Matrix.trace M = (Fintype.card (Fin N → ZMod p) : ℂ) := by
    simp only [M, Matrix.trace_sum]
    rw [Finset.sum_eq_single (1 : T)]
    · simp
    · intro A hA hne
      exact htrace A hne
    · simp
  have hM : M ≠ 0 := by
    intro hzero
    rw [hzero, Matrix.trace_zero] at htraceM
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) htraceM.symm
  obtain ⟨v, hv⟩ : ∃ v : (Fin N → ZMod p) → ℂ, M.mulVec v ≠ 0 := by
    by_contra! hn
    apply hM
    ext i j
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply,
      Matrix.zero_apply] using
      congrFun (hn (Pi.single j 1)) i
  refine ⟨M.mulVec v, hv, ?_⟩
  intro a ha
  let g : T := ⟨pauliWordOperator a, Submonoid.subset_closure ⟨a, ha, rfl⟩⟩
  have hinj : Function.Injective (fun B : T => g * B) := by
    intro B D heq
    apply Subtype.ext
    exact (pauli_word_isUnit a).mul_left_cancel (congrArg Subtype.val heq)
  let e : T ≃ T := Equiv.ofBijective (fun B : T => g * B)
    (Finite.injective_iff_bijective.mp hinj)
  have hinvariant : pauliWordOperator a * M = M := by
    dsimp only [M]
    rw [Finset.mul_sum]
    exact e.sum_comp (fun B : T => B.1)
  rw [Matrix.mulVec_mulVec, hinvariant]

open Classical in
theorem product_vector_of_restricted_commuting {N p : ℕ} [NeZero p]
    (S : Finset (PauliWord N p)) (Q : Set (Fin N))
    (hcommQ : ∀ a ∈ S, ∀ b ∈ S, ∑ n : Q, commutationVector a b n.1 = 0)
    (hV : ∃ ψ : (Fin N → ZMod p) → ℂ, ψ ≠ 0 ∧
      ∀ a ∈ S, (pauliWordOperator a).mulVec ψ = ψ) :
    ∃ ψ : (Fin N → ZMod p) → ℂ, ψ ≠ 0 ∧
      (∀ a ∈ S, (pauliWordOperator a).mulVec ψ = ψ) ∧
      ∃ u : (Q → ZMod p) → ℂ, ∃ v : ((Qᶜ : Set (Fin N)) → ZMod p) → ℂ,
        ∀ x, ψ x = u (fun q => x q.1) * v (fun q => x q.1) := by
  let e := Equiv.piEquivPiSubtypeProd (fun n : Fin N => n ∈ Q) (fun _ => ZMod p)
  let A (i : S) : Matrix (Q → ZMod p) (Q → ZMod p) ℂ :=
    Matrix.of (fun u v => ∏ n : Q, localPauli p (i.1.x n.1) (i.1.z n.1) (u n) (v n))
  let B (i : S) : Matrix ((Qᶜ : Set (Fin N)) → ZMod p)
      ((Qᶜ : Set (Fin N)) → ZMod p) ℂ :=
    Matrix.of (fun u v => ∏ n : (Qᶜ : Set (Fin N)),
      localPauli p (i.1.x n.1) (i.1.z n.1) (u n) (v n))
  let c (i : S) := windowRoot p ^ i.1.phase.val
  obtain ⟨ψ, hψ, hψfix⟩ := hV
  have htotal (a : PauliWord N p) (ha : a ∈ S) (b : PauliWord N p) (hb : b ∈ S) :
      ∑ n, commutationVector a b n = 0 := by
    have heq := congrArg (fun M : Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ =>
      M.mulVec ψ) (pauli_word_commutation a b)
    rw [← Matrix.mulVec_mulVec, hψfix b hb, hψfix a ha,
      Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hψfix a ha, hψfix b hb] at heq
    have hz : (windowRoot p ^ (∑ n, commutationVector a b n).val - 1) • ψ = 0 := by
      rw [sub_smul, one_smul, ← heq, sub_self]
    have hphase := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hψ)
    have hval := (windowRoot_isPrimitiveRoot p).pow_inj
      (∑ n, commutationVector a b n).val_lt (NeZero.pos p)
      (by simpa using hphase)
    apply ZMod.val_injective p
    simpa using hval
  have hBcomm (i j : S) : Commute (B i) (B j) := by
    change _ * _ = _ * _
    dsimp only [B]
    rw [coordinate_product_commutation]
    have hzero : (∑ n : (Qᶜ : Set (Fin N)), commutationVector i.1 j.1 n.1) = 0 := by
      have hs := Fintype.sum_subtype_add_sum_subtype (fun n : Fin N => n ∈ Q)
        (commutationVector i.1 j.1)
      rw [hcommQ i.1 i.2 j.1 j.2, zero_add, htotal i.1 i.2 j.1 j.2] at hs
      exact hs
    change (∑ n : (Qᶜ : Set (Fin N)),
      localSymplectic (i.1.x n.1) (i.1.z n.1) (j.1.x n.1) (j.1.z n.1)) = 0 at hzero
    rw [hzero, ZMod.val_zero, pow_zero, one_smul]
  have hop (i : S) (x y : Fin N → ZMod p) :
      pauliWordOperator i.1 x y =
        (c i • Matrix.kronecker (A i) (B i)) (e x) (e y) := by
    change windowRoot p ^ i.1.phase.val *
        (∏ n, localPauli p (i.1.x n) (i.1.z n) (x n) (y n)) =
      windowRoot p ^ i.1.phase.val *
        ((∏ n : Q, localPauli p (i.1.x n.1) (i.1.z n.1) (x n.1) (y n.1)) *
          ∏ n : (Qᶜ : Set (Fin N)),
            localPauli p (i.1.x n.1) (i.1.z n.1) (x n.1) (y n.1))
    congr 1
    exact (Fintype.prod_subtype_mul_prod_subtype (fun n : Fin N => n ∈ Q)
      (fun n => localPauli p (i.1.x n) (i.1.z n) (x n) (y n))).symm
  have haction (i : S) (ψ : (Fin N → ZMod p) → ℂ) (xy) :
      (c i • Matrix.kronecker (A i) (B i)).mulVec (fun y => ψ (e.symm y)) xy =
        (pauliWordOperator i.1).mulVec ψ (e.symm xy) := by
    change (∑ y, (c i • Matrix.kronecker (A i) (B i)) xy y * ψ (e.symm y)) = _
    calc
      _ = ∑ y, pauliWordOperator i.1 (e.symm xy) (e.symm y) * ψ (e.symm y) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hop]
        simp
      _ = _ := e.symm.sum_comp
        (fun y => pauliWordOperator i.1 (e.symm xy) y * ψ y)
  have hV' : ∃ φ, φ ≠ 0 ∧ ∀ i : S,
      (c i • Matrix.kronecker (A i) (B i)).mulVec φ = φ := by
    refine ⟨fun y => ψ (e.symm y), ?_, ?_⟩
    · intro hz
      apply hψ
      funext x
      simpa using congrFun hz (e x)
    · intro i
      funext xy
      rw [haction, hψfix i.1 i.2]
  obtain ⟨u, v, huv, hfix⟩ := product_fixed_vector A B c hBcomm hV'
  let φ (x : Fin N → ZMod p) := u (e x).1 * v (e x).2
  have hφ : (fun xy => φ (e.symm xy)) = (fun xy => u xy.1 * v xy.2) := by
    funext xy
    simp [φ]
  refine ⟨φ, ?_, ?_, u, v, fun x => rfl⟩
  · intro hz
    apply huv
    funext xy
    have hh := congrFun hz (e.symm xy)
    simpa [φ] using hh
  · intro a ha
    funext x
    calc
      (pauliWordOperator a).mulVec φ x =
          (c ⟨a, ha⟩ • Matrix.kronecker (A ⟨a, ha⟩) (B ⟨a, ha⟩)).mulVec
            (fun y => φ (e.symm y)) (e x) := by
        rw [haction]
        simp
      _ = (c ⟨a, ha⟩ • Matrix.kronecker (A ⟨a, ha⟩) (B ⟨a, ha⟩)).mulVec
          (fun xy => u xy.1 * v xy.2) (e x) :=
        congrArg (fun z => (c ⟨a, ha⟩ •
          Matrix.kronecker (A ⟨a, ha⟩) (B ⟨a, ha⟩)).mulVec z (e x)) hφ
      _ = φ x := congrFun (hfix ⟨a, ha⟩) (e x)


end

end D5.S3.Quantum.Codes.QuditStabilizerProductVector

end
