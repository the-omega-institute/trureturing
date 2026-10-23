/- GID: D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Genuine entanglement forces the Makuta--Kuzaka--Augusiak commutation-rank bound. -/

import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import D5.S3.Quantum.Algebra.WeylPhaseArithmetic
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Stabilizer fixed vectors and the commutation-rank obstruction

Scalar exclusion makes the common fixed subspace of qudit Pauli words nontrivial.
Genuine entanglement then forbids a vanishing coordinate subsum of the commutation space.
Chevalley--Warning converts this obstruction into a lower bound on its dimension.
-/

section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Module
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylPhaseArithmetic

namespace D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

noncomputable section

structure PauliWord (N p : ℕ) where
  phase : ZMod p
  x : Fin N → ZMod p
  z : Fin N → ZMod p

private def localSymplectic {p : ℕ} (x z x' z' : ZMod p) : ZMod p :=
  z * x' - x * z'

def pauliWordOperator {N p : ℕ} [NeZero p] (w : PauliWord N p) :
    Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ :=
  (windowRoot p ^ w.phase.val) • Matrix.of (fun u v =>
    ∏ n, displacement p (w.x n) (w.z n) (u n) (v n))

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
  simpa only [AddChar.toMonoidHom_apply, toAdd_prod,
    toAdd_ofAdd, AddChar.zmodChar_apply] using
    map_prod (AddChar.zmodChar p (windowRoot_isPrimitiveRoot p).pow_eq_one).toMonoidHom
      (fun i => Multiplicative.ofAdd (f i)) s

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
  simp only [Pi.zero_apply, displacement_zero]
  rw [coordinate_product_one]
  ext u v
  by_cases huv : u = v <;>
    simp [Matrix.scalar_apply, huv]

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
      (∏ n, (displacement p (a.x n) (a.z n) * displacement p (b.x n) (b.z n)) (u n) (v n)) =
        (∏ n, windowRoot p ^ (a.z n * b.x n).val) *
          ∏ n, displacement p (a.x n + b.x n) (a.z n + b.z n) (u n) (v n) := by
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
  have hlocal (n : Fin N) : IsUnit (displacement p (w.x n) (w.z n)) :=
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
        displacement p (w.x n) (w.z n) = 1 := (hlocal n).val_inv_mul
  simp_rw [hinv]
  exact coordinate_product_one

private theorem exists_common_eigenvector {ι V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (s : Finset ι) (f : ι → Module.End ℂ V) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∃ χ : ι → ℂ, ∃ v : V, v ≠ 0 ∧ ∀ i ∈ s, f i v = χ i • v := by
  classical
  let : LieRing (Module.End ℂ V) := LieRing.ofAssociativeRing
  let L := LieSubalgebra.lieSpan ℂ (Module.End ℂ V) (Set.range f)
  let : IsLieAbelian L := LieSubalgebra.isLieAbelian_lieSpan_iff.mpr (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact sub_eq_zero.mpr (hcomm i j).eq)
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable ℂ L V
  let := hχ
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  let g (i : ι) : L := ⟨f i, LieSubalgebra.subset_lieSpan ⟨i, rfl⟩⟩
  refine ⟨fun i => χ (g i), v.1, fun hz => hv (Subtype.ext hz), ?_⟩
  intro i _
  exact (LieModule.mem_weightSpace χ v.1).mp v.2 (g i)

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
  let : Fintype ι := Fintype.ofFinite ι
  let T (i : ι) := c i • Matrix.kronecker (A i) (B i)
  let L (i : ι) : Module.End ℂ ((α × β) → ℂ) :=
    (Matrix.kronecker (1 : Matrix α α ℂ) (B i)).mulVecLin
  let W : Submodule ℂ ((α × β) → ℂ) :=
    ⨅ i, LinearMap.fixedSubmodule (T i).mulVecLin
  have hcommT (i j : ι) :
      Commute (Matrix.kronecker (1 : Matrix α α ℂ) (B i)) (T j) := by
    change _ * _ = _ * _
    dsimp only [T, Matrix.kronecker]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, one_mul, mul_one, (hcomm i j).eq]
  have hpres (i : ι) : ∀ ψ ∈ W, L i ψ ∈ W := by
    intro ψ hψ
    simp only [W, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff,
      Matrix.mulVecLin_apply] at hψ ⊢
    intro j
    change (T j).mulVec ((Matrix.kronecker (1 : Matrix α α ℂ) (B i)).mulVec ψ) = _
    rw [Matrix.mulVec_mulVec, ← (hcommT i j).eq, ← Matrix.mulVec_mulVec, hψ j]
    rfl
  have hleftcomm (i j : ι) : Commute (L i) (L j) := by
    change (L i).comp (L j) = (L j).comp (L i)
    dsimp only [L, Matrix.kronecker]
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, (hcomm i j).eq]
  obtain ⟨ψ, hψ, hψfix⟩ := hV
  have hψmem : ψ ∈ W := by
    simpa only [W, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff,
      Matrix.mulVecLin_apply] using hψfix
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr (by
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
      _ = w.1 := (Submodule.mem_iInf _).mp w.2 i
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
    displacement p x z * displacement p x' z' =
      windowRoot p ^ (localSymplectic x z x' z').val •
        (displacement p x' z' * displacement p x z) := by
  change displacement p x z * displacement p x' z' =
    windowRoot p ^ (z * x' - x * z').val •
      (displacement p x' z' * displacement p x z)
  have hunit : IsUnit (windowRoot p ^ (z' * x).val) :=
    isUnit_iff_ne_zero.mpr
      (pow_ne_zero _ ((windowRoot_isPrimitiveRoot p).ne_zero (NeZero.ne p)))
  apply hunit.smul_left_cancel.mp
  rw [smul_smul, ← windowRoot_pow_val_add]
  rw [show z' * x + (z * x' - x * z') = z * x' by ring]
  exact displacement_comm x z x' z'

private theorem coordinate_product_commutation {ι : Type*} {p : ℕ}
    [Fintype ι] [DecidableEq ι] [NeZero p] (x z x' z' : ι → ZMod p) :
    Matrix.of (fun u v : ι → ZMod p => ∏ n, displacement p (x n) (z n) (u n) (v n)) *
        Matrix.of (fun u v : ι → ZMod p => ∏ n, displacement p (x' n) (z' n) (u n) (v n)) =
      windowRoot p ^ (∑ n, localSymplectic (x n) (z n) (x' n) (z' n)).val •
        (Matrix.of (fun u v : ι → ZMod p =>
            ∏ n, displacement p (x' n) (z' n) (u n) (v n)) *
          Matrix.of (fun u v : ι → ZMod p =>
            ∏ n, displacement p (x n) (z n) (u n) (v n))) := by
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
    smul_smul]
  rw [coordinate_product_commutation]
  simp only [smul_smul, commutationVector]
  congr 1
  ring

private theorem pauli_word_trace_zero {N p : ℕ} [NeZero p]
    (w : PauliWord N p) (h : ∃ n, w.x n ≠ 0 ∨ w.z n ≠ 0) :
    Matrix.trace (pauliWordOperator w) = 0 := by
  obtain ⟨n, hn⟩ := h
  rw [pauliWordOperator, Matrix.trace_smul]
  suffices Matrix.trace (Matrix.of (fun u v : Fin N → ZMod p =>
      ∏ j, displacement p (w.x j) (w.z j) (u j) (v j))) = 0 by simp [this]
  change (∑ u : Fin N → ZMod p, ∏ j,
    displacement p (w.x j) (w.z j) (u j) (u j)) = 0
  rw [← Fintype.prod_sum (fun (j : Fin N) (a : ZMod p) =>
    displacement p (w.x j) (w.z j) a a)]
  apply Finset.prod_eq_zero (Finset.mem_univ n)
  exact D5.S3.Quantum.Algebra.WeylDisplacementTrace.displacement_trace_eq_zero
    (w.x n) (w.z n) (by tauto)

private theorem common_fixed_subspace_nontrivial {N p : ℕ} [NeZero p]
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
  let : Fintype T := hfinite.fintype
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
private theorem product_vector_of_restricted_commuting {N p : ℕ} [NeZero p]
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
    Matrix.of (fun u v => ∏ n : Q, displacement p (i.1.x n.1) (i.1.z n.1) (u n) (v n))
  let B (i : S) : Matrix ((Qᶜ : Set (Fin N)) → ZMod p)
      ((Qᶜ : Set (Fin N)) → ZMod p) ℂ :=
    Matrix.of (fun u v => ∏ n : (Qᶜ : Set (Fin N)),
      displacement p (i.1.x n.1) (i.1.z n.1) (u n) (v n))
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
        (∏ n, displacement p (i.1.x n) (i.1.z n) (x n) (y n)) =
      windowRoot p ^ i.1.phase.val *
        ((∏ n : Q, displacement p (i.1.x n.1) (i.1.z n.1) (x n.1) (y n.1)) *
          ∏ n : (Qᶜ : Set (Fin N)),
            displacement p (i.1.x n.1) (i.1.z n.1) (x n.1) (y n.1))
    congr 1
    exact (Fintype.prod_subtype_mul_prod_subtype (fun n : Fin N => n ∈ Q)
      (fun n => displacement p (i.1.x n) (i.1.z n) (x n) (y n))).symm
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

def stabilizerSubspace {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) :
    Submodule ℂ ((Fin N → ZMod p) → ℂ) :=
  ⨅ i, LinearMap.fixedSubmodule (pauliWordOperator (G i)).mulVecLin

def productAcross {N p : ℕ} (Q : Set (Fin N))
    (ψ : (Fin N → ZMod p) → ℂ) : Prop :=
  ∃ u : (Q → ZMod p) → ℂ, ∃ v : ((Qᶜ : Set (Fin N)) → ZMod p) → ℂ,
    ∀ x, ψ x = u (fun q => x q.1) * v (fun q => x q.1)

def genuinelyEntangled {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Prop :=
  ∀ ψ, ψ ∈ stabilizerSubspace G → ψ ≠ 0 →
    ∀ Q : Set (Fin N), Q.Nonempty → Qᶜ.Nonempty → ¬ productAcross Q ψ

def commutationSpace {N p k : ℕ} [Fact p.Prime]
    (G : Fin k → PauliWord N p) :
    Submodule (ZMod p) (Fin N → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun ij : Fin k × Fin k =>
    commutationVector (G ij.1) (G ij.2)))

def generatedOperators {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Submonoid (Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ) :=
  Submonoid.closure (Set.range (fun i => pauliWordOperator (G i)))

def IsStabilizer {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Prop :=
  (∀ i j, Commute (pauliWordOperator (G i)) (pauliWordOperator (G j))) ∧
    (∀ A ∈ generatedOperators G, ∀ c : ℂ,
      A = Matrix.scalar (Fin N → ZMod p) c → c = 1)

def claim : Prop :=
  ∀ (N p k : ℕ), 1 ≤ N → ∀ hp : Nat.Prime p,
    ∀ G : Fin k → PauliWord N p,
      @IsStabilizer N p k ⟨hp.ne_zero⟩ G →
      @genuinelyEntangled N p k ⟨hp.ne_zero⟩ G →
      (N - 1 + (p - 2)) / (p - 1) ≤
        Module.finrank (ZMod p) (@commutationSpace N p k ⟨hp⟩ G)

private theorem zero_sum_subset_exists {p m r : ℕ} [Fact p.Prime]
    (u : Fin r → Fin m → ZMod p) (h : r * (p - 1) < m) :
    ∃ Q : Finset (Fin m), Q.Nonempty ∧ ∀ i, ∑ j ∈ Q, u i j = 0 := by
  classical
  let f : Fin r → MvPolynomial (Fin m) (ZMod p) := fun i =>
    ∑ j, MvPolynomial.C (u i j) * MvPolynomial.X j ^ (p - 1)
  have hp : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hdegree (i : Fin r) : (f i).totalDegree ≤ p - 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have hsum : (∑ i, (f i).totalDegree) < Fintype.card (Fin m) := by
    calc
      (∑ i, (f i).totalDegree) ≤ ∑ _i : Fin r, (p - 1) :=
        Finset.sum_le_sum (fun i _ => hdegree i)
      _ = r * (p - 1) := by simp
      _ < Fintype.card (Fin m) := by simpa using h
  let : Fintype {x : Fin m → ZMod p //
      ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0} :=
    @Subtype.fintype _
      (fun x : Fin m → ZMod p =>
        ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0)
      (fun _ => Finset.decidableDforallFinset) inferInstance
  have hdiv : p ∣ Fintype.card {x : Fin m → ZMod p //
      ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0} :=
    char_dvd_card_solutions_of_sum_lt p hsum
  have hz (i : Fin r) : MvPolynomial.eval (0 : Fin m → ZMod p) (f i) = 0 := by
    simp [f, zero_pow hp.ne']
  have hex : ∃ x : Fin m → ZMod p, x ≠ 0 ∧
      ∀ i, MvPolynomial.eval x (f i) = 0 := by
    by_contra hn
    have hall (x : Fin m → ZMod p) (hx : ∀ i, MvPolynomial.eval x (f i) = 0) :
        x = 0 := by
      by_contra hx0
      exact hn ⟨x, hx0, hx⟩
    have hcard : Fintype.card {x : Fin m → ZMod p //
        ∀ i ∈ (Finset.univ : Finset (Fin r)), MvPolynomial.eval x (f i) = 0} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨0, fun i _ => hz i⟩, ?_⟩
      intro x
      apply Subtype.ext
      exact hall x.1 (fun i => x.2 i (Finset.mem_univ i))
    rw [hcard] at hdiv
    exact (Fact.out : p.Prime).not_dvd_one hdiv
  obtain ⟨x, hx, hfx⟩ := hex
  refine ⟨Finset.univ.filter (fun j => x j ≠ 0), ?_, ?_⟩
  · by_contra hQ
    apply hx
    funext j
    by_contra hj
    exact hQ ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  · intro i
    have hpow (j : Fin m) : x j ^ (p - 1) = if x j ≠ 0 then 1 else 0 := by
      split_ifs with hj
      · exact ZMod.pow_card_sub_one_eq_one hj
      · simp only [not_not] at hj
        simp [hj, zero_pow hp.ne']
    have he := hfx i
    simpa [f, hpow, Finset.sum_filter] using he

private theorem rank_bound_of_no_vanishing_subsum {n p : ℕ} [Fact p.Prime]
    (K : Submodule (ZMod p) (Fin (n + 1) → ZMod p))
    (hno : ∀ Q : Finset (Fin n), Q.Nonempty →
      ∃ v ∈ K, ∑ j ∈ Q, v j.castSucc ≠ 0) :
    n ≤ Module.finrank (ZMod p) K * (p - 1) := by
  classical
  by_contra hn
  let b := Module.finBasis (ZMod p) K
  obtain ⟨Q, hQ, hu⟩ := zero_sum_subset_exists
    (fun i j => (b i).1 j.castSucc) (Nat.lt_of_not_ge hn)
  let L : K →ₗ[ZMod p] ZMod p :=
    ∑ j ∈ Q, (LinearMap.proj j.castSucc).comp K.subtype
  have hL : L = 0 := b.ext (fun i => by simpa [L] using hu i)
  obtain ⟨v, hv, hne⟩ := hno Q hQ
  exact hne (by
    simpa [L] using congrArg (fun T : K →ₗ[ZMod p] ZMod p => T ⟨v, hv⟩) hL)

private theorem no_vanishing_subsum {n p k : ℕ} [Fact p.Prime]
    (G : Fin k → PauliWord (n + 1) p) (hS : IsStabilizer G)
    (hGE : genuinelyEntangled G) (Q : Finset (Fin n)) (hQ : Q.Nonempty) :
    ∃ v ∈ commutationSpace G, ∑ j ∈ Q, v j.castSucc ≠ 0 := by
  classical
  by_contra! hn
  let S : Finset (PauliWord (n + 1) p) := Finset.univ.image G
  have hclosure :
      Submonoid.closure (pauliWordOperator '' (S : Set (PauliWord (n + 1) p))) ≤
        generatedOperators G := by
    apply Submonoid.closure_le.mpr
    rintro A ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact Submonoid.subset_closure ⟨i, rfl⟩
  have hV := common_fixed_subspace_nontrivial S
    (fun A hA c hc => hS.2 A (hclosure hA) c hc)
  let R : Set (Fin (n + 1)) := (Q.image Fin.castSucc : Finset (Fin (n + 1)))
  have hR : R.Nonempty := by
    obtain ⟨j, hj⟩ := hQ
    exact ⟨j.castSucc, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  have hRc : Rᶜ.Nonempty := by
    refine ⟨Fin.last n, ?_⟩
    change Fin.last n ∉ Q.image Fin.castSucc
    rintro hlast
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hlast
    exact Fin.castSucc_ne_last j heq
  have hsum (v : Fin (n + 1) → ZMod p) :
      (∑ j : R, v j.1) = ∑ j ∈ Q, v j.castSucc := by
    change (∑ j : (Q.image Fin.castSucc : Finset (Fin (n + 1))), v j.1) = _
    rw [Finset.sum_coe_sort, Finset.sum_image]
    exact fun a ha b hb heq => Fin.castSucc_injective _ heq
  have hcommQ : ∀ a ∈ S, ∀ b ∈ S, ∑ j : R, commutationVector a b j.1 = 0 := by
    rintro a ha b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [hsum]
    exact hn _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  obtain ⟨ψ, hψ, hfix, hprod⟩ := product_vector_of_restricted_commuting S R
    (by
      intro a ha b hb
      convert! hcommQ a ha b hb using 1
      apply Finset.sum_congr (by ext j; simp)
      intro j hj
      rfl) hV
  have hψmem : ψ ∈ stabilizerSubspace G := by
    simp only [stabilizerSubspace, Submodule.mem_iInf,
      LinearMap.mem_fixedSubmodule_iff, Matrix.mulVecLin_apply]
    exact fun i => hfix (G i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  exact hGE ψ hψmem hψ R hR hRc hprod

theorem result : claim := by
  intro N p k hN hp G hS hGE
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hbound := rank_bound_of_no_vanishing_subsum (commutationSpace G)
    (no_vanishing_subsum G hS hGE)
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  change (n + (p - 2)) / (p - 1) ≤ Module.finrank (ZMod p) (commutationSpace G)
  apply (Nat.div_le_iff_le_mul_add_pred hpos).mpr
  have hbound' : n ≤ (p - 1) * Module.finrank (ZMod p) (commutationSpace G) := by
    simpa only [Nat.mul_comm] using hbound
  simpa only [Nat.sub_sub] using Nat.add_le_add_right hbound' (p - 2)

end

end D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

end
