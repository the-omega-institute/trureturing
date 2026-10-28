/- GID: D5/S3/QuadraticForms/GerzonEqualityParameterIdentity
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/GerzonEqualityParameterIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gerzon equality forces the parameter identity in odd fields for d at least two. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#16342; Proved)
Direct frozen dependencies: none (all imports are pinned Mathlib).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16531.
selfAdjoint_mem_iff: proof_shape: bind-only; escape_witness: none; consumers:
  symmetricCoordinates, rankOne_mem, diagonal_unit_mem, off_unit_mem, identity_mem.
diagonal_apply: proof_shape: bind-only; escape_witness: none; consumers: trace_rankOne,
  trace_rankOne_mul_rankOne.
weightedSelfAdjoint_finrank: proof_shape: bind-only; escape_witness: none; consumers:
  diagonal_identity.
rankOne_mem: proof_shape: bind-only; escape_witness: none; consumers: restrictedMoment,
  diagonal_identity.
trace_rankOne: proof_shape: bind-only; escape_witness: none; consumers: diagonal_identity.
trace_rankOne_mul_rankOne: proof_shape: bind-only; escape_witness: none; consumers:
  diagonal_identity.
fourthMoment_apply: proof_shape: bind-only; escape_witness: none; consumers: fourthMoment_cross,
  restrictedMoment, diagonal_identity.
diagonal_unit_mem: proof_shape: bind-only; escape_witness: none; consumers:
  fourthMoment_coefficient, diagonal_identity.
off_unit_mem: proof_shape: bind-only; escape_witness: none; consumers: fourthMoment_coefficient.
fourthMoment_cross: proof_shape: bind-only; escape_witness: none; consumers:
  fourthMoment_coefficient.
fourthMoment_coefficient: proof_shape: bind-only; escape_witness: none; consumers:
  diagonal_identity.
gram_pair_sum: proof_shape: bind-only; escape_witness: none; consumers: relation_constant,
  independent_nonzero_trace, scalar_frame_nonzero_trace, diagonal_identity.
relation_constant: proof_shape: bind-only; escape_witness: none; consumers: span_zero_trace.
independent_nonzero_trace: proof_shape: bind-only; escape_witness: none; consumers:
  scalar_frame_nonzero_trace, moment_nonzero_trace.
scalar_frame_nonzero_trace: proof_shape: bind-only; escape_witness: none; consumers:
  diagonal_identity.
moment_nonzero_trace: proof_shape: bind-only; escape_witness: none; consumers: diagonal_identity.
span_zero_trace: proof_shape: bind-only; escape_witness: none; consumers: diagonal_identity.
moment_zero_trace: proof_shape: bind-only; escape_witness: none; consumers: diagonal_identity.
identity_mem: proof_shape: bind-only; escape_witness: none; consumers: diagonal_identity.
diagonal_identity: proof_shape: bind-only; escape_witness: none; consumers: parameter_identity.
orthogonal_coordinates: proof_shape: bind-only; escape_witness: none; consumers:
  parameter_identity.
parameter_identity: proof_shape: bind-only; escape_witness: none; consumers: result.
Definitions construct proof coordinates and operators.
The equiangular predicate and claim use the expressions recorded in issue #16342.
The selfadjoint space, diagonal form and rank-one matrices use their Mathlib owners.
No dimension or dimension-minus-one inverse is assumed. The public claim includes d >= 2;
at d = 1 the off-diagonal condition is empty and b is unconstrained.
Utility none: every declaration is field-parametric and dimension-unbounded.
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.LinearCombination

open scoped BigOperators
open Matrix Module

namespace D5.S3.QuadraticForms.GerzonEqualityParameterIdentity

variable {F : Type*} [Field F] {d : ℕ}

private theorem selfAdjoint_mem_iff (mu : Fin d → F) (X : Matrix (Fin d) (Fin d) F) :
    X ∈ selfAdjointMatricesSubmodule (Matrix.diagonal mu) ↔
      ∀ i j, mu i * X i j = mu j * X j i := by
  rw [mem_selfAdjointMatricesSubmodule]
  change (X.transpose * Matrix.diagonal mu = Matrix.diagonal mu * X) ↔ _
  constructor
  · intro h i j
    have hh := congrArg (fun A : Matrix (Fin d) (Fin d) F => A i j) h
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply] at hh
    exact hh.symm.trans (mul_comm _ _)
  · intro h
    ext i j
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      mul_comm] using (h i j).symm

private theorem diagonal_apply (mu u v : Fin d → F) :
    Matrix.toBilin' (Matrix.diagonal mu) u v = ∑ i, mu i * u i * v i := by
  simp [Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, mul_comm, mul_left_comm]

-- A diagonal Gram matrix with nonzero diagonal entries.
noncomputable def symmetricCoordinates (mu : Fin d → F) (hmu : ∀ i, mu i ≠ 0) :
    (selfAdjointMatricesSubmodule (Matrix.diagonal mu)) ≃ₗ[F] (Sym2 (Fin d) → F) where
  toFun X := Sym2.lift ⟨fun i j => mu i * X.val i j, (selfAdjoint_mem_iff mu X.val).mp X.property⟩
  invFun f := ⟨fun i j => f s(i,j) / mu i, by
    apply (selfAdjoint_mem_iff mu _).mpr
    intro i j
    simp only [mul_div_cancel₀ _ (hmu i), mul_div_cancel₀ _ (hmu j)]
    rw [Sym2.eq_swap]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    simp [Sym2.lift_mk, hmu]
  right_inv f := by
    funext p
    induction p using Sym2.inductionOn with
    | hf i j => simp [Sym2.lift_mk, mul_div_cancel₀ _ (hmu i)]
  map_add' X Y := by
    funext p
    induction p using Sym2.inductionOn with | hf i j => simp [Sym2.lift_mk, mul_add]
  map_smul' t X := by
    funext p
    induction p using Sym2.inductionOn with | hf i j => simp [Sym2.lift_mk, mul_left_comm]

private theorem weightedSelfAdjoint_finrank (mu : Fin d → F) (hmu : ∀ i, mu i ≠ 0) :
    Module.finrank F ((selfAdjointMatricesSubmodule (Matrix.diagonal mu))) = (d + 1).choose 2 := by
  rw [(symmetricCoordinates mu hmu).finrank_eq, Module.finrank_pi]
  simp [Sym2.card]

private theorem rankOne_mem (mu : Fin d → F) (v : Fin d → F) :
    Matrix.vecMulVec v (fun k0 => mu k0 * v k0) ∈
      selfAdjointMatricesSubmodule (Matrix.diagonal mu) := by
  rw [selfAdjoint_mem_iff]
  intro i j
  simp only [Matrix.vecMulVec_apply]
  ring

private theorem trace_rankOne (mu : Fin d → F) (v : Fin d → F) :
    Matrix.trace (Matrix.vecMulVec v (fun k0 => mu k0 * v k0)) =
      Matrix.toBilin' (Matrix.diagonal mu) v v := by
  rw [Matrix.trace_vecMulVec, diagonal_apply]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem trace_rankOne_mul_rankOne (mu : Fin d → F) (u v : Fin d → F) :
    Matrix.trace (Matrix.vecMulVec u (fun k0 => mu k0 * u k0) *
      Matrix.vecMulVec v (fun k0 => mu k0 * v k0)) =
      (Matrix.toBilin' (Matrix.diagonal mu)) u v ^ 2 := by
  rw [Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, Matrix.trace_smul, Matrix.trace_vecMulVec]
  simp only [dotProduct, diagonal_apply]
  have h : (∑ i, u i * (mu i * v i)) = ∑ i, mu i * u i * v i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h, smul_eq_mul]
  ring

variable {n : ℕ}

private noncomputable def fourthMoment (mu : Fin d → F) (v : Fin n → Fin d → F) :
    Matrix (Fin d) (Fin d) F →ₗ[F] Matrix (Fin d) (Fin d) F :=
  ∑ k, ((Matrix.traceLinearMap (Fin d) F F).comp
    (LinearMap.mulLeft F (Matrix.vecMulVec (v k) (fun j => mu j * v k j)))).smulRight
      (Matrix.vecMulVec (v k) (fun j => mu j * v k j))

private theorem fourthMoment_apply (mu : Fin d → F) (v : Fin n → Fin d → F)
    (X : Matrix (Fin d) (Fin d) F) :
    fourthMoment mu v X = ∑ k,
      Matrix.trace (Matrix.vecMulVec (v k) (fun j => mu j * v k j) * X) •
        Matrix.vecMulVec (v k) (fun j => mu j * v k j) := by
  simp only [fourthMoment, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, Matrix.traceLinearMap_apply]

private theorem diagonal_unit_mem (mu : Fin d → F) (j : Fin d) :
    Matrix.single j j (1 : F) ∈ (selfAdjointMatricesSubmodule (Matrix.diagonal mu)) := by
  rw [selfAdjoint_mem_iff]
  intro i k
  by_cases hi : i = j <;> by_cases hk : k = j <;>
    subst_vars <;> simp_all [Matrix.single, eq_comm]

private theorem off_unit_mem (mu : Fin d → F) (hmu : ∀ i, mu i ≠ 0) (i j : Fin d) :
    Matrix.single i j (1 : F) + Matrix.single j i (mu i / mu j) ∈
      (selfAdjointMatricesSubmodule (Matrix.diagonal mu)) := by
  rw [selfAdjoint_mem_iff]
  intro k l
  by_cases hk : k = i <;> by_cases hl : l = j <;>
    by_cases hkj : k = j <;> by_cases hli : l = i <;>
    subst_vars <;> simp_all [Matrix.single, eq_comm, mul_add, mul_div_cancel₀]

private theorem fourthMoment_cross (mu : Fin d → F) (hmu : ∀ i, mu i ≠ 0)
    (v : Fin n → Fin d → F) (i j : Fin d) :
    fourthMoment mu v
        (Matrix.single i j (1 : F) + Matrix.single j i (mu i / mu j)) i j =
      2 * fourthMoment mu v (Matrix.single j j (1 : F)) i i := by
  simp only [fourthMoment_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_mul_single, Matrix.vecMulVec_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [hmu j]
  ring

private theorem fourthMoment_coefficient (mu : Fin d → F) (hmu : ∀ i, mu i ≠ 0)
    (v : Fin n → Fin d → F) (A beta : F) (hd : 2 ≤ d)
    (hT : ∀ X ∈ (selfAdjointMatricesSubmodule (Matrix.diagonal mu)),
      fourthMoment mu v X = A • X + (beta * Matrix.trace X) • (1 : Matrix (Fin d) (Fin d) F)) :
    A = 2 * beta := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hcross := fourthMoment_cross mu hmu v i j
  rw [hT _ (off_unit_mem mu hmu i j), hT _ (diagonal_unit_mem mu j)] at hcross
  have hdiag : Matrix.trace (Matrix.single j j (1 : F)) = 1 :=
    Matrix.trace_single_eq_same _ _
  have hoff : Matrix.trace (Matrix.single i j (1 : F) + Matrix.single j i (mu i / mu j)) = 0 := by
    rw [Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hij,
      Matrix.trace_single_eq_of_ne _ _ _ hij.symm, add_zero]
  rw [hdiag, hoff] at hcross
  simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.single, Matrix.one_apply,
    hij, hij.symm, smul_eq_mul] using hcross

open scoped BigOperators
open Module

variable {F S : Type*} [Field F] [AddCommGroup S] [Module F S]
variable {n : ℕ}

theorem gram_pair_sum (K : LinearMap.BilinForm F S) (P : Fin n → S) (a b : F)
    (hgram : ∀ i j, K (P i) (P j) = if i = j then a ^ 2 else b)
    (t : Fin n → F) (j : Fin n) :
    K (∑ i, t i • P i) (P j) = (a ^ 2 - b) * t j + b * ∑ i, t i := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hgram]
  have hi (i : Fin n) : t i * (if i = j then a ^ 2 else b) =
      b * t i + if i = j then (a ^ 2 - b) * t j else 0 := by
    split_ifs with h
    · subst i; ring
    · ring
  simp_rw [hi]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, add_comm]

private theorem relation_constant (K : LinearMap.BilinForm F S) (P : Fin n → S) (a b : F)
    (hgram : ∀ i j, K (P i) (P j) = if i = j then a ^ 2 else b)
    (hneq : a ^ 2 ≠ b) (t : Fin n → F) (hrel : ∑ i, t i • P i = 0) :
    ∀ i j, t i = t j := by
  intro i j
  have hi := gram_pair_sum K P a b hgram t i
  have hj := gram_pair_sum K P a b hgram t j
  rw [hrel, map_zero, LinearMap.zero_apply] at hi hj
  exact mul_left_cancel₀ (sub_ne_zero.mpr hneq) (add_right_cancel (hi.symm.trans hj))

theorem independent_nonzero_trace (K : LinearMap.BilinForm F S)
    (tau : S →ₗ[F] F) (P : Fin n → S) (a b : F)
    (hgram : ∀ i j, K (P i) (P j) = if i = j then a ^ 2 else b)
    (htrace : ∀ i, tau (P i) = a) (hneq : a ^ 2 ≠ b) (ha : a ≠ 0) :
    LinearIndependent F P := by
  apply Fintype.linearIndependent_iff.mpr
  intro t hrel i
  have htr := congrArg tau hrel
  simp only [map_sum, map_smul, htrace, smul_eq_mul, map_zero, ← Finset.sum_mul] at htr
  have hna : (∑ j, t j) = 0 := (mul_eq_zero.mp htr).resolve_right ha
  have hp := gram_pair_sum K P a b hgram t i
  rw [hrel, map_zero, LinearMap.zero_apply, hna, mul_zero, add_zero] at hp
  exact (mul_eq_zero.mp hp.symm).resolve_left (sub_ne_zero.mpr hneq)

private theorem scalar_frame_nonzero_trace [FiniteDimensional F S]
    (K : LinearMap.BilinForm F S) (tau : S →ₗ[F] F) (P : Fin n → S)
    (I : S) (a b : F) (hn : 0 < n) (hdim : Module.finrank F S = n)
    (hgram : ∀ i j, K (P i) (P j) = if i = j then a ^ 2 else b)
    (htrace : ∀ i, tau (P i) = a) (hI : ∀ i, K I (P i) = a)
    (hInz : I ≠ 0) (hneq : a ^ 2 ≠ b) (ha : a ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ ∑ i, P i = c • I := by
  have hli := independent_nonzero_trace K tau P a b hgram htrace hneq ha
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  have hsurj := (span_range_eq_top_iff_surjective_fintypeLinearCombination F P).mp hspan
  obtain ⟨t, ht⟩ := hsurj I
  change ∑ i, t i • P i = I at ht
  let j0 : Fin n := ⟨0, hn⟩
  have hconst (i : Fin n) : t i = t j0 := by
    have hi := gram_pair_sum K P a b hgram t i
    have hj := gram_pair_sum K P a b hgram t j0
    rw [ht, hI] at hi hj
    exact mul_left_cancel₀ (sub_ne_zero.mpr hneq) (add_right_cancel (hi.symm.trans hj))
  have ht' : t j0 • (∑ i, P i) = I := by
    rw [Finset.smul_sum]
    simpa only [hconst] using ht
  have htnz : t j0 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at ht'
    exact hInz ht'.symm
  refine ⟨(t j0)⁻¹, inv_ne_zero htnz, ?_⟩
  calc
    ∑ i, P i = (t j0)⁻¹ • (t j0 • ∑ i, P i) := by rw [smul_smul, inv_mul_cancel₀ htnz, one_smul]
    _ = (t j0)⁻¹ • I := by rw [ht']

private theorem moment_nonzero_trace [FiniteDimensional F S]
    (K : LinearMap.BilinForm F S) (tau : S →ₗ[F] F) (P : Fin n → S)
    (I : S) (T : S →ₗ[F] S) (a b c : F) (hdim : Module.finrank F S = n)
    (hgram : ∀ i j, K (P i) (P j) = if i = j then a ^ 2 else b)
    (htrace : ∀ i, tau (P i) = a) (hneq : a ^ 2 ≠ b) (ha : a ≠ 0)
    (hframe : ∑ i, P i = c • I)
    (hTP : ∀ j, T (P j) = (a ^ 2 - b) • P j + b • ∑ i, P i) :
    ∀ X, T X = (a ^ 2 - b) • X + ((b * c / a) * tau X) • I := by
  have hli := independent_nonzero_trace K tau P a b hgram htrace hneq ha
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  let U : S →ₗ[F] S :=
    (a ^ 2 - b) • LinearMap.id + (b * c / a) • tau.smulRight I
  have heq : T = U := LinearMap.ext_on_range hspan (fun j => by
    rw [hTP, hframe]
    simp [U, htrace, smul_smul, div_mul_cancel₀ _ ha])
  intro X
  simpa [U, smul_smul] using congrArg (fun L : S →ₗ[F] S => L X) heq

private theorem span_zero_trace [FiniteDimensional F S]
    (K : LinearMap.BilinForm F S) (tau : S →ₗ[F] F) (P : Fin n → S)
    (b : F) (hn : 0 < n) (hdim : Module.finrank F S = n)
    (hgram : ∀ i j, K (P i) (P j) = if i = j then (0 : F) ^ 2 else b)
    (htrace : ∀ i, tau (P i) = 0) (hb : b ≠ 0) (htau : Function.Surjective tau) :
    LinearMap.range (Fintype.linearCombination F P) = tau.ker ∧ ∑ i, P i = 0 := by
  let f := Fintype.linearCombination F P
  let j0 : Fin n := ⟨0, hn⟩
  have hneq : (0 : F) ^ 2 ≠ b := by simpa using hb.symm
  have hker : f.ker ≤ F ∙ (1 : Fin n → F) := by
    intro t ht
    change ∑ i, t i • P i = 0 at ht
    have hc := relation_constant K P 0 b hgram hneq t ht
    apply Submodule.mem_span_singleton.mpr
    refine ⟨t j0, ?_⟩
    funext i
    simpa using (hc i j0).symm
  have hone : (1 : Fin n → F) ≠ 0 := by
    intro hz
    have := congrFun hz j0
    simp at this
  have hkerdim : Module.finrank F f.ker ≤ 1 := by
    have h := Submodule.finrank_mono hker
    simpa [finrank_span_singleton hone] using h
  have hle : f.range ≤ tau.ker := by
    rintro X ⟨t, rfl⟩
    change tau (∑ i, t i • P i) = 0
    simp [htrace]
  have htauDim := tau.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr htau, finrank_top, Module.finrank_self, hdim] at htauDim
  have hfDim := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hfDim
  simp only [Fintype.card_fin] at hfDim
  have hrange : f.range = tau.ker := Submodule.eq_of_le_of_finrank_eq hle (by
    have := Submodule.finrank_mono hle
    omega)
  have hkpos : 0 < Module.finrank F f.ker := by
    rw [hrange] at hfDim
    omega
  have hkne : f.ker ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hkpos
    omega
  obtain ⟨t, ht, htnz⟩ := f.ker.ne_bot_iff.mp hkne
  change ∑ i, t i • P i = 0 at ht
  have hc := relation_constant K P 0 b hgram hneq t ht
  have ht0 : t j0 ≠ 0 := by
    intro hz
    apply htnz
    funext i
    simpa [hz] using hc i j0
  have hs : t j0 • (∑ i, P i) = 0 := by
    rw [Finset.smul_sum]
    have hc' (i : Fin n) := hc i j0
    simpa only [hc'] using ht
  exact ⟨hrange, (smul_eq_zero.mp hs).resolve_left ht0⟩

private theorem moment_zero_trace [FiniteDimensional F S]
    (tau : S →ₗ[F] F) (P : Fin n → S) (I : S) (T : S →ₗ[F] S) (b D : F)
    (hrange : LinearMap.range (Fintype.linearCombination F P) = tau.ker)
    (htraceI : tau I = D) (hD : D ≠ 0)
    (hTP : ∀ j, T (P j) = -b • P j) (hTI : T I = 0) :
    ∀ X, T X = -b • X + ((b / D) * tau X) • I := by
  have hker (Y : S) (hY : tau Y = 0) : T Y = -b • Y := by
    have hmem : Y ∈ LinearMap.range (Fintype.linearCombination F P) := by
      rw [hrange]
      exact hY
    obtain ⟨t, rfl⟩ := hmem
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, hTP]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, smul_smul, mul_comm]
  intro X
  have hY : tau (X - (tau X / D) • I) = 0 := by
    simp [htraceI, div_mul_cancel₀ _ hD]
  have h := hker _ hY
  simp only [map_sub, map_smul, hTI, smul_zero, sub_zero, smul_sub, smul_smul] at h
  rw [h, neg_mul]
  simp only [neg_smul, sub_neg_eq_add]
  congr 1
  congr 1
  ring

private noncomputable def restrictedMoment (mu : Fin d → F) (v : Fin n → Fin d → F) :
    selfAdjointMatricesSubmodule (Matrix.diagonal mu) →ₗ[F]
      selfAdjointMatricesSubmodule (Matrix.diagonal mu) :=
  ((fourthMoment mu v).comp
    (selfAdjointMatricesSubmodule (Matrix.diagonal mu)).subtype).codRestrict _ (by
    intro X
    change fourthMoment mu v X.val ∈ selfAdjointMatricesSubmodule (Matrix.diagonal mu)
    rw [fourthMoment_apply]
    change ∑ k, Matrix.trace
      (Matrix.vecMulVec (v k) (fun k0 => mu k0 * v k k0) * X.val) •
        Matrix.vecMulVec (v k) (fun k0 => mu k0 * v k k0) ∈
          selfAdjointMatricesSubmodule (Matrix.diagonal mu)
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (rankOne_mem mu (v k)))

private theorem identity_mem (mu : Fin d → F) :
    (1 : Matrix (Fin d) (Fin d) F) ∈ (selfAdjointMatricesSubmodule (Matrix.diagonal mu)) := by
  rw [selfAdjoint_mem_iff]
  intro i j
  by_cases h : i = j
  · subst j; rfl
  · simp [h, Ne.symm h]

private theorem diagonal_identity (mu : Fin d → F) (hmu : ∀ i, mu i ≠ 0)
    (v : Fin ((d + 1).choose 2) → Fin d → F) (a b : F)
    (hd : 2 ≤ d) (h2 : (2 : F) ≠ 0)
    (hself : ∀ i, (Matrix.toBilin' (Matrix.diagonal mu)) (v i) (v i) = a)
    (hoff : ∀ i j, i ≠ j → (Matrix.toBilin' (Matrix.diagonal mu)) (v i) (v j) ^ 2 = b)
    (hneq : a ^ 2 ≠ b) : a ^ 2 = ((d : F) + 2) * b := by
  let S := (selfAdjointMatricesSubmodule (Matrix.diagonal mu))
  let P : Fin ((d + 1).choose 2) → S := fun i =>
    ⟨Matrix.vecMulVec (v i) (fun k0 => mu k0 * v i k0), rankOne_mem mu (v i)⟩
  let I : S := ⟨1, identity_mem mu⟩
  let tau : S →ₗ[F] F := (Matrix.traceLinearMap (Fin d) F F).comp S.subtype
  let K : LinearMap.BilinForm F S :=
    LinearMap.BilinForm.restrict (LinearMap.compr₂ (LinearMap.mul F (Matrix (Fin d) (Fin d) F))
      (Matrix.traceLinearMap (Fin d) F F)) S
  let T := restrictedMoment mu v
  have hn : 0 < (d + 1).choose 2 := Nat.choose_pos (by omega)
  let j0 : Fin ((d + 1).choose 2) := ⟨0, hn⟩
  let e0 : Fin d := ⟨0, by omega⟩
  have hdim : Module.finrank F S = (d + 1).choose 2 := weightedSelfAdjoint_finrank mu hmu
  have htrace (i) : tau (P i) = a := by
    change Matrix.trace ((Matrix.vecMulVec (v i) (fun k0 => mu k0 * (v i) k0))) = a
    rw [trace_rankOne, hself]
  have hgram (i j) : K (P i) (P j) = if i = j then a ^ 2 else b := by
    change Matrix.trace (Matrix.vecMulVec (v i) (fun k0 => mu k0 * v i k0) *
      Matrix.vecMulVec (v j) (fun k0 => mu k0 * v j k0)) = _
    rw [trace_rankOne_mul_rankOne]
    split_ifs with hij
    · subst j; rw [hself]
    · exact hoff i j hij
  have hIP (i) : K I (P i) = a := by
    change Matrix.trace (1 * (Matrix.vecMulVec (v i) (fun k0 => mu k0 * (v i) k0))) = a
    rw [one_mul, trace_rankOne, hself]
  have hInz : I ≠ 0 := by
    intro hz
    have hh := congrArg (fun X : S => X.val e0 e0) hz
    simp [I] at hh
  have htraceI : tau I = (d : F) := by simp [tau, I, Matrix.trace_one]
  have hTP (j) : T (P j) = (a ^ 2 - b) • P j + b • ∑ i, P i := by
    apply Subtype.ext
    simp only [T, restrictedMoment, LinearMap.codRestrict_apply, LinearMap.comp_apply,
      fourthMoment_apply]
    change ∑ i, K (P i) (P j) • (P i).val = _
    simp only [hgram]
    have he (i) : (if i = j then a ^ 2 else b) • (P i).val =
        (if i = j then (a ^ 2 - b) • (P j).val else 0) + b • (P i).val := by
      split_ifs with hij
      · subst i; rw [sub_smul]; abel
      · simp
    simp_rw [he]
    simp [Finset.sum_add_distrib, Finset.smul_sum]
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by simpa [eq_comm] using hneq
    have htau : Function.Surjective tau := by
      intro t
      refine ⟨⟨t • Matrix.single e0 e0 1, Submodule.smul_mem _ _ (diagonal_unit_mem mu e0)⟩, ?_⟩
      change Matrix.trace (t • Matrix.single e0 e0 1) = t
      simp
    obtain ⟨hrange, hsum⟩ := span_zero_trace K tau P b hn hdim hgram htrace hb htau
    have hN : (((d + 1).choose 2 : ℕ) : F) = 1 := by
      have hh := gram_pair_sum K P 0 b hgram (fun _ => 1) j0
      simp only [one_smul, hsum, map_zero, LinearMap.zero_apply, zero_pow (by decide : 2 ≠ 0),
        zero_sub, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hh
      apply mul_left_cancel₀ hb
      linear_combination -hh
    have hcount : 2 * (((d + 1).choose 2 : ℕ) : F) = (d : F) * ((d : F) + 1) := by
      have hh := Nat.add_one_mul_choose_eq d 1
      have hh' : 2 * (d + 1).choose 2 = d * (d + 1) := by
        simpa [mul_comm] using hh.symm
      have hcast := congrArg (fun k : ℕ => (k : F)) hh'
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hcast
    have hD : (d : F) ≠ 0 := by
      intro hz
      rw [hN, hz] at hcount
      simp only [mul_one, zero_mul] at hcount
      exact h2 hcount
    have hTP' (j) : T (P j) = -b • P j := by
      simpa [hsum] using hTP j
    have hTI : T I = 0 := by
      apply Subtype.ext
      simp only [T, restrictedMoment, LinearMap.codRestrict_apply, LinearMap.comp_apply,
        fourthMoment_apply]
      change ∑ i, Matrix.trace (Matrix.vecMulVec (v i) (fun k0 => mu k0 * v i k0) * 1) •
        Matrix.vecMulVec (v i) (fun k0 => mu k0 * v i k0) = 0
      simp only [mul_one, trace_rankOne, hself, zero_smul, Finset.sum_const_zero]
    have hform := moment_zero_trace tau P I T b (d : F) hrange htraceI hD hTP' hTI
    have hcoef : -b = 2 * (b / (d : F)) :=
      fourthMoment_coefficient mu hmu v (-b) (b / (d : F)) hd (by
        intro X hX
        exact congrArg Subtype.val (hform ⟨X, hX⟩))
    have hh := congrArg (fun x : F => x * (d : F)) hcoef
    rw [mul_assoc, div_mul_cancel₀ _ hD] at hh
    simp only [zero_pow (by decide : 2 ≠ 0)]
    linear_combination hh
  · obtain ⟨c, hc, hframe⟩ :=
      scalar_frame_nonzero_trace K tau P I a b hn hdim hgram htrace hIP hInz hneq ha
    have hform := moment_nonzero_trace K tau P I T a b c hdim hgram htrace hneq ha hframe hTP
    have hcoef : a ^ 2 - b = 2 * (b * c / a) :=
      fourthMoment_coefficient mu hmu v (a ^ 2 - b) (b * c / a) hd (by
        intro X hX
        exact congrArg Subtype.val (hform ⟨X, hX⟩))
    have htr := congrArg tau hframe
    simp only [map_sum, htrace, map_smul, htraceI, smul_eq_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htr
    have hp := gram_pair_sum K P a b hgram (fun _ => 1) j0
    simp only [one_smul] at hp
    rw [hframe, map_smul, LinearMap.smul_apply, smul_eq_mul, hIP] at hp
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hp
    have hcoef' := congrArg (fun x : F => x * a) hcoef
    rw [mul_assoc, div_mul_cancel₀ _ ha] at hcoef'
    apply mul_left_cancel₀ hc
    linear_combination a * hp + b * htr + hcoef'

def IsEquiangularSystem {F : Type*} [Field F] {d n : ℕ}
    (B : LinearMap.BilinForm F (Fin d → F))
    (φ : Fin n → Fin d → F) (a b : F) : Prop :=
  (∀ j, B (φ j) (φ j) = a) ∧ ∀ i j, i ≠ j → B (φ i) (φ j) ^ 2 = b

def claim : Prop :=
  ∀ (F : Type) [Field F] [Fintype F], ringChar F ≠ 2 →
    ∀ d : ℕ, 2 ≤ d →
      ∀ B : LinearMap.BilinForm F (Fin d → F), B.IsSymm → B.Nondegenerate →
        ∀ (φ : Fin ((d + 1).choose 2) → Fin d → F) (a b : F),
          IsEquiangularSystem B φ a b → a ^ 2 ≠ b →
            a ^ 2 = ((d : F) + 2) * b

private theorem orthogonal_coordinates (B : LinearMap.BilinForm F (Fin d → F))
    (e : Basis (Fin d) F (Fin d → F)) (he : B.IsOrthoᵢ e) (x y : Fin d → F) :
    B x y = (Matrix.toBilin' (Matrix.diagonal (fun i => B (e i) (e i))))
      (fun i => e.repr x i) (fun i => e.repr y i) := by
  have hmatrix : B.toMatrix e = Matrix.diagonal (fun i => B (e i) (e i)) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply_ne _ hij, he hij]
  rw [Matrix.toBilin'_apply', ← hmatrix]
  simpa using B.dotProduct_toMatrix_mulVec e (e.equivFun x) (e.equivFun y) |>.symm

private theorem parameter_identity {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (d : ℕ) (hd : 2 ≤ d) (B : LinearMap.BilinForm F (Fin d → F))
    (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (φ : Fin ((d + 1).choose 2) → Fin d → F) (a b : F)
    (heq : IsEquiangularSystem B φ a b) (hneq : a ^ 2 ≠ b) :
    a ^ 2 = ((d : F) + 2) * b := by
  let : Invertible (2 : F) := invertibleOfNonzero h2
  have hex : ∃ e : Basis (Fin d) F (Fin d → F), B.IsOrthoᵢ e := by
    have hdimension : Module.finrank F (Fin d → F) = d := by
      rw [Module.finrank_pi]
      simp
    have hh := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hB)
    rw [hdimension] at hh
    exact hh
  obtain ⟨e, he⟩ := hex
  exact diagonal_identity (fun i => B (e i) (e i))
    (he.not_isOrtho_basis_self_of_separatingLeft hnd.1)
    (fun j i => e.repr (φ j) i) a b hd h2
    (fun j => (orthogonal_coordinates B e he (φ j) (φ j)).symm.trans (heq.1 j))
    (fun i j hij => by rw [← orthogonal_coordinates B e he]; exact heq.2 i j hij)
    hneq

theorem result : claim := by
  intro F _ _ hchar d hd B hB hnd φ a b heq hneq
  exact parameter_identity (Ring.two_ne_zero hchar) d hd B hB hnd φ a b heq hneq

end D5.S3.QuadraticForms.GerzonEqualityParameterIdentity
