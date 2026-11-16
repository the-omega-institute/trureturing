/- GID: D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialTransposeSaturation/Singular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact tensor ranks of the rectangular singular pencil blocks. -/

/-
proof_shape: samePencil_transpose_injective: content; consumer=samePencil_rank.
proof_shape: samePencil_rank, right_right_rank and tensor_rank inherit content
  through samePencil_transpose_injective when same-delivery helpers are inlined.
proof_shape: remaining rank formulas and coordinate/splitting helpers are
  consumed bind-only declarations in the terminal classification.
escape_witness: samePencil_transpose_injective proves the shifted tensor
recurrence has zero kernel by induction on the first index.
admission_basis: escape-witness
Direct frozen dependencies: ShiftPencilBlocks.pencil_rank_of_le,
ShiftPencilBlocks.pencil_rank_of_ge, QuantumMaxFlowBound.rank_map_algebraMap.
Protected baseline statement_id for ShiftPencilBlocks:
sha256:e50a8706f88f9e79731c6a392fba050f8a9a3943a3f17a745dbc487343433882.
Protected baseline statement_id for QuantumMaxFlowBound:
sha256:06b305ef00d70bec3cf0f07510dc024d6d39db5dfc8aec9d8456823c6e2eda29.
-/

import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
import Mathlib.LinearAlgebra.Matrix.Dual
import D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open Matrix Module
open scoped Kronecker
open D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks

private def samePencil (r s : ℕ) :
    Matrix (Fin r × Fin s) (Fin (r + 1) × Fin (s + 1)) ℚ :=
  rectId r (r + 1) ⊗ₖ rectId s (s + 1) + shift1 r ⊗ₖ shift1 s

private theorem samePencil_transpose_injective (r s : ℕ) :
    Function.Injective (samePencil r s)ᵀ.mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change (samePencil r s)ᵀ.mulVec z = 0 at hz
  have hzall (k : ℕ) : ∀ i : Fin r, i.val = k → ∀ j : Fin s, z (i, j) = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi j
      have he := congrFun hz (i.castSucc, j.castSucc)
      change (∑ a : Fin r × Fin s,
        samePencil r s a (i.castSucc, j.castSucc) * z a) = 0 at he
      simp only [samePencil, Matrix.add_apply, Matrix.kronecker_apply,
        rectId, shift1, Matrix.submatrix_apply, Matrix.one_apply,
        Fin.val_castSucc, Fintype.sum_prod_type, add_mul,
        Finset.sum_add_distrib] at he
      have hfirst : (∑ a : Fin r, ∑ b : Fin s,
          (if a.val = i.val then (1 : ℚ) else 0) *
          (if b.val = j.val then 1 else 0) * z (a, b)) = z (i, j) := by
        simp [Fin.val_inj, ite_mul, mul_ite]
      have hsecond : (∑ a : Fin r, ∑ b : Fin s,
          (if a.val + 1 = i.val then (1 : ℚ) else 0) *
          (if b.val + 1 = j.val then 1 else 0) * z (a, b)) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        by_cases ha : a.val + 1 = i.val
        · have haz := ih a.val (by omega) a rfl b
          simp [haz]
        · simp [ha]
      rw [hfirst, hsecond, add_zero] at he
      exact he
  funext ⟨i, j⟩
  exact hzall i.val i rfl j

private theorem samePencil_rank (r s : ℕ) : (samePencil r s).rank = r * s := by
  rw [← Matrix.rank_transpose, Matrix.rank,
    LinearMap.finrank_range_of_inj (samePencil_transpose_injective r s)]
  simp

private theorem mixedPencil_rank (r s : ℕ) :
    (pencil r s).rank = r * s + min r s := by
  rcases le_total r s with h | h
  · rw [pencil_rank_of_le r s h, min_eq_left h]
    ring
  · rw [pencil_rank_of_ge r s h, min_eq_right h]
    ring

/-- The first rectangular shift coefficient, including its zero-index case. -/
def rightE (r : ℕ) : Matrix (Fin r) (Fin (r + 1)) ℂ :=
  (rectId r (r + 1)).map (algebraMap ℚ ℂ)

/-- The second rectangular shift coefficient. -/
def rightF (r : ℕ) : Matrix (Fin r) (Fin (r + 1)) ℂ :=
  (shift1 r).map (algebraMap ℚ ℂ)

/-- Two right singular blocks have full row rank in their tensor sum. -/
private theorem right_right_rank (r s : ℕ) :
    (tensorSum (rightE r) (rightF r) (rightE s) (rightF s)).rank = r * s := by
  have he : tensorSum (rightE r) (rightF r) (rightE s) (rightF s) =
      (samePencil r s).map (algebraMap ℚ ℂ) := by
    ext i j
    simp [tensorSum, rightE, rightF, samePencil, Matrix.kronecker_apply]
  rw [he, rank_map_algebraMap, samePencil_rank]

/-- Partially transposing two right blocks gives the exact mixed-pencil rank. -/
private theorem right_right_partialTranspose_rank (r s : ℕ) :
    (partialTranspose (rightE r) (rightF r) (rightE s) (rightF s)).rank =
      r * s + min r s := by
  have he : partialTranspose (rightE r) (rightF r) (rightE s) (rightF s) =
      (pencil r s)ᵀ.map (algebraMap ℚ ℂ) := by
    ext i j
    simp [partialTranspose, tensorSum, rightE, rightF, pencil, Matrix.kronecker_apply]
  rw [he, rank_map_algebraMap, Matrix.rank_transpose, mixedPencil_rank]

/-- Opposite orientations interchange the two rank formulas. -/
private theorem right_left_rank (r s : ℕ) :
    (tensorSum (rightE r) (rightF r) (rightE s)ᵀ (rightF s)ᵀ).rank =
      r * s + min r s := by
  have he : tensorSum (rightE r) (rightF r) (rightE s)ᵀ (rightF s)ᵀ =
      (pencil r s).map (algebraMap ℚ ℂ) := by
    ext i j
    simp [tensorSum, rightE, rightF, pencil, Matrix.kronecker_apply]
  rw [he, rank_map_algebraMap, mixedPencil_rank]

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open LinearMap Submodule Module Matrix
open scoped Kronecker TensorProduct
open ChainSplitting.FinitePair

namespace ChainSplitting.FinitePair.SplitData

variable {p : Pencil ℂ} {r : ℕ} (s : SplitData p r)

/-- The source of the actual extracted chain summand. -/
abbrev source := span ℂ (Set.range s.chain)

/-- The target of the actual extracted chain summand. -/
abbrev target := span ℂ (Set.range (fun j : Fin r => p.second (s.chain j.castSucc)))

def sourceBasis : Basis (Fin (r + 1)) ℂ s.source := Basis.span s.domain_independent

def targetBasis : Basis (Fin r) ℂ s.target := Basis.span s.codomain_independent

/-- The two restricted arrows, realized by their commuting projection. -/
def firstBlock : s.source →ₗ[ℂ] s.target :=
  s.codomain_isProj.codRestrict.comp (p.first.comp s.source.subtype)

def secondBlock : s.source →ₗ[ℂ] s.target :=
  s.codomain_isProj.codRestrict.comp (p.second.comp s.source.subtype)

/-- The actual finite pencil represented by the extracted chain spans. -/
def block : Pencil ℂ where
  domain := s.source
  codomain := s.target
  first := s.firstBlock
  second := s.secondBlock

private theorem firstBlock_coe (x : s.source) : (s.firstBlock x : p.codomain) = p.first x := by
  change s.codomainProjection (p.first x) = p.first x
  have h := LinearMap.congr_fun s.first_commute x
  simpa only [LinearMap.comp_apply, s.domain_isProj.map_id x x.property] using h

private theorem secondBlock_coe (x : s.source) : (s.secondBlock x : p.codomain) = p.second x := by
  change s.codomainProjection (p.second x) = p.second x
  have h := LinearMap.congr_fun s.second_commute x
  simpa only [LinearMap.comp_apply, s.domain_isProj.map_id x x.property] using h

private theorem first_chain_zero : p.first (s.chain 0) = 0 := by
  have he := congrFun s.boundary_zero 0
  simpa [ChainSplitting.boundary, Fin.snoc_apply_zero, Function.comp_def] using he

private theorem second_chain_last : p.second (s.chain (Fin.last r)) = 0 := by
  have he := congrFun s.boundary_zero (Fin.last (r + 1))
  simpa [ChainSplitting.boundary, Function.comp_def] using he

private theorem chain_step (j : Fin r) :
    p.first (s.chain j.succ) = p.second (s.chain j.castSucc) := by
  have he : Fin.snoc (p.first ∘ s.chain) 0 =
      (@Fin.cons _ (fun _ => p.codomain)) 0 (p.second ∘ s.chain) :=
    sub_eq_zero.mp s.boundary_zero
  have h := congrFun he j.succ.castSucc
  rw [Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ] at h
  exact h

private theorem first_basis_zero : s.firstBlock (s.sourceBasis 0) = 0 := by
  apply Subtype.ext
  rw [s.firstBlock_coe]
  simpa [sourceBasis] using s.first_chain_zero

private theorem first_basis_succ (j : Fin r) :
    s.firstBlock (s.sourceBasis j.succ) = s.targetBasis j := by
  apply Subtype.ext
  rw [s.firstBlock_coe]
  simpa [sourceBasis, targetBasis] using s.chain_step j

private theorem second_basis_castSucc (j : Fin r) :
    s.secondBlock (s.sourceBasis j.castSucc) = s.targetBasis j := by
  apply Subtype.ext
  rw [s.secondBlock_coe]
  simp [sourceBasis, targetBasis]

private theorem second_basis_last : s.secondBlock (s.sourceBasis (Fin.last r)) = 0 := by
  apply Subtype.ext
  rw [s.secondBlock_coe]
  simpa [sourceBasis] using s.second_chain_last

/-- The chain relation gives the shift matrix in its actual span bases. -/
private theorem firstBlock_matrix : LinearMap.toMatrix s.sourceBasis s.targetBasis s.firstBlock =
    rightF r := by
  ext i j
  cases j using Fin.cases with
  | zero =>
    simp [LinearMap.toMatrix_apply, s.first_basis_zero, rightF,
      D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.shift1]
  | succ j =>
    simp [LinearMap.toMatrix_apply, s.first_basis_succ, rightF,
      D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks.shift1,
      Matrix.submatrix_apply, Matrix.one_apply, Finsupp.single_apply, Fin.ext_iff, eq_comm]

/-- The second chain arrow is the truncated identity matrix. -/
private theorem secondBlock_matrix : LinearMap.toMatrix s.sourceBasis s.targetBasis s.secondBlock =
    rightE r := by
  ext i j
  cases j using Fin.lastCases with
  | last =>
    simp [LinearMap.toMatrix_apply, s.second_basis_last, rightE,
      D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rectId,
      Matrix.submatrix_apply, Matrix.one_apply, Nat.ne_of_lt i.isLt]
  | cast j =>
    simp [LinearMap.toMatrix_apply, s.second_basis_castSucc, rightE,
      D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rectId,
      Matrix.submatrix_apply, Matrix.one_apply, Finsupp.single_apply, Fin.ext_iff, eq_comm]

end ChainSplitting.FinitePair.SplitData


private theorem finrank_range_of_factorization
    {A B C D : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup D] [Module ℂ D]
    (T : A →ₗ[ℂ] B) (S : C →ₗ[ℂ] D) (i : D →ₗ[ℂ] B) (π : A →ₗ[ℂ] C)
    (hi : Function.Injective i) (hπ : LinearMap.range π = ⊤)
    (he : T = i.comp (S.comp π)) :
    finrank ℂ (LinearMap.range T) = finrank ℂ (LinearMap.range S) := by
  rw [he, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hπ]
  exact (Submodule.equivMapOfInjective i hi (LinearMap.range S)).finrank_eq.symm

private theorem concatenation_ranks_of_factorization
    {A B C D : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup D] [Module ℂ D]
    (f₁ f₂ : A →ₗ[ℂ] B) (g₁ g₂ : C →ₗ[ℂ] D)
    (i : D →ₗ[ℂ] B) (π : A →ₗ[ℂ] C)
    (hi : Function.Injective i) (hπ : LinearMap.range π = ⊤)
    (hf : f₁ = i.comp (g₁.comp π)) (hg : f₂ = i.comp (g₂.comp π)) :
    finrank ℂ ↥(LinearMap.range f₁ ⊔ LinearMap.range f₂) =
      finrank ℂ ↥(LinearMap.range g₁ ⊔ LinearMap.range g₂) ∧
    finrank ℂ (LinearMap.range (f₁.prod f₂)) =
      finrank ℂ (LinearMap.range (g₁.prod g₂)) := by
  have hπ₂ : LinearMap.range (LinearMap.prodMap π π) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    rintro ⟨x, y⟩
    obtain ⟨a, ha⟩ := LinearMap.range_eq_top.mp hπ x
    obtain ⟨b, hb⟩ := LinearMap.range_eq_top.mp hπ y
    exact ⟨(a, b), Prod.ext ha hb⟩
  have hi₂ : Function.Injective (LinearMap.prodMap i i) := by
    intro x y h
    exact Prod.ext (hi (congrArg Prod.fst h)) (hi (congrArg Prod.snd h))
  constructor
  · rw [← LinearMap.range_coprod, ← LinearMap.range_coprod]
    apply finrank_range_of_factorization _ _ i (LinearMap.prodMap π π) hi hπ₂
    rw [hf, hg]
    apply LinearMap.ext
    intro x
    simp [LinearMap.coprod_apply, map_add]
  · apply finrank_range_of_factorization _ _ (LinearMap.prodMap i i) π hi₂ hπ
    rw [hf, hg]
    rfl

namespace ChainSplitting.FinitePair.SplitData

section ProjectedRank

variable {p : Pencil ℂ} {r : ℕ} (s : SplitData p r)
  {U' V' : Type*} [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup V'] [Module ℂ V'] (g₁ g₂ : U' →ₗ[ℂ] V')

private theorem firstBlock_factor :
    s.target.subtype.comp (s.firstBlock.comp s.domain_isProj.codRestrict) =
      s.codomainProjection.comp p.first := by
  ext x
  change s.codomainProjection (p.first (s.domainProjection x)) =
    s.codomainProjection (p.first x)
  calc
    _ = p.first (s.domainProjection (s.domainProjection x)) :=
      LinearMap.congr_fun s.first_commute (s.domainProjection x)
    _ = p.first (s.domainProjection x) := congrArg p.first
      (s.domain_isProj.map_id _ (s.domain_isProj.map_mem x))
    _ = _ := (LinearMap.congr_fun s.first_commute x).symm

private theorem secondBlock_factor :
    s.target.subtype.comp (s.secondBlock.comp s.domain_isProj.codRestrict) =
      s.codomainProjection.comp p.second := by
  ext x
  change s.codomainProjection (p.second (s.domainProjection x)) =
    s.codomainProjection (p.second x)
  calc
    _ = p.second (s.domainProjection (s.domainProjection x)) :=
      LinearMap.congr_fun s.second_commute (s.domainProjection x)
    _ = p.second (s.domainProjection x) := congrArg p.second
      (s.domain_isProj.map_id _ (s.domain_isProj.map_mem x))
    _ = _ := (LinearMap.congr_fun s.second_commute x).symm

/-- The projected tensor component and its actual span restriction have the
same rank. The factorization uses surjectivity onto the chain span and the
split injection of the target span. -/
private theorem projected_tensor_rank : finrank ℂ (LinearMap.range
    ((TensorProduct.map s.codomainProjection (LinearMap.id : Module.End ℂ V')).comp
      (TensorProduct.map p.first g₁ + TensorProduct.map p.second g₂))) =
    finrank ℂ (LinearMap.range
      (TensorProduct.map s.firstBlock g₁ + TensorProduct.map s.secondBlock g₂)) := by
  let i := TensorProduct.map s.target.subtype (LinearMap.id : Module.End ℂ V')
  let π := TensorProduct.map s.domain_isProj.codRestrict (LinearMap.id : Module.End ℂ U')
  let T := TensorProduct.map s.firstBlock g₁ + TensorProduct.map s.secondBlock g₂
  have hl : (TensorProduct.map s.codomain_isProj.codRestrict
      (LinearMap.id : Module.End ℂ V')).comp i = LinearMap.id := by
    dsimp [i]
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
    have h : s.codomain_isProj.codRestrict.comp s.target.subtype = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact s.codomain_isProj.codRestrict_apply_cod x
    rw [h, TensorProduct.map_id]
  have hi : Function.Injective i := by
    intro x y h
    have he := congrArg (TensorProduct.map s.codomain_isProj.codRestrict
      (LinearMap.id : Module.End ℂ V')) h
    simpa only [← LinearMap.comp_apply, hl, LinearMap.id_apply] using he
  have hr : π.comp (TensorProduct.map s.source.subtype
      (LinearMap.id : Module.End ℂ U')) = LinearMap.id := by
    dsimp [π]
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
    have h : s.domain_isProj.codRestrict.comp s.source.subtype = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact s.domain_isProj.codRestrict_apply_cod x
    rw [h, TensorProduct.map_id]
  have hπ : LinearMap.range π = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro x
    refine ⟨TensorProduct.map s.source.subtype (LinearMap.id : Module.End ℂ U') x, ?_⟩
    exact LinearMap.congr_fun hr x
  have hf : (TensorProduct.map s.codomainProjection (LinearMap.id : Module.End ℂ V')).comp
      (TensorProduct.map p.first g₁ + TensorProduct.map p.second g₂) =
      i.comp (T.comp π) := by
    dsimp [i, T, π]
    simp only [LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
      LinearMap.id_comp, LinearMap.comp_id, s.firstBlock_factor, s.secondBlock_factor]
  exact finrank_range_of_factorization _ T i π hi hπ hf

/-- Projection to the simultaneous complementary source kernel. -/
def sourceComplementProjection : p.domain →ₗ[ℂ] LinearMap.ker s.domainProjection :=
  (LinearMap.id - s.domainProjection).codRestrict (LinearMap.ker s.domainProjection) (by
    intro x
    change s.domainProjection (x - s.domainProjection x) = 0
    rw [map_sub, s.domain_isProj.map_id _ (s.domain_isProj.map_mem x), sub_self])

/-- Projection to the simultaneous complementary target kernel. -/
def targetComplementProjection : p.codomain →ₗ[ℂ] LinearMap.ker s.codomainProjection :=
  (LinearMap.id - s.codomainProjection).codRestrict (LinearMap.ker s.codomainProjection) (by
    intro x
    change s.codomainProjection (x - s.codomainProjection x) = 0
    rw [map_sub, s.codomain_isProj.map_id _ (s.codomain_isProj.map_mem x), sub_self])

private theorem remainder_first_factor : (LinearMap.ker s.codomainProjection).subtype.comp
    (s.remainder.first.comp s.sourceComplementProjection) =
    (LinearMap.id - s.codomainProjection).comp p.first := by
  ext x
  change p.first (x - s.domainProjection x) = p.first x - s.codomainProjection (p.first x)
  rw [map_sub]
  exact congrArg (fun y => p.first x - y) (LinearMap.congr_fun s.first_commute x).symm

private theorem remainder_second_factor : (LinearMap.ker s.codomainProjection).subtype.comp
    (s.remainder.second.comp s.sourceComplementProjection) =
    (LinearMap.id - s.codomainProjection).comp p.second := by
  ext x
  change p.second (x - s.domainProjection x) = p.second x - s.codomainProjection (p.second x)
  rw [map_sub]
  exact congrArg (fun y => p.second x - y) (LinearMap.congr_fun s.second_commute x).symm

/-- The other component in rank additivity is exactly the tensor sum of the
actual simultaneous complementary kernels. -/
private theorem remainder_tensor_rank : finrank ℂ (LinearMap.range
    ((LinearMap.id - TensorProduct.map s.codomainProjection
      (LinearMap.id : Module.End ℂ V')).comp
      (TensorProduct.map p.first g₁ + TensorProduct.map p.second g₂))) =
    finrank ℂ (LinearMap.range
      (TensorProduct.map s.remainder.first g₁ + TensorProduct.map s.remainder.second g₂)) := by
  let i := TensorProduct.map (LinearMap.ker s.codomainProjection).subtype
    (LinearMap.id : Module.End ℂ V')
  let π := TensorProduct.map s.sourceComplementProjection (LinearMap.id : Module.End ℂ U')
  let T := TensorProduct.map s.remainder.first g₁ + TensorProduct.map s.remainder.second g₂
  have hi' : s.targetComplementProjection.comp
      (LinearMap.ker s.codomainProjection).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (x : p.codomain) - s.codomainProjection x = x
    rw [LinearMap.mem_ker.mp x.property, sub_zero]
  have hl : (TensorProduct.map s.targetComplementProjection
      (LinearMap.id : Module.End ℂ V')).comp i = LinearMap.id := by
    dsimp [i]
    rw [← TensorProduct.map_comp, hi', LinearMap.id_comp, TensorProduct.map_id]
  have hi : Function.Injective i := by
    intro x y h
    have he := congrArg (TensorProduct.map s.targetComplementProjection
      (LinearMap.id : Module.End ℂ V')) h
    simpa only [← LinearMap.comp_apply, hl, LinearMap.id_apply] using he
  have hπ' : s.sourceComplementProjection.comp
      (LinearMap.ker s.domainProjection).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (x : p.domain) - s.domainProjection x = x
    rw [LinearMap.mem_ker.mp x.property, sub_zero]
  have hr : π.comp (TensorProduct.map (LinearMap.ker s.domainProjection).subtype
      (LinearMap.id : Module.End ℂ U')) = LinearMap.id := by
    dsimp [π]
    rw [← TensorProduct.map_comp, hπ', LinearMap.id_comp, TensorProduct.map_id]
  have hπ : LinearMap.range π = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro x
    refine ⟨TensorProduct.map (LinearMap.ker s.domainProjection).subtype
      (LinearMap.id : Module.End ℂ U') x, ?_⟩
    exact LinearMap.congr_fun hr x
  have he : (LinearMap.id - TensorProduct.map s.codomainProjection
      (LinearMap.id : Module.End ℂ V')).comp
      (TensorProduct.map p.first g₁ + TensorProduct.map p.second g₂) =
      i.comp (T.comp π) := by
    have hsub : (LinearMap.id : Module.End ℂ (p.codomain ⊗[ℂ] V')) -
        TensorProduct.map s.codomainProjection (LinearMap.id : Module.End ℂ V') =
        TensorProduct.map (LinearMap.id - s.codomainProjection)
          (LinearMap.id : Module.End ℂ V') := by
      ext x y
      change x ⊗ₜ[ℂ] y - s.codomainProjection x ⊗ₜ[ℂ] y =
        (x - s.codomainProjection x) ⊗ₜ[ℂ] y
      exact (TensorProduct.sub_tmul x (s.codomainProjection x) y).symm
    rw [hsub]
    dsimp [i, T, π]
    simp only [LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
      LinearMap.id_comp, LinearMap.comp_id, s.remainder_first_factor,
      s.remainder_second_factor]
  exact finrank_range_of_factorization _ T i π hi hπ he

end ProjectedRank

/-- Tensor rank is additive for the actual extracted finite pencil and its
simultaneous complementary pencil. -/
theorem tensor_split {p : Pencil ℂ} {r : ℕ} (s : SplitData p r) (q : Pencil ℂ) :
    finrank ℂ (LinearMap.range
      (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second)) =
    finrank ℂ (LinearMap.range
      (TensorProduct.map s.block.first q.first + TensorProduct.map s.block.second q.second)) +
    finrank ℂ (LinearMap.range
      (TensorProduct.map s.remainder.first q.first +
        TensorProduct.map s.remainder.second q.second)) := by
  have hQ : s.codomainProjection.comp s.codomainProjection = s.codomainProjection := by
    ext x
    exact s.codomain_isProj.map_id _ (s.codomain_isProj.map_mem x)
  have h := finrank_tensorSum_split p.first p.second q.first q.second
    s.domainProjection s.codomainProjection hQ s.first_commute s.second_commute
  dsimp only at h
  rw [s.projected_tensor_rank q.first q.second, s.remainder_tensor_rank q.first q.second] at h
  exact h

section Concatenation

variable {p : Pencil ℂ} {r : ℕ} (s : SplitData p r)

private theorem projected_concatenation_ranks :
    finrank ℂ ↥(LinearMap.range (s.codomainProjection.comp p.first) ⊔
      LinearMap.range (s.codomainProjection.comp p.second)) =
      finrank ℂ ↥(LinearMap.range s.firstBlock ⊔ LinearMap.range s.secondBlock) ∧
    finrank ℂ (LinearMap.range ((s.codomainProjection.comp p.first).prod
      (s.codomainProjection.comp p.second))) =
      finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)) := by
  apply concatenation_ranks_of_factorization _ _ _ _ s.target.subtype
    s.domain_isProj.codRestrict s.target.injective_subtype
  · apply LinearMap.range_eq_top.mpr
    intro x
    exact ⟨x, s.domain_isProj.codRestrict_apply_cod x⟩
  · exact s.firstBlock_factor.symm
  · exact s.secondBlock_factor.symm

private theorem remainder_concatenation_ranks :
    finrank ℂ ↥(LinearMap.range ((LinearMap.id - s.codomainProjection).comp p.first) ⊔
      LinearMap.range ((LinearMap.id - s.codomainProjection).comp p.second)) =
      finrank ℂ ↥(LinearMap.range s.remainder.first ⊔ LinearMap.range s.remainder.second) ∧
    finrank ℂ (LinearMap.range (((LinearMap.id - s.codomainProjection).comp p.first).prod
      ((LinearMap.id - s.codomainProjection).comp p.second))) =
      finrank ℂ (LinearMap.range (s.remainder.first.prod s.remainder.second)) := by
  apply concatenation_ranks_of_factorization _ _ _ _
    (LinearMap.ker s.codomainProjection).subtype s.sourceComplementProjection
    (LinearMap.ker s.codomainProjection).injective_subtype
  · apply LinearMap.range_eq_top.mpr
    intro x
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (x : p.domain) - s.domainProjection x = x
    rw [LinearMap.mem_ker.mp x.property, sub_zero]
  · exact s.remainder_first_factor.symm
  · exact s.remainder_second_factor.symm

/-- Horizontal concatenation rank adds over the actual chain splitting. -/
theorem horizontal_split : finrank ℂ ↥(LinearMap.range p.first ⊔ LinearMap.range p.second) =
    finrank ℂ ↥(LinearMap.range s.firstBlock ⊔ LinearMap.range s.secondBlock) +
      finrank ℂ ↥(LinearMap.range s.remainder.first ⊔ LinearMap.range s.remainder.second) := by
  have hQ : s.codomainProjection.comp s.codomainProjection = s.codomainProjection := by
    ext x
    exact s.codomain_isProj.map_id _ (s.codomain_isProj.map_mem x)
  have hcomm : s.codomainProjection.comp (p.first.coprod p.second) =
      (p.first.coprod p.second).comp
        (LinearMap.prodMap s.domainProjection s.domainProjection) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prodMap_apply, map_add]
    exact congrArg₂ (· + ·) (LinearMap.congr_fun s.first_commute x.1)
      (LinearMap.congr_fun s.second_commute x.2)
  have h := finrank_range_split (p.first.coprod p.second)
    (LinearMap.prodMap s.domainProjection s.domainProjection) s.codomainProjection hQ hcomm
  have hbase : finrank ℂ (LinearMap.range (p.first.coprod p.second)) =
      finrank ℂ ↥(LinearMap.range p.first ⊔ LinearMap.range p.second) :=
    congrArg (fun H : Submodule ℂ p.codomain => finrank ℂ H)
      (LinearMap.range_coprod p.first p.second)
  have hS : finrank ℂ (LinearMap.range
      (s.codomainProjection.comp (p.first.coprod p.second))) =
      finrank ℂ ↥(LinearMap.range (s.codomainProjection.comp p.first) ⊔
        LinearMap.range (s.codomainProjection.comp p.second)) := by
    apply congrArg (fun H : Submodule ℂ p.codomain => finrank ℂ H)
    rw [LinearMap.comp_coprod, LinearMap.range_coprod]
  have hW : finrank ℂ (LinearMap.range
      ((LinearMap.id - s.codomainProjection).comp (p.first.coprod p.second))) =
      finrank ℂ ↥(LinearMap.range ((LinearMap.id - s.codomainProjection).comp p.first) ⊔
        LinearMap.range ((LinearMap.id - s.codomainProjection).comp p.second)) := by
    apply congrArg (fun H : Submodule ℂ p.codomain => finrank ℂ H)
    rw [LinearMap.comp_coprod, LinearMap.range_coprod]
  rw [hbase, hS, hW, s.projected_concatenation_ranks.1,
    s.remainder_concatenation_ranks.1] at h
  exact h

/-- Vertical concatenation rank adds over the same simultaneous splitting. -/
theorem vertical_split : finrank ℂ (LinearMap.range (p.first.prod p.second)) =
    finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)) +
      finrank ℂ (LinearMap.range (s.remainder.first.prod s.remainder.second)) := by
  let Q := LinearMap.prodMap s.codomainProjection s.codomainProjection
  have hQ : Q.comp Q = Q := by
    ext x <;> exact s.codomain_isProj.map_id _ (s.codomain_isProj.map_mem _)
  have hcomm : Q.comp (p.first.prod p.second) =
      (p.first.prod p.second).comp s.domainProjection := by
    ext x
    · exact LinearMap.congr_fun s.first_commute x
    · exact LinearMap.congr_fun s.second_commute x
  have h := finrank_range_split (p.first.prod p.second) s.domainProjection Q hQ hcomm
  have hproj : Q.comp (p.first.prod p.second) =
      (s.codomainProjection.comp p.first).prod (s.codomainProjection.comp p.second) := rfl
  have hrem : (LinearMap.id - Q).comp (p.first.prod p.second) =
      ((LinearMap.id - s.codomainProjection).comp p.first).prod
        ((LinearMap.id - s.codomainProjection).comp p.second) := rfl
  have hS := congrArg
    (fun L : p.domain →ₗ[ℂ] p.codomain × p.codomain => finrank ℂ (LinearMap.range L)) hproj
  have hW := congrArg
    (fun L : p.domain →ₗ[ℂ] p.codomain × p.codomain => finrank ℂ (LinearMap.range L)) hrem
  rw [hS, hW, s.projected_concatenation_ranks.2, s.remainder_concatenation_ranks.2] at h
  exact h

/-- The second chain arrow already spans the entire extracted target. -/
private theorem secondBlock_surjective : Function.Surjective s.secondBlock := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← s.targetBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact ⟨s.sourceBasis j.castSucc, s.second_basis_castSucc j⟩

theorem horizontal_rank : finrank ℂ ↥(LinearMap.range s.firstBlock ⊔
    LinearMap.range s.secondBlock) = r := by
  rw [LinearMap.range_eq_top.mpr s.secondBlock_surjective, sup_top_eq, finrank_top]
  simpa using Module.finrank_eq_card_basis s.targetBasis

private theorem first_coordinate (j : Fin r) :
    (s.targetBasis.coord j).comp s.firstBlock = s.sourceBasis.coord j.succ := by
  apply s.sourceBasis.ext
  intro k
  cases k using Fin.cases with
  | zero => simp [s.first_basis_zero]
  | succ k => simp [s.first_basis_succ, Finsupp.single_apply, eq_comm]

private theorem second_coordinate_zero (hr : 0 < r) :
    (s.targetBasis.coord ⟨0, hr⟩).comp s.secondBlock = s.sourceBasis.coord 0 := by
  apply s.sourceBasis.ext
  intro k
  cases k using Fin.lastCases with
  | last => simp [s.second_basis_last, Fin.ext_iff, Nat.ne_of_gt hr]
  | cast k => simp [s.second_basis_castSucc, Finsupp.single_apply, Fin.ext_iff]

/-- A positive-length chain has no common kernel inside its extracted source. -/
private theorem joint_injective (hr : 0 < r) :
    Function.Injective (s.firstBlock.prod s.secondBlock) := by
  intro x y h
  apply s.sourceBasis.repr.injective
  apply Finsupp.ext
  intro j
  cases j using Fin.cases with
  | zero =>
    have he := congrArg (s.targetBasis.coord ⟨0, hr⟩) (congrArg Prod.snd h)
    change ((s.targetBasis.coord ⟨0, hr⟩).comp s.secondBlock) x =
      ((s.targetBasis.coord ⟨0, hr⟩).comp s.secondBlock) y at he
    simpa only [s.second_coordinate_zero hr, Basis.coord_apply] using he
  | succ j =>
    have he := congrArg (s.targetBasis.coord j) (congrArg Prod.fst h)
    change ((s.targetBasis.coord j).comp s.firstBlock) x =
      ((s.targetBasis.coord j).comp s.firstBlock) y at he
    simpa only [s.first_coordinate j, Basis.coord_apply] using he

private theorem vertical_rank_of_pos (hr : 0 < r) :
    finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)) = r + 1 := by
  rw [LinearMap.finrank_range_of_inj (s.joint_injective hr)]
  simpa using Module.finrank_eq_card_basis s.sourceBasis

/-- A zero-index block is a common zero column and contributes no vertical
concatenation rank. -/
theorem vertical_rank : finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)) =
    if r = 0 then 0 else r + 1 := by
  by_cases hr : r = 0
  · subst r
    simp only [if_pos rfl]
    have ht : finrank ℂ s.target = 0 := by
      simpa using Module.finrank_eq_card_basis s.targetBasis
    apply Nat.eq_zero_of_le_zero
    calc
      _ ≤ finrank ℂ (s.target × s.target) := Submodule.finrank_le _
      _ = 0 := by simp [Module.finrank_prod, ht]
  · rw [if_neg hr]
    exact s.vertical_rank_of_pos (Nat.pos_of_ne_zero hr)

end Concatenation

variable {p q : Pencil ℂ} {r t : ℕ} (s : SplitData p r) (z : SplitData q t)

/-- Two extracted right chains have the standard exact tensor rank. -/
theorem tensor_rank : finrank ℂ (LinearMap.range
    (TensorProduct.map s.firstBlock z.firstBlock +
      TensorProduct.map s.secondBlock z.secondBlock)) = r * t := by
  rw [finrank_tensorSum_toMatrix s.sourceBasis s.targetBasis z.sourceBasis z.targetBasis,
    s.firstBlock_matrix, s.secondBlock_matrix, z.firstBlock_matrix, z.secondBlock_matrix]
  simpa only [tensorSum, add_comm] using right_right_rank r t

/-- Dualizing the first actual chain gives the mixed exact rank. -/
theorem partialTranspose_rank : finrank ℂ (LinearMap.range
    (TensorProduct.map s.firstBlock.dualMap z.firstBlock +
      TensorProduct.map s.secondBlock.dualMap z.secondBlock)) = r * t + min r t := by
  rw [finrank_tensorSum_toMatrix s.targetBasis.dualBasis s.sourceBasis.dualBasis
    z.sourceBasis z.targetBasis]
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def,
    LinearMap.toMatrix_transpose, LinearMap.toMatrix_transpose]
  rw [s.firstBlock_matrix, s.secondBlock_matrix, z.firstBlock_matrix, z.secondBlock_matrix]
  simpa only [partialTranspose, tensorSum, add_comm] using
    right_right_partialTranspose_rank r t

/-- A left chain in the second factor gives the opposite-orientation rank. -/
theorem mixed_tensor_rank : finrank ℂ (LinearMap.range
    (TensorProduct.map s.firstBlock z.firstBlock.dualMap +
      TensorProduct.map s.secondBlock z.secondBlock.dualMap)) = r * t + min r t := by
  rw [finrank_tensorSum_toMatrix s.sourceBasis s.targetBasis
    z.targetBasis.dualBasis z.sourceBasis.dualBasis]
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def,
    LinearMap.toMatrix_transpose, LinearMap.toMatrix_transpose,
    s.firstBlock_matrix, s.secondBlock_matrix, z.firstBlock_matrix, z.secondBlock_matrix]
  simpa only [tensorSum, add_comm] using right_left_rank r t

end ChainSplitting.FinitePair.SplitData

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation
