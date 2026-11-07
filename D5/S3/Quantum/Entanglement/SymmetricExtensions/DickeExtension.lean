/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unnormalized Dicke diagonal operators and Bose symmetric extension cones. -/

import D5.S3.QuantumStates.ZeroWeightSupportFace
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Actual tensor-factor extension predicates without trace normalization. -/

open scoped BigOperators ComplexOrder Kronecker
open Matrix
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumStates.ZeroWeightSupportFace

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

/-- The computational tensor basis split into the ordered sites `a,b` and their complement. -/
def edgeSplit (a b : I) (hab : a ≠ b) :
    (I → L) ≃ (L × L) × ({k : I // k ≠ a ∧ k ≠ b} → L) where
  toFun x := ((x a, x b), fun k => x k)
  invFun u k := if ha : k = a then u.1.1 else
    if hb : k = b then u.1.2 else u.2 ⟨k, ha, hb⟩
  left_inv x := by
    funext k
    dsimp
    split_ifs <;> simp_all
  right_inv u := by
    rcases u with ⟨⟨x,y⟩,z⟩
    apply Prod.ext
    · simp [Ne.symm hab]
    · funext k
      simp [k.property.1, k.property.2]

/-- The actual unnormalized partial trace over every site other than the ordered pair. -/
noncomputable def edgeMarginal (a b : I) (hab : a ≠ b)
    (E : Matrix (I → L) (I → L) ℂ) : Matrix (L × L) (L × L) ℂ :=
  partialTraceRight (E.submatrix (edgeSplit a b hab).symm (edgeSplit a b hab).symm)

/-- The standard two-particle Dicke vector; off-diagonal vectors have coefficient `1/√2`. -/
noncomputable def dickeVector {n : ℕ} (i j : Fin n) (x : Fin n × Fin n) : ℂ :=
  if i = j then (if x = (i,i) then 1 else 0) else
    (Real.sqrt 2 : ℂ)⁻¹ *
      ((if x = (i,j) then 1 else 0) + (if x = (j,i) then 1 else 0))

/-- The unnormalized cone coordinates, with only upper-triangular coefficients used. -/
noncomputable def dickeOperator {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ∑ i, ∑ j, if i ≤ j then
    (Y i j : ℂ) • Matrix.vecMulVec (dickeVector i j) (star (dickeVector i j)) else 0

/-- All nonempty proper standard-basis partial-transpose inequalities. -/
def FullyPPT (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  ∀ S : Finset I, S.Nonempty → S ≠ Finset.univ → (partialTransposeOn S E).PosSemidef

/-- The product projector onto the root factor times the symmetric leaf factors. -/
noncomputable def leafProjector (root : I) : Matrix (I → L) (I → L) ℂ :=
  Local.localP ({root} : Finset I)

/-- A star extension on the original tensor factors, with a genuine support sandwich. -/
def StarExtension (root : I) (ρ : Matrix (L × L) (L × L) ℂ)
    (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  E.PosSemidef ∧ leafProjector root * E * leafProjector root = E ∧
    (∀ i (hi : root ≠ i), edgeMarginal root i hi E = ρ) ∧ FullyPPT E

/-- A complete graph extension on the same factors, supported on the full Bose subspace. -/
def CompleteExtension (ρ : Matrix (L × L) (L × L) ℂ)
    (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  E.PosSemidef ∧ P I L * E * P I L = E ∧
    (∀ a b (hab : a ≠ b), edgeMarginal a b hab E = ρ) ∧ FullyPPT E

/-- A star extension with Bose leaf support and no partial-transpose requirement. -/
def StarExtensionCore (root : I) (ρ : Matrix (L × L) (L × L) ℂ)
    (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  E.PosSemidef ∧ leafProjector root * E * leafProjector root = E ∧
    ∀ i (hi : root ≠ i), edgeMarginal root i hi E = ρ

/-- A complete Bose extension with no partial-transpose requirement. -/
def CompleteExtensionCore (ρ : Matrix (L × L) (L × L) ℂ)
    (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  E.PosSemidef ∧ P I L * E * P I L = E ∧
    ∀ a b (hab : a ≠ b), edgeMarginal a b hab E = ρ

private lemma dicke_swap {n : ℕ} (i j : Fin n) (x : Fin n × Fin n) :
    dickeVector i j x.swap = dickeVector i j x := by
  rcases x with ⟨a,b⟩
  simp only [dickeVector, Prod.swap_prod_mk, Prod.mk.injEq]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    congr 1
    exact propext (and_comm)
  · simp only [hij, ite_false]
    congr 1
    simp only [and_comm]
    exact add_comm _ _

private lemma dicke_operator_swap {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (x y : Fin n × Fin n) :
    dickeOperator Y x.swap y = dickeOperator Y x y := by
  simp only [dickeOperator, Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.zero_apply, dicke_swap]

private noncomputable def edgeLift (a b : I) (hab : a ≠ b)
    (A : Matrix (L × L) (L × L) ℂ) : Matrix (I → L) (I → L) ℂ :=
  (A ⊗ₖ 1).submatrix (edgeSplit a b hab) (edgeSplit a b hab)

private lemma edge_trace_duality (a b : I) (hab : a ≠ b)
    (E : Matrix (I → L) (I → L) ℂ) (A : Matrix (L × L) (L × L) ℂ) :
    Matrix.trace (E * edgeLift a b hab A) =
      Matrix.trace (edgeMarginal a b hab E * A) := by
  classical
  let e := edgeSplit (L := L) a b hab
  change (∑ x, ∑ y, E x y * edgeLift a b hab A y x) = _
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp]
  change (∑ x, ∑ y, E (e.symm x) (e.symm y) *
    (A ⊗ₖ (1 : Matrix _ _ ℂ)) (e (e.symm y)) (e (e.symm x))) = _
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [edgeMarginal, partialTraceRight, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  exact Finset.sum_comm

private noncomputable def antiPair : Matrix (L × L) (L × L) ℂ :=
  (2 : ℂ)⁻¹ • (1 - Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L))

private lemma antiPair_projection :
    (antiPair (L := L))ᴴ = antiPair ∧ antiPair (L := L) * antiPair = antiPair := by
  let U : Matrix (L × L) (L × L) ℂ := Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L)
  have hs : (Equiv.prodComm L L : Equiv.Perm (L × L)) *
      Equiv.prodComm L L = 1 := by ext x <;> rfl
  have hi : (Equiv.prodComm L L : Equiv.Perm (L × L))⁻¹ =
      Equiv.prodComm L L := by ext x <;> rfl
  have hUU : U * U = 1 := by
    change (Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L)) * _ = _
    rw [← Matrix.permMatrix_mul, hs, Matrix.permMatrix_one]
  constructor
  · simp [antiPair, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hi]
  · change ((2 : ℂ)⁻¹ • (1-U)) * ((2 : ℂ)⁻¹ • (1-U)) =
      (2 : ℂ)⁻¹ • (1-U)
    simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, one_mul, mul_one, hUU]
    module

/-- The actual orthogonal projector onto the symmetric two-factor subspace.
It is `(1 + flip)/2` in the ordered product basis. -/
noncomputable def pairSymmetricProjector : Matrix (L × L) (L × L) ℂ :=
  1 - antiPair

private lemma antiPair_mul_pairSymmetricProjector :
    antiPair (L := L) * pairSymmetricProjector = 0 := by
  simp only [pairSymmetricProjector, mul_sub, mul_one,
    antiPair_projection.2, sub_self]

private lemma pair_anti_trace_of_supported (ρ : Matrix (L × L) (L × L) ℂ)
    (hρ : pairSymmetricProjector * ρ * pairSymmetricProjector = ρ) :
    Matrix.trace (ρ * antiPair) = 0 := by
  have hz : antiPair * ρ = 0 := by
    calc
      antiPair * ρ = antiPair * (pairSymmetricProjector * ρ * pairSymmetricProjector) := by
        rw [hρ]
      _ = 0 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, antiPair_mul_pairSymmetricProjector]
        simp
  rw [Matrix.trace_mul_comm, hz, Matrix.trace_zero]

private lemma dicke_operator_flip_left {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin n) (Fin n)) * dickeOperator Y =
      dickeOperator Y := by
  apply Matrix.ext
  intro x y
  change ((Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin n) (Fin n))) *ᵥ
    (fun z => dickeOperator Y z y)) x = _
  rw [Matrix.permMatrix_mulVec]
  exact dicke_operator_swap Y x y

private lemma dicke_operator_flip_right {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    dickeOperator Y * Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin n) (Fin n)) =
      dickeOperator Y := by
  ext x y
  change ((fun z => dickeOperator Y x z) ᵥ*
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin n) (Fin n))) y = _
  rw [Matrix.vecMul_permMatrix]
  change dickeOperator Y x y.swap = dickeOperator Y x y
  simp only [dickeOperator, Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.zero_apply, Pi.star_apply, dicke_swap]

private lemma dicke_anti_trace {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    Matrix.trace (dickeOperator Y * antiPair) = 0 := by
  rw [Matrix.trace_mul_comm]
  simp only [antiPair, smul_mul, sub_mul, one_mul, dicke_operator_flip_left, sub_self,
    smul_zero, Matrix.trace_zero]

private lemma dicke_pair_supported {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    pairSymmetricProjector * dickeOperator Y * pairSymmetricProjector = dickeOperator Y := by
  have hl : antiPair * dickeOperator Y = 0 := by
    simp only [antiPair, smul_mul, sub_mul, one_mul, dicke_operator_flip_left,
      sub_self, smul_zero]
  have hr : dickeOperator Y * antiPair = 0 := by
    simp only [antiPair, Matrix.mul_smul, mul_sub, mul_one, dicke_operator_flip_right,
      sub_self, smul_zero]
  simp only [pairSymmetricProjector, sub_mul, one_mul, mul_sub, mul_one, hl, hr,
    sub_zero]

private lemma edgeLift_projection (a b : I) (hab : a ≠ b) :
    (edgeLift a b hab (antiPair (L := L)))ᴴ = edgeLift a b hab antiPair ∧
      edgeLift a b hab (antiPair (L := L)) * edgeLift a b hab antiPair =
        edgeLift a b hab antiPair := by
  constructor
  · simp only [edgeLift, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, antiPair_projection.1]
  · simp only [edgeLift]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul,
      antiPair_projection.2, Matrix.one_mul]


omit [Fintype I] [Fintype L] [DecidableEq L] in
private lemma edge_split_swap (a b : I) (hab : a ≠ b) (x : I → L) :
    (edgeSplit a b hab).symm (((x a,x b).swap), fun k => x k) =
      x ∘ Equiv.swap a b := by
  funext k
  by_cases ha : k = a
  · subst k
    simp [edgeSplit]
  · by_cases hb : k = b
    · subst k
      simp [edgeSplit, Ne.symm hab]
    · simp [edgeSplit, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]

private lemma edgeLift_anti_mul (a b : I) (hab : a ≠ b)
    (E : Matrix (I → L) (I → L) ℂ) (x y : I → L) :
    ((edgeLift a b hab (antiPair (L := L))) * E) x y =
      (2 : ℂ)⁻¹ * (E x y - E (x ∘ Equiv.swap a b) y) := by
  classical
  let e := edgeSplit (L := L) a b hab
  change (((antiPair ⊗ₖ 1).submatrix e e) *ᵥ (fun z => E z y)) x = _
  rw [Matrix.submatrix_mulVec_equiv]
  have hk (u : L × L) (c : {k : I // k ≠ a ∧ k ≠ b} → L) :
      ((antiPair ⊗ₖ (1 : Matrix _ _ ℂ)) *ᵥ
        ((fun z => E z y) ∘ e.symm)) (u,c) =
      (antiPair *ᵥ (fun v : L × L => E (e.symm (v,c)) y)) u := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kronecker_apply, Matrix.one_apply, Function.comp_apply]
    simp
  change ((antiPair ⊗ₖ 1) *ᵥ ((fun z => E z y) ∘ e.symm)) (e x) = _
  rw [hk (e x).1 (e x).2]
  rw [antiPair, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.permMatrix_mulVec]
  change (2 : ℂ)⁻¹ * (E (e.symm (e x)) y -
    E (e.symm (((x a,x b).swap), fun k => x k)) y) = _
  rw [Equiv.symm_apply_apply, edge_split_swap]

private lemma edge_swap_fixed_of_zero_anti_weight (a b : I) (hab : a ≠ b)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hm : Matrix.trace (edgeMarginal a b hab E * antiPair) = 0) :
    ∀ x y, E (x ∘ Equiv.swap a b) y = E x y := by
  have ht : Matrix.trace (E * edgeLift a b hab antiPair) = 0 := by
    rw [edge_trace_duality, hm]
  have hzero := (zero_weight_support_face E (edgeLift a b hab antiPair)
    hE (edgeLift_projection a b hab).1 (edgeLift_projection a b hab).2 ht).1.1
  intro x y
  have h := congrArg (fun M => M x y) hzero
  rw [edgeLift_anti_mul, Matrix.zero_apply] at h
  have hd : E x y - E (x ∘ Equiv.swap a b) y = 0 :=
    (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))
  exact (sub_eq_zero.mp hd).symm

private lemma edge_swap_fixed {n : ℕ} (a b : I) (hab : a ≠ b)
    (Y : Fin n → Fin n → ℝ)
    (E : Matrix (I → Fin n) (I → Fin n) ℂ)
    (hE : E.PosSemidef) (hm : edgeMarginal a b hab E = dickeOperator Y) :
    ∀ x y, E (x ∘ Equiv.swap a b) y = E x y :=
  edge_swap_fixed_of_zero_anti_weight a b hab E hE (by rw [hm, dicke_anti_trace])

private lemma symmetric_of_star_swaps (root : I) (v : (I → L) → ℂ)
    (hv : ∀ i, root ≠ i → ∀ x, v (x ∘ Equiv.swap root i) = v x) :
    IsSymmetricVector v := by
  have hswap (a b : I) (x : I → L) : v (x ∘ Equiv.swap a b) = v x := by
    by_cases ha : a = root
    · subst a
      by_cases hb : root = b
      · subst b
        simp
      · exact hv b hb x
    by_cases hb : b = root
    · subst b
      rw [Equiv.swap_comm]
      exact hv a (Ne.symm ha) x
    by_cases hab : a = b
    · subst b
      simp
    have hs : Equiv.swap root a * Equiv.swap root b * Equiv.swap root a =
        Equiv.swap a b := by
      rw [Equiv.swap_comm root b]
      exact Equiv.swap_mul_swap_mul_swap hb (Ne.symm hab)
    rw [← hs]
    change v (((x ∘ Equiv.swap root a) ∘ Equiv.swap root b) ∘
      Equiv.swap root a) = v x
    rw [hv a (Ne.symm ha), hv b (Ne.symm hb), hv a (Ne.symm ha)]
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro x; rfl
  | swap_mul σ a b hab ih =>
      intro x
      change v ((x ∘ Equiv.swap a b) ∘ σ) = v x
      rw [ih, hswap]

private lemma support_of_columns (E : Matrix (I → L) (I → L) ℂ)
    (hE : E.IsHermitian) (hcol : ∀ y, IsSymmetricVector (fun x => E x y)) :
    P I L * E * P I L = E := by
  have hl : P I L * E = E := by
    ext x y
    exact congrFun (P_mulVec_of_symmetric (fun z => E z y) (hcol y)) x
  have hr : E * P I L = E := by
    have h := congrArg Matrix.conjTranspose hl
    simpa only [Matrix.conjTranspose_mul, hE.eq, (P_hermitian I L).eq] using h
  rw [hl, hr]

private lemma edge_covariance_of_conjugation (E : Matrix (I → L) (I → L) ℂ)
    (σ : Equiv.Perm I) (a b : I) (hab : a ≠ b) :
    (∀ x y, E (x ∘ σ) (y ∘ σ) = E x y) →
      edgeMarginal (σ a) (σ b) (σ.injective.ne hab) E = edgeMarginal a b hab E := by
  intro hinv
  classical
  let eR : {k : I // k ≠ a ∧ k ≠ b} ≃
      {k : I // k ≠ σ a ∧ k ≠ σ b} :=
    σ.subtypeEquiv (fun k => by simp only [σ.injective.ne_iff])
  let eC := Equiv.arrowCongr eR (Equiv.refl L)
  have hf (u : L × L) (c : {k : I // k ≠ a ∧ k ≠ b} → L) :
      (edgeSplit (σ a) (σ b) (σ.injective.ne hab)).symm (u,eC c) ∘ σ =
        (edgeSplit a b hab).symm (u,c) := by
    funext k
    by_cases ha : k = a
    · subst k
      simp [edgeSplit]
    by_cases hb : k = b
    · subst k
      simp [edgeSplit, Ne.symm hab]
    simp [edgeSplit, Function.comp_def, ha, hb, eC, eR, Equiv.subtypeEquiv,
      Equiv.arrowCongr, Equiv.refl]
  ext u v
  simp only [edgeMarginal, partialTraceRight, Matrix.submatrix_apply]
  rw [← eC.sum_comp]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← hinv, hf, hf]

private lemma edge_covariance (E : Matrix (I → L) (I → L) ℂ)
    (hE : E.IsHermitian) (hcol : ∀ y, IsSymmetricVector (fun x => E x y))
    (σ : Equiv.Perm I) (a b : I) (hab : a ≠ b) :
    edgeMarginal (σ a) (σ b) (σ.injective.ne hab) E = edgeMarginal a b hab E := by
  apply edge_covariance_of_conjugation E σ a b hab
  intro x y
  calc
    E (x ∘ σ) (y ∘ σ) = E x (y ∘ σ) := hcol (y ∘ σ) σ x
    _ = star (E (y ∘ σ) x) := (hE.apply x (y ∘ σ)).symm
    _ = star (E y x) := congrArg star (hcol x σ y)
    _ = E x y := hE.apply x y

private lemma all_edges_equal (E : Matrix (I → L) (I → L) ℂ)
    (hE : E.IsHermitian) (hcol : ∀ y, IsSymmetricVector (fun x => E x y))
    (u v a b : I) (huv : u ≠ v) (hab : a ≠ b) :
    edgeMarginal a b hab E = edgeMarginal u v huv E := by
  let f : Bool → I := fun t => if t then v else u
  let g : Bool → I := fun t => if t then b else a
  have hf : Function.Injective f := by
    intro x y h
    cases x <;> cases y <;> simp_all [f]
  have hg : Function.Injective g := by
    intro x y h
    cases x <;> cases y <;> simp_all [g]
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have h0 : σ u = a := hσ false
  have h1 : σ v = b := hσ true
  subst a
  subst b
  exact edge_covariance E hE hcol σ u v huv

/-- Permutations acting trivially on each actual column of an operator. -/
private def columnStabilizer (E : Matrix (I → L) (I → L) ℂ) :
    Subgroup (Equiv.Perm I) where
  carrier := {sigma | ∀ x y, E (x ∘ sigma) y = E x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro sigma tau hs ht x y
    change E ((x ∘ sigma) ∘ tau) y = E x y
    rw [ht, hs]
  inv_mem' := by
    intro σ hs x y
    have h := hs (x ∘ (σ⁻¹ : Equiv.Perm I)) y
    simpa only [Function.comp_assoc, Equiv.Perm.inv_def,
      Equiv.symm_comp_self, Function.comp_id] using h.symm

private lemma columns_fixed_of_reachable (G : SimpleGraph I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hsupport : ∀ a b (h : G.Adj a b),
      pairSymmetricProjector * edgeMarginal a b h.ne E * pairSymmetricProjector =
        edgeMarginal a b h.ne E)
    {a b : I} (hpath : G.Reachable a b) :
    Equiv.swap a b ∈ columnStabilizer E := by
  obtain ⟨p⟩ := hpath
  induction p with
  | nil => intro x y; simp
  | @cons a b c hab p ih =>
      apply SubmonoidClass.swap_mem_trans (columnStabilizer E) _ ih
      exact edge_swap_fixed_of_zero_anti_weight a b hab.ne E hE
        (pair_anti_trace_of_supported _ (hsupport a b hab))

/-- A connected graph of Bose-supported marginals forces full Bose support.
The equality concerns every ordered pair, including reversed pairs. -/
theorem support_of_connected_graph (G : SimpleGraph I) (hG : G.Connected)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hsupport : ∀ a b (h : G.Adj a b),
      pairSymmetricProjector * edgeMarginal a b h.ne E * pairSymmetricProjector =
        edgeMarginal a b h.ne E) :
    P I L * E * P I L = E ∧
      ∀ u v a b (huv : u ≠ v) (hab : a ≠ b),
        edgeMarginal a b hab E = edgeMarginal u v huv E := by
  letI : Nonempty I := hG.nonempty
  let root : I := Classical.arbitrary I
  have hcol : ∀ y, IsSymmetricVector (fun x => E x y) := by
    intro y
    apply symmetric_of_star_swaps root
    intro i hi x
    exact columns_fixed_of_reachable G E hE hsupport (hG.preconnected root i) x y
  exact ⟨support_of_columns E hE.isHermitian hcol,
    all_edges_equal E hE.isHermitian hcol⟩

#print axioms support_of_connected_graph


/-- Register permutations preserving every connected component, including singleton components. -/
def componentGroup (G : SimpleGraph I) : Subgroup (Equiv.Perm I) where
  carrier := {σ | ∀ i, G.Reachable i (σ i)}
  one_mem' := fun i => SimpleGraph.Reachable.refl i
  mul_mem' := by
    intro σ τ hσ hτ i
    exact (hτ i).trans (hσ (τ i))
  inv_mem' := by
    intro σ hσ i
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hσ (σ⁻¹ i)).symm

private lemma component_swap_mem (G : SimpleGraph I) {a b : I}
    (h : G.Reachable a b) : Equiv.swap a b ∈ componentGroup G := by
  intro i
  by_cases ha : i = a
  · subst i
    simpa only [Equiv.swap_apply_left] using h
  by_cases hb : i = b
  · subst i
    simpa only [Equiv.swap_apply_right] using h.symm
  simpa only [Equiv.swap_apply_of_ne_of_ne ha hb] using SimpleGraph.Reachable.refl i

private lemma component_group_le_columns (G : SimpleGraph I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hsupport : ∀ a b (h : G.Adj a b),
      pairSymmetricProjector * edgeMarginal a b h.ne E * pairSymmetricProjector =
        edgeMarginal a b h.ne E) :
    componentGroup G ≤ columnStabilizer E := by
  classical
  let S : Set (Equiv.Perm I) := {σ | ∃ a b, a ≠ b ∧ G.Reachable a b ∧ σ = Equiv.swap a b}
  have hS : ∀ σ ∈ S, σ.IsSwap := by
    rintro σ ⟨a,b,hab,_,rfl⟩
    exact ⟨a,b,hab,rfl⟩
  have hcl : Subgroup.closure S ≤ columnStabilizer E := by
    apply (Subgroup.closure_le (columnStabilizer E)).mpr
    rintro σ ⟨a,b,_,hr,rfl⟩
    exact columns_fixed_of_reachable G E hE hsupport hr
  intro σ hσ
  apply hcl
  apply (mem_closure_isSwap hS).mpr
  refine ⟨Set.toFinite _, fun x => ?_⟩
  by_cases hx : x = σ x
  · rw [← hx]
    exact MulAction.mem_orbit_self x
  · exact ⟨⟨Equiv.swap x (σ x), Subgroup.subset_closure ⟨x,σ x,hx,hσ x,rfl⟩⟩,
      Equiv.swap_apply_left x (σ x)⟩

open private Q_mulVec Q_mul Q_one Q_star
  Average.expect_formula Average.avg_left Average.avg_idempotent Average.avg_hermitian from
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor

private noncomputable def componentRepresentation (G : SimpleGraph I) :
    componentGroup G →* Matrix (I → L) (I → L) ℂ where
  toFun σ := Q σ.val
  map_one' := Q_one
  map_mul' σ τ := Q_mul σ.val τ.val

/-- The actual permutation average on each connected component. Its tensor-product
factorization is given separately; isolated registers contribute their identity factors. -/
noncomputable def componentProjector (G : SimpleGraph I) :
    Matrix (I → L) (I → L) ℂ := by
  classical
  exact Finset.expect Finset.univ (componentRepresentation (L := L) G)

private lemma component_projector_hermitian (G : SimpleGraph I) :
    (componentProjector (L := L) G).IsHermitian := by
  classical
  exact Average.avg_hermitian (componentRepresentation G) (fun σ => Q_star σ.val)

private lemma component_projector_fix (G : SimpleGraph I) (σ : componentGroup G) :
    Q σ.val * componentProjector (L := L) G = componentProjector G := by
  classical
  exact Average.avg_left (componentRepresentation G) σ

private lemma component_projector_mul_of_columns (G : SimpleGraph I)
    (E : Matrix (I → L) (I → L) ℂ)
    (hc : componentGroup G ≤ columnStabilizer E) : componentProjector G * E = E := by
  classical
  have hcard : (Fintype.card (componentGroup G) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hf (σ : componentGroup G) : Q σ.val * E = E := by
    ext x y
    exact congrFun (Q_mulVec σ.val (fun z => E z y)) x |>.trans (hc σ.property x y)
  simp only [componentProjector, Average.expect_formula, Matrix.smul_mul, Matrix.sum_mul,
    componentRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, hf, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Edge Bose support forces support on the component permutation average.
No connectedness assumption is made, and no register is discarded. -/
theorem component_support_of_edges (G : SimpleGraph I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hsupport : ∀ a b (h : G.Adj a b),
      pairSymmetricProjector * edgeMarginal a b h.ne E * pairSymmetricProjector =
        edgeMarginal a b h.ne E) :
    componentProjector G * E * componentProjector G = E := by
  have hl := component_projector_mul_of_columns G E
    (component_group_le_columns G E hE hsupport)
  have hr := congrArg Matrix.conjTranspose hl
  simp only [Matrix.conjTranspose_mul, hE.isHermitian.eq,
    (component_projector_hermitian G).eq] at hr
  rw [hl, hr]

#print axioms component_support_of_edges


private lemma pair_support_of_column_swap (a b : I) (hab : a ≠ b)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hfix : ∀ x y, E (x ∘ Equiv.swap a b) y = E x y) :
    pairSymmetricProjector * edgeMarginal a b hab E * pairSymmetricProjector =
      edgeMarginal a b hab E := by
  let e := edgeSplit (L := L) a b hab
  let ρ := edgeMarginal a b hab E
  have hρ : ρ.IsHermitian :=
    (partialTraceRight_posSemidef (hE.submatrix e.symm)).isHermitian
  have hs (x : I → L) : e.symm ((e x).1.swap, (e x).2) = x ∘ Equiv.swap a b :=
    edge_split_swap a b hab x
  have hm (u v : L × L) : ρ u.swap v = ρ u v := by
    change (∑ c, E (e.symm (u.swap,c)) (e.symm (v,c))) =
      ∑ c, E (e.symm (u,c)) (e.symm (v,c))
    apply Finset.sum_congr rfl
    intro c hc
    have hc' := hs (e.symm (u,c))
    simp only [e.apply_symm_apply] at hc'
    rw [hc', hfix]
  have hf : Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L) * ρ = ρ := by
    ext u v
    change (Equiv.Perm.permMatrix ℂ (Equiv.prodComm L L) *ᵥ (fun z => ρ z v)) u = _
    rw [Matrix.permMatrix_mulVec]
    exact hm u v
  have hl : antiPair * ρ = 0 := by
    simp only [antiPair, smul_mul, sub_mul, one_mul, hf, sub_self, smul_zero]
  have hr := congrArg Matrix.conjTranspose hl
  simp only [Matrix.conjTranspose_mul, hρ.eq, antiPair_projection.1,
    Matrix.conjTranspose_zero] at hr
  change (1 - antiPair) * ρ * (1 - antiPair) = ρ
  simp only [sub_mul, one_mul, mul_sub, mul_one, hl, hr,
    sub_zero]

/-- Exact support characterization for arbitrary graphs. The component projector
retains isolated singleton registers and allows correlations between components. -/
theorem edges_iff_component_support (G : SimpleGraph I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef) :
    (∀ a b (h : G.Adj a b),
      pairSymmetricProjector * edgeMarginal a b h.ne E * pairSymmetricProjector =
        edgeMarginal a b h.ne E) ↔
      componentProjector G * E * componentProjector G = E := by
  constructor
  · exact component_support_of_edges G E hE
  · intro hsupport a b hab
    have hg : Equiv.swap a b ∈ componentGroup G := component_swap_mem G hab.reachable
    have hp := component_projector_fix (L := L) G ⟨Equiv.swap a b,hg⟩
    have hf : Q (Equiv.swap a b) * E = E := by
      calc
        Q (Equiv.swap a b) * E = Q (Equiv.swap a b) *
            (componentProjector G * E * componentProjector G) := by rw [hsupport]
        _ = componentProjector G * E * componentProjector G := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hp]
        _ = E := hsupport
    apply pair_support_of_column_swap a b hab.ne E hE
    intro x y
    have hx := congrArg (fun M => M x y) hf
    have hq := congrFun (Q_mulVec (Equiv.swap a b) (fun z => E z y)) x
    exact hq.symm.trans hx

#print axioms edges_iff_component_support

/-- Bose-supported root marginals force global Bose support and all ordered marginals.
No leaf support, normalization, invertibility or partial-transpose premise is used. -/
theorem support_of_bose_root_marginals (root : I)
    (ρ : Matrix (L × L) (L × L) ℂ)
    (hρ : pairSymmetricProjector * ρ * pairSymmetricProjector = ρ)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hm : ∀ i (hi : root ≠ i), edgeMarginal root i hi E = ρ) :
    P I L * E * P I L = E ∧
      ∀ a b (hab : a ≠ b), edgeMarginal a b hab E = ρ := by
  have hcol : ∀ y, IsSymmetricVector (fun x => E x y) := by
    intro y
    apply symmetric_of_star_swaps root
    intro i hi x
    apply edge_swap_fixed_of_zero_anti_weight root i hi E hE _ x y
    rw [hm i hi]
    exact pair_anti_trace_of_supported ρ hρ
  refine ⟨support_of_columns E hE.isHermitian hcol, ?_⟩
  intro a b hab
  by_cases ha : root = a
  · subst a
    exact hm b hab
  · rw [all_edges_equal E hE.isHermitian hcol root a a b ha hab]
    exact hm a ha

theorem same_matrix_core (root : I)
    (ρ : Matrix (L × L) (L × L) ℂ)
    (hρ : pairSymmetricProjector * ρ * pairSymmetricProjector = ρ)
    (E : Matrix (I → L) (I → L) ℂ) :
    StarExtensionCore root ρ E ↔ CompleteExtensionCore ρ E := by
  constructor
  · rintro ⟨hE, _, hm⟩
    exact ⟨hE, support_of_bose_root_marginals root ρ hρ E hE hm⟩
  · rintro ⟨hE, hsym, hm⟩
    refine ⟨hE, ?_, fun i hi => hm root i hi⟩
    let PL := leafProjector (L := L) root
    have hlp : PL * P I L = P I L := PiS_mul_P ({root} : Finset I)
    have hplh : PLᴴ = PL := PiS_hermitian (L := L) ({root} : Finset I)
    have hpr : P I L * PL = P I L := by
      have h := congrArg Matrix.conjTranspose hlp
      simpa only [Matrix.conjTranspose_mul, (P_hermitian I L).eq, hplh] using h
    change PL * E * PL = E
    calc
      PL * E * PL = PL * (P I L * E * P I L) * PL := by rw [hsym]
      _ = P I L * E * P I L := by
        simp only [← Matrix.mul_assoc, hlp]
        rw [Matrix.mul_assoc (P I L * E), hpr]
      _ = E := hsym

/-- The same individual-matrix equality with every fully PPT condition retained. -/
theorem same_matrix (root : I)
    (ρ : Matrix (L × L) (L × L) ℂ)
    (hρ : pairSymmetricProjector * ρ * pairSymmetricProjector = ρ)
    (E : Matrix (I → L) (I → L) ℂ) :
    StarExtension root ρ E ↔ CompleteExtension ρ E := by
  constructor
  · rintro ⟨hE, hleaf, hm, hppt⟩
    obtain ⟨hE, hsym, hm⟩ := (same_matrix_core root ρ hρ E).mp ⟨hE, hleaf, hm⟩
    exact ⟨hE, hsym, hm, hppt⟩
  · rintro ⟨hE, hsym, hm, hppt⟩
    obtain ⟨hE, hleaf, hm⟩ := (same_matrix_core root ρ hρ E).mpr ⟨hE, hsym, hm⟩
    exact ⟨hE, hleaf, hm, hppt⟩

#print axioms support_of_bose_root_marginals
#print axioms same_matrix_core
#print axioms same_matrix

/-- The unchanged unnormalized all-register Dicke cone-equivalence event. -/
theorem result (n r : ℕ) (_hn : 1 ≤ n) (hr : 2 ≤ r)
    (Y : Fin n → Fin n → ℝ) (_hY : ∀ i j, i ≤ j → 0 ≤ Y i j) :
    (∃ E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ,
      StarExtension (⟨0, by omega⟩ : Fin r) (dickeOperator Y) E) ↔
    (∃ E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ,
      CompleteExtension (dickeOperator Y) E) := by
  let root : Fin r := ⟨0,by omega⟩
  let leaf : Fin r := ⟨1,by omega⟩
  have hrl : root ≠ leaf := by
    intro h
    have := congrArg Fin.val h
    simp [root,leaf] at this
  constructor
  · rintro ⟨E,hE,hleaf,hm,hppt⟩
    have hcol : ∀ y, IsSymmetricVector (fun x => E x y) := by
      intro y
      apply symmetric_of_star_swaps root
      intro i hi x
      exact edge_swap_fixed root i hi Y E hE (hm i hi) x y
    refine ⟨E,hE,support_of_columns E hE.isHermitian hcol,?_,hppt⟩
    intro a b hab
    rw [all_edges_equal E hE.isHermitian hcol root leaf a b hrl hab]
    exact hm leaf hrl
  · rintro ⟨E,hE⟩
    exact ⟨E, (same_matrix root (dickeOperator Y) (dicke_pair_supported Y) E).mpr hE⟩

#print axioms result


end D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
