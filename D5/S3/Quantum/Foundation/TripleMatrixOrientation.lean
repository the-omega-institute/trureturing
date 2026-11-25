/- GID: D5/S3/Quantum/Foundation/TripleMatrixOrientation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TripleMatrixOrientation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole-cone pair positivity forces one transpose orientation on the actual triple. -/

import D5.S3.Quantum.Foundation.PositiveMarginalMatrixComposition
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtBell
import D5.S3.Quantum.Information.PartialTraceMutualInformation

/-!
# Orientation of an actual single-sector matrix triple

This formalizes the single-sector deductions in (29)–(35) of
`Library/QuantumStates/barnumhilgert2019spectral.md`.
The two normalized unitary tensor forms are explicit hypotheses. Their
external source is Xu–Zheng–Fošner, *Linear maps preserving tensor products
of rank-one Hermitian matrices*, Main Theorem, p. 409, (1.1)–(1.2), and
Proposition 2.1, pp. 410–411, for a single factor of dimension at least two.
See <https://doi.org/10.1017/S1446788714000603>.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace PositiveMarginalMatrixComposition.TripleOrientation

variable {m n d : ℕ}

abbrev CMat (I : Type*) := Matrix I I ℂ

/-- Pack a product matrix into the usual `Fin (m * n)` coordinates. -/
def pack (X : CMat (Fin m × Fin n)) : Mat (m * n) :=
  X.submatrix finProdFinEquiv.symm finProdFinEquiv.symm

def unpack (X : Mat (m * n)) : CMat (Fin m × Fin n) :=
  X.submatrix finProdFinEquiv finProdFinEquiv

@[simp] theorem unpack_pack (X : CMat (Fin m × Fin n)) : unpack (pack X) = X := by
  ext i j
  simp [pack, unpack]

@[simp] theorem pack_unpack (X : Mat (m * n)) : pack (unpack X) = X := by
  ext i j
  change X (finProdFinEquiv (finProdFinEquiv.symm i))
    (finProdFinEquiv (finProdFinEquiv.symm j)) = X i j
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def transposeIf {I : Type*} (b : Bool) (X : CMat I) : CMat I :=
  if b then Xᵀ else X

@[simp] theorem transposeIf_xor {I : Type*} (b c : Bool) (X : CMat I) :
    transposeIf b (transposeIf c X) = transposeIf (b ^^ c) X := by
  cases b <;> cases c <;> rfl

@[simp] theorem trace_transposeIf {I : Type*} [Fintype I] (b : Bool) (X : CMat I) :
    (transposeIf b X).trace = X.trace := by
  cases b <;> simp [transposeIf]

theorem transposeIf_kronecker {I J : Type*} (b : Bool) (X : CMat I) (Y : CMat J) :
    transposeIf b (X ⊗ₖ Y) = transposeIf b X ⊗ₖ transposeIf b Y := by
  cases b <;> rfl

theorem transposeIf_pack (b : Bool) (X : CMat (Fin m × Fin n)) :
    transposeIf b (pack X) = pack (transposeIf b X) := by
  cases b <;> rfl

theorem transposeIf_psd {I : Type*} {X : CMat I} (b : Bool) :
    (transposeIf b X).PosSemidef ↔ X.PosSemidef := by
  cases b
  · rfl
  · exact Matrix.posSemidef_transpose_iff

/-- Unitary conjugation, used on the actual output carriers. -/
def adj {I : Type*} [Fintype I] [DecidableEq I] (U : ↥(unitary (CMat I))) :
    CMat I ≃⋆ₐ[ℂ] CMat I :=
  Unitary.conjStarAlgAut ℂ (CMat I) U

theorem adj_herm {I : Type*} [Fintype I] [DecidableEq I] (U : ↥(unitary (CMat I)))
    {X : CMat I} (hx : X.IsHermitian) : (adj U X).IsHermitian := by
  change star (adj U X) = adj U X
  rw [← map_star, Matrix.star_eq_conjTranspose, hx.eq]

theorem adj_psd {I : Type*} [Fintype I] [DecidableEq I] (U : ↥(unitary (CMat I)))
    {X : CMat I} : (adj U X).PosSemidef ↔ X.PosSemidef :=
  (Unitary.isUnit_coe (U := U)).posSemidef_star_right_conjugate_iff

@[simp] theorem adj_trace {I : Type*} [Fintype I] [DecidableEq I]
    (U : ↥(unitary (CMat I))) (X : CMat I) : (adj U X).trace = X.trace := by
  change ((U.val * X) * star U.val).trace = _
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

def adjH (U : ↥(unitary (Mat n))) : H n ≃ₗ[ℝ] H n where
  toFun x := ⟨adj U x.val, adj_herm U x.property⟩
  invFun x := ⟨adj (star U) x.val, adj_herm (star U) x.property⟩
  left_inv x := Subtype.ext (by
    change adj (star U) (adj U x.val) = x.val
    unfold adj
    rw [← Unitary.conjStarAlgAut_symm]
    exact (adj U).symm_apply_apply _)
  right_inv x := Subtype.ext (by
    change adj U (adj (star U) x.val) = x.val
    unfold adj
    rw [← Unitary.conjStarAlgAut_symm]
    exact (adj U).apply_symm_apply _)
  map_add' x y := Subtype.ext (map_add (adj U) x.val y.val)
  map_smul' c x :=
    Subtype.ext (((adj U).toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul c x.val)

@[simp] theorem val_adjH (U : ↥(unitary (Mat n))) (x : H n) :
    (adjH U x).val = adj U x.val := rfl

def transposeH (b : Bool) : H n ≃ₗ[ℝ] H n where
  toFun x := ⟨transposeIf b x.val, by
    cases b
    · exact x.property
    · exact Matrix.IsHermitian.transpose x.property⟩
  invFun x := ⟨transposeIf b x.val, by
    cases b
    · exact x.property
    · exact Matrix.IsHermitian.transpose x.property⟩
  left_inv x := Subtype.ext (by cases b <;> rfl)
  right_inv x := Subtype.ext (by cases b <;> rfl)
  map_add' x y := Subtype.ext (by cases b <;> rfl)
  map_smul' c x := Subtype.ext (by cases b <;> rfl)

@[simp] theorem val_transposeH (b : Bool) (x : H n) :
    (transposeH b x).val = transposeIf b x.val := rfl

private theorem herm (x : H n) : x.val.IsHermitian := x.property

def tensor (x : H m) (y : H n) : H (m * n) :=
  ⟨pack (x.val ⊗ₖ y.val), (show (x.val ⊗ₖ y.val).IsHermitian by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (herm x).eq, (herm y).eq]
  ).submatrix _⟩

theorem tensor_psd {x : H m} {y : H n} (hx : x.val.PosSemidef) (hy : y.val.PosSemidef) :
    (tensor x y).val.PosSemidef :=
  (hx.kronecker hy).submatrix _

/-- Exact signed tensor form of one actual preparation. -/
def TensorNormalForm (M : H m →ₗ[ℝ] H n →ₗ[ℝ] H (m * n))
    (U : ↥(unitary (Mat (m * n)))) (b c : Bool) : Prop :=
  ∀ x y, M x y = adjH U (tensor (transposeH b x) (transposeH c y))

theorem eq_of_products {a b k : ℕ} {F : H a →ₗ[ℝ] H b →ₗ[ℝ] H k}
    (hF : Spans F) {G : H k →ₗ[ℝ] H d} (h : ∀ x y, G (F x y) = 0) : G = 0 := by
  apply (LinearMap.cancel_right (lift_surjective hF)).mp
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.comp_apply, TensorProduct.lift.tmul, LinearMap.zero_apply] using h x y

open D5.S3.Quantum.Entanglement.AbsolutePPT
open UniformSchmidtBell UniformSchmidtIncidence
open D5.S3.Quantum.Information.PartialTraceMutualInformation

private theorem bell_obstruction (hn : 2 ≤ n) :
    ∃ X : CMat (Fin n × Fin n), X.PosSemidef ∧
      ¬ (Bipartite.partialTranspose X).PosSemidef := by
  let U := bellUnitary n
  let D := Matrix.diagonal (UniformSchmidtBell.pack (fun _ : Edge n => 1) (fun _ => 0))
  refine ⟨adj U D, (adj_psd U).mpr (Matrix.posSemidef_diagonal_iff.mpr ?_), ?_⟩
  · intro i
    unfold UniformSchmidtBell.pack
    rcases (bellEquiv n).symm i with (e | e) | i <;> norm_num
  · intro hp
    have hc := hp.submatrix (fun i : Fin n => (i,i))
    change ((Bipartite.partialTranspose (U.val * D * U.valᴴ)).submatrix
      (fun i => (i,i)) (fun i => (i,i))).PosSemidef at hc
    have he := bell_pt_principal (fun _ : Edge n => 1) (fun _ => 0)
    change ((Bipartite.partialTranspose (U.val * D * U.valᴴ)).submatrix
      (fun i => (i,i)) (fun i => (i,i))) = _ at he
    rw [he] at hc
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
    let f : Fin 2 → Fin n := ![i,j]
    have hq := (hc.submatrix f).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
    norm_num [f, K, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hij, Ne.symm hij] at hq

/-- The whole pair matrix with the indicated factors transposed. -/
def pairMask (b c : Bool) (X : CMat (Fin m × Fin n)) : CMat (Fin m × Fin n) :=
  fun i j => X (if b then j.1 else i.1, if c then j.2 else i.2)
               (if b then i.1 else j.1, if c then i.2 else j.2)

def pairMaskH (b c : Bool) : H (m * n) →ₗ[ℝ] H (m * n) where
  toFun x := ⟨pack (pairMask b c (unpack x.val)),
    (Matrix.IsHermitian.ext fun _i _j => (herm x).apply _ _).submatrix _⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem val_pairMaskH (b c : Bool) (x : H (m * n)) :
    (pairMaskH b c x).val = pack (pairMask b c (unpack x.val)) := rfl

theorem pairMaskH_tensor (b c : Bool) (x : H m) (y : H n) :
    pairMaskH b c (tensor x y) = tensor (transposeH b x) (transposeH c y) := by
  apply Subtype.ext
  change pack (pairMask b c (unpack (pack (x.val ⊗ₖ y.val)))) = _
  rw [unpack_pack]
  cases b <;> cases c <;> rfl

private theorem pack_psd {X : CMat (Fin m × Fin n)} :
    (pack X).PosSemidef ↔ X.PosSemidef :=
  Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm

/-- Whole-cone positivity of a pair mask forces equal bits in an active sector. -/
theorem pairMaskH_bits (hn : 2 ≤ n) (b c : Bool)
    (hp : ∀ x : H (n * n), x.val.PosSemidef → (pairMaskH b c x).val.PosSemidef) :
    b = c := by
  obtain ⟨X, hX, hpt⟩ := bell_obstruction hn
  let x : H (n * n) := ⟨pack X, hX.isHermitian.submatrix _⟩
  have hh := hp x (pack_psd.mpr hX)
  rw [val_pairMaskH, show x.val = pack X from rfl, unpack_pack, pack_psd] at hh
  cases b <;> cases c
  · rfl
  · exact (hpt hh).elim
  · exact (hpt (show (Bipartite.partialTranspose X).PosSemidef from hh.transpose)).elim
  · rfl

/-- Discard the right factor in packed coordinates. -/
def traceLast : H (m * n) →ₗ[ℝ] H m where
  toFun x := ⟨partialTraceRight (unpack x.val), Matrix.IsHermitian.ext (by
    intro i j
    simp only [partialTraceRight, star_sum]
    exact Finset.sum_congr rfl fun k _ => (herm x).apply _ _)⟩
  map_add' x y := Subtype.ext (partialTraceRight_add (unpack x.val) (unpack y.val))
  map_smul' c x := Subtype.ext (by
    ext i j
    simp [partialTraceRight, unpack, Finset.smul_sum, Matrix.smul_apply])

theorem traceLast_psd {x : H (m * n)} (hx : x.val.PosSemidef) :
    (traceLast x).val.PosSemidef :=
  partialTraceRight_posSemidef (hx.submatrix _)

theorem pack_trace (X : CMat (Fin m × Fin n)) : (pack X).trace = X.trace := by
  exact finProdFinEquiv.symm.sum_comp (fun i => X i i)

@[simp] theorem traceLast_tp (x : H (m * n)) : tr (traceLast x) = tr x := by
  change (partialTraceRight (unpack x.val)).trace.re = x.val.trace.re
  rw [trace_partialTraceRight, ← pack_trace, pack_unpack]

theorem traceLast_tensor (x : H m) (y : H n) : traceLast (tensor x y) = tr y • x := by
  apply Subtype.ext
  change partialTraceRight (unpack (pack (x.val ⊗ₖ y.val))) = _
  rw [unpack_pack]
  change partialTraceRight (Matrix.kronecker x.val y.val) = _
  rw [partialTraceRight_kronecker]
  have hy : ((tr y : ℝ) : ℂ) = y.val.trace := by
    apply Complex.conj_eq_iff_re.mp
    change star y.val.trace = y.val.trace
    rw [← Matrix.trace_conjTranspose, (herm y).eq]
  rw [← hy]
  rfl

/-- Partial trace hits every PSD matrix, by tensoring a normalized PSD spectator. -/
theorem traceLast_psd_surjective {c : H n} (hc : c.val.PosSemidef) (ht : tr c = 1)
    (x : H m) (hx : x.val.PosSemidef) :
    ∃ z : H (m * n), z.val.PosSemidef ∧ traceLast z = x := by
  exact ⟨tensor x c, tensor_psd hx hc, by rw [traceLast_tensor, ht, one_smul]⟩

/-- Reindex both rows and columns by the same permutation. -/
def reindexH (e : Equiv.Perm (Fin n)) : H n ≃ₗ[ℝ] H n where
  toFun x := ⟨x.val.submatrix e e, (herm x).submatrix _⟩
  invFun x := ⟨x.val.submatrix e.symm e.symm, (herm x).submatrix _⟩
  left_inv x := Subtype.ext (by ext i j; simp)
  right_inv x := Subtype.ext (by ext i j; simp)
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

abbrev TripleSize (n : ℕ) := (n * n) * n

def slots (n : ℕ) : Fin (TripleSize n) ≃ (Fin 3 → Fin n) where
  toFun i :=
    let jk := (finProdFinEquiv.symm i).1
    let ij := finProdFinEquiv.symm jk
    ![ij.1,ij.2,(finProdFinEquiv.symm i).2]
  invFun f := finProdFinEquiv (finProdFinEquiv (f 0, f 1), f 2)
  left_inv i := by
    change finProdFinEquiv (finProdFinEquiv ((finProdFinEquiv.symm
      (finProdFinEquiv.symm i).1).1, (finProdFinEquiv.symm (finProdFinEquiv.symm i).1).2),
      (finProdFinEquiv.symm i).2) = i
    rw [Prod.mk.eta, Equiv.apply_symm_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv f := by
    have hl := (finProdFinEquiv (m := n * n) (n := n)).symm_apply_apply
      (finProdFinEquiv (f 0, f 1), f 2)
    have hr := (finProdFinEquiv (m := n) (n := n)).symm_apply_apply (f 0, f 1)
    change ![(finProdFinEquiv.symm (finProdFinEquiv.symm
      (finProdFinEquiv (finProdFinEquiv (f 0, f 1), f 2))).1).1,
      (finProdFinEquiv.symm (finProdFinEquiv.symm
      (finProdFinEquiv (finProdFinEquiv (f 0, f 1), f 2))).1).2,
      (finProdFinEquiv.symm (finProdFinEquiv (finProdFinEquiv (f 0, f 1), f 2))).2] = f
    rw [hl, hr]
    funext i
    fin_cases i <;> rfl

/-- In the target slot `i`, place the source factor `σ i`. -/
def slotPerm (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin (TripleSize n)) :=
  (slots n).trans ((Equiv.arrowCongr σ (Equiv.refl _)).trans (slots n).symm)

def permute (σ : Equiv.Perm (Fin 3)) : H (TripleSize n) ≃ₗ[ℝ] H (TripleSize n) :=
  reindexH (slotPerm σ)

def tripleTensor (f : Fin 3 → H n) : H (TripleSize n) :=
  tensor (tensor (f 0) (f 1)) (f 2)

private theorem tripleTensor_entry (f : Fin 3 → H n) (i j : Fin (TripleSize n)) :
    (tripleTensor f).val i j = ∏ k : Fin 3, (f k).val (slots n i k) (slots n j k) := by
  rw [Fin.prod_univ_three]
  rfl

theorem permute_tensor (σ : Equiv.Perm (Fin 3)) (f : Fin 3 → H n) :
    permute σ (tripleTensor f) = tripleTensor (f ∘ σ) := by
  apply Subtype.ext
  ext i j
  change (tripleTensor f).val (slotPerm σ i) (slotPerm σ j) = _
  rw [tripleTensor_entry, tripleTensor_entry]
  have he (q : Fin (TripleSize n)) (k : Fin 3) :
      slots n (slotPerm σ q) k = slots n q (σ.symm k) := by
    simp [slotPerm, Equiv.arrowCongr]
  simp only [he]
  symm
  apply Fintype.prod_equiv σ
  intro k
  simp


theorem tensor_transposeH (b : Bool) (x : H m) (y : H n) :
    transposeH b (tensor x y) = tensor (transposeH b x) (transposeH b y) := by
  apply Subtype.ext
  change transposeIf b (pack (x.val ⊗ₖ y.val)) = _
  rw [transposeIf_pack, transposeIf_kronecker]
  rfl

@[simp] theorem transposeH_xor (b c : Bool) (x : H n) :
    transposeH b (transposeH c x) = transposeH (b ^^ c) x :=
  Subtype.ext (transposeIf_xor b c x.val)

@[simp] theorem transposeH_false (x : H n) : transposeH false x = x := rfl

theorem adjH_psd (U : ↥(unitary (Mat n))) (x : H n) :
    (adjH U x).val.PosSemidef ↔ x.val.PosSemidef := adj_psd U

@[simp] theorem adjH_tp (U : ↥(unitary (Mat n))) (x : H n) :
    tr (adjH U x) = tr x := by simp [tr]

theorem transposeH_psd (b : Bool) (x : H n) :
    (transposeH b x).val.PosSemidef ↔ x.val.PosSemidef := transposeIf_psd b

@[simp] theorem transposeH_tp (b : Bool) (x : H n) :
    tr (transposeH b x) = tr x := by simp [tr]

private theorem pack_mul (X Y : CMat (Fin m × Fin n)) : pack (X * Y) = pack X * pack Y :=
  (Matrix.submatrix_mul_equiv X Y _ finProdFinEquiv.symm _).symm

private theorem pack_one : pack (1 : CMat (Fin m × Fin n)) = 1 :=
  Matrix.submatrix_one_equiv _

/-- Extend a unitary on the first factor by the identity on the last. -/
def extendUnitary (U : ↥(unitary (Mat m))) (n : ℕ) : ↥(unitary (Mat (m * n))) := by
  refine ⟨pack (U.val ⊗ₖ (1 : Mat n)), Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change pack (U.val ⊗ₖ (1 : Mat n)) * pack (U.val ⊗ₖ (1 : Mat n))ᴴ = 1
  rw [← pack_mul, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, mul_one]
  change pack ((U.val * star U.val) ⊗ₖ (1 : Mat n)) = 1
  have hu : U.val * star U.val = 1 := Unitary.coe_mul_star_self U
  rw [hu]
  change pack (Matrix.kronecker (1 : Mat m) (1 : Mat n)) = 1
  exact (congrArg pack (Matrix.one_kronecker_one (α := ℂ) (m := Fin m) (n := Fin n))).trans pack_one

private theorem adjH_extend_tensor (U : ↥(unitary (Mat m))) (x : H m) (y : H n) :
    adjH (extendUnitary U n) (tensor x y) = tensor (adjH U x) y := by
  apply Subtype.ext
  change pack (U.val ⊗ₖ (1 : Mat n)) * pack (x.val ⊗ₖ y.val) *
    pack (U.val ⊗ₖ (1 : Mat n))ᴴ = pack ((U.val * x.val * U.valᴴ) ⊗ₖ y.val)
  rw [← pack_mul, ← pack_mul, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one]

/-- Coordinates before removing the common triple transpose. -/
def tripleFrame (U : ↥(unitary (Mat (n * n)))) (V : ↥(unitary (Mat (TripleSize n))))
    (α : Bool) : H (TripleSize n) ≃ₗ[ℝ] H (TripleSize n) :=
  (transposeH α).trans ((adjH (extendUnitary U n)).trans ((transposeH α).trans (adjH V)))

theorem tripleFrame_psd (U : ↥(unitary (Mat (n * n)))) (V : ↥(unitary (Mat (TripleSize n))))
    (α : Bool) (x : H (TripleSize n)) :
    (tripleFrame U V α x).val.PosSemidef ↔ x.val.PosSemidef := by
  simp only [tripleFrame, LinearEquiv.trans_apply, adjH_psd, transposeH_psd]

@[simp] theorem tripleFrame_tp (U : ↥(unitary (Mat (n * n)))) (V : ↥(unitary (Mat (TripleSize n))))
    (α : Bool) (x : H (TripleSize n)) : tr (tripleFrame U V α x) = tr x := by
  simp [tripleFrame]

variable {M : H n →ₗ[ℝ] H n →ₗ[ℝ] H (n * n)}
variable {L : H (n * n) →ₗ[ℝ] H n →ₗ[ℝ] H (TripleSize n)}
variable {U : ↥(unitary (Mat (n * n)))} {V : ↥(unitary (Mat (TripleSize n)))}
variable {ε δ α β : Bool}

set_option maxHeartbeats 800000 in
-- Rewriting the nested real-linear maps and packed tensor transposes exceeds the default budget.
/-- Composition of the two exact binary forms gives (32), with
`t₁ = α xor ε`, `t₂ = α xor δ` and `t₃ = β`. -/
theorem triple_normal (hm : TensorNormalForm M U ε δ) (hl : TensorNormalForm L V α β)
    (x y z : H n) :
    L (M x y) z = tripleFrame U V α
      (tensor (tensor (transposeH (α ^^ ε) x) (transposeH (α ^^ δ) y)) (transposeH β z)) := by
  have cancel (a b : Bool) : (a ^^ (a ^^ b)) = b := by cases a <;> cases b <;> rfl
  rw [hl (M x y) z]
  conv_lhs => rw [hm x y]
  simp only [tripleFrame, LinearEquiv.trans_apply, tensor_transposeH, transposeH_xor,
    adjH_extend_tensor, cancel]


theorem eq_on_nested
    (hm : Spans M) (hl : Spans L)
    {F G : H (TripleSize n) →ₗ[ℝ] H d}
    (h : ∀ x y z, F (L (M x y) z) = G (L (M x y) z)) : F = G := by
  apply sub_eq_zero.mp
  apply eq_of_products hl
  intro q z
  have he : (F - G).comp (L.flip z) = 0 := by
    apply eq_of_products hm
    intro x y
    exact sub_eq_zero.mpr (h x y z)
  exact LinearMap.congr_fun he q

def bits (ε δ α β : Bool) : Fin 3 → Bool := ![α ^^ ε, α ^^ δ, β]

set_option maxHeartbeats 1000000 in
-- Elaborating the two real tensor lifts and the permuted trace formula exceeds the default budget.
/-- Equation (33) on the whole triple carrier, from all-vector readback. -/
theorem retained_pair_formula (hm : TensorNormalForm M U ε δ)
    (hl : TensorNormalForm L V α β) (hM : Spans M) (hL : Spans L)
    (σ : Equiv.Perm (Fin 3)) (p : H (TripleSize n) →ₗ[ℝ] H (n * n))
    (hread : ∀ f : Fin 3 → H n, p (L (M (f 0) (f 1)) (f 2)) =
      tr (f (σ 2)) • M (f (σ 0)) (f (σ 1))) :
    p = (adjH U).toLinearMap.comp
      ((pairMaskH (ε ^^ bits ε δ α β (σ 0)) (δ ^^ bits ε δ α β (σ 1))).comp
        (traceLast.comp ((permute σ).toLinearMap.comp (tripleFrame U V α).symm.toLinearMap))) := by
  apply eq_on_nested hM hL
  intro x y z
  let f : Fin 3 → H n := ![x,y,z]
  let g (k : Fin 3) := transposeH (bits ε δ α β k) (f k)
  have hq : L (M x y) z = tripleFrame U V α (tripleTensor g) :=
    triple_normal hm hl x y z
  have hr : p (L (M x y) z) = tr (f (σ 2)) • M (f (σ 0)) (f (σ 1)) := hread f
  rw [hr, hq, hm (f (σ 0)) (f (σ 1))]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    permute_tensor]
  change _ = adjH U (pairMaskH _ _ (traceLast (tensor (tensor (g (σ 0)) (g (σ 1))) (g (σ 2)))))
  simp only [traceLast_tensor, map_smul, pairMaskH_tensor, g, transposeH_tp, transposeH_xor]
  have cancel (a b : Bool) : ((a ^^ b) ^^ b) = a := by cases a <;> cases b <;> rfl
  simp only [cancel]

theorem permute_psd (σ : Equiv.Perm (Fin 3)) (x : H (TripleSize n)) :
    (permute σ x).val.PosSemidef ↔ x.val.PosSemidef := by
  constructor
  · intro hp
    have h := hp.submatrix (slotPerm σ).symm
    simpa [permute, reindexH] using h
  · intro hp
    exact hp.submatrix _

private theorem normalized_spectator (hn : 0 < n) :
    ∃ c : H n, c.val.PosSemidef ∧ tr c = 1 := by
  let c := frameProjection (1 : ↥(unitary (Mat n))) ⟨0, hn⟩
  exact ⟨c, proj_psd _ _, by simpa [c, tr] using congrArg Complex.re (proj_trace
    (1 : ↥(unitary (Mat n))) ⟨0, hn⟩)⟩

set_option maxHeartbeats 800000 in
-- Transporting the spectator through the whole-space formula requires extra reduction.
/-- A positive pair map forces the two induced transpose bits to coincide. -/
theorem retained_pair_bits (hn : 2 ≤ n) (hm : TensorNormalForm M U ε δ)
    (hl : TensorNormalForm L V α β) (hM : Spans M) (hL : Spans L)
    (σ : Equiv.Perm (Fin 3)) (p : H (TripleSize n) →ₗ[ℝ] H (n * n))
    (hread : ∀ f : Fin 3 → H n, p (L (M (f 0) (f 1)) (f 2)) =
      tr (f (σ 2)) • M (f (σ 0)) (f (σ 1)))
    (hp : ∀ x, x.val.PosSemidef → (p x).val.PosSemidef) :
    (bits ε δ α β (σ 0) ^^ bits ε δ α β (σ 1)) = (ε ^^ δ) := by
  let b := bits ε δ α β (σ 0)
  let c := bits ε δ α β (σ 1)
  change (b ^^ c) = (ε ^^ δ)
  have he := retained_pair_formula hm hl hM hL σ p hread
  obtain ⟨s, hs, ht⟩ := normalized_spectator (n := n) (by omega)
  have hbc : (ε ^^ b) = (δ ^^ c) := by
    apply pairMaskH_bits hn
    intro x hx
    obtain ⟨y, hy, hxy⟩ := traceLast_psd_surjective hs ht x hx
    let z := (permute σ).symm y
    have hz : z.val.PosSemidef := (permute_psd σ z).mp (by simpa [z] using hy)
    have hh := hp (tripleFrame U V α z) ((tripleFrame_psd U V α z).mpr hz)
    rw [he] at hh
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      z, LinearEquiv.apply_symm_apply, hxy] at hh
    exact (adjH_psd U _).mp hh
  have xor_compare (e f i j : Bool) (h : (e ^^ i) = (f ^^ j)) :
      (i ^^ j) = (e ^^ f) := by
    cases e <;> cases f <;> cases i <;> cases j <;> first | contradiction | rfl
  exact xor_compare ε δ b c hbc

private def order13 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
private def order23 : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 0 2)

set_option maxHeartbeats 800000 in
-- Specializing both retained-pair formulas with the concrete Fin permutations requires extra reduction.
/-- The two actual positive retained-pair maps close the parity triangle.
Both local bits coincide, and the nested triple has one common bit. -/
theorem align_bits
    (hn : 2 ≤ n) (hm : TensorNormalForm M U ε δ) (hl : TensorNormalForm L V α β)
    (hM : Spans M) (hL : Spans L)
    (p13 p23 : H (TripleSize n) →ₗ[ℝ] H (n * n))
    (pos13 : ∀ w, w.val.PosSemidef → (p13 w).val.PosSemidef)
    (pos23 : ∀ w, w.val.PosSemidef → (p23 w).val.PosSemidef)
    (read13 : ∀ x y z, p13 (L (M x y) z) = tr y • M x z)
    (read23 : ∀ x y z, p23 (L (M x y) z) = tr x • M y z) :
    let t₁ := α ^^ ε
    let t₂ := α ^^ δ
    let t₃ := β
    (t₁ ^^ t₃) = (ε ^^ δ) ∧ (t₂ ^^ t₃) = (ε ^^ δ) ∧
    (t₁ ^^ t₂) = (ε ^^ δ) ∧ (ε ^^ δ) = false ∧ t₁ = t₃ ∧ t₂ = t₃ := by
  have h13 : ((α ^^ ε) ^^ β) = (ε ^^ δ) :=
    retained_pair_bits hn hm hl hM hL order13 p13
      (fun f => read13 (f 0) (f 1) (f 2)) pos13
  have h23 : ((α ^^ δ) ^^ β) = (ε ^^ δ) :=
    retained_pair_bits hn hm hl hM hL order23 p23
      (fun f => read23 (f 0) (f 1) (f 2)) pos23
  exact ⟨h13, h23, by cases α <;> cases ε <;> cases δ <;> rfl, by
    cases ε <;> cases δ <;> cases α <;> cases β <;> first | contradiction | decide⟩

end PositiveMarginalMatrixComposition.TripleOrientation
