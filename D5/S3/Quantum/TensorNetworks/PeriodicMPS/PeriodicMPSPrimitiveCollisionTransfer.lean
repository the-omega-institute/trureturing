/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionTransfer
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformAntisymmetricTransfer]
   utility: none
   digest: The common marginal and strictly positive transfer. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformAntisymmetricTransfer
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Exact transfer data for the Ising-weight periodic bond-two collision. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

open Matrix
open scoped Matrix Kronecker ComplexOrder
open PeriodicMPSParentIntersection (Bond TwoSiteSpanning twoFlattening)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal normalizedMarginal_eq_rawTwo)
open PeriodicMPSUniformAntisymmetricTransfer
  (BondMatrix TransferMatrix mixedTransfer mixedRaw mixedRaw_trace conjugateCore rawTwo_eq_mixedRaw)
open PeriodicMPSUniformHardCoreTransferRecurrence (binaryInsertion binaryTransfer)

private def gi : GaussianInt := ⟨0, 1⟩

private def isingG : Fin 2 → BondMatrix GaussianInt :=
  ![!![2 + gi, 2 - gi; 0, 0], !![0, 0; 2 - gi, 2 + gi]]

/-- Gaussian integer cores before extension of scalars. -/
def coresG (partner : Bool) (i : Fin 2) : BondMatrix GaussianInt :=
  if partner then (isingG i).map star - gi • (isingG (1 - i)).map star else isingG i

/-- The unscaled Ising cores and their antiunitary partner, in Gaussian integer units. -/
noncomputable def cores (partner : Bool) (i : Fin 2) : Bond :=
  GaussianInt.toComplex.mapMatrix (coresG partner i)

theorem ising_cores :
    cores false = ![!![2 + Complex.I, 2 - Complex.I; 0, 0],
                    !![0, 0; 2 - Complex.I, 2 + Complex.I]] := by
  funext i
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [cores, coresG, isingG, gi, GaussianInt.toComplex_def', map_ofNat]

theorem partner_core (i : Fin 2) :
    cores true i = conjugateCore (cores false) i -
      Complex.I • conjugateCore (cores false) (1 - i) := by
  ext j k
  simp [cores, coresG, conjugateCore, gi, GaussianInt.toComplex_def',
    GaussianInt.toComplex_star, Matrix.smul_apply, smul_eq_mul]

private abbrev Pair := Fin 2 × Fin 2

/-- The nonzero transfer eigenvalue in the unscaled core convention. -/
def collisionScale (b : Bool) : ℕ := if b then 20 else 10
private def factor (b : Bool) : ℕ := if b then 16 else 1

/-- Entrywise complex conjugates over the Gaussian integers. -/
def braG (b : Bool) (i : Fin 2) : BondMatrix GaussianInt := (coresG b i).map star

private theorem map_bra (b : Bool) (i : Fin 2) :
    GaussianInt.toComplex.mapMatrix (braG b i) = conjugateCore (cores b) i := by
  ext j k
  exact GaussianInt.toComplex_star _

private theorem map_kronecker {R S n : Type*} [CommSemiring R] [CommSemiring S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (M N : Matrix n n R) :
    f.mapMatrix (M ⊗ₖ N) = f.mapMatrix M ⊗ₖ f.mapMatrix N := by
  ext i j
  exact map_mul f _ _

private theorem map_transfer (b : Bool) :
    GaussianInt.toComplex.mapMatrix (mixedTransfer (coresG b) (braG b)) =
      mixedTransfer (cores b) (conjugateCore (cores b)) := by
  simp only [mixedTransfer, binaryTransfer, map_add, map_kronecker, map_bra, cores]

private theorem map_raw (b : Bool) (m : ℕ) :
    GaussianInt.toComplex.mapMatrix (mixedRaw (coresG b) (braG b) m) =
      mixedRaw (cores b) (conjugateCore (cores b)) m := by
  ext p q
  change GaussianInt.toComplex (_ : GaussianInt) = _
  rw [mixedRaw, mixedRaw, AddMonoidHom.map_trace GaussianInt.toComplex]
  change (GaussianInt.toComplex.mapMatrix (_ * _ ^ m)).trace = _
  simp only [binaryInsertion, map_mul, map_pow, map_transfer, map_kronecker, map_bra, cores]

private theorem transfer_cube (b : Bool) :
    let T := mixedTransfer (coresG b) (braG b)
    T ^ 3 = ((collisionScale b : ℕ) : GaussianInt) • T ^ 2 := by
  cases b <;> funext i j <;> rcases i with ⟨i₁, i₂⟩ <;> rcases j with ⟨j₁, j₂⟩ <;>
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;> decide +kernel

private theorem transfer_stabilizes (b : Bool) (r : ℕ) :
    let T := mixedTransfer (coresG b) (braG b)
    T ^ (r + 2) = (((collisionScale b : ℕ) : GaussianInt) ^ r) • T ^ 2 := by
  dsimp only
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show r + 1 + 2 = (r + 2) + 1 by omega, pow_succ, ih, Matrix.smul_mul,
      ← pow_succ, transfer_cube, smul_smul, ← pow_succ]

private def numeratorG : TransferMatrix GaussianInt :=
  Matrix.reindex (finProdFinEquiv : Pair ≃ Fin 4).symm finProdFinEquiv.symm
    !![2500, ⟨900, 1200⟩, ⟨900, 1200⟩, 900;
       ⟨900, -1200⟩, 2500, 900, ⟨900, -1200⟩;
       ⟨900, -1200⟩, 900, 2500, ⟨900, -1200⟩;
       900, ⟨900, 1200⟩, ⟨900, 1200⟩, 2500]

private theorem raw_base (b : Bool) :
    mixedRaw (coresG b) (braG b) 2 = (factor b : GaussianInt) • numeratorG := by
  cases b <;> funext i j <;> rcases i with ⟨i₁, i₂⟩ <;> rcases j with ⟨j₁, j₂⟩ <;>
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;> decide +kernel

private theorem raw_uniform_G (b : Bool) (r : ℕ) :
    mixedRaw (coresG b) (braG b) (r + 2) =
      (((collisionScale b : GaussianInt) ^ r) * (factor b : GaussianInt)) • numeratorG := by
  funext p q
  change (binaryInsertion (braG b) (coresG b) q p *
    mixedTransfer (coresG b) (braG b) ^ (r + 2)).trace = _
  rw [transfer_stabilizes, Matrix.mul_smul, Matrix.trace_smul]
  change _ • mixedRaw (coresG b) (braG b) 2 p q = _
  rw [raw_base, Matrix.smul_apply, Matrix.smul_apply, smul_smul]

private noncomputable def numerator : TransferMatrix ℂ :=
  GaussianInt.toComplex.mapMatrix numeratorG

private theorem numerator_trace : numerator.trace = 10000 := by
  rw [numerator]
  change (numeratorG.map GaussianInt.toComplex).trace = _
  rw [← AddMonoidHom.map_trace GaussianInt.toComplex]
  rw [show numeratorG.trace = (10000 : GaussianInt) by decide +kernel]
  exact map_ofNat _ _

private theorem raw_uniform (b : Bool) (r : ℕ) :
    rawTwo (cores b) r = (((collisionScale b : ℝ) ^ r) * (factor b : ℝ)) • numerator := by
  rw [rawTwo_eq_mixedRaw, ← map_raw, raw_uniform_G]
  ext p q
  simp [numerator, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem rawTwo_trace_initial (b : Bool) :
    (rawTwo (cores b) 0).trace = (collisionScale b : ℂ) ^ 4 := by
  rw [raw_uniform, Matrix.trace_smul, Complex.real_smul, numerator_trace]
  cases b <;> norm_num [collisionScale, factor]

/-- The common normalized two-site matrix, in lexicographic order on the two bits. -/
noncomputable def collisionMarginal : TransferMatrix ℂ := (10000 : ℝ)⁻¹ • numerator

theorem normalized_collision_marginal (b : Bool) (r : ℕ) :
    normalizedMarginal (r + 2) (cores b) = collisionMarginal := by
  let s : ℝ := (collisionScale b : ℝ) ^ r * (factor b : ℝ)
  have hs : 0 < s := by cases b <;> dsimp [s, collisionScale, factor] <;> positivity
  rw [normalizedMarginal_eq_rawTwo, raw_uniform]
  change ((s • numerator).trace.re)⁻¹ • (s • numerator) = _
  rw [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul, numerator_trace]
  rw [collisionMarginal, smul_smul]
  congr 1
  field_simp
  norm_num

theorem collision_marginal_trace : collisionMarginal.trace = 1 := by
  rw [collisionMarginal, Matrix.trace_smul, Complex.real_smul, numerator_trace]
  norm_num

theorem collision_marginal_posDef : collisionMarginal.PosDef := by
  have hraw : rawTwo (cores false) 0 = numerator := by
    simpa [collisionScale, factor] using raw_uniform false 0
  have hpsd : numerator.PosSemidef := by
    rw [← hraw, rawTwo]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hdet : numeratorG.det = (6553600000000 : GaussianInt) := by decide +kernel
  have hd : numerator.det ≠ 0 := by
    rw [numerator]
    rw [← RingHom.map_det, hdet, map_ofNat]
    norm_num
  have hpd := hpsd.posDef_iff_det_ne_zero.mpr hd
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [collisionMarginal, Matrix.IsHermitian, Matrix.conjTranspose_smul] using
      congrArg (fun M : TransferMatrix ℂ => (10000 : ℝ)⁻¹ • M) hpd.isHermitian.eq
  · intro x hx
    rw [collisionMarginal, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul]
    exact mul_pos (by norm_num) (hpd.dotProduct_mulVec_pos hx)

private def eigenbasisG : TransferMatrix GaussianInt :=
  Matrix.reindex (finProdFinEquiv : Pair ≃ Fin 4).symm finProdFinEquiv.symm
    !![5, 0, -1, 5;
       ⟨-3, 4⟩, -1, 0, ⟨3, -4⟩;
       ⟨-3, 4⟩, 1, 0, ⟨3, -4⟩;
       5, 0, 1, 5]

private def eigenvaluesG (p : Pair) : GaussianInt :=
  ![400, 1600, 1600, 6400] (finProdFinEquiv p)

private theorem eigenbasis_identity :
    numeratorG * eigenbasisG = eigenbasisG * Matrix.diagonal eigenvaluesG := by
  funext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

open Polynomial in
/-- The characteristic polynomial of the common physical marginal. -/
theorem collision_marginal_charpoly :
    collisionMarginal.charpoly =
      (X - C (1 / 25)) * (X - C (4 / 25)) ^ 2 * (X - C (16 / 25)) := by
  let f := GaussianInt.toComplex
  let W := f.mapMatrix eigenbasisG
  let e : Pair → ℂ := fun p => (10000 : ℂ)⁻¹ * f (eigenvaluesG p)
  have hu : IsUnit W.det := by
    change IsUnit (f.mapMatrix eigenbasisG).det
    rw [← RingHom.map_det, show eigenbasisG.det = (⟨120, -160⟩ : GaussianInt) by decide +kernel,
      isUnit_iff_ne_zero]
    intro h
    have h' := congrArg Complex.re h
    norm_num [f, GaussianInt.toComplex_def'] at h'
  have h := congrArg f.mapMatrix eigenbasis_identity
  simp only [map_mul] at h
  change numerator * W = W * f.mapMatrix (Matrix.diagonal eigenvaluesG) at h
  have h' : collisionMarginal * W = W * Matrix.diagonal e := by
    rw [collisionMarginal, Matrix.smul_mul, h, ← Matrix.mul_smul]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, e, f, Complex.real_smul]
  have hsim : collisionMarginal = W * Matrix.diagonal e * W⁻¹ := by
    rw [← h', mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one]
  rw [hsim, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul,
    Matrix.charpoly_diagonal]
  have he00 : e (0, 0) = 1 / 25 := by
    dsimp only [e, f]
    rw [show eigenvaluesG (0, 0) = 400 by decide +kernel, map_ofNat]
    norm_num
  have he01 : e (0, 1) = 4 / 25 := by
    dsimp only [e, f]
    rw [show eigenvaluesG (0, 1) = 1600 by decide +kernel, map_ofNat]
    norm_num
  have he10 : e (1, 0) = 4 / 25 := by
    dsimp only [e, f]
    rw [show eigenvaluesG (1, 0) = 1600 by decide +kernel, map_ofNat]
    norm_num
  have he11 : e (1, 1) = 16 / 25 := by
    dsimp only [e, f]
    rw [show eigenvaluesG (1, 1) = 6400 by decide +kernel, map_ofNat]
    norm_num
  simp only [Fintype.prod_prod_type, Fin.prod_univ_two, he00, he01, he10, he11]
  ring

private def blockedG (b : Bool) : TransferMatrix GaussianInt :=
  fun i p => (coresG b p.1 * coresG b p.2) i.1 i.2

theorem twoSiteSpanning_cores (b : Bool) : TwoSiteSpanning (cores b) := by
  let M : TransferMatrix ℂ := GaussianInt.toComplex.mapMatrix (blockedG b)
  have hdet : M.det ≠ 0 := by
    change (GaussianInt.toComplex.mapMatrix (blockedG b)).det ≠ 0
    rw [← RingHom.map_det]
    cases b
    · rw [show (blockedG false).det = (-1600 : GaussianInt) by decide +kernel]
      norm_num [map_neg, map_ofNat]
    · rw [show (blockedG true).det = (-25600 : GaussianInt) by decide +kernel]
      norm_num [map_neg, map_ofNat]
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (M.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  apply Submodule.eq_top_iff'.mpr
  intro X
  obtain ⟨v, hv⟩ := hsurj (fun i => X i.1 i.2)
  have hv' : (∑ p : Pair, v p • (cores b p.1 * cores b p.2)) = X := by
    ext i j
    have h := congrFun hv (i, j)
    simp only [Matrix.mulVec, dotProduct] at h
    rw [← h, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
    change _ = GaussianInt.toComplex.mapMatrix (_ * _) i j * _
    simp only [map_mul, cores]
  rw [← hv']
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The completely positive transfer in the Gaussian integer scaling of the cores. -/
noncomputable def transferStep (b : Bool) (H : Bond) : Bond :=
  cores b 0 * H * (cores b 0)ᴴ + cores b 1 * H * (cores b 1)ᴴ

private theorem step_vector (b : Bool) (H : Bond) :
    (fun p : Pair => transferStep b H p.2 p.1) =
      mixedTransfer (cores b) (conjugateCore (cores b)) *ᵥ (fun p : Pair => H p.2 p.1) := by
  funext ⟨i, j⟩
  simp only [transferStep, mixedTransfer, binaryTransfer, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, conjugateCore, Matrix.map_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two, starRingEnd_apply]
  ring

private def twiceFactor (b : Bool) : ℕ := if b then 4 else 1

private theorem transfer_square_entry (b : Bool) (p q : Pair) :
    ((mixedTransfer (coresG b) (braG b)) ^ 2) p q =
      if p.1 = p.2 then (twiceFactor b : GaussianInt) *
        (if q.1 = q.2 then 50 else 30) else 0 := by
  cases b <;> rcases p with ⟨i, j⟩ <;> rcases q with ⟨k, l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

private theorem transfer_square_complex (b : Bool) (p q : Pair) :
    (mixedTransfer (cores b) (conjugateCore (cores b)) ^ 2) p q =
      if p.1 = p.2 then (twiceFactor b : ℂ) *
        (if q.1 = q.2 then 50 else 30) else 0 := by
  rw [← map_transfer, ← map_pow]
  change GaussianInt.toComplex (_ : GaussianInt) = _
  rw [transfer_square_entry]
  split <;> rename_i hp
  · split <;> rename_i hq <;> norm_num [hp, hq, map_ofNat]
  · simp

/-- The transfer divided by its nonzero eigenvalue. -/
noncomputable def stabilizedTransfer (b : Bool) : TransferMatrix ℂ :=
  (collisionScale b : ℂ)⁻¹ • mixedTransfer (cores b) (conjugateCore (cores b))

theorem stabilizedTransfer_cube (b : Bool) :
    stabilizedTransfer b ^ 3 = stabilizedTransfer b ^ 2 := by
  have h := congrArg GaussianInt.toComplex.mapMatrix (transfer_cube b)
  simp only [map_pow, map_transfer] at h
  have hcast (n : ℕ) (M : TransferMatrix GaussianInt) :
      GaussianInt.toComplex.mapMatrix ((n : GaussianInt) • M) =
        (n : ℂ) • GaussianInt.toComplex.mapMatrix M := by
    ext p q
    simp [smul_eq_mul]
  rw [hcast, map_pow, map_transfer] at h
  unfold stabilizedTransfer
  rw [smul_pow, smul_pow, h, smul_smul]
  congr 1
  have hb : (collisionScale b : ℂ) ≠ 0 := by cases b <;> norm_num [collisionScale]
  field_simp

theorem stabilizedTransfer_square (b : Bool) :
    stabilizedTransfer b ^ 2 =
      Matrix.vecMulVec (fun p : Pair => if p.1 = p.2 then 1 else 0)
        (fun q : Pair => if q.1 = q.2 then 1 / 2 else 3 / 10) := by
  unfold stabilizedTransfer
  rw [smul_pow]
  ext p q
  rw [Matrix.smul_apply, transfer_square_complex, Matrix.vecMulVec_apply]
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> cases b <;>
    norm_num [collisionScale, twiceFactor, hp, hq, smul_eq_mul]

/-- Two steps prepare a scalar multiple of the identity. -/
theorem transferStep_twice (b : Bool) (H : Bond) :
    transferStep b (transferStep b H) =
      ((twiceFactor b : ℂ) * (20 * H.trace + 30 * ((fun _ => 1) ⬝ᵥ (H *ᵥ fun _ => 1)))) • 1 := by
  ext i j
  change (fun p : Pair => transferStep b (transferStep b H) p.2 p.1) (j, i) = _
  rw [step_vector, step_vector, Matrix.mulVec_mulVec, ← pow_two]
  simp only [Matrix.mulVec, dotProduct, transfer_square_complex, Matrix.trace, Matrix.diag_apply,
    Matrix.smul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, mul_one,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Each core pair has a strongly positive transfer after two steps. -/
theorem transferStep_twice_posDef (b : Bool) {H : Bond} (hH : H.PosSemidef) (hne : H ≠ 0) :
    (transferStep b (transferStep b H)).PosDef := by
  have ht : 0 < H.trace := lt_of_le_of_ne hH.trace_nonneg
    (Ne.symm (fun he => hne (hH.trace_eq_zero_iff.mp he)))
  have hq : 0 ≤ (fun _ => 1) ⬝ᵥ (H *ᵥ fun _ => 1) := by
    have he : star (fun _ : Fin 2 => (1 : ℂ)) = fun _ => 1 := funext fun _ => star_one _
    simpa only [he] using hH.dotProduct_mulVec_nonneg (fun _ => 1)
  have hk : 0 < (twiceFactor b : ℂ) := by cases b <;> norm_num [twiceFactor]
  have hscalar : 0 < (twiceFactor b : ℂ) *
      (20 * H.trace + 30 * ((fun _ => 1) ⬝ᵥ (H *ᵥ fun _ => 1))) :=
    mul_pos hk (add_pos_of_pos_of_nonneg (mul_pos (by norm_num) ht) (mul_nonneg (by norm_num) hq))
  rw [transferStep_twice]
  have he (c : ℂ) : c • (1 : Bond) = Matrix.diagonal fun _ => c := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [he]
  exact Matrix.posDef_diagonal_iff.mpr (fun _ => hscalar)

end D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision
