import D5.S3.Analytic.ExponentialSum.MatrixResidueArbitraryTimeUniqueness
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceConnectedSpectral
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic

/-!
# Finite self-adjoint boundary heat at arbitrary sample times

The residue at a real spectral value is the compression of its entire
orthogonal eigenspace projection. The heat readout is the compression of the
matrix exponential. Both constructions allow invisible eigenspaces.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Matrix

namespace BoundaryHeatArbitraryTimeUniqueness

variable {n m d : Type*} [Fintype n] [Fintype m] [Fintype d]
variable [DecidableEq n] [DecidableEq m] [DecidableEq d]
variable {H : Matrix n n ℂ} {K : Matrix m m ℂ}

def eigenvalueSet (hH : H.IsHermitian) : Finset ℝ :=
  Finset.univ.image hH.eigenvalues

private theorem eigenvalue_mem (hH : H.IsHermitian) (i : n) :
    hH.eigenvalues i ∈ eigenvalueSet hH :=
  Finset.mem_image_of_mem _ (Finset.mem_univ i)

private def eigenMask (hH : H.IsHermitian) (x : ℝ) (i : n) : ℂ :=
  if hH.eigenvalues i = x then 1 else 0

private abbrev eigenU (hH : H.IsHermitian) : Matrix n n ℂ :=
  hH.eigenvectorUnitary

private theorem eigenU_star_mul (hH : H.IsHermitian) :
    (eigenU hH)ᴴ * eigenU hH = 1 :=
  Unitary.coe_star_mul_self hH.eigenvectorUnitary

private theorem eigenU_mul_star (hH : H.IsHermitian) :
    eigenU hH * (eigenU hH)ᴴ = 1 :=
  Unitary.coe_mul_star_self hH.eigenvectorUnitary

/-- The orthogonal spectral projection onto the eigenspace at `x`.
Its diagonal in the Mathlib eigenbasis includes every occurrence of `x`. -/
def spectralProjection (hH : H.IsHermitian) (x : ℝ) : Matrix n n ℂ :=
  eigenU hH * Matrix.diagonal (eigenMask hH x) * (eigenU hH)ᴴ

def residue (hH : H.IsHermitian) (V : Matrix n d ℂ) (x : ℝ) : Matrix d d ℂ :=
  Vᴴ * spectralProjection hH x * V

def compressedHeat {𝕜 : Type*} [RCLike 𝕜] (L : Matrix n n 𝕜)
    (V : Matrix n d 𝕜) (t : ℝ) : Matrix d d 𝕜 :=
  Vᴴ * NormedSpace.exp ((-t) • L) * V

private theorem diagonal_mask_posSemidef (hH : H.IsHermitian) (x : ℝ) :
    (Matrix.diagonal (eigenMask hH x)).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases hi : hH.eigenvalues i = x <;> simp [eigenMask, hi]

theorem spectralProjection_posSemidef (hH : H.IsHermitian) (x : ℝ) :
    (spectralProjection hH x).PosSemidef :=
  (diagonal_mask_posSemidef hH x).mul_mul_conjTranspose_same (eigenU hH)

theorem residue_posSemidef (hH : H.IsHermitian) (V : Matrix n d ℂ) (x : ℝ) :
    (residue hH V x).PosSemidef :=
  (spectralProjection_posSemidef hH x).conjTranspose_mul_mul_same V

theorem spectralProjection_mul_self (hH : H.IsHermitian) (x : ℝ) :
    spectralProjection hH x * spectralProjection hH x = spectralProjection hH x := by
  have hMask :
      Matrix.diagonal (eigenMask hH x) * Matrix.diagonal (eigenMask hH x) =
        Matrix.diagonal (eigenMask hH x) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : hH.eigenvalues i = x <;> simp [eigenMask, hi]
  unfold spectralProjection
  calc
    _ = eigenU hH *
          (Matrix.diagonal (eigenMask hH x) * ((eigenU hH)ᴴ * eigenU hH) *
            Matrix.diagonal (eigenMask hH x)) * (eigenU hH)ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = eigenU hH * Matrix.diagonal (eigenMask hH x) * (eigenU hH)ᴴ := by
          rw [eigenU_star_mul, Matrix.mul_one, hMask]

private theorem eigenU_conj_diagonal (hH : H.IsHermitian) :
    H = eigenU hH * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) *
      (eigenU hH)ᴴ := by
  simpa only [eigenU, Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal,
    Function.comp_def, Matrix.star_eq_conjTranspose] using hH.spectral_theorem

theorem mul_spectralProjection (hH : H.IsHermitian) (x : ℝ) :
    H * spectralProjection hH x = (x : ℂ) • spectralProjection hH x := by
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let P := Matrix.diagonal (eigenMask hH x)
  have hDP : D * P = (x : ℂ) • P := by
    dsimp only [D, P]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1
    funext i
    by_cases hi : hH.eigenvalues i = x <;> simp [eigenMask, hi, smul_eq_mul]
  have hHdiag : H = eigenU hH * D * (eigenU hH)ᴴ := eigenU_conj_diagonal hH
  calc
    H * spectralProjection hH x =
        eigenU hH * (D * ((eigenU hH)ᴴ * eigenU hH) * P) * (eigenU hH)ᴴ := by
      calc
        H * spectralProjection hH x =
            (eigenU hH * D * (eigenU hH)ᴴ) * spectralProjection hH x :=
          congrArg (fun A => A * spectralProjection hH x) hHdiag
        _ = _ := by
          change (eigenU hH * D * (eigenU hH)ᴴ) *
            (eigenU hH * P * (eigenU hH)ᴴ) = _
          simp only [Matrix.mul_assoc]
    _ = (x : ℂ) • spectralProjection hH x := by
      change _ = (x : ℂ) • (eigenU hH * P * (eigenU hH)ᴴ)
      rw [eigenU_star_mul, Matrix.mul_one, hDP, Matrix.mul_smul, Matrix.smul_mul]

theorem residue_eq_zero_of_notMem (hH : H.IsHermitian) (V : Matrix n d ℂ)
    {x : ℝ} (hx : x ∉ eigenvalueSet hH) : residue hH V x = 0 := by
  have hMask : eigenMask hH x = 0 := by
    funext i
    have hi : hH.eigenvalues i ≠ x := fun he => hx (he ▸ eigenvalue_mem hH i)
    simp [eigenMask, hi]
  simp [residue, spectralProjection, hMask]

private theorem rank_diagonal_mask (hH : H.IsHermitian) (x : ℝ) :
    (Matrix.diagonal (eigenMask hH x)).rank =
      (Finset.univ.filter fun i => hH.eigenvalues i = x).card := by
  rw [Matrix.rank_diagonal, ← Fintype.card_subtype (fun i => hH.eigenvalues i = x)]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  by_cases hi : hH.eigenvalues i = x <;> simp [eigenMask, hi]

/-- The rank sum over any selection of spectral values is bounded by the
number of eigenbasis vectors whose eigenvalues lie in that selection. -/
theorem sum_rank_residue_le_card_filter (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (carrier : Finset ℝ) :
    (∑ x ∈ carrier, (residue hH V x).rank) ≤
      (Finset.univ.filter fun i => hH.eigenvalues i ∈ carrier).card := by
  calc
    _ ≤ ∑ x ∈ carrier, (Matrix.diagonal (eigenMask hH x)).rank := by
      apply Finset.sum_le_sum
      intro x _
      calc
        (residue hH V x).rank ≤ (spectralProjection hH x).rank := by
          unfold residue
          exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
        _ ≤ (Matrix.diagonal (eigenMask hH x)).rank := by
          unfold spectralProjection
          exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    _ = _ := by
      simp only [rank_diagonal_mask]
      exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ carrier hH.eigenvalues

theorem sum_rank_residue_le (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (carrier : Finset ℝ) (r : ℕ) (hdim : Fintype.card n ≤ Fintype.card d + r) :
    (∑ x ∈ carrier, (residue hH V x).rank) ≤ Fintype.card d + r := by
  exact (sum_rank_residue_le_card_filter hH V carrier).trans
    (((Finset.card_filter_le _ _).trans_eq Finset.card_univ).trans hdim)

private theorem sum_diagonal_masks (hH : H.IsHermitian) (carrier : Finset ℝ)
    (hcarrier : eigenvalueSet hH ⊆ carrier) (f : ℝ → ℝ) :
    (∑ x ∈ carrier, f x • Matrix.diagonal (eigenMask hH x)) =
      Matrix.diagonal (fun i => (f (hH.eigenvalues i) : ℂ)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, eigenMask]
    rw [Finset.sum_eq_single (hH.eigenvalues i)]
    · simp [Complex.real_smul]
    · intro x _ hne
      simp [Ne.symm hne]
    · exact fun h => (h (hcarrier (eigenvalue_mem hH i))).elim
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply]

private theorem sum_smul_residue (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (carrier : Finset ℝ) (hcarrier : eigenvalueSet hH ⊆ carrier) (f : ℝ → ℝ) :
    (∑ x ∈ carrier, f x • residue hH V x) =
      Vᴴ * (eigenU hH * Matrix.diagonal (fun i => (f (hH.eigenvalues i) : ℂ)) *
        (eigenU hH)ᴴ) * V := by
  rw [← sum_diagonal_masks hH carrier hcarrier f]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    residue, spectralProjection]

/-- The total is the actual Gram of the port, hence identity for an isometry. -/
theorem sum_residue (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (carrier : Finset ℝ) (hcarrier : eigenvalueSet hH ⊆ carrier) :
    (∑ x ∈ carrier, residue hH V x) = Vᴴ * V := by
  have h := sum_smul_residue hH V carrier hcarrier (fun _ => 1)
  simpa only [one_smul, Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one,
    eigenU_mul_star] using h

private theorem exp_smul_eq_diagonalization (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-t) • H) =
      eigenU hH * Matrix.diagonal (fun i => (Real.exp (-t * hH.eigenvalues i) : ℂ)) *
        (eigenU hH)ᴴ := by
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let U := Unitary.toUnits hH.eigenvectorUnitary
  have hScale : (-t) • H =
      (↑U : Matrix n n ℂ) * ((-t) • D) * (↑U⁻¹ : Matrix n n ℂ) := by
    change (-t) • H = eigenU hH * ((-t) • D) * (eigenU hH)ᴴ
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg (fun A : Matrix n n ℂ => (-t) • A) (eigenU_conj_diagonal hH)
  rw [hScale, Matrix.exp_units_conj]
  have hExp : NormedSpace.exp ((-t) • D) =
      Matrix.diagonal (fun i => (Real.exp (-t * hH.eigenvalues i) : ℂ)) := by
    dsimp only [D]
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp]
    simp only [Pi.smul_apply, Complex.real_smul, ← Complex.ofReal_mul,
      ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]
  simp only [hExp, U, eigenU, Unitary.val_toUnits_apply, Unitary.val_inv_toUnits_apply,
    ← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]

theorem compressedHeat_eq_sum (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (carrier : Finset ℝ) (hcarrier : eigenvalueSet hH ⊆ carrier) (t : ℝ) :
    compressedHeat H V t = ∑ x ∈ carrier, Real.exp (-t * x) • residue hH V x := by
  rw [sum_smul_residue hH V carrier hcarrier, compressedHeat, exp_smul_eq_diagonalization hH]

/-- Two physical systems can have different state dimensions. Equality
at a finite set of real times whose union with time zero has size at least
`2*r+2` determines every residue and the boundary heat at every real time. -/
theorem residue_and_heat_eq_of_time_samples
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (V : Matrix n d ℂ) (W : Matrix m d ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (r : ℕ) (hDimH : Fintype.card n ≤ Fintype.card d + r)
    (hDimK : Fintype.card m ≤ Fintype.card d + r)
    (times : Finset ℝ) (hcount : 2 * r + 2 ≤ (insert 0 times).card)
    (hsamples : ∀ t ∈ times, compressedHeat H V t = compressedHeat K W t) :
    (∀ x : ℝ, residue hH V x = residue hK W x) ∧
      (∀ t : ℝ, compressedHeat H V t = compressedHeat K W t) := by
  classical
  let carrier := eigenvalueSet hH ∪ eigenvalueSet hK
  have hLeft : eigenvalueSet hH ⊆ carrier := Finset.subset_union_left
  have hRight : eigenvalueSet hK ⊆ carrier := Finset.subset_union_right
  have hTotalH : (∑ x ∈ carrier, residue hH V x) = 1 :=
    (sum_residue hH V carrier hLeft).trans hV
  have hTotalK : (∑ x ∈ carrier, residue hK W x) = 1 :=
    (sum_residue hK W carrier hRight).trans hW
  have hPosDef : (∑ x ∈ carrier, residue hH V x).PosDef := by
    rw [hTotalH]
    exact Matrix.PosDef.one
  have hEq := MatrixResidueArbitraryTimeUniqueness.eq_on_carrier_of_exponential_moments
    carrier (insert 0 times) r hcount (residue hH V) (residue hK W)
    (fun x _ => residue_posSemidef hH V x) (fun x _ => residue_posSemidef hK W x)
    hPosDef
    (sum_rank_residue_le hH V carrier r hDimH) (sum_rank_residue_le hK W carrier r hDimK)
    (by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using
          hTotalH.trans hTotalK.symm
      · exact (compressedHeat_eq_sum hH V carrier hLeft t).symm.trans
          ((hsamples t ht).trans (compressedHeat_eq_sum hK W carrier hRight t)))
  constructor
  · intro x
    by_cases hx : x ∈ carrier
    · exact hEq x hx
    · rw [residue_eq_zero_of_notMem hH V (fun h => hx (hLeft h)),
        residue_eq_zero_of_notMem hK W (fun h => hx (hRight h))]
  · intro t
    rw [compressedHeat_eq_sum hH V carrier hLeft t, compressedHeat_eq_sum hK W carrier hRight t]
    exact Finset.sum_congr rfl fun x hx => congrArg (fun M => Real.exp (-t * x) • M) (hEq x hx)

/-- With an isometric port on each system, any `2*r+1` distinct positive
times determine every residue and the entire boundary heat curve. -/
theorem residue_and_heat_eq_of_positive_time_samples
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (V : Matrix n d ℂ) (W : Matrix m d ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (r : ℕ) (hDimH : Fintype.card n ≤ Fintype.card d + r)
    (hDimK : Fintype.card m ≤ Fintype.card d + r)
    (times : Finset ℝ) (hpositive : ∀ t ∈ times, 0 < t) (hcount : 2 * r + 1 ≤ times.card)
    (hsamples : ∀ t ∈ times, compressedHeat H V t = compressedHeat K W t) :
    (∀ x : ℝ, residue hH V x = residue hK W x) ∧
      (∀ t : ℝ, compressedHeat H V t = compressedHeat K W t) := by
  have hzero : (0 : ℝ) ∉ times := fun ht => (lt_irrefl 0) (hpositive 0 ht)
  have hc : 2 * r + 2 ≤ (insert (0 : ℝ) times).card := by
    rw [Finset.card_insert_of_notMem hzero]
    omega
  exact residue_and_heat_eq_of_time_samples hH hK V W hV hW r hDimH hDimK times hc hsamples

section RealHeat

private def complexify {a b : Type*} (A : Matrix a b ℝ) : Matrix a b ℂ :=
  A.map Complex.ofRealHom

private theorem complexify_injective {a b : Type*} :
    Function.Injective (complexify : Matrix a b ℝ → Matrix a b ℂ) := by
  intro A B h
  exact Matrix.ext fun i j => Complex.ofReal_injective
    (congrArg (fun M : Matrix a b ℂ => M i j) h)

private theorem complexify_mul {a b c : Type*} [Fintype b]
    (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    complexify (A * B) = complexify A * complexify B :=
  Matrix.map_mul (f := Complex.ofRealHom)

private theorem complexify_conjTranspose {a b : Type*} (A : Matrix a b ℝ) :
    complexify Aᴴ = (complexify A)ᴴ := by
  apply Matrix.ext
  intro i j
  simp [complexify, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal]

private theorem complexify_one {a : Type*} [DecidableEq a] :
    complexify (1 : Matrix a a ℝ) = 1 :=
  Matrix.map_one Complex.ofRealHom (map_zero _) (map_one _)

open scoped Matrix.Norms.Operator in
private theorem complexify_exp {a : Type*} [Fintype a] [DecidableEq a]
    (A : Matrix a a ℝ) :
    complexify (NormedSpace.exp A) = NormedSpace.exp (complexify A) := by
  let f : Matrix a a ℝ →+* Matrix a a ℂ := Complex.ofRealHom.mapMatrix
  have hf : Continuous f := by
    change Continuous (fun A : Matrix a a ℝ => A.map Complex.ofReal)
    exact continuous_id.matrix_map Complex.continuous_ofReal
  exact NormedSpace.map_exp f hf A

private theorem complexify_compressedHeat (L : Matrix n n ℝ) (V : Matrix n d ℝ) (t : ℝ) :
    complexify (compressedHeat L V t) = compressedHeat (complexify L) (complexify V) t := by
  have hScale : complexify ((-t) • L) = (-t) • complexify L := by
    apply Matrix.ext
    intro i j
    simp [complexify, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  simp only [compressedHeat, complexify_mul, complexify_conjTranspose, complexify_exp, hScale]

/-- The same sample bound for real symmetric generators and real isometric ports. -/
theorem real_heat_eq_of_positive_time_samples
    {L : Matrix n n ℝ} {M : Matrix m m ℝ} (hL : L.IsHermitian) (hM : M.IsHermitian)
    (V : Matrix n d ℝ) (W : Matrix m d ℝ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (r : ℕ) (hDimL : Fintype.card n ≤ Fintype.card d + r)
    (hDimM : Fintype.card m ≤ Fintype.card d + r)
    (times : Finset ℝ) (hpositive : ∀ t ∈ times, 0 < t) (hcount : 2 * r + 1 ≤ times.card)
    (hsamples : ∀ t ∈ times, compressedHeat L V t = compressedHeat M W t) :
    ∀ t : ℝ, compressedHeat L V t = compressedHeat M W t := by
  have hLc : (complexify L).IsHermitian := by
    rw [Matrix.IsHermitian, ← complexify_conjTranspose, hL.eq]
  have hMc : (complexify M).IsHermitian := by
    rw [Matrix.IsHermitian, ← complexify_conjTranspose, hM.eq]
  have hVc : (complexify V)ᴴ * complexify V = 1 := by
    rw [← complexify_conjTranspose, ← complexify_mul, hV, complexify_one]
  have hWc : (complexify W)ᴴ * complexify W = 1 := by
    rw [← complexify_conjTranspose, ← complexify_mul, hW, complexify_one]
  have he := (residue_and_heat_eq_of_positive_time_samples hLc hMc
    (complexify V) (complexify W) hVc hWc r hDimL hDimM times hpositive hcount
    (fun t ht => by rw [← complexify_compressedHeat, ← complexify_compressedHeat, hsamples t ht])).2
  intro t
  apply complexify_injective
  simpa only [complexify_compressedHeat] using he t

end RealHeat

private theorem spectralProjection_fixes_eigenvector (hH : H.IsHermitian)
    (x : ℝ) (v : n → ℂ) (hv : H *ᵥ v = (x : ℂ) • v) :
    spectralProjection hH x *ᵥ v = v := by
  let U := eigenU hH
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let z := Uᴴ *ᵥ v
  have hD : Uᴴ * H = D * Uᴴ := by
    calc
      _ = Uᴴ * (U * D * Uᴴ) := congrArg (fun A => Uᴴ * A) (eigenU_conj_diagonal hH)
      _ = _ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eigenU_star_mul, Matrix.one_mul]
  have hCoord : D *ᵥ z = (x : ℂ) • z := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, ← hD, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hMask : Matrix.diagonal (eigenMask hH x) *ᵥ z = z := by
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases hi : hH.eigenvalues i = x
    · simp [eigenMask, hi]
    · have hc := congrFun hCoord i
      change (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) *ᵥ z) i =
        (x : ℂ) * z i at hc
      rw [Matrix.mulVec_diagonal] at hc
      have hz : z i = 0 := by
        apply (mul_eq_zero.mp (_ : ((hH.eigenvalues i : ℂ) - (x : ℂ)) * z i = 0)).resolve_left
        · exact sub_ne_zero.mpr (fun he => hi (Complex.ofReal_injective he))
        · rw [sub_mul, hc, sub_self]
      simp [eigenMask, hi, hz]
  change (U * Matrix.diagonal (eigenMask hH x) * Uᴴ) *ᵥ v = v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, show Uᴴ *ᵥ v = z from rfl, hMask]
  dsimp only [z]
  rw [Matrix.mulVec_mulVec, eigenU_mul_star, Matrix.one_mulVec]

private theorem zero_mem_eigenvalueSet (hH : H.IsHermitian) [Nonempty n]
    (hOne : H *ᵥ (1 : n → ℂ) = 0) : (0 : ℝ) ∈ eigenvalueSet hH := by
  classical
  by_contra hz
  have hp : spectralProjection hH 0 = 0 := by
    simpa only [residue, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
      (residue_eq_zero_of_notMem hH (1 : Matrix n n ℂ) hz)
  have hFix := spectralProjection_fixes_eigenvector hH 0 1 (by simpa using hOne)
  rw [hp, Matrix.zero_mulVec] at hFix
  exact zero_ne_one (congrFun hFix (Classical.choice ‹Nonempty n›))

private theorem zero_projection_eq_constant (hH : H.IsHermitian) [Nonempty n]
    (hOne : H *ᵥ (1 : n → ℂ) = 0)
    (hKernel : ∀ v, H *ᵥ v = 0 → ∀ i j, v i = v j) :
    spectralProjection hH 0 = Matrix.of (fun _ _ => (Fintype.card n : ℂ)⁻¹) := by
  let P := spectralProjection hH 0
  have hHP : H * P = 0 := by
    simpa only [Complex.ofReal_zero, zero_smul] using mul_spectralProjection hH 0
  have hCols (j i k : n) : P i j = P k j := by
    have hz : H *ᵥ (P *ᵥ Pi.single j 1) = 0 := by
      rw [Matrix.mulVec_mulVec, hHP, Matrix.zero_mulVec]
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hKernel _ hz i k
  have hHerm : Pᴴ = P := (spectralProjection_posSemidef hH 0).isHermitian.eq
  have hEntry (i j : n) : star (P j i) = P i j :=
    congrArg (fun A : Matrix n n ℂ => A i j) hHerm
  have hRows (i j k : n) : P i j = P i k := by
    rw [← hEntry i j, ← hEntry i k, hCols i j k]
  have hFix : P *ᵥ (1 : n → ℂ) = 1 :=
    spectralProjection_fixes_eigenvector hH 0 1 (by simpa using hOne)
  have hCard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card n ≠ 0)
  apply Matrix.ext
  intro i j
  have hSum : (Fintype.card n : ℂ) * P i j = 1 := by
    calc
      _ = ∑ k : n, P i j := by simp
      _ = ∑ k : n, P i k := Finset.sum_congr rfl fun k _ => hRows i j k
      _ = 1 := by simpa [Matrix.mulVec, dotProduct] using congrFun hFix i
  change P i j = (Fintype.card n : ℂ)⁻¹
  exact (eq_div_iff hCard).mpr (by simpa [mul_comm] using hSum) |>.trans (one_div _)

private theorem sum_rank_residue_erase_zero (hH : H.IsHermitian) [Nonempty n]
    (hOne : H *ᵥ (1 : n → ℂ) = 0) (V : Matrix n d ℂ) (carrier : Finset ℝ) :
    (∑ x ∈ carrier.erase 0, (residue hH V x).rank) ≤ Fintype.card n - 1 := by
  have hZero := zero_mem_eigenvalueSet hH hOne
  change (0 : ℝ) ∈ Finset.univ.image hH.eigenvalues at hZero
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hZero
  refine (sum_rank_residue_le_card_filter hH V (carrier.erase 0)).trans ?_
  have hle : (Finset.univ.filter fun j => hH.eigenvalues j ∈ carrier.erase 0).card ≤
      (Finset.univ.erase i).card := by
    apply Finset.card_le_card
    intro j hj
    have hj0 := (Finset.mem_filter.mp hj).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    subst j
    exact (Finset.notMem_erase 0 carrier) (hi ▸ hj0)
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] using hle

private theorem sum_residue_erase_zero (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (carrier : Finset ℝ) (hcarrier : eigenvalueSet hH ⊆ carrier)
    (hz : (0 : ℝ) ∈ carrier) :
    (∑ x ∈ carrier.erase 0, residue hH V x) = Vᴴ * V - residue hH V 0 := by
  apply eq_sub_of_add_eq
  exact (Finset.sum_erase_add carrier (residue hH V) hz).trans (sum_residue hH V carrier hcarrier)

private theorem sum_heat_erase_zero (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (carrier : Finset ℝ) (hcarrier : eigenvalueSet hH ⊆ carrier)
    (hz : (0 : ℝ) ∈ carrier) (t : ℝ) :
    (∑ x ∈ carrier.erase 0, Real.exp (-t * x) • residue hH V x) =
      compressedHeat H V t - residue hH V 0 := by
  apply eq_sub_of_add_eq
  have he := Finset.sum_erase_add carrier (fun x => Real.exp (-t * x) • residue hH V x) hz
  rw [compressedHeat_eq_sum hH V carrier hcarrier t]
  simpa only [mul_zero, Real.exp_zero, one_smul] using he

private theorem sum_residue_change_port (hH : H.IsHermitian) (V : Matrix n d ℂ)
    (T : Matrix d d ℂ) (carrier : Finset ℝ) (f : ℝ → ℝ) :
    (∑ x ∈ carrier, f x • residue hH (V * T) x) =
      Tᴴ * (∑ x ∈ carrier, f x • residue hH V x) * T := by
  simp only [residue, Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

section Centered

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- A shared stationary atom can be removed before the rank estimate. The
whitening is by the inverse positive square root of the common centered Gram. -/
theorem heat_eq_of_samples_of_common_stationary_atom [Nonempty n] [Nonempty m]
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hH0 : H *ᵥ (1 : n → ℂ) = 0) (hK0 : K *ᵥ (1 : m → ℂ) = 0)
    (V : Matrix n d ℂ) (W : Matrix m d ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (S : Matrix d d ℂ) (hSH : residue hH V 0 = S) (hSK : residue hK W 0 = S)
    (hGram : (1 - S).PosDef)
    (r : ℕ) (hDimH : Fintype.card n - 1 ≤ Fintype.card d + r)
    (hDimK : Fintype.card m - 1 ≤ Fintype.card d + r)
    (times : Finset ℝ) (hpositive : ∀ t ∈ times, 0 < t) (hcount : 2 * r + 1 ≤ times.card)
    (hsamples : ∀ t ∈ times, compressedHeat H V t = compressedHeat K W t) :
    ∀ t : ℝ, compressedHeat H V t = compressedHeat K W t := by
  classical
  let carrier := eigenvalueSet hH ∪ eigenvalueSet hK
  have hLeft : eigenvalueSet hH ⊆ carrier := Finset.subset_union_left
  have hRight : eigenvalueSet hK ⊆ carrier := Finset.subset_union_right
  have hz : (0 : ℝ) ∈ carrier := hLeft (zero_mem_eigenvalueSet hH hH0)
  let R : Matrix d d ℂ := CFC.sqrt (1 - S)
  let T : Matrix d d ℂ := R⁻¹
  have hR : IsUnit R ∧ (1 - S) = R * R :=
    CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt.mp
      (Matrix.isStrictlyPositive_iff_posDef.mpr hGram)
  have hT : Tᴴ = T :=
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (1 - S))).isHermitian.inv).eq
  have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.1
  have hTR : T * R = 1 := Matrix.nonsing_inv_mul R hdet
  have hRT : R * T = 1 := Matrix.mul_nonsing_inv R hdet
  have hWhite : Tᴴ * (1 - S) * T = 1 := by
    rw [hT, hR.2, ← Matrix.mul_assoc T R R, hTR, Matrix.one_mul, hRT]
  have hTotalH : (∑ x ∈ carrier.erase 0, residue hH (V * T) x) = 1 := by
    have he := sum_residue_change_port hH V T (carrier.erase 0) (fun _ => 1)
    simp only [one_smul] at he
    rw [he, sum_residue_erase_zero hH V carrier hLeft hz, hV, hSH, hWhite]
  have hTotalK : (∑ x ∈ carrier.erase 0, residue hK (W * T) x) = 1 := by
    have he := sum_residue_change_port hK W T (carrier.erase 0) (fun _ => 1)
    simp only [one_smul] at he
    rw [he, sum_residue_erase_zero hK W carrier hRight hz, hW, hSK, hWhite]
  have hHeatH (t : ℝ) :
      (∑ x ∈ carrier.erase 0, Real.exp (-t * x) • residue hH (V * T) x) =
        Tᴴ * (compressedHeat H V t - S) * T := by
    rw [sum_residue_change_port, sum_heat_erase_zero hH V carrier hLeft hz, hSH]
  have hHeatK (t : ℝ) :
      (∑ x ∈ carrier.erase 0, Real.exp (-t * x) • residue hK (W * T) x) =
        Tᴴ * (compressedHeat K W t - S) * T := by
    rw [sum_residue_change_port, sum_heat_erase_zero hK W carrier hRight hz, hSK]
  have hPosDef : (∑ x ∈ carrier.erase 0, residue hH (V * T) x).PosDef := by
    rw [hTotalH]
    exact Matrix.PosDef.one
  have hEq := MatrixResidueArbitraryTimeUniqueness.eq_on_carrier_of_positive_time_samples
    (carrier.erase 0) times r hpositive hcount (residue hH (V * T)) (residue hK (W * T))
    (fun x _ => residue_posSemidef hH (V * T) x)
    (fun x _ => residue_posSemidef hK (W * T) x)
    hPosDef (hTotalH.trans hTotalK.symm)
    ((sum_rank_residue_erase_zero hH hH0 (V * T) carrier).trans hDimH)
    ((sum_rank_residue_erase_zero hK hK0 (W * T) carrier).trans hDimK)
    (fun t ht => by rw [hHeatH, hHeatK, hsamples t ht])
  intro t
  have hMoment :
      (∑ x ∈ carrier.erase 0, Real.exp (-t * x) • residue hH (V * T) x) =
        ∑ x ∈ carrier.erase 0, Real.exp (-t * x) • residue hK (W * T) x :=
    Finset.sum_congr rfl fun x hx => congrArg (fun A => Real.exp (-t * x) • A) (hEq x hx)
  rw [hHeatH, hHeatK, hT] at hMoment
  have hRecover (A : Matrix d d ℂ) : R * (T * A * T) * R = A := by
    calc
      _ = (R * T) * A * (T * R) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRT, hTR, Matrix.one_mul, Matrix.mul_one]
  have hUnwhite := congrArg (fun A : Matrix d d ℂ => R * A * R) hMoment
  rw [hRecover, hRecover] at hUnwhite
  exact sub_left_injective hUnwhite

end Centered

section Graph

/-- Insert port coordinates at their labeled vertices. -/
def portMatrix {𝕜 : Type*} [Zero 𝕜] [One 𝕜] (e : d ↪ n) : Matrix n d 𝕜 :=
  (1 : Matrix n n 𝕜).submatrix id e

private theorem port_compression {𝕜 : Type*} [RCLike 𝕜]
    (e : d ↪ n) (A : Matrix n n 𝕜) :
    (portMatrix e)ᴴ * A * portMatrix e = A.submatrix e e := by
  unfold portMatrix
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  have hLeft : ((1 : Matrix n n 𝕜).submatrix e id) * A = A.submatrix e id := by
    simpa only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] using
      Matrix.one_submatrix_mul e (Equiv.refl n) A
  rw [hLeft]
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp, Function.comp_id,
    Matrix.submatrix_submatrix] using
    Matrix.mul_submatrix_one (Equiv.refl n) e (A.submatrix e id)

private theorem port_isometry (e : d ↪ n) :
    (portMatrix (𝕜 := ℂ) e)ᴴ * portMatrix (𝕜 := ℂ) e = 1 := by
  simpa only [Matrix.mul_one, Matrix.submatrix_one_embedding] using
    port_compression e (1 : Matrix n n ℂ)

private def stationaryAtom (d : Type*) (N : ℕ) : Matrix d d ℂ :=
  Matrix.of fun _ _ => (N : ℂ)⁻¹

private theorem port_zero_residue (hH : H.IsHermitian) [Nonempty n]
    (hOne : H *ᵥ (1 : n → ℂ) = 0)
    (hKernel : ∀ v, H *ᵥ v = 0 → ∀ i j, v i = v j)
    (e : d ↪ n) :
    residue hH (portMatrix e) 0 = stationaryAtom d (Fintype.card n) := by
  rw [residue, port_compression, zero_projection_eq_constant hH hOne hKernel]
  rfl

private theorem centered_port_gram_posDef (hH : H.IsHermitian) [Nonempty n]
    (hOne : H *ᵥ (1 : n → ℂ) = 0)
    (hKernel : ∀ v, H *ᵥ v = 0 → ∀ i j, v i = v j)
    (e : d ↪ n) (hv : ∃ v : n, ∀ a : d, e a ≠ v) :
    (1 - stationaryAtom d (Fintype.card n)).PosDef := by
  obtain ⟨v, hv⟩ := hv
  let Q := spectralProjection hH 0
  let J : Matrix n d ℂ := portMatrix e
  let Z : Matrix n d ℂ := (1 - Q) * J
  have hQ : Qᴴ = Q := (spectralProjection_posSemidef hH 0).isHermitian.eq
  have hQ2 : Q * Q = Q := spectralProjection_mul_self hH 0
  have hCenter : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp [hQ2]
  have hJJ : Jᴴ * J = 1 := port_isometry e
  have hGram : Zᴴ * Z = 1 - stationaryAtom d (Fintype.card n) := by
    calc
      _ = Jᴴ * ((1 - Q) * (1 - Q)) * J := by
        dsimp only [Z]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ]
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hCenter, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]
        exact congrArg (fun A : Matrix d d ℂ => 1 - A) (port_zero_residue hH hOne hKernel e)
  have hZ : Function.Injective Z.mulVec := by
    intro a b hab
    have hDiff : Z *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    change ((1 - Q) * J) *ᵥ (a - b) = 0 at hDiff
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hDiff
    have hConst (i j : n) : (J *ᵥ (a - b)) i = (J *ᵥ (a - b)) j := by
      rw [hDiff]
      have hQconst := zero_projection_eq_constant hH hOne hKernel
      change Q = Matrix.of (fun _ _ => (Fintype.card n : ℂ)⁻¹) at hQconst
      rw [hQconst] <;> rfl
    have hHidden : (J *ᵥ (a - b)) v = 0 := by
      simp only [J, portMatrix, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
        id_eq, Matrix.one_apply]
      exact Finset.sum_eq_zero fun a _ => by rw [if_neg (Ne.symm (hv a)), zero_mul]
    have hZero : J *ᵥ (a - b) = 0 := funext fun i => (hConst i v).trans hHidden
    have hCancel : Jᴴ *ᵥ (J *ᵥ (a - b)) = 0 := by rw [hZero, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec] at hCancel
    exact sub_eq_zero.mp hCancel
  rw [← hGram]
  exact Matrix.PosDef.conjTranspose_mul_self Z hZ

private theorem complex_graph_kernel_constant (G : SimpleGraph n) [DecidableRel G.Adj]
    (hG : G.Connected) (v : n → ℂ) (hv : G.lapMatrix ℂ *ᵥ v = 0) (i j : n) :
    v i = v j := by
  have hRe : G.lapMatrix ℝ *ᵥ (fun k => (v k).re) = 0 := by
    funext k
    have he := congrArg Complex.re (congrFun hv k)
    rw [G.lapMatrix_mulVec_apply] at he ⊢
    simpa [Complex.sub_re, Complex.mul_re, Complex.re_sum] using he
  have hIm : G.lapMatrix ℝ *ᵥ (fun k => (v k).im) = 0 := by
    funext k
    have he := congrArg Complex.im (congrFun hv k)
    rw [G.lapMatrix_mulVec_apply] at he ⊢
    simpa [Complex.sub_im, Complex.mul_im, Complex.im_sum] using he
  exact Complex.ext
    ((G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hRe) i j (hG i j))
    ((G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hIm) i j (hG i j))

private theorem complexify_graph_lap (G : SimpleGraph n) [DecidableRel G.Adj] :
    complexify (G.lapMatrix ℝ) = G.lapMatrix ℂ := by
  apply Matrix.ext
  intro i j
  simp only [complexify, Matrix.map_apply, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    RingHom.map_sub]
  by_cases hij : i = j <;> by_cases hAdj : G.Adj i j <;> simp [hij, hAdj]

private theorem complexify_port (e : d ↪ n) :
    complexify (portMatrix e) = (portMatrix e : Matrix n d ℂ) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = e j <;> simp [complexify, portMatrix, Matrix.one_apply, h]

/-- The real boundary submatrix of the unit-mass graph heat kernel. -/
def graphBoundaryHeat (G : SimpleGraph n) [DecidableRel G.Adj]
    (e : d ↪ n) (t : ℝ) : Matrix d d ℝ :=
  (NormedSpace.exp ((-t) • G.lapMatrix ℝ)).submatrix e e

private theorem complexify_graph_heat (G : SimpleGraph n) [DecidableRel G.Adj]
    (e : d ↪ n) (t : ℝ) :
    complexify (graphBoundaryHeat G e t) =
      compressedHeat (G.lapMatrix ℂ) (portMatrix e) t := by
  have h := complexify_compressedHeat (G.lapMatrix ℝ) (portMatrix e) t
  unfold compressedHeat at h
  rw [port_compression, complexify_graph_lap, complexify_port] at h
  exact h

private theorem heat_eq_at_ports_of_constant_kernel [Nonempty n] [Nonempty m]
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hH0 : H *ᵥ (1 : n → ℂ) = 0) (hK0 : K *ᵥ (1 : m → ℂ) = 0)
    (hKernelH : ∀ v, H *ᵥ v = 0 → ∀ i j, v i = v j)
    (hKernelK : ∀ v, K *ᵥ v = 0 → ∀ i j, v i = v j)
    (e : d ↪ n) (e' : d ↪ m) (q : ℕ) (hq : 1 ≤ q)
    (hn : Fintype.card n = Fintype.card d + q)
    (hm : Fintype.card m = Fintype.card d + q)
    (times : Finset ℝ) (hpositive : ∀ t ∈ times, 0 < t) (hcount : 2 * q - 1 ≤ times.card)
    (hsamples : ∀ t ∈ times, compressedHeat H (portMatrix e) t =
      compressedHeat K (portMatrix e') t) :
    ∀ t : ℝ, compressedHeat H (portMatrix e) t = compressedHeat K (portMatrix e') t := by
  have hHidden : ∃ v : n, ∀ a : d, e a ≠ v := by
    by_contra! hs
    have hc := Fintype.card_le_of_surjective e (show Function.Surjective e from hs)
    omega
  have hN : Fintype.card m = Fintype.card n := hm.trans hn.symm
  have hSH := port_zero_residue hH hH0 hKernelH e
  have hSK := port_zero_residue hK hK0 hKernelK e'
  rw [hN] at hSK
  have hGram := centered_port_gram_posDef hH hH0 hKernelH e hHidden
  have hDimH : Fintype.card n - 1 ≤ Fintype.card d + (q - 1) := by omega
  have hDimK : Fintype.card m - 1 ≤ Fintype.card d + (q - 1) := by omega
  have hCount : 2 * (q - 1) + 1 ≤ times.card := by omega
  exact heat_eq_of_samples_of_common_stationary_atom hH hK hH0 hK0
    (portMatrix e) (portMatrix e') (port_isometry e) (port_isometry e')
    (stationaryAtom d (Fintype.card n)) hSH hSK hGram
    (q - 1) hDimH hDimK times hpositive hCount hsamples

/-- For connected simple graphs with unit vertex masses, equal total mass
and a common number `q ≥ 1` of hidden vertices, `2*q-1` distinct positive
samples determine the entire real boundary heat curve. The two graphs may
use different vertex-label types and different port embeddings. -/
theorem graph_boundary_heat_eq_of_positive_time_samples
    (G : SimpleGraph n) (G' : SimpleGraph m) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hG : G.Connected) (hG' : G'.Connected)
    (e : d ↪ n) (e' : d ↪ m) (q : ℕ) (hq : 1 ≤ q)
    (hn : Fintype.card n = Fintype.card d + q)
    (hm : Fintype.card m = Fintype.card d + q)
    (times : Finset ℝ) (hpositive : ∀ t ∈ times, 0 < t) (hcount : 2 * q - 1 ≤ times.card)
    (hsamples : ∀ t ∈ times, graphBoundaryHeat G e t = graphBoundaryHeat G' e' t) :
    ∀ t : ℝ, graphBoundaryHeat G e t = graphBoundaryHeat G' e' t := by
  letI : Nonempty n := hG.nonempty
  letI : Nonempty m := hG'.nonempty
  have he := heat_eq_at_ports_of_constant_kernel
    (G.isHermitian_lapMatrix ℂ) (G'.isHermitian_lapMatrix ℂ)
    (G.lapMatrix_mulVec_one_eq_zero ℂ) (G'.lapMatrix_mulVec_one_eq_zero ℂ)
    (complex_graph_kernel_constant G hG) (complex_graph_kernel_constant G' hG')
    e e' q hq hn hm times hpositive hcount
    (fun t ht => by
      rw [← complexify_graph_heat G e, ← complexify_graph_heat G' e', hsamples t ht])
  intro t
  apply complexify_injective
  simpa only [complexify_graph_heat] using he t

open D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation (wLap)
open D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
  (constProj proj_sq proj_mul lap_proj lap_one lap_hermitian)
open D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceConnectedSpectral (positive_shift)

private theorem weighted_kernel_constant {N : ℕ} (hN : 0 < N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (hG : G.Connected)
    (w : Sym2 (Fin N) → ℝ) (hw : ∀ i j, G.Adj i j → 0 < w s(i, j))
    (v : Fin N → ℝ) (hv : wLap G w *ᵥ v = 0) (i j : Fin N) :
    v i = v j := by
  let P := constProj N
  let L := wLap G w
  let z := v - P *ᵥ v
  have hL : L *ᵥ z = 0 := by
    dsimp only [z, L, P]
    rw [Matrix.mulVec_sub, hv, Matrix.mulVec_mulVec, lap_proj, Matrix.zero_mulVec, sub_self]
  have hP : P *ᵥ z = 0 := by
    dsimp only [z, P]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, proj_sq hN, sub_self]
  have hz : (L + P) *ᵥ z = (L + P) *ᵥ 0 := by
    rw [Matrix.add_mulVec, hL, hP, add_zero, Matrix.mulVec_zero]
  have hInject : Function.Injective (L + P).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (positive_shift hN G hG w hw).isUnit
  have hvP : v = P *ᵥ v := sub_eq_zero.mp (hInject hz)
  calc
    v i = (P *ᵥ v) i := congrFun hvP i
    _ = (P *ᵥ v) j := by
      dsimp only [P]
      rw [proj_mul, proj_mul]
    _ = v j := congrFun hvP.symm j

private theorem complexify_kernel_constant {A : Matrix n n ℝ}
    (hA : ∀ v, A *ᵥ v = 0 → ∀ i j, v i = v j)
    (v : n → ℂ) (hv : complexify A *ᵥ v = 0) (i j : n) :
    v i = v j := by
  have hRe : A *ᵥ (fun k => (v k).re) = 0 := by
    funext k
    have hk := congrArg Complex.re (congrFun hv k)
    simpa [Matrix.mulVec, dotProduct, complexify, Complex.re_sum, Complex.mul_re] using hk
  have hIm : A *ᵥ (fun k => (v k).im) = 0 := by
    funext k
    have hk := congrArg Complex.im (congrFun hv k)
    simpa [Matrix.mulVec, dotProduct, complexify, Complex.im_sum, Complex.mul_im] using hk
  exact Complex.ext (hA _ hRe i j) (hA _ hIm i j)

private theorem complexify_mulVec_one_eq_zero {A : Matrix n n ℝ}
    (hA : A *ᵥ (1 : n → ℝ) = 0) : complexify A *ᵥ (1 : n → ℂ) = 0 := by
  funext i
  have h := Complex.ofRealHom.map_mulVec A (1 : n → ℝ) i
  have hOne : (Complex.ofRealHom ∘ (1 : n → ℝ)) = (1 : n → ℂ) := by
    funext j
    simp only [Function.comp_apply, Pi.one_apply, map_one]
  rw [hA, hOne] at h
  simpa only [complexify, Pi.zero_apply, map_zero] using h.symm

private theorem complexify_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (complexify A).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_conjTranspose, hA.eq]

/-- Boundary heat for positive edge conductances and unit vertex masses. -/
def weightedGraphBoundaryHeat {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (w : Sym2 (Fin N) → ℝ) (e : d ↪ Fin N) (t : ℝ) : Matrix d d ℝ :=
  (NormedSpace.exp ((-t) • wLap G w)).submatrix e e

private theorem complexify_weighted_graph_heat {N : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (w : Sym2 (Fin N) → ℝ) (e : d ↪ Fin N) (t : ℝ) :
    complexify (weightedGraphBoundaryHeat G w e t) =
      compressedHeat (complexify (wLap G w)) (portMatrix e) t := by
  have h := complexify_compressedHeat (wLap G w) (portMatrix e) t
  unfold compressedHeat at h
  rw [port_compression, complexify_port] at h
  exact h

/-- Connected graphs with positive edge conductances, unit vertex masses,
`q ≥ 1` hidden vertices and the same labeled port type have the same whole
boundary heat curve if they agree at `2*q-1` distinct positive times. -/
theorem weighted_graph_boundary_heat_eq_of_positive_time_samples
    {N M : ℕ} (G : SimpleGraph (Fin N)) (G' : SimpleGraph (Fin M))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (hG : G.Connected) (hG' : G'.Connected)
    (w : Sym2 (Fin N) → ℝ) (w' : Sym2 (Fin M) → ℝ)
    (hw : ∀ i j, G.Adj i j → 0 < w s(i, j))
    (hw' : ∀ i j, G'.Adj i j → 0 < w' s(i, j))
    (e : d ↪ Fin N) (e' : d ↪ Fin M) (q : ℕ) (hq : 1 ≤ q)
    (hN : N = Fintype.card d + q) (hM : M = Fintype.card d + q)
    (times : Finset ℝ) (hpositive : ∀ t ∈ times, 0 < t) (hcount : 2 * q - 1 ≤ times.card)
    (hsamples : ∀ t ∈ times, weightedGraphBoundaryHeat G w e t =
      weightedGraphBoundaryHeat G' w' e' t) :
    ∀ t : ℝ, weightedGraphBoundaryHeat G w e t = weightedGraphBoundaryHeat G' w' e' t := by
  letI : Nonempty (Fin N) := hG.nonempty
  letI : Nonempty (Fin M) := hG'.nonempty
  have hNpos : 0 < N := by omega
  have hMpos : 0 < M := by omega
  have he := heat_eq_at_ports_of_constant_kernel
    (complexify_isHermitian (lap_hermitian G w)) (complexify_isHermitian (lap_hermitian G' w'))
    (complexify_mulVec_one_eq_zero (lap_one G w)) (complexify_mulVec_one_eq_zero (lap_one G' w'))
    (complexify_kernel_constant (weighted_kernel_constant hNpos G hG w hw))
    (complexify_kernel_constant (weighted_kernel_constant hMpos G' hG' w' hw'))
    e e' q hq (by simpa only [Fintype.card_fin] using hN)
    (by simpa only [Fintype.card_fin] using hM) times hpositive hcount
    (fun t ht => by
      rw [← complexify_weighted_graph_heat G w e, ← complexify_weighted_graph_heat G' w' e',
        hsamples t ht])
  intro t
  apply complexify_injective
  simpa only [complexify_weighted_graph_heat] using he t

end Graph

end BoundaryHeatArbitraryTimeUniqueness
