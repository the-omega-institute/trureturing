/- GID: D5/S3/Combinatorics/SpectralGraph/TwoPortHeatRealization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TwoPortHeatRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.MatrixExponential]
   utility: none
   digest: Two ports need six physical vertices at linear order five, even from four moments. -/

import Mathlib.Analysis.Analytic.Uniqueness
import D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization

/-! The hidden ground equations complete the action determined by the first four port moments. -/

set_option autoImplicit false

open Matrix
open scoped Matrix BigOperators

namespace D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization

noncomputable section

abbrev Port := Fin 2
abbrev Vertex (m : ℕ) := Port ⊕ Fin m
abbrev Generator (m : ℕ) := Matrix (Vertex m) (Vertex m) ℝ
abbrev PortMatrix := Matrix Port Port ℝ
private abbrev Pair := Port ⊕ Port
private abbrev HiddenBasis := Port ⊕ Unit

/-- The symmetric normalized generator and positive square roots of the masses.
The unit port entries fix the physical port insertion and readout. -/
def IsPhysical {m : ℕ} (S : Generator m) (z : Vertex m → ℝ) : Prop :=
  S.IsSymm ∧ (∀ i, 0 < z i) ∧ (∀ i, z (.inl i) = 1) ∧
    S *ᵥ z = 0 ∧ ∀ i j, i ≠ j → S i j ≤ 0

/-- Calibrated input at the two marked vertices. -/
def ports (m : ℕ) : Matrix (Vertex m) Port ℝ := Matrix.fromRows 1 0

/-- The moments include the stationary part of the heat kernel. -/
def moment {m : ℕ} (S : Generator m) (k : ℕ) : PortMatrix := (ports m)ᵀ * S ^ k * ports m

private def cross : Matrix (Fin 4) Port ℝ :=
  (1 / 1000 : ℝ) • !![1001, 1; 1001, 1001; 1, 1001; 1, 1]

private def hiddenFactor : Matrix (Fin 4) Port ℝ :=
  (1 / 1000 : ℝ) • !![1, 1001; 1, 1; 1001, 1; 1001, 1001]

private def shift {m : ℕ} (D : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) - D

private def hidden : Matrix (Fin 4) (Fin 4) ℝ := shift (hiddenFactor * hiddenFactorᵀ)

private def groundCoeff : Pair → ℝ :=
  Sum.elim (fun _ => 1 / 4) (fun _ => 1 / (4 * (1 - 2 * (1001 / 250000))))

private def hiddenFrame {m : ℕ} (X : Matrix (Fin m) Port ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) Pair ℝ :=
  Matrix.fromCols X (shift D * X)

private def hiddenGround : Fin 4 → ℝ := hiddenFrame cross hidden *ᵥ groundCoeff

private def within : PortMatrix := Matrix.diagonal (crossᵀ *ᵥ hiddenGround) + !![1, -1; -1, 1]

/-- The complete six-vertex generator with the rational couplings from the two-port example. -/
def generator : Generator 4 := Matrix.fromBlocks within (-crossᵀ) (-cross) hidden

/-- The positive ground gives masses zᵢ² and conductances −zᵢ Sᵢⱼ zⱼ. -/
def ground : Vertex 4 → ℝ := Sum.elim (fun _ => 1) hiddenGround

private theorem shift_hidden : shift hidden = hiddenFactor * hiddenFactorᵀ := by
  simp [hidden, shift]

private theorem hiddenGround_exact : hiddenGround =
    ![20875 / 41333, 124249 / 247998, 20875 / 41333, 126251 / 247998] := by
  funext i
  fin_cases i <;>
    norm_num [hiddenGround, hiddenFrame, shift_hidden, groundCoeff, hiddenFactor, cross,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Fin.sum_univ_four]

private theorem generator_symm : generator.IsSymm := by
  unfold generator within hidden shift
  change (Matrix.fromBlocks _ _ _ _)ᵀ = _
  rw [Matrix.fromBlocks_transpose]
  congr 1
  · rw [Matrix.transpose_add, Matrix.diagonal_transpose]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  all_goals simp [Matrix.transpose_sub, Matrix.transpose_mul]

private theorem generator_complete (i j : Vertex 4) (hne : i ≠ j) : generator i j < 0 := by
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    first | exact (hne rfl).elim | norm_num [generator, within, hidden, shift, cross,
      hiddenFactor, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.one_apply]

private theorem generator_physical : IsPhysical generator ground := by
  refine ⟨generator_symm, ?_, fun _ => rfl, ?_, fun i j h => (generator_complete i j h).le⟩
  · intro i
    rcases i with i | i
    · exact zero_lt_one
    · fin_cases i <;> norm_num [ground, hiddenGround_exact]
  · funext i
    rcases i with i | i <;> fin_cases i <;>
      norm_num [generator, ground, hiddenGround_exact, within, hidden, shift, cross,
        hiddenFactor, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply,
        Matrix.one_apply, Matrix.diagonal_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two, Fin.sum_univ_four]

private theorem mul_ports {m : ℕ} (A : Generator m) :
    A * ports m = Matrix.fromRows A.toBlocks₁₁ A.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [ports, Matrix.fromBlocks_mul_fromRows]

private theorem moment_eq_block {m : ℕ} (S : Generator m) (k : ℕ) :
    moment S k = (S ^ k).toBlocks₁₁ := by
  rw [moment, Matrix.mul_assoc, mul_ports, ports, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp

private theorem ports_power {m : ℕ} (S : Generator m) (k : ℕ) :
    S ^ k * ports m = Matrix.fromRows (moment S k) (S ^ k).toBlocks₂₁ := by
  rw [moment_eq_block, mul_ports]

private theorem block_data {m : ℕ} (S : Generator m) (hs : S.IsSymm) :
    S = Matrix.fromBlocks (moment S 1) (-(-S.toBlocks₂₁)ᵀ) S.toBlocks₂₁ S.toBlocks₂₂ := by
  rw [moment_eq_block, pow_one, Matrix.transpose_neg, neg_neg]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks S]
  congr 1
  ext i j
  exact hs.apply _ _

private def momentFrame {m : ℕ} (S : Generator m) : Matrix (Vertex m) Pair ℝ :=
  Matrix.fromCols (S ^ 1 * ports m) (S ^ 2 * ports m)

private theorem momentFrame_gram {m : ℕ} (S : Generator m) (hs : S.IsSymm) :
    (momentFrame S)ᵀ * momentFrame S =
      Matrix.fromBlocks (moment S 2) (moment S 3) (moment S 3) (moment S 4) := by
  have hp (a b : ℕ) : (S ^ a * ports m)ᵀ * (S ^ b * ports m) = moment S (a + b) := by
    rw [moment, Matrix.transpose_mul, Matrix.transpose_pow, hs.eq, pow_add]
    simp only [Matrix.mul_assoc]
  rw [momentFrame, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
  rw [hp, hp, hp, hp]

private def shiftCoefficients (C : PortMatrix) : Matrix Pair Pair ℝ :=
  Matrix.fromBlocks (-1) (-((4 : ℝ) • (1 : PortMatrix) + C)) 0 1

private theorem momentFrame_shift {m : ℕ} (S : Generator m) :
    momentFrame S * shiftCoefficients (moment S 1) =
      Matrix.fromRows (Matrix.fromCols (moment S 1) (moment S 2) * shiftCoefficients (moment S 1))
        (hiddenFrame (-S.toBlocks₂₁) S.toBlocks₂₂) := by
  rw [momentFrame, ports_power, ports_power, Matrix.fromCols_fromRows_eq_fromBlocks,
    ← Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromRows_mul]
  congr 1
  have hlow : (S ^ 2).toBlocks₂₁ =
      S.toBlocks₂₁ * moment S 1 + S.toBlocks₂₂ * S.toBlocks₂₁ := by
    rw [moment_eq_block, pow_one, pow_two]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks S, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₂₁]
  rw [pow_one, hlow, shiftCoefficients, Matrix.fromCols_mul_fromBlocks, hiddenFrame]
  congr 1
  · simp
  · simp only [shift, Matrix.mul_neg, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    abel

private theorem matching_hidden_gram {m : ℕ} (S : Generator m) (hs : S.IsSymm)
    (hm : ∀ k : Fin 5, moment S k = moment generator k) :
    (hiddenFrame (-S.toBlocks₂₁) S.toBlocks₂₂)ᵀ * hiddenFrame (-S.toBlocks₂₁) S.toBlocks₂₂ =
      (hiddenFrame cross hidden)ᵀ * hiddenFrame cross hidden := by
  have hm' (k : ℕ) (hk : k < 5) : moment S k = moment generator k := hm ⟨k, hk⟩
  let W := shiftCoefficients (moment S 1)
  have h : (momentFrame S * W)ᵀ * (momentFrame S * W) =
      (momentFrame generator * W)ᵀ * (momentFrame generator * W) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (momentFrame S)ᵀ, ← Matrix.mul_assoc (momentFrame generator)ᵀ,
      momentFrame_gram S hs, momentFrame_gram generator generator_symm,
      hm' 2 (by decide), hm' 3 (by decide), hm' 4 (by decide)]
  dsimp only [W] at h
  rw [momentFrame_shift S, hm' 1 (by decide), momentFrame_shift generator,
    hm' 2 (by decide)] at h
  simpa [generator, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows] using h

private def column {n : Type*} (v : n → ℝ) : Matrix n Unit ℝ := Matrix.of fun i _ => v i

private def firstPair : Matrix Pair Port ℝ := Matrix.fromRows 1 0
private def secondPair : Matrix Pair Port ℝ := Matrix.fromRows 0 1

private def basisCoefficients : Matrix Pair HiddenBasis ℝ :=
  Matrix.fromCols firstPair (column groundCoeff)

private def actionCoefficients : Matrix Pair HiddenBasis ℝ :=
  Matrix.fromCols secondPair (column ((4 : ℝ) • groundCoeff - firstPair *ᵥ (fun _ => 1)))

private def targetBasis : Matrix (Fin 4) HiddenBasis ℝ :=
  hiddenFrame cross hidden * basisCoefficients

private theorem hiddenFrame_first {m : ℕ} (X : Matrix (Fin m) Port ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) : hiddenFrame X D * firstPair = X := by
  simp [hiddenFrame, firstPair, Matrix.fromCols_mul_fromRows]

private theorem hiddenFrame_second {m : ℕ} (X : Matrix (Fin m) Port ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) : hiddenFrame X D * secondPair = shift D * X := by
  simp [hiddenFrame, secondPair, Matrix.fromCols_mul_fromRows]

private theorem mul_column {n k : Type*} [Fintype k] (A : Matrix n k ℝ) (v : k → ℝ) :
    A * column v = column (A *ᵥ v) := rfl

private theorem hiddenBasis_apply {m : ℕ} (X : Matrix (Fin m) Port ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) :
    hiddenFrame X D * basisCoefficients =
      Matrix.fromCols X (column (hiddenFrame X D *ᵥ groundCoeff)) := by
  rw [basisCoefficients, Matrix.mul_fromCols, hiddenFrame_first, mul_column]

private theorem hiddenBasis_action {m : ℕ} (X : Matrix (Fin m) Port ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ)
    (hg : D *ᵥ (hiddenFrame X D *ᵥ groundCoeff) = X *ᵥ (fun _ => 1)) :
    shift D * (hiddenFrame X D * basisCoefficients) = hiddenFrame X D * actionCoefficients := by
  rw [hiddenBasis_apply, actionCoefficients, Matrix.mul_fromCols, Matrix.mul_fromCols,
    hiddenFrame_second, mul_column, mul_column]
  congr 2
  rw [shift, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hg, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, hiddenFrame_first]

private def basisIndex : Fin 3 → HiddenBasis := ![.inl 0, .inl 1, .inr ()]

private theorem targetBasis_rank : targetBasis.rank = 3 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := targetBasis.submatrix Fin.castSucc basisIndex
  have hA : A = !![1001/1000, 1/1000, 20875/41333;
      1001/1000, 1001/1000, 124249/247998; 1/1000, 1001/1000, 20875/41333] := by
    change (hiddenFrame cross hidden * basisCoefficients).submatrix Fin.castSucc basisIndex = _
    rw [hiddenBasis_apply]
    change (Matrix.fromCols cross (column hiddenGround)).submatrix Fin.castSucc basisIndex = _
    rw [hiddenGround_exact]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [basisIndex, cross, column]
  have hu : IsUnit A := by
    rw [hA, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    norm_num [Matrix.det_fin_three]
  obtain ⟨u, hu⟩ := hu
  have hminor := Matrix.rank_submatrix_le targetBasis Fin.castSucc basisIndex
  change A.rank ≤ targetBasis.rank at hminor
  rw [← hu, Matrix.rank_unit] at hminor
  exact le_antisymm (by simpa using targetBasis.rank_le_card_width) (by simpa using hminor)

private theorem ground_blocks {m : ℕ} (S : Generator m) (z : Vertex m → ℝ)
    (hp : IsPhysical S z) :
    (-S.toBlocks₂₁)ᵀ *ᵥ (z ∘ Sum.inr) = moment S 1 *ᵥ (fun _ => 1) ∧
    S.toBlocks₂₂ *ᵥ (z ∘ Sum.inr) = (-S.toBlocks₂₁) *ᵥ (fun _ => 1) := by
  have hz : z = Sum.elim (fun _ => 1) (z ∘ Sum.inr) := by
    funext i
    cases i with
    | inl i => exact hp.2.2.1 i
    | inr i => rfl
  have he := hp.2.2.2.1
  nth_rw 1 [block_data S hp.1] at he
  rw [hz, Matrix.fromBlocks_mulVec] at he
  constructor
  · have he' := congrArg (fun w : Vertex m → ℝ => w ∘ Sum.inl) he
    change moment S 1 *ᵥ (fun _ => 1) + (-(-S.toBlocks₂₁)ᵀ) *ᵥ (z ∘ Sum.inr) = 0 at he'
    rwa [Matrix.neg_mulVec, ← sub_eq_add_neg, sub_eq_zero, eq_comm] at he'
  · have he' := congrArg (fun w : Vertex m → ℝ => w ∘ Sum.inr) he
    change S.toBlocks₂₁ *ᵥ (fun _ => 1) + S.toBlocks₂₂ *ᵥ (z ∘ Sum.inr) = 0 at he'
    rw [Matrix.neg_mulVec]
    exact eq_neg_of_add_eq_zero_right he'

private theorem hidden_symm {m : ℕ} (S : Generator m) (hs : S.IsSymm) :
    S.toBlocks₂₂.IsSymm := by
  ext i j
  exact hs.apply _ _

private theorem shift_symm {m : ℕ} {D : Matrix (Fin m) (Fin m) ℝ} (hs : D.IsSymm) :
    (shift D).IsSymm := by
  simp [Matrix.IsSymm, shift, Matrix.transpose_sub, Matrix.transpose_smul, hs.eq]

private theorem hidden_ground_readout {m : ℕ} (X : Matrix (Fin m) Port ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (C : PortMatrix) (g : Fin m → ℝ)
    (hs : D.IsSymm) (hg₁ : Xᵀ *ᵥ g = C *ᵥ (fun _ => 1))
    (hg₂ : D *ᵥ g = X *ᵥ (fun _ => 1)) :
    (hiddenFrame X D)ᵀ *ᵥ g = Sum.elim (C *ᵥ (fun _ => 1))
      ((4 : ℝ) • (C *ᵥ (fun _ => 1)) - (Xᵀ * X) *ᵥ (fun _ => 1)) := by
  rw [hiddenFrame, Matrix.transpose_fromCols, Matrix.fromRows_mulVec, Matrix.transpose_mul,
    (shift_symm hs).eq, ← Matrix.mulVec_mulVec, shift, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hg₂, Matrix.mulVec_sub, Matrix.mulVec_smul, hg₁, Matrix.mulVec_mulVec]

private theorem target_ground_blocks :
    crossᵀ *ᵥ hiddenGround = moment generator 1 *ᵥ (fun _ => 1) ∧
    hidden *ᵥ hiddenGround = cross *ᵥ (fun _ => 1) := by
  simpa [generator, ground, Function.comp_def] using
    ground_blocks generator ground generator_physical

private theorem cycle_bounds : FourPortHeatRealization.CycleBounds
    (((hiddenFrame cross hidden)ᵀ * hiddenFrame cross hidden).submatrix
      (![.inl 0, .inl 1, .inr 1, .inr 0] : Fin 4 → Pair)
      (![.inl 0, .inl 1, .inr 1, .inr 0] : Fin 4 → Pair)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      norm_num [hiddenFrame, shift_hidden, hiddenFactor, cross, Matrix.mul_apply,
        Fin.sum_univ_four, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · intro i
    fin_cases i <;>
      norm_num [hiddenFrame, shift_hidden, hiddenFactor, cross, Matrix.mul_apply,
        Fin.sum_univ_four, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  all_goals norm_num [hiddenFrame, shift_hidden, hiddenFactor, cross, Matrix.mul_apply,
    Fin.sum_univ_four, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem quad_transfer {n k : Type*} [Fintype n] [Fintype k] (A : Matrix n k ℝ)
    (P : Matrix n n ℝ) (w : k → ℝ) :
    (A *ᵥ w) ⬝ᵥ (P *ᵥ (A *ᵥ w)) = w ⬝ᵥ ((Aᵀ * (P * A)) *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem hidden_width (m : ℕ) (S : Generator m) (z : Vertex m → ℝ)
    (hp : IsPhysical S z) (hm : ∀ k : Fin 5, moment S k = moment generator k) : 4 ≤ m := by
  by_contra! hsmall
  let X : Matrix (Fin m) Port ℝ := -S.toBlocks₂₁
  let D := S.toBlocks₂₂
  let F := hiddenFrame X D
  let B := F * basisCoefficients
  let g := z ∘ Sum.inr
  have hm₁ : moment S 1 = moment generator 1 := hm ⟨1, by decide⟩
  have hG : Fᵀ * F = (hiddenFrame cross hidden)ᵀ * hiddenFrame cross hidden :=
    matching_hidden_gram S hp.1 hm
  have hBgram : Bᵀ * B = targetBasisᵀ * targetBasis := by
    unfold B targetBasis
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᵀ, ← Matrix.mul_assoc (hiddenFrame cross hidden)ᵀ, hG]
  have hB : B.rank = 3 := by
    rw [← Matrix.rank_transpose_mul_self, hBgram, Matrix.rank_transpose_mul_self, targetBasis_rank]
  have hr := B.rank_le_card_height
  simp only [hB, Fintype.card_fin] at hr
  have hm₃ : m = 3 := by omega
  have honto : Function.Surjective B.mulVec := Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by
    simp [hB, hm₃])
  have hFonto : Function.Surjective F.mulVec := by
    intro v
    obtain ⟨w, hw⟩ := honto v
    exact ⟨basisCoefficients *ᵥ w, by rwa [Matrix.mulVec_mulVec]⟩
  have hFinj : Function.Injective Fᵀ.mulVec := by
    obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hFonto
    intro v w he
    have h := congrArg (fun u => Rᵀ *ᵥ u) he
    simpa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hR] using h
  have hX : Xᵀ * X = crossᵀ * cross := by
    have h := congrArg (fun M : Matrix Pair Pair ℝ => M.toBlocks₁₁) hG
    simpa [F, hiddenFrame, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols] using h
  -- The ground equations determine its inner products with every column of F.
  have hg : g = F *ᵥ groundCoeff := by
    have hread := hidden_ground_readout X D (moment S 1) g (hidden_symm S hp.1)
      (ground_blocks S z hp).1 (ground_blocks S z hp).2
    have ht := hidden_ground_readout cross hidden (moment generator 1) hiddenGround
      (hidden_symm generator generator_symm) target_ground_blocks.1 target_ground_blocks.2
    apply hFinj
    rw [show Fᵀ *ᵥ g = _ from hread, hm₁, hX, ← ht, Matrix.mulVec_mulVec, hG]
    rw [hiddenGround, Matrix.mulVec_mulVec]
  -- The common coefficients also give the action of the shifted block on the spanning basis.
  have hq : Bᵀ * (shift D * B) = targetBasisᵀ * (shift hidden * targetBasis) := by
    unfold B targetBasis
    rw [hiddenBasis_action X D (hg ▸ (ground_blocks S z hp).2),
      hiddenBasis_action cross hidden target_ground_blocks.2]
    change (F * basisCoefficients)ᵀ * (F * actionCoefficients) = _
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᵀ, ← Matrix.mul_assoc (hiddenFrame cross hidden)ᵀ, hG]
  have hquad (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ (shift D *ᵥ v) := by
    obtain ⟨w, rfl⟩ := honto v
    rw [quad_transfer B (shift D) w, hq, ← quad_transfer targetBasis (shift hidden) w,
      shift_hidden, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hP (i j : Fin m) : 0 ≤ shift D i j := by
    by_cases h : i = j
    · subst j
      simpa [Matrix.mulVec, single_one_dotProduct, dotProduct_single_one]
        using hquad (Pi.single i 1)
    · simpa [D, shift, Matrix.sub_apply, Matrix.toBlocks₂₂, Matrix.one_apply, h]
        using neg_nonneg.mpr (hp.2.2.2.2 (.inr i) (.inr j) (by simpa using h))
  have hXnonneg (i : Fin m) (j : Port) : 0 ≤ X i j :=
    neg_nonneg.mpr (hp.2.2.2.2 (.inr i) (.inl j) (by simp))
  let order : Fin 4 → Pair := ![.inl 0, .inl 1, .inr 1, .inr 0]
  let A : Matrix (Fin 4) (Fin m) ℝ := Fᵀ.submatrix order id
  have hA (i j) : 0 ≤ A i j := by
    change 0 ≤ F j (order i)
    rcases h : order i with k | k
    · exact hXnonneg j k
    · change 0 ≤ ∑ l, shift D j l * X l k
      exact Finset.sum_nonneg fun l _ => mul_nonneg (hP j l) (hXnonneg l k)
  have hAG : A * Aᵀ = (Fᵀ * F).submatrix order order := by
    ext i j
    rfl
  exact (not_le_of_gt hsmall) (FourPortHeatRealization.cycle_gram_width m A hA (by
    rw [hAG, hG]
    exact cycle_bounds))


/-- The three-block Hankel matrix of the two calibrated port moments. -/
def hankel {m : ℕ} (S : Generator m) : Matrix (Fin 3 × Port) (Fin 3 × Port) ℝ :=
  Matrix.of fun i j => moment S (i.1.val + j.1.val) i.2 j.2

/-- The port columns and their first two generator iterates. -/
def reachFrame {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℝ)
    (B : Matrix n Port ℝ) : Matrix n (Fin 3 × Port) ℝ :=
  Matrix.of fun i j => (T ^ j.1.val * B) i j.2

private def outputFrame {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℝ)
    (C : Matrix Port n ℝ) : Matrix (Fin 3 × Port) n ℝ :=
  Matrix.of fun i j => (C * T ^ i.1.val) i.2 j

private theorem hankel_factor {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℝ)
    (B : Matrix n Port ℝ) (C : Matrix Port n ℝ) :
    outputFrame T C * reachFrame T B =
      Matrix.of fun (i j : Fin 3 × Port) => (C * T ^ (i.1.val + j.1.val) * B) i.2 j.2 := by
  ext i j
  change (outputFrame T C * reachFrame T B) i j =
    (C * T ^ (i.1.val + j.1.val) * B) i.2 j.2
  rw [pow_add, ← Matrix.mul_assoc C, Matrix.mul_assoc (C * _)]
  rfl

private theorem hankel_rank_eq (S : Generator 4) (hs : S.IsSymm) :
    (hankel S).rank = (reachFrame S (ports 4)).rank := by
  have h : outputFrame S (ports 4)ᵀ = (reachFrame S (ports 4))ᵀ := by
    ext i j
    change ((ports 4)ᵀ * S ^ i.1.val) i.2 j = (S ^ i.1.val * ports 4)ᵀ i.2 j
    rw [Matrix.transpose_mul, Matrix.transpose_pow, hs.eq]
  rw [← show outputFrame S (ports 4)ᵀ * reachFrame S (ports 4) = hankel S from
    hankel_factor S (ports 4) (ports 4)ᵀ, h, Matrix.rank_transpose_mul_self]

private def hiddenLift : Matrix (Fin 4) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 1; 1, -1, 1]
private def lift : Matrix (Vertex 4) (Vertex 3) ℝ := Matrix.fromBlocks 1 0 0 hiddenLift
private def firstThree : Vertex 3 → Vertex 4 := Sum.map id Fin.castSucc
private def reduced : Generator 3 := (generator * lift).submatrix firstThree id

private theorem invariant_lift : generator * lift = lift * reduced := by
  have hlast (j : Vertex 3) : (generator * lift) (.inr 3) j =
      (generator * lift) (.inr 0) j - (generator * lift) (.inr 1) j +
        (generator * lift) (.inr 2) j := by
    rcases j with j | j <;> fin_cases j <;>
      norm_num [generator, lift, hiddenLift, hidden, shift, cross, hiddenFactor,
        Matrix.mul_apply, Matrix.one_apply, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
        Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_three]
  unfold reduced
  generalize generator * lift = M at hlast ⊢
  ext i j
  rcases i with i | i
  · simp [lift, firstThree, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · fin_cases i <;>
      simp [lift, firstThree, hiddenLift, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_three, hlast, sub_eq_add_neg]

private theorem lift_ports : lift * ports 3 = ports 4 := by
  simp [lift, ports, Matrix.fromBlocks_mul_fromRows]

private theorem ports_lift : (ports 4)ᵀ * lift = (ports 3)ᵀ := by
  simp [lift, ports, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]

private theorem power_lift (k : ℕ) : generator ^ k * lift = lift * reduced ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, invariant_lift,
      Matrix.mul_assoc]

private theorem reach_lift (k : ℕ) : generator ^ k * ports 4 = lift * (reduced ^ k * ports 3) := by
  rw [← Matrix.mul_assoc, ← power_lift, Matrix.mul_assoc, lift_ports]

private theorem rank_lower : 5 ≤ (reachFrame generator (ports 4)).rank := by
  let inds : Vertex 3 → Fin 3 × Port := Sum.elim (fun j => (0, j)) ![(1, 0), (1, 1), (2, 0)]
  let H := (reachFrame generator (ports 4)).submatrix firstThree inds
  let minor : Matrix (Fin 3) (Fin 3) ℝ := H.toBlocks₂₂
  have h11 : H.toBlocks₁₁ = 1 := by
    ext i j
    change (generator ^ (0 : ℕ) * ports 4) (.inl i) j = _
    simp [ports]
  have h21 : H.toBlocks₂₁ = 0 := by
    ext i j
    change (generator ^ (0 : ℕ) * ports 4) (.inr i.castSucc) j = _
    simp [ports]
  have hminor : minor.det ≠ 0 := by
    norm_num [minor, H, reachFrame, firstThree, inds, ports, pow_two, generator,
      within, hidden, shift, cross, hiddenFactor, hiddenGround_exact, Matrix.det_fin_three,
      Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Matrix.toBlocks₂₂, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  have hdet : H.det ≠ 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks H, h11, h21, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, one_mul]
    exact hminor
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det (A := H)).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsub := Matrix.rank_submatrix_le (reachFrame generator (ports 4)) firstThree inds
  change H.rank ≤ _ at hsub
  rw [← hU, Matrix.rank_unit] at hsub
  simpa using hsub

/-- The reachable space spanned by all powers of the generator on the ports. -/
def reachable (S : Generator 4) : Submodule ℝ (Vertex 4 → ℝ) :=
  Submodule.span ℝ {v | ∃ (k : ℕ) (j : Port), v = (S ^ k * ports 4).col j}

private theorem reach_dimension : Module.finrank ℝ (reachable generator) = 5 := by
  have hl : (reachFrame generator (ports 4)).rank ≤ Module.finrank ℝ (reachable generator) := by
    rw [Matrix.rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, j⟩, rfl⟩
    exact Submodule.subset_span ⟨k.val, j, rfl⟩
  have hu : Module.finrank ℝ (reachable generator) ≤ lift.rank := by
    rw [Matrix.rank]
    apply Submodule.finrank_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨k, j, rfl⟩
    refine ⟨(reduced ^ k * ports 3).col j, ?_⟩
    rw [reach_lift]
    rfl
  have hb : lift.rank ≤ 5 := by simpa using lift.rank_le_card_width
  exact le_antisymm (hu.trans hb) (rank_lower.trans hl)

private theorem target_hankel_rank : (hankel generator).rank = 5 := by
  rw [hankel_rank_eq generator generator_symm]
  refine le_antisymm ?_ rank_lower
  have h : reachFrame generator (ports 4) = lift * reachFrame reduced (ports 3) := by
    ext i j
    change (generator ^ j.1.val * ports 4) i j.2 = _
    rw [reach_lift]
    rfl
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using lift.rank_le_card_width)

/-- The matrix impulse response for dynamics u′ = −Tu + Ba with readout Cu. -/
def linearHeat {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℝ)
    (B : Matrix n Port ℝ) (C : Matrix Port n ℝ) (t : ℝ) : PortMatrix :=
  C * NormedSpace.exp ((-t) • T) * B

/-- The heat response using the two calibrated ports. -/
def portHeat {m : ℕ} (S : Generator m) : ℝ → PortMatrix :=
  linearHeat S (ports m) (ports m)ᵀ

open scoped Matrix.Norms.Operator in
private def sandwich {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix Port n ℝ) (B : Matrix n Port ℝ) : Matrix n n ℝ →L[ℝ] PortMatrix :=
  (show Matrix n n ℝ →ₗ[ℝ] PortMatrix from
    { toFun := fun X => C * X * B
      map_add' := fun X Y => by
        change C * (X + Y) * B = C * X * B + C * Y * B
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        change C * (c • X) * B = c • (C * X * B)
        rw [Matrix.mul_smul, Matrix.smul_mul] }).toContinuousLinearMap

open scoped Matrix.Norms.Operator in
private theorem linearHeat_analytic {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ) :
    AnalyticOnNhd ℝ (linearHeat T B C) Set.univ := by
  intro t _
  have hin : AnalyticAt ℝ (fun s : ℝ => (-s) • T) t :=
    analyticAt_id.neg.smul analyticAt_const
  have he := (NormedSpace.exp_analytic (𝕂 := ℝ) ((-t) • T)).comp
    (f := fun s : ℝ => (-s) • T) hin
  exact ((sandwich C B).analyticAt _).comp he

open scoped Matrix.Norms.Operator in
private theorem heat_eq_of_positive {n d : Type*} [Fintype n] [DecidableEq n]
    [Fintype d] [DecidableEq d] (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ)
    (R : Matrix d d ℝ) (B' : Matrix d Port ℝ) (C' : Matrix Port d ℝ)
    (h : Set.EqOn (linearHeat T B C) (linearHeat R B' C') (Set.Ioi 0)) :
    linearHeat T B C = linearHeat R B' C' := by
  apply (linearHeat_analytic T B C).eq_of_eventuallyEq (linearHeat_analytic R B' C')
    (z₀ := 1)
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)] with t ht
  exact h ht

open scoped Matrix.Norms.Operator in
private theorem reduced_heat : portHeat reduced = portHeat generator := by
  funext t
  change sandwich (ports 3)ᵀ (ports 3) (NormedSpace.exp ((-t) • reduced)) =
    sandwich (ports 4)ᵀ (ports 4) (NormedSpace.exp ((-t) • generator))
  simp only [NormedSpace.exp_eq_tsum ℝ]
  rw [(sandwich (ports 3)ᵀ (ports 3)).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℝ) _),
    (sandwich (ports 4)ᵀ (ports 4)).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℝ) _)]
  apply tsum_congr
  intro k
  rw [map_smul, map_smul, smul_pow, smul_pow, map_smul, map_smul]
  congr 2
  change (ports 3)ᵀ * reduced ^ k * ports 3 = (ports 4)ᵀ * generator ^ k * ports 4
  rw [Matrix.mul_assoc, Matrix.mul_assoc, reach_lift, ← Matrix.mul_assoc (ports 4)ᵀ, ports_lift]

open scoped Matrix.Norms.Operator in
private theorem heat_deriv {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ) (t : ℝ) :
    deriv (linearHeat T B C) t = linearHeat T (-(T * B)) C t := by
  have h := ((sandwich C B).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (-T) t)).deriv
  change deriv (fun x : ℝ => C * NormedSpace.exp (x • (-T)) * B) t =
    C * (NormedSpace.exp (t • (-T)) * (-T)) * B at h
  unfold linearHeat
  simpa only [smul_neg, neg_smul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] using h

private theorem moments_of_heat {n d : Type*} [Fintype n] [DecidableEq n]
    [Fintype d] [DecidableEq d] (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ)
    (R : Matrix d d ℝ) (B' : Matrix d Port ℝ) (C' : Matrix Port d ℝ)
    (h : linearHeat T B C = linearHeat R B' C') (k : ℕ) :
    C * T ^ k * B = C' * R ^ k * B' := by
  induction k generalizing B B' with
  | zero => simpa [linearHeat] using congrFun h 0
  | succ k ih =>
    have hd : linearHeat T (-(T * B)) C = linearHeat R (-(R * B')) C' := by
      funext t
      rw [← heat_deriv, ← heat_deriv, h]
    have hneg := ih _ _ hd
    simpa only [pow_succ, Matrix.mul_assoc, Matrix.mul_neg, neg_inj] using hneg

/-- The consecutive calibrated moments through degree four. -/
def momentWindow {m : ℕ} (S : Generator m) : Fin 5 → PortMatrix := fun k => moment S k

/-- Exact stationary-inclusive linear order and the physical order bound from U₀ through U₄. -/
def ExactOrderGap (moments : Fin 5 → PortMatrix) : Prop :=
  IsPhysical generator ground ∧
  (∀ i j, i ≠ j → generator i j < 0) ∧
  Module.finrank ℝ (reachable generator) = 5 ∧ (hankel generator).rank = 5 ∧
  (∃ T : Generator 3, portHeat T = portHeat generator) ∧
  (∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) Port ℝ)
    (C : Matrix Port (Fin n) ℝ),
      Set.EqOn (linearHeat T B C) (portHeat generator) (Set.Ioi 0) → 5 ≤ n) ∧
  (∀ (m : ℕ) (S : Generator m) (z : Vertex m → ℝ), IsPhysical S z →
    (∀ k : Fin 5, moment S k = moments k) → 6 ≤ Fintype.card (Vertex m)) ∧
  (∀ (m : ℕ) (S : Generator m) (z : Vertex m → ℝ), IsPhysical S z →
    Set.EqOn (portHeat S) (portHeat generator) (Set.Ioi 0) → 6 ≤ Fintype.card (Vertex m))

/-- A complete six-vertex network has stationary-inclusive Hankel and linear order five.
Every physical competitor with the same moments through degree four needs at least six vertices. -/
theorem exact_order_gap : ExactOrderGap (momentWindow generator) := by
  refine ⟨generator_physical, generator_complete, reach_dimension, target_hankel_rank,
    ⟨reduced, reduced_heat⟩, ?_, ?_, ?_⟩
  · intro n T B C he
    have h := heat_eq_of_positive T B C generator (ports 4) (ports 4)ᵀ he
    have hm := moments_of_heat T B C generator (ports 4) (ports 4)ᵀ h
    have hf : outputFrame T C * reachFrame T B = hankel generator := by
      rw [hankel_factor]
      ext i j
      exact congrFun (congrFun (hm (i.1.val + j.1.val)) i.2) j.2
    calc
      5 = (outputFrame T C * reachFrame T B).rank := by rw [hf, target_hankel_rank]
      _ ≤ (outputFrame T C).rank := Matrix.rank_mul_le_left _ _
      _ ≤ n := by simpa using (outputFrame T C).rank_le_card_width
  · intro m S z hp hm
    have h := hidden_width m S z hp hm
    simpa using (show 6 ≤ 2 + m by omega)
  · intro m S z hp hh
    have h := heat_eq_of_positive S (ports m) (ports m)ᵀ generator (ports 4) (ports 4)ᵀ hh
    have hm := moments_of_heat S (ports m) (ports m)ᵀ generator (ports 4) (ports 4)ᵀ h
    have h := hidden_width m S z hp (fun k => hm k)
    simpa using (show 6 ≤ 2 + m by omega)

#print axioms exact_order_gap

end

end D5.S3.Combinatorics.SpectralGraph.TwoPortHeatRealization
