/- GID: D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.claim; result=D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.result; claim=D5/S3/Quantum/Measurement/ExtremePOVMRankThreeThreeTwoSix.claim
   digest: An extreme eight-outcome POVM on complex seven-space has ranks (3,3,2,2,2,2,2,2). -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix

/-- Extremality in the convex set of finite POVMs. -/
def IsExtreme {n : ℕ} (M : Fin n → Matrix (Fin 7) (Fin 7) ℂ) : Prop :=
  IsPOVM M ∧
    ∀ A B : Fin n → Matrix (Fin 7) (Fin 7) ℂ,
      IsPOVM A → IsPOVM B →
      (∀ j, M j = (1 / 2 : ℂ) • (A j + B j)) → A = M ∧ B = M

/-- The non-rank-one part of the rank vector of a POVM. -/
def bigRanks {n : ℕ} (M : Fin n → Matrix (Fin 7) (Fin 7) ℂ) : Multiset ℕ :=
  (Finset.univ.val.map (fun j => (M j).rank)).filter (fun r => 2 ≤ r)

def claim : Prop :=
  ∀ (n : ℕ) (M : Fin n → Matrix (Fin 7) (Fin 7) ℂ),
    IsPOVM M → IsExtreme M →
      bigRanks M ≠ ({3, 3, 2, 2, 2, 2, 2, 2} : Multiset ℕ)

private def vector (a₀ a₁ a₂ f₀ f₁ f₂ g : ℂ) : Fin 7 → ℂ :=
  ![a₀, a₁, a₂, f₀, f₁, f₂, g]

private def blocks : Fin 8 → Finset (Fin 7 → ℂ) := ![
  {vector 1 0 0 0 0 0 0, vector 0 1 0 0 0 0 0, vector 0 0 1 0 0 0 0},
  {vector 0 0 0 1 0 0 0, vector 0 0 0 0 1 0 0, vector 0 0 0 0 0 1 0},
  {vector 1 0 0 1 0 0 0, vector 0 1 0 0 1 0 0},
  {vector 1 0 0 Complex.I 0 0 0, vector 0 1 0 0 Complex.I 0 0},
  {vector 1 0 0 1 0 0 1, vector 0 0 1 0 0 1 0},
  {vector 1 0 0 Complex.I 0 0 1, vector 0 0 1 0 0 Complex.I 0},
  {vector 0 1 0 0 1 0 1, vector 0 0 1 0 0 1 1},
  {vector 0 1 0 0 Complex.I 0 1, vector 0 0 1 0 0 Complex.I 1}
]

private def effect (j : Fin 8) : Matrix (Fin 7) (Fin 7) ℂ :=
  ∑ b : blocks j, Matrix.vecMulVec b.1 (star b.1)

private def frame : Matrix (Fin 7) (Fin 7) ℂ := ∑ j, effect j

set_option maxHeartbeats 2000000 in
private theorem frame_posDef : frame.PosDef := by
  classical
  have hpsd : frame.PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro j hj
    apply Matrix.posSemidef_sum Finset.univ
    intro b hb
    exact Matrix.posSemidef_vecMulVec_self_star b.1
  have hframe : frame =
      !![5, 0, 0, 2 - 2 * Complex.I, 0, 0, 2;
        0, 5, 0, 0, 2 - 2 * Complex.I, 0, 2;
        0, 0, 5, 0, 0, 2 - 2 * Complex.I, 2;
        2 + 2 * Complex.I, 0, 0, 5, 0, 0, 1 + Complex.I;
        0, 2 + 2 * Complex.I, 0, 0, 5, 0, 1 + Complex.I;
        0, 0, 2 + 2 * Complex.I, 0, 0, 5, 1 + Complex.I;
        2, 2, 2, 1 - Complex.I, 1 - Complex.I, 1 - Complex.I, 6] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [frame, effect, blocks, vector, Matrix.sum_apply,
        Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_succ]
    all_goals ring
  apply hpsd.posDef_iff_mulVec_injective.mpr
  rw [hframe]
  intro x y hxy
  have hz :
      (!![5, 0, 0, 2 - 2 * Complex.I, 0, 0, 2;
        0, 5, 0, 0, 2 - 2 * Complex.I, 0, 2;
        0, 0, 5, 0, 0, 2 - 2 * Complex.I, 2;
        2 + 2 * Complex.I, 0, 0, 5, 0, 0, 1 + Complex.I;
        0, 2 + 2 * Complex.I, 0, 0, 5, 0, 1 + Complex.I;
        0, 0, 2 + 2 * Complex.I, 0, 0, 5, 1 + Complex.I;
        2, 2, 2, 1 - Complex.I, 1 - Complex.I, 1 - Complex.I, 6] :
        Matrix (Fin 7) (Fin 7) ℂ) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub]
    apply sub_eq_zero.mpr
    simpa using hxy
  have h0 := congr_fun hz 0
  have h1 := congr_fun hz 1
  have h2 := congr_fun hz 2
  have h3 := congr_fun hz 3
  have h4 := congr_fun hz 4
  have h5 := congr_fun hz 5
  have h6 := congr_fun hz 6
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.sub_apply]
    at h0 h1 h2 h3 h4 h5 h6
  have hd0 : 17 * (x 3 - y 3) + (1 + Complex.I) * (x 6 - y 6) = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      5 * h3 - (2 + 2 * Complex.I) * h0
  have hd1 : 17 * (x 4 - y 4) + (1 + Complex.I) * (x 6 - y 6) = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      5 * h4 - (2 + 2 * Complex.I) * h1
  have hd2 : 17 * (x 5 - y 5) + (1 + Complex.I) * (x 6 - y 6) = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      5 * h5 - (2 + 2 * Complex.I) * h2
  have ha0 : 85 * (x 0 - y 0) + 30 * (x 6 - y 6) = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      17 * h0 - (2 - 2 * Complex.I) * hd0
  have ha1 : 85 * (x 1 - y 1) + 30 * (x 6 - y 6) = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      17 * h1 - (2 - 2 * Complex.I) * hd1
  have ha2 : 85 * (x 2 - y 2) + 30 * (x 6 - y 6) = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      17 * h2 - (2 - 2 * Complex.I) * hd2
  have hg' : 60 * (x 6 - y 6) = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      17 * h6 - (2 / 5 : ℂ) * ha0 - (2 / 5 : ℂ) * ha1 - (2 / 5 : ℂ) * ha2
      - (1 - Complex.I) * hd0 - (1 - Complex.I) * hd1 - (1 - Complex.I) * hd2
  have hg : x 6 - y 6 = 0 := by
    rcases mul_eq_zero.mp hg' with h | h
    · norm_num at h
    · exact h
  have hd0' : x 3 - y 3 = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      (1 / 17 : ℂ) * hd0 - ((1 + Complex.I) / 17) * hg
  have hd1' : x 4 - y 4 = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      (1 / 17 : ℂ) * hd1 - ((1 + Complex.I) / 17) * hg
  have hd2' : x 5 - y 5 = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      (1 / 17 : ℂ) * hd2 - ((1 + Complex.I) / 17) * hg
  have ha0' : x 0 - y 0 = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      (1 / 85 : ℂ) * ha0 - (6 / 17 : ℂ) * hg
  have ha1' : x 1 - y 1 = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      (1 / 85 : ℂ) * ha1 - (6 / 17 : ℂ) * hg
  have ha2' : x 2 - y 2 = 0 := by
    linear_combination (norm := (ring_nf; try simp [Complex.I_sq]))
      (1 / 85 : ℂ) * ha2 - (6 / 17 : ℂ) * hg
  funext i
  fin_cases i
  · exact sub_eq_zero.mp ha0'
  · exact sub_eq_zero.mp ha1'
  · exact sub_eq_zero.mp ha2'
  · exact sub_eq_zero.mp hd0'
  · exact sub_eq_zero.mp hd1'
  · exact sub_eq_zero.mp hd2'
  · exact sub_eq_zero.mp hg

private theorem normalizer_exists :
    ∃ R : Matrix (Fin 7) (Fin 7) ℂ, IsUnit R.det ∧ R * frame * Rᴴ = 1 := by
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self.mp
    frame_posDef.isStrictlyPositive) with ⟨b, hb, hframe⟩
  have hdet : IsUnit b.det := (Matrix.isUnit_iff_isUnit_det b).mp hb
  have hstardet : IsUnit bᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  refine ⟨b⁻¹, ?_, ?_⟩
  · exact Matrix.isUnit_iff_isUnit_det _ |>.mp (Matrix.isUnit_nonsing_inv_iff.mpr hb)
  · rw [hframe, Matrix.conjTranspose_nonsing_inv]
    calc
      b⁻¹ * (b * bᴴ) * bᴴ⁻¹ = (b⁻¹ * b) * (bᴴ * bᴴ⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [Matrix.nonsing_inv_mul b hdet, Matrix.mul_nonsing_inv bᴴ hstardet]
        simp

private def normalizer : Matrix (Fin 7) (Fin 7) ℂ :=
  Classical.choose normalizer_exists

private theorem normalizer_unit : IsUnit normalizer.det := by
  exact (Classical.choose_spec normalizer_exists).1

private theorem normalizer_identity : normalizer * frame * normalizerᴴ = 1 := by
  exact (Classical.choose_spec normalizer_exists).2

private def witness (j : Fin 8) : Matrix (Fin 7) (Fin 7) ℂ :=
  normalizer * effect j * normalizerᴴ

private theorem effect_posSemidef (j : Fin 8) : (effect j).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro b hb
  exact Matrix.posSemidef_vecMulVec_self_star b.1

private theorem witness_posSemidef (j : Fin 8) : (witness j).PosSemidef := by
  exact (effect_posSemidef j).mul_mul_conjTranspose_same normalizer

private theorem witness_sum : ∑ j, witness j = 1 := by
  simp only [witness]
  simp_rw [Matrix.mul_assoc]
  rw [← Matrix.mul_sum, ← Matrix.sum_mul, show (∑ j, effect j) = frame from rfl]
  simpa only [Matrix.mul_assoc] using normalizer_identity

private theorem witness_povm : IsPOVM witness := by
  exact ⟨witness_posSemidef, witness_sum⟩

private def columns (j : Fin 8) : Matrix (Fin 7) (blocks j) ℂ := fun i b => b.1 i

private def left (j : Fin 8) : Matrix (blocks j) (Fin 7) ℂ :=
  fun b i => if (if j = 1 then 3 ≤ i.val else i.val < 3) then star (b.1 i) else 0

set_option maxHeartbeats 2000000 in
private theorem left_columns (j : Fin 8) : left j * columns j = 1 := by
  classical
  ext ⟨b, hb⟩ ⟨c, hc⟩
  fin_cases j <;> norm_num [blocks] at hb hc
  all_goals
    rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
    all_goals norm_num [left, columns, vector, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Subtype.mk.injEq, funext_iff, Fin.forall_fin_succ]

private theorem effect_columns (j : Fin 8) : effect j = columns j * (columns j)ᴴ := by
  ext i k
  change (∑ b : blocks j, Matrix.vecMulVec b.1 (star b.1)) i k = _
  simp only [Matrix.sum_apply, columns, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Pi.star_apply]

private theorem effect_rank (j : Fin 8) : (effect j).rank = (blocks j).card := by
  classical
  rw [effect_columns, Matrix.rank_self_mul_conjTranspose]
  apply le_antisymm
  · simpa using (columns j).rank_le_card_width
  · have h := Matrix.rank_mul_le_right (left j) (columns j)
    rw [left_columns, Matrix.rank_one] at h
    simpa using h

private theorem witness_rank (j : Fin 8) : (witness j).rank = (effect j).rank := by
  have hstar : IsUnit normalizerᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact normalizer_unit.star
  rw [witness, Matrix.mul_assoc,
    Matrix.rank_mul_eq_right_of_isUnit_det normalizer (effect j * normalizerᴴ)
      normalizer_unit,
    Matrix.rank_mul_eq_left_of_isUnit_det normalizerᴴ (effect j) hstar]

private theorem witness_bigRanks :
    bigRanks witness = ({3, 3, 2, 2, 2, 2, 2, 2} : Multiset ℕ) := by
  classical
  have h : (fun j : Fin 8 => (witness j).rank) = ![3, 3, 2, 2, 2, 2, 2, 2] := by
    funext j
    rw [witness_rank, effect_rank]
    fin_cases j <;> norm_num [blocks, vector]
  change (Finset.univ.val.map (fun j => (witness j).rank)).filter (fun r => 2 ≤ r) = _
  rw [h]
  decide

private theorem within_block_product_independent :
    LinearIndependent ℂ
      (fun p : Σ j : Fin 8, (blocks j × blocks j) =>
        Matrix.vecMulVec p.2.1.1 (star p.2.2.1)) := by sorry

private def normalizeMap :
  Matrix (Fin 7) (Fin 7) ℂ →ₗ[ℂ] Matrix (Fin 7) (Fin 7) ℂ :=
  (mulRightLinearMap (Fin 7) ℂ normalizerᴴ).comp
    (mulLeftLinearMap (Fin 7) ℂ normalizer)

private theorem normalizeMap_ker : LinearMap.ker normalizeMap = ⊥ := by
  apply le_antisymm
  · intro X hX
    have hstar : IsUnit normalizerᴴ.det := by
      rw [Matrix.det_conjTranspose]
      exact normalizer_unit.star
    have hright := Matrix.mul_left_injective_of_inv (l := Fin 7) normalizerᴴ (normalizerᴴ)⁻¹
      (Matrix.mul_nonsing_inv normalizerᴴ hstar)
    have hleft := Matrix.mul_right_injective_of_inv (l := Fin 7) normalizer⁻¹ normalizer
      (Matrix.nonsing_inv_mul normalizer normalizer_unit)
    apply hleft
    apply hright
    simpa [normalizeMap, mulLeftLinearMap, mulRightLinearMap] using hX
  · exact bot_le

private theorem normalized_product_independent :
    LinearIndependent ℂ
      (fun p : Σ j : Fin 8, (blocks j × blocks j) =>
        normalizer * Matrix.vecMulVec p.2.1.1 (star p.2.2.1) * normalizerᴴ) := by
  simpa [normalizeMap, mulLeftLinearMap, mulRightLinearMap,
    Function.comp_def] using
    within_block_product_independent.map' normalizeMap normalizeMap_ker

private theorem supported_decomposition {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : Matrix (Fin 7) ι ℂ) (w : Matrix ι (Fin 7) ℂ) (hwu : w * u = 1)
    (a b : Matrix (Fin 7) (Fin 7) ℂ) (ha : a.PosSemidef) (hb : b.PosSemidef)
    (hm : u * uᴴ = (1 / 2 : ℂ) • (a + b)) :
    a - u * uᴴ = u * (w * (a - u * uᴴ) * wᴴ) * uᴴ := by
  have hs : a + b = (2 : ℂ) • (u * uᴴ) := by
    rw [hm, smul_smul]
    norm_num
  have hk : ∀ y, uᴴ *ᵥ y = 0 → a *ᵥ y = 0 := by
    intro y hy
    apply ha.dotProduct_mulVec_zero_iff.mp
    have hq : star y ⬝ᵥ a *ᵥ y + star y ⬝ᵥ b *ᵥ y = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hs, Matrix.smul_mulVec,
        ← Matrix.mulVec_mulVec, hy]
      simp
    exact (add_eq_zero_iff_of_nonneg (ha.dotProduct_mulVec_nonneg y)
      (hb.dotProduct_mulVec_nonneg y)).mp hq |>.1
  let d := a - u * uᴴ
  have hd : d.IsHermitian := ha.isHermitian.sub (isHermitian_mul_conjTranspose_self u)
  have hdk : ∀ y, uᴴ *ᵥ y = 0 → d *ᵥ y = 0 := by
    intro y hy
    change (a - u * uᴴ) *ᵥ y = 0
    rw [Matrix.sub_mulVec, hk y hy, ← Matrix.mulVec_mulVec, hy]
    simp
  have hstar : uᴴ * wᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hwu, Matrix.conjTranspose_one]
  have hr : d = d * wᴴ * uᴴ := by
    apply Matrix.ext_iff_mulVec.mpr
    intro z
    have hz : uᴴ *ᵥ (z - wᴴ *ᵥ (uᴴ *ᵥ z)) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec, sub_self]
    have hh := hdk _ hz
    rw [Matrix.mulVec_sub] at hh
    simpa only [← Matrix.mulVec_mulVec] using sub_eq_zero.mp hh
  have hl : d = u * w * d := by
    have hh := congrArg Matrix.conjTranspose hr
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hd.eq, Matrix.mul_assoc] using hh
  change d = u * (w * d * wᴴ) * uᴴ
  calc
    d = u * w * d := hl
    _ = u * w * (d * wᴴ * uᴴ) := congrArg (fun t => u * w * t) hr
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem normalized_expansion (j : Fin 8)
    (x : Matrix (blocks j) (blocks j) ℂ) :
    (normalizer * columns j) * x * (normalizer * columns j)ᴴ =
      ∑ b : blocks j, ∑ c : blocks j, x b c •
        (normalizer * Matrix.vecMulVec b.1 (star c.1) * normalizerᴴ) := by
  have hx : columns j * x * (columns j)ᴴ =
      ∑ b : blocks j, ∑ c : blocks j, x b c • Matrix.vecMulVec b.1 (star c.1) := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, columns, Pi.star_apply, smul_eq_mul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  calc
    _ = normalizeMap (columns j * x * (columns j)ᴴ) := by
      change _ = normalizer * (columns j * x * (columns j)ᴴ) * normalizerᴴ
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hx]
      simp only [map_sum, map_smul]
      rfl

private theorem decomposition_eq_of_product_independence
    (A B : Fin 8 → Matrix (Fin 7) (Fin 7) ℂ)
    (hA : IsPOVM A) (hB : IsPOVM B)
    (hmid : ∀ j, witness j = (1 / 2 : ℂ) • (A j + B j)) :
    A = witness ∧ B = witness := by
  classical
  let u := fun j => normalizer * columns j
  let w := fun j => left j * normalizer⁻¹
  let x := fun j => w j * (A j - witness j) * (w j)ᴴ
  have hwu : ∀ j, w j * u j = 1 := by
    intro j
    change (left j * normalizer⁻¹) * (normalizer * columns j) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc normalizer⁻¹ normalizer,
      Matrix.nonsing_inv_mul normalizer normalizer_unit, Matrix.one_mul, left_columns]
  have heffect : ∀ j, witness j = u j * (u j)ᴴ := by
    intro j
    change normalizer * effect j * normalizerᴴ = _
    rw [effect_columns]
    dsimp only [u]
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hrep : ∀ j, A j - witness j =
      ∑ b : blocks j, ∑ c : blocks j, x j b c •
        (normalizer * Matrix.vecMulVec b.1 (star c.1) * normalizerᴴ) := by
    intro j
    have hh := supported_decomposition (u j) (w j) (hwu j) (A j) (B j)
      (hA.1 j) (hB.1 j) ((heffect j).symm.trans (hmid j))
    rw [← heffect j] at hh
    exact hh.trans (normalized_expansion j (x j))
  have hsum : (∑ p : Σ j : Fin 8, (blocks j × blocks j),
      x p.1 p.2.1 p.2.2 •
        (normalizer * Matrix.vecMulVec p.2.1.1 (star p.2.2.1) * normalizerᴴ)) = 0 := by
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_prod_type, ← hrep]
    rw [Finset.sum_sub_distrib, hA.2, witness_sum, sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp normalized_product_independent _ hsum
  have hx : ∀ j, x j = 0 := by
    intro j
    ext b c
    exact hcoeff ⟨j, b, c⟩
  have ha : A = witness := by
    funext j
    apply sub_eq_zero.mp
    rw [hrep j, hx j]
    simp
  refine ⟨ha, ?_⟩
  funext j
  have hm := hmid j
  rw [ha] at hm
  have he := congrArg (fun t => (2 : ℂ) • t) hm
  norm_num [smul_smul] at he
  have he' : witness j + witness j = witness j + B j := by
    simpa only [two_smul] using he
  exact (add_left_cancel he').symm

private theorem witness_extreme : IsExtreme witness := by
  refine ⟨witness_povm, ?_⟩
  intro A B hA hB hmid
  exact decomposition_eq_of_product_independence A B hA hB hmid

theorem result : ¬ claim := by
  intro h
  exact h 8 witness witness_povm witness_extreme witness_bigRanks

end D5.S3.Quantum.Measurement.ExtremePOVMRankThreeThreeTwoSix
