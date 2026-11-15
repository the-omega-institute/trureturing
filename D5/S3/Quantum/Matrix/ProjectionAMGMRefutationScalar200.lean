/- GID: D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.claimScalar; result=D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.result; claim=D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.claimScalar
   digest: A finite real unit-column basis at dimension 200 refutes the original all-order scalar projection inequality. -/

/- Fixed scalar n=200 counterexample for the all-order coordinate-descent
   projection AM-GM statement. The arithmetic mean and complete reversed
   permutation-product average are imported unchanged from
   ProjectionAMGMRefutation. The dependent family P0 is only a comparison;
   the final witness is the unit-column basis a200 at finite K=1000000000.
-/

import D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

namespace D5.S3.Quantum.Matrix.ProjectionAMGMRefutationScalar200

noncomputable section

abbrev meanProj {n N : ℕ} (A : Fin n → Matrix (Fin N) (Fin N) ℝ) :=
  D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.meanProj A
abbrev symProd {n N : ℕ} (A : Fin n → Matrix (Fin N) (Fin N) ℝ) :=
  D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.symProd A

/-- The scalar coordinate-descent domain: unit columns which form a basis. -/
def IsCDFamily {n : ℕ} (a : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, a i ⬝ᵥ a i = 1) ∧ LinearIndependent ℝ a

/-- Complement projection attached to a scalar coordinate column. -/
def cdProj {n : ℕ} (a : Fin n → Fin n → ℝ) (i : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ) - Matrix.vecMulVec (a i) (a i)

/-- The unchanged all-order scalar claim registered for issue 17674. -/
def claimScalar : Prop :=
  ∀ (n : ℕ) (a : Fin n → Fin n → ℝ), 1 ≤ n → IsCDFamily a →
    (meanProj (fun i => cdProj a i) ^ n -
      symProd (fun i => cdProj a i)).PosSemidef

private def std (j : Fin 200) : Fin 200 → ℝ := Pi.single j 1

private def nextIndex (i : Fin 200) : Fin 200 :=
  ⟨(i.val + 1) % 200, Nat.mod_lt _ (by decide)⟩

private def K : ℝ := 1000000000
private def s : ℝ := Real.sqrt (K ^ 2 + 1)

private def a200 (i : Fin 200) : Fin 200 → ℝ :=
  if i = 0 then std 1
  else if i = 199 then (1 / Real.sqrt 2) • (std 0 - std 1)
  else (1 / s) • (K • std 1 + std (nextIndex i))

private def z : Fin 200 → ℝ := std 0 + (200 : ℝ) • std 1

private def P200 (i : Fin 200) : Matrix (Fin 200) (Fin 200) ℝ := cdProj a200 i

private lemma std_dot_std (i j : Fin 200) : std i ⬝ᵥ std j = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [std, dotProduct, Pi.single_apply]
  · simp [std, dotProduct, Pi.single_apply, h, Ne.symm h]

private lemma std_norm (i : Fin 200) : std i ⬝ᵥ std i = 1 := by
  simpa using std_dot_std i i

private lemma nextIndex_eq (i : Fin 200) (h0 : i ≠ 0) (h199 : i ≠ 199) :
    nextIndex i ≠ 0 ∧ nextIndex i ≠ 1 := by
  dsimp [nextIndex]
  constructor <;> intro h
  · have : (i.val + 1) % 200 = 0 := by simpa using h
    have hi : i.val + 1 < 200 := by omega
    omega
  · have : (i.val + 1) % 200 = 1 := by simpa using h
    have hi : i.val + 1 < 200 := by omega
    omega

private lemma a200_unit (i : Fin 200) : a200 i ⬝ᵥ a200 i = 1 := by
  classical
  by_cases h0 : i = 0
  · subst i; simp [a200, std_norm]
  by_cases h199 : i = 199
  · subst i
    have ht : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    norm_num [a200, dotProduct_smul, smul_dotProduct, dotProduct_sub,
      sub_dotProduct, std_dot_std, smul_eq_mul]
    field_simp [hn]
    nlinarith [ht]
  · rw [a200, ite_eq_right h0, ite_eq_right h199]
    have hn := nextIndex_eq i h0 h199
    have hs : s ^ 2 = K ^ 2 + 1 := by
      dsimp [s]
      rw [Real.sq_sqrt]
      positivity
    have hsn : s ≠ 0 := by
      unfold s
      positivity
    simp [dotProduct_smul, smul_dotProduct, add_dotProduct, dotProduct_add,
      std_dot_std, hn.2, Ne.symm hn.2, smul_eq_mul]
    field_simp [hsn]
    nlinarith [hs]

private lemma s_pos : 0 < s := by
  unfold s
  positivity

private lemma a200_spans :
    Submodule.span ℝ (Set.range a200) = ⊤ := by
  classical
  let S := Submodule.span ℝ (Set.range a200)
  have ha (i : Fin 200) : a200 i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have he2 : std 1 ∈ S := by simpa [a200] using ha 0
  have he1 : std 0 ∈ S := by
    have h := S.add_mem (S.smul_mem (Real.sqrt 2) (ha 199)) he2
    simpa [a200, smul_smul, ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))] using h
  have he (j : Fin 200) : std j ∈ S := by
    by_cases hj0 : j = 0
    · simpa [hj0] using he1
    by_cases hj1 : j = 1
    · simpa [hj1] using he2
    let i : Fin 200 := ⟨j.val - 1, by omega⟩
    have hi0 : i ≠ 0 := by apply Fin.ne_of_val_ne; dsimp [i]; omega
    have hi199 : i ≠ 199 := by apply Fin.ne_of_val_ne; dsimp [i]; omega
    have hn : nextIndex i = j := by
      apply Fin.ext
      dsimp [nextIndex, i]
      omega
    have h := S.sub_mem (S.smul_mem s (ha i)) (S.smul_mem K he2)
    simpa [a200, hi0, hi199, hn, smul_smul, ne_of_gt s_pos] using h
  apply top_unique
  intro x _
  have hx : x = ∑ j : Fin 200, x j • std j := by
    ext k
    simp [std, Pi.single_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  rw [hx]
  exact S.sum_mem fun j _ => S.smul_mem (x j) (he j)

private lemma a200_independent : LinearIndependent ℝ a200 := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact a200_spans.ge
  · simp

private lemma a200_isCDFamily : IsCDFamily a200 :=
  ⟨a200_unit, a200_independent⟩

private lemma cdProj_projection {n : ℕ} (a : Fin n → Fin n → ℝ)
    (i : Fin n) (hu : a i ⬝ᵥ a i = 1) : IsStarProjection (cdProj a i) := by
  classical
  unfold cdProj
  apply IsStarProjection.one_sub
  rw [isStarProjection_iff']
  constructor
  · simp [Matrix.vecMulVec_mul_vecMulVec, hu]
  · change (Matrix.vecMulVec (a i) (a i))ᴴ = _
    simp

private lemma cdProj_contraction {n : ℕ} (a : Fin n → Fin n → ℝ)
    (i : Fin n) (hu : a i ⬝ᵥ a i = 1) : ‖cdProj a i‖ ≤ 1 := by
  exact IsStarProjection.norm_le _ (cdProj_projection a i hu)

private lemma P200_contraction (i : Fin 200) : ‖P200 i‖ ≤ 1 :=
  cdProj_contraction a200 i (a200_unit i)

private def a0 (i : Fin 200) : Fin 200 → ℝ :=
  if i = 199 then a200 199 else std 1

private def P0 (i : Fin 200) : Matrix (Fin 200) (Fin 200) ℝ := cdProj a0 i

private def P : Matrix (Fin 200) (Fin 200) ℝ :=
  1 - Matrix.vecMulVec (std 1) (std 1)

private def Q : Matrix (Fin 200) (Fin 200) ℝ := P200 199

private def embed2 (w : Fin 2 → ℝ) : Fin 200 → ℝ := w 0 • std 0 + w 1 • std 1

private lemma a0_unit (i : Fin 200) : a0 i ⬝ᵥ a0 i = 1 := by
  by_cases hi : i = 199
  · simpa [a0, hi] using a200_unit 199
  · simpa [a0, hi] using std_norm 1

private lemma P0_contraction (i : Fin 200) : ‖P0 i‖ ≤ 1 :=
  cdProj_contraction a0 i (a0_unit i)

private lemma P0_eq (i : Fin 200) : P0 i = if i = 199 then Q else P := by
  by_cases hi : i = 199 <;> simp [P0, a0, cdProj, hi, Q, P200, P]

private lemma P0_endpoints : P200 0 = P0 0 ∧ P200 199 = P0 199 := by
  constructor <;> simp [P200, P0, cdProj, a0, a200]

private lemma embed2_dot (u v : Fin 2 → ℝ) : embed2 u ⬝ᵥ embed2 v = u ⬝ᵥ v := by
  simp only [embed2, dotProduct_add, add_dotProduct, smul_dotProduct,
    dotProduct_smul, std_dot_std]
  simp [dotProduct, Fin.sum_univ_two, smul_eq_mul]
  ring

private lemma embed2_v2 : embed2 ![1, 200] = z := by simp [embed2, z]

private def planeProj (j : Fin 200) : Matrix (Fin 200) (Fin 200) ℝ :=
  Matrix.vecMulVec (std 1) (std 1) + Matrix.vecMulVec (std j) (std j)

private def planeError (j : Fin 200) : Matrix (Fin 200) (Fin 200) ℝ :=
  Matrix.vecMulVec (std 1) (std 1) - K • Matrix.vecMulVec (std 1) (std j) -
    K • Matrix.vecMulVec (std j) (std 1) - Matrix.vecMulVec (std j) (std j)

private lemma planeProj_projection (j : Fin 200) (hj : j ≠ 1) :
    IsStarProjection (planeProj j) := by
  rw [isStarProjection_iff']
  constructor
  · change planeProj j * planeProj j = _
    simp [planeProj, mul_add, add_mul, Matrix.vecMulVec_mul_vecMulVec,
      std_dot_std, hj, Ne.symm hj]
  · change (planeProj j)ᴴ = _
    simp [planeProj]

private lemma planeError_square (j : Fin 200) (hj : j ≠ 1) :
    planeError j * planeError j = (K ^ 2 + 1) • planeProj j := by
  simp [planeError, planeProj, sub_mul, mul_sub,
    Matrix.vecMulVec_mul_vecMulVec, std_dot_std, hj, Ne.symm hj]
  module

private lemma planeError_selfAdjoint (j : Fin 200) : IsSelfAdjoint (planeError j) := by
  change (planeError j)ᴴ = planeError j
  simp [planeError]
  abel

private lemma s_sq : s ^ 2 = K ^ 2 + 1 := by
  unfold s
  rw [Real.sq_sqrt]
  positivity

private lemma P200_middle_error (i : Fin 200) (h0 : i ≠ 0) (h199 : i ≠ 199) :
    P200 i - P0 i = (1 / s ^ 2 : ℝ) • planeError (nextIndex i) := by
  have hs : s ≠ 0 := ne_of_gt s_pos
  ext r c
  simp [P200, P0, cdProj, a0, a200, h0, h199, planeError,
    Matrix.vecMulVec_apply, smul_eq_mul]
  field_simp [hs]
  ring_nf
  rw [s_sq]
  ring

private lemma P200_middle_norm (i : Fin 200) (h0 : i ≠ 0) (h199 : i ≠ 199) :
    ‖P200 i - P0 i‖ ≤ 1 / s := by
  let j := nextIndex i
  have hj : j ≠ 1 := (nextIndex_eq i h0 h199).2
  have hproj := IsStarProjection.norm_le _ (planeProj_projection j hj)
  have hself := planeError_selfAdjoint j
  have hnorm := hself.norm_mul_self
  rw [planeError_square j hj, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ K ^ 2 + 1)] at hnorm
  rw [P200_middle_error i h0 h199, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have hs := s_pos
  have hsn : s ≠ 0 := ne_of_gt hs
  have he : ‖planeError j‖ ≤ s := by
    nlinarith [s_sq, mul_le_mul_of_nonneg_left hproj (by positivity : 0 ≤ K ^ 2 + 1)]
  calc
    (1 / s ^ 2) * ‖planeError (nextIndex i)‖ ≤ (1 / s ^ 2) * s :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = 1 / s := by field_simp [hsn]

private lemma total_factor_error : ∑ i : Fin 200, ‖P200 i - P0 i‖ ≤ 198 / s := by
  have heach (i : Fin 200) : ‖P200 i - P0 i‖ ≤
      if i = 0 ∨ i = 199 then 0 else 1 / s := by
    by_cases h0 : i = 0
    · subst i; simp [P0_endpoints.1]
    by_cases hn : i = 199
    · subst i; simp [P0_endpoints.2]
    · simpa [h0, hn] using P200_middle_norm i h0 hn
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => heach i)
  have hsum : (∑ i : Fin 200, if i = 0 ∨ i = 199 then (0 : ℝ) else 1 / s) = 198 / s := by
    have hterm (i : Fin 200) : (if i = 0 ∨ i = 199 then (0 : ℝ) else 1 / s) =
        1 / s - (if i = 0 then 1 / s else 0) - (if i = 199 then 1 / s else 0) := by
      by_cases h0 : i = 0 <;> by_cases hn : i = 199 <;> simp_all
    simp_rw [hterm]
    simp [Finset.sum_sub_distrib]
    ring
  rwa [hsum] at h

private lemma list_prod_contraction {R ι : Type*} [NormedRing R] [NormOneClass R]
    (f : ι → R) (hf : ∀ i, ‖f i‖ ≤ 1) (l : List ι) :
    ‖(l.map f).prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, one_mul] using
      (norm_mul_le (f i) (l.map f).prod).trans
        (mul_le_mul (hf i) ih (norm_nonneg _) zero_le_one)

private lemma list_prod_sub_bound {R ι : Type*} [NormedRing R] [NormOneClass R]
    (f g : ι → R) (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1)
    (l : List ι) :
    ‖(l.map f).prod - (l.map g).prod‖ ≤ (l.map fun i => ‖f i - g i‖).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hx := list_prod_contraction f hf l
    calc
      ‖f i * (l.map f).prod - g i * (l.map g).prod‖ =
          ‖(f i - g i) * (l.map f).prod +
            g i * ((l.map f).prod - (l.map g).prod)‖ := by congr 1; noncomm_ring
      _ ≤ ‖(f i - g i) * (l.map f).prod‖ +
          ‖g i * ((l.map f).prod - (l.map g).prod)‖ := norm_add_le _ _
      _ ≤ ‖f i - g i‖ * 1 + 1 * (l.map fun i => ‖f i - g i‖).sum := by
        apply add_le_add
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
        · exact (norm_mul_le _ _).trans (mul_le_mul (hg i) ih (norm_nonneg _) zero_le_one)
      _ = _ := by ring

private lemma pow_sub_bound {R : Type*} [NormedRing R] [NormOneClass R]
    (A B : R) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (n : ℕ) :
    ‖A ^ n - B ^ n‖ ≤ n * ‖A - B‖ := by
  simpa [nsmul_eq_mul] using list_prod_sub_bound (fun _ : Unit => A) (fun _ => B)
    (fun _ => hA) (fun _ => hB) (List.replicate n ())

private lemma mean_contraction {n N : ℕ} (hn : n ≠ 0)
    (A : Fin n → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i, ‖A i‖ ≤ 1) :
    ‖meanProj A‖ ≤ 1 := by
  unfold meanProj D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.meanProj
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |(n : ℝ)⁻¹| * ‖∑ i, A i‖ ≤ |(n : ℝ)⁻¹| * ∑ i, ‖A i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
    _ ≤ |(n : ℝ)⁻¹| * (n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hA i)
    _ = 1 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn)

private lemma mean_sub_bound {n N : ℕ}
    (A B : Fin n → Matrix (Fin N) (Fin N) ℝ) :
    ‖meanProj A - meanProj B‖ ≤ |(n : ℝ)⁻¹| * ∑ i, ‖A i - B i‖ := by
  unfold meanProj D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.meanProj
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)

private lemma symProd_sub_bound {n N : ℕ} (hN : N ≠ 0)
    (A B : Fin n → Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (hB : ∀ i, ‖B i‖ ≤ 1) :
    ‖symProd A - symProd B‖ ≤ ∑ i, ‖A i - B i‖ := by
  classical
  have : NeZero N := ⟨hN⟩
  have hword (σ : Equiv.Perm (Fin n)) :
      ‖(List.ofFn (fun k => A (σ k))).reverse.prod -
        (List.ofFn (fun k => B (σ k))).reverse.prod‖ ≤ ∑ i, ‖A i - B i‖ := by
    have h := list_prod_sub_bound A B hA hB (List.ofFn σ).reverse
    simp only [List.map_reverse, List.map_ofFn, List.sum_reverse, List.sum_ofFn,
      Function.comp_def] at h
    exact h.trans_eq (Equiv.sum_comp σ (fun i => ‖A i - B i‖))
  unfold symProd D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.symProd
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs]
  calc
    |(n.factorial : ℝ)⁻¹| * ‖∑ σ : Equiv.Perm (Fin n),
        ((List.ofFn (fun k => A (σ k))).reverse.prod -
          (List.ofFn (fun k => B (σ k))).reverse.prod)‖ ≤
        |(n.factorial : ℝ)⁻¹| * ∑ σ : Equiv.Perm (Fin n),
          ‖(List.ofFn (fun k => A (σ k))).reverse.prod -
            (List.ofFn (fun k => B (σ k))).reverse.prod‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
    _ ≤ |(n.factorial : ℝ)⁻¹| *
        ((n.factorial : ℝ) * ∑ i, ‖A i - B i‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [Fintype.card_perm] using Finset.sum_le_sum (s := Finset.univ)
        (fun (σ : Equiv.Perm (Fin n)) _ => hword σ)
    _ = _ := by
      rw [abs_of_nonneg (by positivity)]
      field_simp

private lemma sum_perm_eval_zero {E : Type*} [AddCommMonoid E]
    (n : ℕ) (f : Fin (n + 1) → E) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), f (σ 0)) = n.factorial • ∑ j, f j := by
  classical
  rw [← (Equiv.Perm.decomposeFin (n := n)).symm.sum_comp]
  simp [Fintype.sum_prod_type, Equiv.Perm.decomposeFin_symm_apply_zero,
    Fintype.card_perm, ← Finset.smul_sum]

private lemma sum_perm_eval {E : Type*} [AddCommMonoid E]
    (n : ℕ) (f : Fin (n + 1) → E) (i : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), f (σ i)) = n.factorial • ∑ j, f j := by
  classical
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap 0 i))
    (fun σ : Equiv.Perm (Fin (n + 1)) => f (σ 0))
  have heq : (∑ σ : Equiv.Perm (Fin (n + 1)), f (σ i)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), f (σ 0) := by
    simpa [Equiv.Perm.mul_apply] using h
  rw [heq, sum_perm_eval_zero]

private lemma sum_perm_inv_eval {E : Type*} [AddCommMonoid E]
    (n : ℕ) (f : Fin (n + 1) → E) (i : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), f (σ.symm i)) = n.factorial • ∑ j, f j := by
  classical
  have h := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin (n + 1))))
    (fun σ : Equiv.Perm (Fin (n + 1)) => f (σ i))
  rw [← sum_perm_eval n f i]
  exact h

private lemma single_word {R : Type*} [Monoid R] (P Q : R) :
    ∀ (n : ℕ) (k : Fin (n + 1)),
      (List.ofFn (fun j => if j = k then Q else P)).reverse.prod =
        P ^ (n - k.val) * Q * P ^ k.val := by
  intro n
  induction n with
  | zero => intro k; have hk : k = 0 := Fin.ext (by omega); simp [hk]
  | succ n ih =>
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [List.ofFn_succ, List.reverse_cons, List.prod_append, List.ofFn_const,
        pow_succ, mul_assoc]
    · rw [List.ofFn_succ]
      have hz : (0 : Fin (n + 1 + 1)) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
      simp only [List.reverse_cons, List.prod_append,
        List.prod_singleton, Fin.succ_inj, hz, ite_false]
      rw [ih]
      simp only [Fin.val_succ, Nat.add_sub_add_right, pow_succ, mul_assoc]

private lemma P0_word (σ : Equiv.Perm (Fin 200)) :
    (List.ofFn (fun k => P0 (σ k))).reverse.prod =
      P ^ (199 - (σ.symm 199).val) * Q * P ^ (σ.symm 199).val := by
  have hf (k : Fin 200) : P0 (σ k) = if k = σ.symm 199 then Q else P := by
    simp only [P0_eq, ← Equiv.eq_symm_apply]
  simp_rw [hf]
  exact single_word P Q 199 (σ.symm 199)

private lemma symProd_P0_position_average :
    symProd P0 = (1 / 200 : ℝ) • ∑ k : Fin 200, P ^ (199 - k.val) * Q * P ^ k.val := by
  unfold symProd D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.symProd
  simp_rw [P0_word]
  have hsum : (∑ σ : Equiv.Perm (Fin 200),
      P ^ (199 - (σ.symm 199).val) * Q * P ^ (σ.symm 199).val) =
      (Nat.factorial 199) • ∑ k : Fin 200, P ^ (199 - k.val) * Q * P ^ k.val :=
    sum_perm_inv_eval 199 (fun k => P ^ (199 - k.val) * Q * P ^ k.val) 199
  have hnormalize (n : ℕ) (X : Matrix (Fin 200) (Fin 200) ℝ) :
      ((Nat.factorial (n + 1) : ℝ)⁻¹) • (Nat.factorial n • X) =
        (1 / (n + 1 : ℝ)) • X := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    apply congrArg (fun c : ℝ => c • X)
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hf : (Nat.factorial n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hf, hn]
  rw [hsum]
  simpa only [Nat.reduceAdd, Nat.cast_ofNat,
    show (199 : ℝ) + 1 = 200 by norm_num] using hnormalize 199 _

private lemma binomial_three_terms (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    1 + (n + 1 : ℝ) * t + (n : ℝ) * (n + 1) / 2 * t ^ 2 ≤ (1 + t) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right ih (by positivity : 0 ≤ 1 + t)
    have hrem : 0 ≤ (n : ℝ) * (n + 1) / 2 * t ^ 3 := by positivity
    push_cast
    rw [pow_succ (1 + t) (n + 1)]
    nlinarith

private lemma rational_power_bound : (401 / 402 : ℝ) ^ 196 < 5 / 8 := by
  have hlo := binomial_three_terms (1 / 401) (by norm_num) 195
  have hc : (195 : ℝ) + 1 = 196 := by norm_num
  simp only [Nat.cast_ofNat, Nat.reduceAdd, hc] at hlo
  have hlarge : (8 / 5 : ℝ) < (402 / 401 : ℝ) ^ 196 := by
    convert (lt_of_lt_of_le (by norm_num : (8 / 5 : ℝ) <
      1 + 196 * (1 / 401) + 195 * 196 / 2 * (1 / 401) ^ 2) hlo) using 1
    norm_num
  have hinv : (401 / 402 : ℝ) ^ 196 * (402 / 401 : ℝ) ^ 196 = 1 := by
    rw [← mul_pow]
    norm_num
  have hpos : 0 < (401 / 402 : ℝ) ^ 196 := by positivity
  nlinarith [mul_lt_mul_of_pos_left hlarge hpos]

private def B2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![399 / 400, 1 / 400; 1 / 400, 1 / 400]

private def v2 : Fin 2 → ℝ := ![1, 200]

private lemma P_projection : IsStarProjection P := by
  simpa [P, cdProj] using cdProj_projection (fun _ : Fin 200 => std 1) 0 (std_norm 1)

private lemma P_embed2 (w : Fin 2 → ℝ) : P *ᵥ embed2 w = w 0 • std 0 := by
  rw [P, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  simp [embed2, dotProduct_add, dotProduct_smul, std_dot_std]

private lemma Q_embed2 (w : Fin 2 → ℝ) :
    Q *ᵥ embed2 w = ((w 0 + w 1) / 2) • (std 0 + std 1) := by
  unfold Q P200 cdProj
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  ext j
  simp [a200, embed2, dotProduct_add, sub_dotProduct,
    smul_dotProduct, dotProduct_smul, std_dot_std, smul_eq_mul]
  field_simp [hsn]
  rw [hs2]
  ring

private lemma mean_P0_eq : meanProj P0 = (1 / 200 : ℝ) • ((199 : ℝ) • P + Q) := by
  have heq (i : Fin 200) : P0 i = P + if i = 199 then Q - P else 0 := by
    rw [P0_eq]
    split_ifs <;> abel
  unfold meanProj D5.S3.Quantum.Matrix.ProjectionAMGMRefutation.meanProj
  simp_rw [heq]
  simp [Finset.sum_add_distrib, ← Nat.cast_smul_eq_nsmul ℝ]
  module

private lemma mean_P0_embed2 (w : Fin 2 → ℝ) :
    meanProj P0 *ᵥ embed2 w = embed2 (B2 *ᵥ w) := by
  rw [mean_P0_eq, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    P_embed2, Q_embed2]
  ext j
  simp [embed2, B2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  ring

private lemma mean_P0_pow_embed2 (m : ℕ) (w : Fin 2 → ℝ) :
    meanProj P0 ^ m *ᵥ embed2 w = embed2 (B2 ^ m *ᵥ w) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, mean_P0_embed2,
      Matrix.mulVec_mulVec, ← pow_succ']

private lemma P_z : P *ᵥ z = std 0 := by
  simpa [embed2_v2] using P_embed2 ![1, 200]

private lemma aux_word_form (k : Fin 200) :
    z ⬝ᵥ ((P ^ (199 - k.val) * Q * P ^ k.val) *ᵥ z) =
      (1 / 2 : ℝ) + if k = 0 ∨ k = 199 then 100 else 0 := by
  have hp (m : ℕ) (hm : m ≠ 0) : P ^ m = P := P_projection.pow_eq hm
  have hval : (199 : Fin 200).val = 199 := by decide
  have hdot0 : z ⬝ᵥ std 0 = 1 := by simp [z, add_dotProduct, smul_dotProduct, std_dot_std]
  have hdot1 : z ⬝ᵥ std 1 = 200 := by simp [z, add_dotProduct, smul_dotProduct, std_dot_std]
  by_cases h0 : k = 0
  · subst k
    simp only [Fin.val_zero, Nat.sub_zero, pow_zero, mul_one, hp 199 (by decide)]
    rw [← Matrix.mulVec_mulVec, ← embed2_v2, Q_embed2]
    rw [Matrix.mulVec_smul]
    have hP : P *ᵥ (std 0 + std 1) = std 0 := by
      simpa [embed2] using P_embed2 ![1, 1]
    rw [hP, dotProduct_smul]
    norm_num [embed2_v2, hdot0]
  by_cases h199 : k = 199
  · subst k
    simp only [hval, Nat.sub_self, pow_zero, one_mul,
      hp 199 (by decide)]
    rw [← Matrix.mulVec_mulVec, P_z]
    have hQ : Q *ᵥ std 0 = (1 / 2 : ℝ) • (std 0 + std 1) := by
      simpa [embed2] using Q_embed2 ![1, 0]
    rw [hQ, dotProduct_smul, dotProduct_add, hdot0, hdot1]
    norm_num
  · have hk0 : k.val ≠ 0 := by intro hv; exact h0 (Fin.ext hv)
    have hk199 : k.val ≠ 199 := by
      intro hv
      apply h199
      exact Fin.ext (hv.trans hval.symm)
    have hkn : 199 - k.val ≠ 0 := by have := k.isLt; omega
    rw [hp _ hkn, hp _ hk0, ← Matrix.mulVec_mulVec, P_z]
    have hQ : Q *ᵥ std 0 = (1 / 2 : ℝ) • (std 0 + std 1) := by
      simpa [embed2] using Q_embed2 ![1, 0]
    rw [← Matrix.mulVec_mulVec, hQ, Matrix.mulVec_smul]
    have hP : P *ᵥ (std 0 + std 1) = std 0 := by
      simpa [embed2] using P_embed2 ![1, 1]
    rw [hP, dotProduct_smul, hdot0]
    simp [h0, h199]

private lemma symProd_P0_form : z ⬝ᵥ (symProd P0 *ᵥ z) = (3 / 2 : ℝ) := by
  rw [symProd_P0_position_average, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.sum_mulVec, dotProduct_sum]
  simp_rw [aux_word_form]
  have hi (k : Fin 200) : (if k = 0 ∨ k = 199 then (100 : ℝ) else 0) =
      (if k = 0 then 100 else 0) + (if k = 199 then 100 else 0) := by
    by_cases h0 : k = 0 <;> by_cases hn : k = 199 <;> simp_all
  simp_rw [hi]
  norm_num [Finset.sum_add_distrib]

private lemma B2_symmetric : B2ᵀ = B2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B2]

private lemma B2_norm_bound : ‖B2‖ ≤ (401 / 402 : ℝ) := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  let a : ℝ := (401 / 402) ^ 2 - (399 ^ 2 + 1) / 400 ^ 2
  let b : ℝ := -(400 / 400 ^ 2)
  let d : ℝ := (401 / 402) ^ 2 - 2 / 400 ^ 2
  have ha : 0 < a := by norm_num [a]
  have hdet : 0 ≤ a * d - b ^ 2 := by norm_num [a, b, d]
  have hsq := sq_nonneg (a * x 0 + b * x 1)
  have hy := mul_nonneg hdet (sq_nonneg (x 1))
  have hform : 0 ≤ a * (x 0) ^ 2 + 2 * b * x 0 * x 1 + d * (x 1) ^ 2 := by
    by_contra hn
    have hneg := mul_neg_of_pos_of_neg ha (lt_of_not_ge hn)
    nlinarith
  simp only [EuclideanSpace.real_norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
    Fin.sum_univ_two, Matrix.mulVec, dotProduct, B2, Matrix.of_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_pow] at *
  dsimp [a, b, d] at hform
  nlinarith

private lemma B2_squared_vector : B2 ^ 2 *ᵥ v2 = ![119601 / 80000, 1 / 200] := by
  ext i
  fin_cases i <;> norm_num [B2, v2, pow_two, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

private lemma B2_squared_vector_norm :
    ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (B2 ^ 2 *ᵥ v2)‖ ^ 2 < (9 / 4 : ℝ) := by
  rw [B2_squared_vector, EuclideanSpace.real_norm_sq_eq]
  norm_num [Fin.sum_univ_two]

private lemma dot_self_eq_l2_sq {n : ℕ} (x : Fin n → ℝ) :
    x ⬝ᵥ x = ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

private lemma B2_power_form_bound : v2 ⬝ᵥ ((B2 ^ 200) *ᵥ v2) < (45 / 32 : ℝ) := by
  let w : EuclideanSpace ℝ (Fin 2) := (EuclideanSpace.equiv (Fin 2) ℝ).symm (B2 ^ 2 *ᵥ v2)
  have h98 : ‖B2 ^ 98‖ ≤ (401 / 402 : ℝ) ^ 98 :=
    (norm_pow_le B2 98).trans (pow_le_pow_left₀ (norm_nonneg _) B2_norm_bound 98)
  have hmul := Matrix.l2_opNorm_mulVec (B2 ^ 98) w
  have hmul' : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm
      (B2 ^ 98 *ᵥ (B2 ^ 2 *ᵥ v2))‖ ≤ (401 / 402 : ℝ) ^ 98 * ‖w‖ := by
    exact hmul.trans (mul_le_mul_of_nonneg_right h98 (norm_nonneg _))
  have hsq : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm
      (B2 ^ 98 *ᵥ (B2 ^ 2 *ᵥ v2))‖ ^ 2 ≤ (401 / 402 : ℝ) ^ 196 * ‖w‖ ^ 2 := by
    calc
      _ ≤ ((401 / 402 : ℝ) ^ 98 * ‖w‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hmul'
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hw : ‖w‖ ^ 2 < (9 / 4 : ℝ) := B2_squared_vector_norm
  have hnonneg : 0 ≤ (401 / 402 : ℝ) ^ 196 := by positivity
  have hp := mul_le_mul_of_nonneg_left hw.le hnonneg
  have hstrict := mul_lt_mul_of_pos_right rational_power_bound (by norm_num : (0:ℝ) < 9 / 4)
  have hform : v2 ⬝ᵥ (B2 ^ 200 *ᵥ v2) =
      ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm
        (B2 ^ 98 *ᵥ (B2 ^ 2 *ᵥ v2))‖ ^ 2 := by
    calc
      v2 ⬝ᵥ (B2 ^ 200 *ᵥ v2) = (B2 ^ 100 *ᵥ v2) ⬝ᵥ (B2 ^ 100 *ᵥ v2) := by
        rw [show 200 = 100 + 100 from rfl, pow_add, ← Matrix.mulVec_mulVec,
          dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_pow, B2_symmetric]
      _ = _ := by
        rw [dot_self_eq_l2_sq, show 100 = 98 + 2 from rfl, pow_add, ← Matrix.mulVec_mulVec]
  rw [hform]
  linarith

private lemma auxiliary_negative_form :
    z ⬝ᵥ ((meanProj P0 ^ 200 - symProd P0) *ᵥ z) < (-3 / 32 : ℝ) := by
  have hm : z ⬝ᵥ (meanProj P0 ^ 200 *ᵥ z) = v2 ⬝ᵥ (B2 ^ 200 *ᵥ v2) := by
    simp_rw [show z = embed2 v2 by simp [z, embed2, v2]]
    rw [mean_P0_pow_embed2, embed2_dot]
  rw [Matrix.sub_mulVec, dotProduct_sub, hm, symProd_P0_form]
  linarith [B2_power_form_bound]

private lemma total_operator_error :
    ‖(meanProj P200 ^ 200 - symProd P200) -
      (meanProj P0 ^ 200 - symProd P0)‖ ≤ 396 / s := by
  have hmean0 := mean_contraction (by decide : 200 ≠ 0) P0 P0_contraction
  have hmean := mean_contraction (by decide : 200 ≠ 0) P200 P200_contraction
  have hm : ‖meanProj P200 - meanProj P0‖ ≤ (1 / 200 : ℝ) * (198 / s) := by
    have h := mean_sub_bound P200 P0
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_left total_factor_error (by norm_num))
  have hp := (pow_sub_bound (meanProj P200) (meanProj P0) hmean hmean0 200).trans
    (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 200))
  have hg := (symProd_sub_bound (by decide : 200 ≠ 0) P200 P0
    P200_contraction P0_contraction).trans total_factor_error
  calc
    ‖(meanProj P200 ^ 200 - symProd P200) -
        (meanProj P0 ^ 200 - symProd P0)‖ =
        ‖(meanProj P200 ^ 200 - meanProj P0 ^ 200) - (symProd P200 - symProd P0)‖ := by
      congr 1
      abel
    _ ≤ ‖meanProj P200 ^ 200 - meanProj P0 ^ 200‖ + ‖symProd P200 - symProd P0‖ := norm_sub_le _ _
    _ ≤ 200 * ((1 / 200 : ℝ) * (198 / s)) + 198 / s := add_le_add hp hg
    _ = 396 / s := by ring

private lemma quadratic_form_error {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ (x ⬝ᵥ x) * ‖A‖ := by
  let v : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm x
  have hinner := abs_real_inner_le_norm v (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A v)
  have hop := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A).le_opNorm v
  have h : |⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A v⟫| ≤ ‖v‖ * (‖A‖ * ‖v‖) :=
    hinner.trans (mul_le_mul_of_nonneg_left hop (norm_nonneg _))
  rw [Matrix.inner_toEuclideanCLM] at h
  change |x ⬝ᵥ (A *ᵥ x)| ≤ ‖v‖ * (‖A‖ * ‖v‖) at h
  calc
    |x ⬝ᵥ (A *ᵥ x)| ≤ ‖v‖ * (‖A‖ * ‖v‖) := h
    _ = (x ⬝ᵥ x) * ‖A‖ := by
      rw [dot_self_eq_l2_sq]
      dsimp [v]
      ring

private lemma z_squared_norm : z ⬝ᵥ z = 40001 := by
  norm_num [z, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    std_dot_std, smul_eq_mul]

private lemma s_gt_K : K < s := by
  have hK : 0 < K := by norm_num [K]
  have hs := s_pos
  nlinarith [s_sq]

private lemma strict_negative_certificate :
    z ⬝ᵥ ((meanProj P200 ^ 200 - symProd P200) *ᵥ z) <
      -3 / 32 + 15840396 / 1000000000 := by
  let E := (meanProj P200 ^ 200 - symProd P200) -
    (meanProj P0 ^ 200 - symProd P0)
  have he := (quadratic_form_error E z).trans
    (mul_le_mul_of_nonneg_left total_operator_error (by rw [z_squared_norm]; norm_num))
  rw [z_squared_norm] at he
  have hform : z ⬝ᵥ ((meanProj P200 ^ 200 - symProd P200) *ᵥ z) =
      z ⬝ᵥ ((meanProj P0 ^ 200 - symProd P0) *ᵥ z) + z ⬝ᵥ (E *ᵥ z) := by
    dsimp [E]
    simp only [Matrix.sub_mulVec, dotProduct_sub]
    ring
  have herror : (40001 : ℝ) * (396 / s) < 15840396 / 1000000000 := by
    have hK : (0 : ℝ) < K := by norm_num [K]
    have hinv := one_div_lt_one_div_of_lt hK s_gt_K
    calc
      (40001 : ℝ) * (396 / s) = 15840396 * (1 / s) := by ring
      _ < 15840396 * (1 / K) := mul_lt_mul_of_pos_left hinv (by norm_num)
      _ = 15840396 / 1000000000 := by norm_num [K]
  rw [hform]
  have ha := auxiliary_negative_form
  have hb := le_abs_self (z ⬝ᵥ (E *ᵥ z))
  linarith

private lemma P200_not_posSemidef : ¬ (meanProj P200 ^ 200 - symProd P200).PosSemidef := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg z
  simp only [star_trivial] at hn
  have hneg : z ⬝ᵥ ((meanProj P200 ^ 200 - symProd P200) *ᵥ z) < 0 := by
    have hgap : (-3 / 32 + 15840396 / 1000000000 : ℝ) < -1 / 16 := by norm_num
    linarith [strict_negative_certificate]
  linarith

/-- The original registered all-order scalar projection inequality is false. -/
theorem result : ¬ claimScalar := by
  intro h
  exact P200_not_posSemidef (h 200 a200 (by norm_num) a200_isCDFamily)

end
end D5.S3.Quantum.Matrix.ProjectionAMGMRefutationScalar200
