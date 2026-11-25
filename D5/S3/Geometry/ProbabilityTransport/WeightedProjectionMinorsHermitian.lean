/- GID: D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinorsHermitian
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/WeightedProjectionMinorsHermitian
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Real and complex weighted-minor comparison with signed weights, two-sided bounds and pair families. -/

import D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinors

/-! The weighted-minor comparison over `𝕜 = ℝ` or `ℂ`: for `x, y, z ∈ 𝕜ⁿ` with
`⟪z, x⟫ = ⟪z, y⟫ = 0`, the pair minors `p_ij` and triple minors `q_ijk` satisfy
`∑_{i<j<k} |q_ijk|² = ‖z‖² ∑_{i<j} |p_ij|²`, the pair-family domination, and for arbitrary real
weights `∑ min{a} |q|² ≤ ‖z‖² ∑ a |p|² ≤ ∑ max{a} |q|²`.

admission_basis: escape-witness. Escape witnesses: adjoint and energy (the Hermitian energy identity
`∑|lift z v|² + 6∑|contract z v|² = 3‖z‖²∑|v|²`), contraction (Hermitian Cauchy–Schwarz contraction
bound), recover_minors with mass_identity, family_domination, weighted_all_tuples, and the ordered
identity. Consumed bind-only helpers: general (normalization of `z` by homogeneity and
symmetrization of weights and relations), sum_rotate, sum_swap, lift_alt, lower_skew,
lower_lift, conj_mul_norm, pair_skew, triple_lift, contract_pair, unit_conj, projection_alt,
projection_locality, pair_projection_le, triple_alt, triple_zero, triple_norm_sym, triple_smul,
sum_pull, ordered_weighted, signed_upper, signed_lower, ordered_family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinorsHermitian

open scoped BigOperators ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]


private def Skew (v : ι → ι → 𝕜) : Prop := ∀ i j, v i j = -v j i

private def Alt (b : ι → ι → ι → 𝕜) : Prop :=
  (∀ i j k, b j i k = -b i j k) ∧ (∀ i j k, b k i j = b i j k)

private def lift (z : ι → 𝕜) (v : ι → ι → 𝕜) (i j k : ι) : 𝕜 :=
  z i * v j k - z j * v i k + z k * v i j

private def lower (z : ι → 𝕜) (b : ι → ι → ι → 𝕜) (i j : ι) : 𝕜 :=
  ∑ k, conj (z k) * b k i j

private def contract (z : ι → 𝕜) (v : ι → ι → 𝕜) (i : ι) : 𝕜 :=
  ∑ k, conj (z k) * v k i

private theorem sum_rotate {M : Type*} [AddCommMonoid M] (f : ι → ι → ι → M) :
    (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f k i j := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem sum_swap {M : Type*} [AddCommMonoid M] (f : ι → ι → ι → M) :
    (∑ i, ∑ j, ∑ k, f j i k) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]

omit [Fintype ι] in
private theorem lift_alt (z : ι → 𝕜) {v : ι → ι → 𝕜} (hv : Skew v) : Alt (lift z v) := by
  constructor
  · intro i j k
    simp only [lift, hv j i]
    ring
  · intro i j k
    simp only [lift, hv k j, hv k i]
    ring

private theorem lower_skew (z : ι → 𝕜) {b : ι → ι → ι → 𝕜} (hb : Alt b) : Skew (lower z b) := by
  intro i j
  unfold lower
  have h : ∀ k, b k i j = -b k j i := by
    intro k
    rw [← hb.2 k i j, hb.1 k j i]
  simp_rw [h, mul_neg, Finset.sum_neg_distrib]

private theorem adjoint (z : ι → 𝕜) (v : ι → ι → 𝕜) {b : ι → ι → ι → 𝕜} (hb : Alt b) :
    (∑ i, ∑ j, ∑ k, conj (lift z v i j k) * b i j k) =
      3 * ∑ i, ∑ j, conj (v i j) * lower z b i j := by
  let f : ι → ι → ι → 𝕜 := fun i j k => conj (z i) * conj (v j k) * b i j k
  have h₁ : (∑ i, ∑ j, ∑ k, conj (z j) * conj (v i k) * b i j k) =
      -(∑ i, ∑ j, ∑ k, f i j k) := by
    calc
      _ = -(∑ i, ∑ j, ∑ k, f j i k) := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        dsimp [f]
        rw [hb.1 i j k]
        ring
      _ = _ := congrArg Neg.neg (sum_swap f)
  have h₂ : (∑ i, ∑ j, ∑ k, conj (z k) * conj (v i j) * b i j k) =
      ∑ i, ∑ j, ∑ k, f i j k := by
    calc
      _ = ∑ i, ∑ j, ∑ k, f k i j := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        dsimp [f]
        rw [hb.2 i j k]
      _ = _ := sum_rotate f
  have h₃ : (∑ i, ∑ j, conj (v i j) * lower z b i j) =
      ∑ i, ∑ j, ∑ k, f i j k := by
    simp only [lower, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ j, ∑ k, conj (z k) * conj (v i j) * b i j k := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        rw [hb.2 i j k]
        ring
      _ = _ := h₂
  simp only [lift, map_add, map_sub, map_mul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [h₁, h₂, h₃]
  dsimp [f]
  ring

private theorem lower_lift (z : ι → 𝕜) (v : ι → ι → 𝕜) (i j : ι) :
    lower z (lift z v) i j =
      (∑ k, conj (z k) * z k) * v i j - z i * contract z v j + z j * contract z v i := by
  calc
    _ = ∑ k, (conj (z k) * z k * v i j - z i * (conj (z k) * v k j) +
        z j * (conj (z k) * v k i)) := by
      apply Finset.sum_congr rfl; intro k _
      dsimp [lift]
      ring
    _ = _ := by
      simp only [contract, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.sum_mul]

private theorem conj_mul_norm (a : 𝕜) : conj a * a = ((‖a‖ ^ 2 : ℝ) : 𝕜) := by
  rw [RCLike.conj_mul]; push_cast; ring

private theorem energy (z : ι → 𝕜) {v : ι → ι → 𝕜} (hv : Skew v) :
    (∑ i, ∑ j, ∑ k, ‖lift z v i j k‖ ^ 2) + 6 * (∑ i, ‖contract z v i‖ ^ 2) =
      3 * (∑ k, ‖z k‖ ^ 2) * (∑ i, ∑ j, ‖v i j‖ ^ 2) := by
  have h := adjoint z v (lift_alt z hv)
  have cross₁ : (∑ i, ∑ j, conj (v i j) * (z i * contract z v j)) =
      ∑ j, conj (contract z v j) * contract z v j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    simp only [contract, map_sum, map_mul, RCLike.conj_conj, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    ring
  have cross₂ : (∑ i, ∑ j, conj (v i j) * (z j * contract z v i)) =
      -(∑ i, conj (contract z v i) * contract z v i) := by
    calc
      _ = -(∑ j, ∑ i, conj (v j i) * (z j * contract z v i)) := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro i _
        rw [hv j i, map_neg]
        ring
      _ = _ := congrArg Neg.neg cross₁
  simp only [lower_lift, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at h
  rw [cross₁, cross₂] at h
  have diag : (∑ i, ∑ j, conj (v i j) * ((∑ k, conj (z k) * z k) * v i j)) =
      (∑ k, conj (z k) * z k) * (∑ i, ∑ j, conj (v i j) * v i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [diag] at h
  simp only [conj_mul_norm] at h
  have h' : (((∑ i, ∑ j, ∑ k, ‖lift z v i j k‖ ^ 2) + 6 * (∑ i, ‖contract z v i‖ ^ 2) : ℝ) : 𝕜) =
      ((3 * (∑ k, ‖z k‖ ^ 2) * (∑ i, ∑ j, ‖v i j‖ ^ 2) : ℝ) : 𝕜) := by
    push_cast at h ⊢
    linear_combination h
  exact_mod_cast h'



/-! complex contraction and minors -/

private noncomputable def mass₂ (v : ι → ι → 𝕜) : ℝ := (∑ i, ∑ j, ‖v i j‖ ^ 2) / 2

private noncomputable def mass₃ (b : ι → ι → ι → 𝕜) : ℝ := (∑ i, ∑ j, ∑ k, ‖b i j k‖ ^ 2) / 6

private theorem contraction (z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    {b : ι → ι → ι → 𝕜} (hb : Alt b) :
    mass₂ (lower z b) ≤ mass₃ b := by
  let d := lower z b
  let D := ∑ i, ∑ j, ‖d i j‖ ^ 2
  let B := ∑ i, ∑ j, ∑ k, ‖b i j k‖ ^ 2
  let Q := ∑ i, ∑ j, ∑ k, ‖lift z d i j k‖ ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : Q ≤ 3 * D := by
    have he := energy z (lower_skew z hb)
    rw [hz] at he
    have hk : 0 ≤ ∑ i, ‖contract z d i‖ ^ 2 := by positivity
    dsimp [Q, D, d]
    dsimp [d] at hk
    linarith
  have hi : (∑ i, ∑ j, ∑ k, conj (lift z d i j k) * b i j k) = ((3 * D : ℝ) : 𝕜) := by
    rw [adjoint z d hb]
    have e : ∀ i j, conj (d i j) * lower z b i j = ((‖d i j‖ ^ 2 : ℝ) : 𝕜) :=
      fun i j => conj_mul_norm _
    simp only [e, D]
    push_cast
    ring
  have hle : 3 * D ≤ ∑ i, ∑ j, ∑ k, ‖lift z d i j k‖ * ‖b i j k‖ := by
    have h1 : ‖((3 * D : ℝ) : 𝕜)‖ = 3 * D := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    rw [← h1, ← hi]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (ι × ι × ι))
    (fun p => ‖lift z d p.1 p.2.1 p.2.2‖)
    (fun p => ‖b p.1 p.2.1 p.2.2‖)
  simp only [Fintype.sum_prod_type] at hcs
  change (∑ i, ∑ j, ∑ k, ‖lift z d i j k‖ * ‖b i j k‖) ^ 2 ≤ Q * B at hcs
  have h3 : (3 * D) ^ 2 ≤ Q * B := (pow_le_pow_left₀ (by positivity) hle 2).trans hcs
  have hm : Q * B ≤ 3 * D * B := mul_le_mul_of_nonneg_right hQ hB
  have hfinal : 3 * D ≤ B := by
    rcases eq_or_lt_of_le hD with hzero | hpos
    · rw [← hzero]; linarith
    · nlinarith
  change D / 2 ≤ B / 6
  linarith

private def pairMinor (x y : ι → 𝕜) (i j : ι) : 𝕜 := x i * y j - x j * y i

private def tripleMinor (x y z : ι → 𝕜) (i j k : ι) : 𝕜 :=
  Matrix.det !![x i, x j, x k; y i, y j, y k; z i, z j, z k]

omit [Fintype ι] in
private theorem pair_skew (x y : ι → 𝕜) : Skew (pairMinor x y) := by
  intro i j; unfold pairMinor; ring

omit [Fintype ι] in
private theorem triple_lift (x y z : ι → 𝕜) : tripleMinor x y z = lift z (pairMinor x y) := by
  funext i j k
  simp [tripleMinor, Matrix.det_fin_three, lift, pairMinor]
  ring

private theorem contract_pair (x y z : ι → 𝕜) (i : ι) :
    contract z (pairMinor x y) i =
      (∑ k, conj (z k) * x k) * y i - (∑ k, conj (z k) * y k) * x i := by
  simp only [contract, pairMinor, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring

private theorem unit_conj (z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1) : ∑ k, conj (z k) * z k = 1 := by
  simp only [conj_mul_norm]
  rw [← RCLike.ofReal_sum, hz, RCLike.ofReal_one]

private theorem recover_minors (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0) :
    lower z (tripleMinor x y z) = pairMinor x y := by
  rw [triple_lift]
  funext i j
  rw [lower_lift, unit_conj z hz, contract_pair, contract_pair, hzx, hzy]
  ring

private theorem mass_identity (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0) :
    mass₃ (tripleMinor x y z) = mass₂ (pairMinor x y) := by
  have h := energy z (pair_skew x y)
  have hc : ∀ i, contract z (pairMinor x y) i = 0 := fun i => by
    rw [contract_pair, hzx, hzy]; ring
  simp only [hc, norm_zero, hz, ← triple_lift] at h
  unfold mass₂ mass₃
  simp at h
  linarith

private def pairProjection (F : ι → ι → Prop) [DecidableRel F]
    (v : ι → ι → 𝕜) (i j : ι) : 𝕜 := if F i j then v i j else 0

private def tripleProjection (F : ι → ι → Prop) [DecidableRel F]
    (b : ι → ι → ι → 𝕜) (i j k : ι) : 𝕜 :=
  if F i j ∨ F i k ∨ F j k then b i j k else 0

omit [Fintype ι] in
private theorem projection_alt (F : ι → ι → Prop) [DecidableRel F]
    (hF : ∀ i j, F i j ↔ F j i) {b : ι → ι → ι → 𝕜} (hb : Alt b) :
    Alt (tripleProjection F b) := by
  constructor
  · intro i j k
    have e : (F j i ∨ F j k ∨ F i k) ↔ (F i j ∨ F i k ∨ F j k) := by rw [hF j i]; tauto
    by_cases h : F i j ∨ F i k ∨ F j k
    · simp only [tripleProjection, if_pos h, if_pos (e.2 h), hb.1 i j k]
    · simp only [tripleProjection, if_neg h, if_neg (mt e.1 h), neg_zero]
  · intro i j k
    have e : (F k i ∨ F k j ∨ F i j) ↔ (F i j ∨ F i k ∨ F j k) := by
      rw [hF k i, hF k j]; tauto
    by_cases h : F i j ∨ F i k ∨ F j k
    · simp only [tripleProjection, if_pos h, if_pos (e.2 h), hb.2 i j k]
    · simp only [tripleProjection, if_neg h, if_neg (mt e.1 h)]

private theorem projection_locality (z : ι → 𝕜) (F : ι → ι → Prop)
    [DecidableRel F] (b : ι → ι → ι → 𝕜) :
    pairProjection F (lower z (tripleProjection F b)) = pairProjection F (lower z b) := by
  funext i j
  by_cases h : F i j
  · simp only [pairProjection, if_pos h, lower]
    apply Finset.sum_congr rfl; intro k _
    simp [tripleProjection, h]
  · simp [pairProjection, h]

private theorem pair_projection_le (F : ι → ι → Prop) [DecidableRel F]
    (v : ι → ι → 𝕜) : mass₂ (pairProjection F v) ≤ mass₂ v := by
  unfold mass₂
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  by_cases h : F i j <;> simp [pairProjection, h]

omit [Fintype ι] in
private theorem triple_alt (x y z : ι → 𝕜) : Alt (tripleMinor x y z) := by
  rw [triple_lift]; exact lift_alt z (pair_skew x y)

private theorem family_domination (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0)
    (F : ι → ι → Prop) [DecidableRel F] (hF : ∀ i j, F i j ↔ F j i) :
    mass₂ (pairProjection F (pairMinor x y)) ≤
      mass₃ (tripleProjection F (tripleMinor x y z)) := by
  calc
    _ = mass₂ (pairProjection F (lower z (tripleProjection F (tripleMinor x y z)))) := by
      rw [projection_locality, recover_minors x y z hz hzx hzy]
    _ ≤ mass₂ (lower z (tripleProjection F (tripleMinor x y z))) := pair_projection_le _ _
    _ ≤ _ := contraction z hz (projection_alt F hF (triple_alt x y z))


private theorem weighted_all_tuples (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 ≤ A i j) :
    3 * (∑ i, ∑ j, A i j * ‖pairMinor x y i j‖ ^ 2) ≤
      ∑ i, ∑ j, ∑ k, max (A i j) (max (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 := by
  classical
  have ht (r : ℝ) := family_domination x y z hz hzx hzy
    (fun i j => r ≤ A i j) (fun i j => by rw [hA i j])
  have hthreshold (r : ℝ) :
      (∑ p : ι × ι, if r ≤ A p.1 p.2 then 3 * ‖pairMinor x y p.1 p.2‖ ^ 2 else 0) ≤
      ∑ p : ι × ι × ι,
        if r ≤ max (A p.1 p.2.1) (max (A p.1 p.2.2) (A p.2.1 p.2.2))
        then ‖tripleMinor x y z p.1 p.2.1 p.2.2‖ ^ 2 else 0 := by
    have h := ht r
    unfold mass₂ mass₃ pairProjection tripleProjection at h
    simp only [Fintype.sum_prod_type]
    have hi (a : 𝕜) (P : Prop) [Decidable P] : ‖(if P then a else 0)‖ ^ 2 =
        if P then ‖a‖ ^ 2 else 0 := by split_ifs <;> simp
    simp_rw [hi] at h
    simp only [le_max_iff]
    have hpull : (∑ i, ∑ j, if r ≤ A i j then 3 * ‖pairMinor x y i j‖ ^ 2 else 0) =
        3 * (∑ i, ∑ j, if r ≤ A i j then ‖pairMinor x y i j‖ ^ 2 else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [hpull]
    linarith
  have hw := AlternatingArrayContraction.weighted_threshold
    (fun p : ι × ι => A p.1 p.2)
    (fun p : ι × ι => 3 * ‖pairMinor x y p.1 p.2‖ ^ 2)
    (fun p : ι × ι × ι => max (A p.1 p.2.1) (max (A p.1 p.2.2) (A p.2.1 p.2.2)))
    (fun p : ι × ι × ι => ‖tripleMinor x y z p.1 p.2.1 p.2.2‖ ^ 2)
    (fun p => hpos _ _)
    (fun p => (hpos p.1 p.2.1).trans (le_max_left _ _)) hthreshold
  simp only [Fintype.sum_prod_type] at hw
  calc
    _ = ∑ i, ∑ j, A i j * (3 * ‖pairMinor x y i j‖ ^ 2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    _ ≤ _ := hw

variable [LinearOrder ι]

omit [Fintype ι] [LinearOrder ι] in
private theorem triple_zero (x y z : ι → 𝕜) (i k : ι) : tripleMinor x y z i i k = 0 := by
  have h := (triple_alt x y z).1 i i k
  have : (2 : 𝕜) * tripleMinor x y z i i k = 0 := by linear_combination h
  simpa using this

omit [Fintype ι] [LinearOrder ι] in
private theorem triple_norm_sym (x y z : ι → 𝕜) :
    (∀ i j k, ‖tripleMinor x y z j i k‖ = ‖tripleMinor x y z i j k‖) ∧
    (∀ i j k, ‖tripleMinor x y z k i j‖ = ‖tripleMinor x y z i j k‖) := by
  have hb := triple_alt x y z
  exact ⟨fun i j k => by rw [hb.1, norm_neg], fun i j k => by rw [hb.2]⟩

private theorem ordered_weighted (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 ≤ A i j) :
    (∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        max (A i j) (max (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 else 0 := by
  have hs := triple_norm_sym x y z
  have hp := AlternatingArrayContraction.pair_ordering (fun i j => A i j * ‖pairMinor x y i j‖ ^ 2)
    (fun i j => by rw [hA j i, pair_skew x y j i, norm_neg])
    (fun i => by simp [pairMinor])
  have hq := AlternatingArrayContraction.triple_ordering
    (fun i j k => max (A i j) (max (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2)
    (fun i j k => by rw [hA j i, hs.1, max_comm (A j k) (A i k)])
    (fun i j k => by
      rw [hA k i, hA k j, hs.2]
      congr 1
      simp only [max_left_comm, max_comm])
    (fun i k => by simp [triple_zero])
  have h := weighted_all_tuples x y z hz hzx hzy A hA hpos
  rw [hp, hq] at h
  linarith

private theorem ordered_identity (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0) :
    (∑ i, ∑ j, if i < j then ‖pairMinor x y i j‖ ^ 2 else 0) =
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then ‖tripleMinor x y z i j k‖ ^ 2 else 0 := by
  have hs := triple_norm_sym x y z
  have hp := AlternatingArrayContraction.pair_ordering (fun i j => ‖pairMinor x y i j‖ ^ 2)
    (fun i j => by rw [pair_skew x y j i, norm_neg]) (fun i => by simp [pairMinor])
  have hq := AlternatingArrayContraction.triple_ordering (fun i j k => ‖tripleMinor x y z i j k‖ ^ 2)
    (fun i j k => by rw [hs.1]) (fun i j k => by rw [hs.2])
    (fun i k => by simp [triple_zero])
  have hm := mass_identity x y z hz hzx hzy
  unfold mass₂ mass₃ at hm
  linarith

private theorem signed_upper (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        max (A i j) (max (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 else 0 := by
  set c : ℝ := ∑ i, ∑ j, |A i j| with hc
  have hbig : ∀ i j, |A i j| ≤ c := fun i j => by
    calc |A i j| ≤ ∑ j, |A i j| :=
          Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ c :=
          Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hpos : ∀ i j, 0 ≤ A i j + c := fun i j => by
    have := neg_abs_le (A i j); have := hbig i j; linarith
  have h := ordered_weighted x y z hz hzx hzy (fun i j => A i j + c)
    (fun i j => by simp only [hA i j]) hpos
  have hmax : ∀ i j k, max (A i j + c) (max (A i k + c) (A j k + c)) =
      max (A i j) (max (A i k) (A j k)) + c := fun i j k => by
    rw [max_add_add_right, max_add_add_right]
  simp only [hmax] at h
  have e1 : (∑ i, ∑ j, if i < j then (A i j + c) * ‖pairMinor x y i j‖ ^ 2 else 0) =
      (∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0) +
        c * ∑ i, ∑ j, if i < j then ‖pairMinor x y i j‖ ^ 2 else 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have e2 : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        (max (A i j) (max (A i k) (A j k)) + c) * ‖tripleMinor x y z i j k‖ ^ 2 else 0) =
      (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        max (A i j) (max (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 else 0) +
        c * ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then ‖tripleMinor x y z i j k‖ ^ 2 else 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [e1, e2, ordered_identity x y z hz hzx hzy] at h
  linarith

private theorem signed_lower (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        min (A i j) (min (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 else 0) ≤
      ∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0 := by
  have h := signed_upper x y z hz hzx hzy (fun i j => -A i j) (fun i j => by simp only [hA i j])
  simp only [max_neg_neg, neg_mul] at h
  have e1 : (∑ i, ∑ j, if i < j then -(A i j * ‖pairMinor x y i j‖ ^ 2) else 0) =
      -(∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0) := by
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have e2 : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        -(min (A i j) (min (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2) else 0) =
      -(∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        min (A i j) (min (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 else 0) := by
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [e1, e2] at h
  linarith


private theorem ordered_family (x y z : ι → 𝕜) (hz : ∑ k, ‖z k‖ ^ 2 = 1)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0)
    (F : ι → ι → Prop) [DecidableRel F] (hF : ∀ i j, F i j ↔ F j i) :
    (∑ i, ∑ j, if i < j ∧ F i j then ‖pairMinor x y i j‖ ^ 2 else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k ∧ (F i j ∨ F i k ∨ F j k) then
        ‖tripleMinor x y z i j k‖ ^ 2 else 0 := by
  let A : ι → ι → ℝ := fun i j => if F i j then 1 else 0
  have h := ordered_weighted x y z hz hzx hzy A
    (fun i j => by simp only [A]; rw [if_congr (hF i j) rfl rfl])
    (fun i j => by simp only [A]; split_ifs <;> norm_num)
  have hmax : ∀ i j k, max (A i j) (max (A i k) (A j k)) =
      if F i j ∨ F i k ∨ F j k then 1 else 0 := fun i j k => by
    simp only [A]; split_ifs <;> simp_all
  simp only [hmax] at h
  convert h using 3 with i _ j _
  · split_ifs <;> simp_all [A]
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp_all


omit [Fintype ι] [LinearOrder ι] in
private theorem triple_smul (c : 𝕜) (x y z : ι → 𝕜) (i j k : ι) :
    ‖tripleMinor x y (fun l => c * z l) i j k‖ ^ 2 = ‖c‖ ^ 2 * ‖tripleMinor x y z i j k‖ ^ 2 := by
  have h : tripleMinor x y (fun l => c * z l) i j k = c * tripleMinor x y z i j k := by
    simp [tripleMinor, Matrix.det_fin_three]; ring
  rw [h, norm_mul, mul_pow]

omit [LinearOrder ι] in
private theorem sum_pull (a : ℝ) (P : ι → ι → ι → Prop) [∀ i j k, Decidable (P i j k)]
    (w v : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if P i j k then w i j k * (a * v i j k) else 0) =
      a * ∑ i, ∑ j, ∑ k, if P i j k then w i j k * v i j k else 0 := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- The four comparisons with arbitrary weights and relations and an arbitrary `z ⟂ x, y`. -/
private theorem general (x y z : ι → 𝕜)
    (hzx : ∑ k, conj (z k) * x k = 0) (hzy : ∑ k, conj (z k) * y k = 0) :
    (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then 1 * ‖tripleMinor x y z i j k‖ ^ 2 else 0) =
      (∑ k, ‖z k‖ ^ 2) * (∑ i, ∑ j, if i < j then ‖pairMinor x y i j‖ ^ 2 else 0) ∧
    (∀ (F : ι → ι → Prop) [DecidableRel F],
      (∑ k, ‖z k‖ ^ 2) * (∑ i, ∑ j, if i < j ∧ F i j then ‖pairMinor x y i j‖ ^ 2 else 0) ≤
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k ∧ (F i j ∨ F i k ∨ F j k) then
          1 * ‖tripleMinor x y z i j k‖ ^ 2 else 0) ∧
    (∀ A : ι → ι → ℝ,
      (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
          min (A i j) (min (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 else 0) ≤
        (∑ k, ‖z k‖ ^ 2) * (∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0) ∧
      (∑ k, ‖z k‖ ^ 2) * (∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0) ≤
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
          max (A i j) (max (A i k) (A j k)) * ‖tripleMinor x y z i j k‖ ^ 2 else 0) := by
  set s := ∑ k, ‖z k‖ ^ 2 with hs
  rcases (show 0 ≤ s by positivity).eq_or_lt with h0 | hpos
  · have hz : ∀ k, z k = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp h0.symm k
        (Finset.mem_univ k)
      simpa using this
    have hq : ∀ i j k, tripleMinor x y z i j k = 0 := fun i j k => by
      simp [tripleMinor, Matrix.det_fin_three, hz]
    simp [hq, ← h0]
  -- normalize `z`
  set c : 𝕜 := (((√s)⁻¹ : ℝ) : 𝕜) with hc
  have hc2 : ‖c‖ ^ 2 = s⁻¹ := by
    rw [hc, RCLike.norm_ofReal, abs_of_nonneg (by positivity), inv_pow, Real.sq_sqrt hpos.le]
  let z' : ι → 𝕜 := fun l => c * z l
  have hz' : ∑ k, ‖z' k‖ ^ 2 = 1 := by
    simp only [z', norm_mul, mul_pow, ← Finset.mul_sum, hc2, ← hs]
    exact inv_mul_cancel₀ hpos.ne'
  have hzx' : ∑ k, conj (z' k) * x k = 0 := by
    simp only [z', map_mul, mul_assoc, ← Finset.mul_sum, hzx, mul_zero]
  have hzy' : ∑ k, conj (z' k) * y k = 0 := by
    simp only [z', map_mul, mul_assoc, ← Finset.mul_sum, hzy, mul_zero]
  have hscale : ∀ (P : ι → ι → ι → Prop) [∀ i j k, Decidable (P i j k)] (w : ι → ι → ι → ℝ),
      (∑ i, ∑ j, ∑ k, if P i j k then w i j k * ‖tripleMinor x y z' i j k‖ ^ 2 else 0) =
        s⁻¹ * ∑ i, ∑ j, ∑ k, if P i j k then w i j k * ‖tripleMinor x y z i j k‖ ^ 2 else 0 := by
    intro P _ w
    simp only [z', triple_smul, hc2]
    exact sum_pull _ P w _
  -- symmetrized weights and relations
  have tri : ∀ (P : ι → ι → ι → Prop) [∀ i j k, Decidable (P i j k)] (f g : ι → ι → ι → ℝ),
      (∀ i j k, i < j → j < k → P i j k → f i j k = g i j k) →
      (∑ i, ∑ j, ∑ k, if i < j ∧ j < k ∧ P i j k then f i j k else 0) =
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k ∧ P i j k then g i j k else 0 := by
    intro P _ f g h
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hh
    · exact h i j k hh.1 hh.2.1 hh.2.2
    · rfl
  refine ⟨?_, fun F _ => ?_, fun A => ?_⟩
  · have h := ordered_identity x y z' hz' hzx' hzy'
    have e := hscale (fun i j k => i < j ∧ j < k) (fun _ _ _ => 1)
    simp only [one_mul] at e ⊢
    rw [e] at h
    field_simp at h
    linarith
  · let F' : ι → ι → Prop := fun i j => F (min i j) (max i j)
    have hF' : ∀ i j, F' i j ↔ F' j i := fun i j => by simp only [F', min_comm, max_comm]
    have h := ordered_family x y z' hz' hzx' hzy' F' hF'
    have e1 : (∑ i, ∑ j, if i < j ∧ F' i j then ‖pairMinor x y i j‖ ^ 2 else 0) =
        ∑ i, ∑ j, if i < j ∧ F i j then ‖pairMinor x y i j‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j
      · simp [F', hij, min_eq_left hij.le, max_eq_right hij.le]
      · simp [hij]
    have e2 : (∑ i, ∑ j, ∑ k, if i < j ∧ j < k ∧ (F' i j ∨ F' i k ∨ F' j k) then
          ‖tripleMinor x y z' i j k‖ ^ 2 else 0) =
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k ∧ (F i j ∨ F i k ∨ F j k) then
          ‖tripleMinor x y z' i j k‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => ?_
      by_cases hij : i < j
      · by_cases hjk : j < k
        · have hik := hij.trans hjk
          simp [F', hij, hjk, min_eq_left hij.le, max_eq_right hij.le, min_eq_left hik.le,
            max_eq_right hik.le, min_eq_left hjk.le, max_eq_right hjk.le]
        · simp [hjk]
      · simp [hij]
    rw [e1, e2] at h
    have e := hscale (fun i j k => i < j ∧ j < k ∧ (F i j ∨ F i k ∨ F j k)) (fun _ _ _ => 1)
    simp only [one_mul] at e ⊢
    rw [e] at h
    rw [le_inv_mul_iff₀ hpos] at h
    linarith
  · let A' : ι → ι → ℝ := fun i j => A (min i j) (max i j)
    have hA' : ∀ i j, A' i j = A' j i := fun i j => by simp only [A', min_comm, max_comm]
    have e1 : (∑ i, ∑ j, if i < j then A' i j * ‖pairMinor x y i j‖ ^ 2 else 0) =
        ∑ i, ∑ j, if i < j then A i j * ‖pairMinor x y i j‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i < j
      · simp [A', hij, min_eq_left hij.le, max_eq_right hij.le]
      · simp [hij]
    have eT : ∀ (m : ℝ → ℝ → ℝ → ℝ),
        (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
            m (A' i j) (A' i k) (A' j k) * ‖tripleMinor x y z' i j k‖ ^ 2 else 0) =
          ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
            m (A i j) (A i k) (A j k) * ‖tripleMinor x y z' i j k‖ ^ 2 else 0 := by
      intro m
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => ?_
      by_cases hh : i < j ∧ j < k
      · have hik := hh.1.trans hh.2
        simp [A', hh, min_eq_left hh.1.le, max_eq_right hh.1.le, min_eq_left hik.le,
          max_eq_right hik.le, min_eq_left hh.2.le, max_eq_right hh.2.le]
      · simp [hh]
    have hl := signed_lower x y z' hz' hzx' hzy' A' hA'
    have hu := signed_upper x y z' hz' hzx' hzy' A' hA'
    rw [e1, eT (fun a b c => min a (min b c))] at hl
    rw [e1, eT (fun a b c => max a (max b c))] at hu
    rw [hscale (fun i j k => i < j ∧ j < k)] at hl hu
    constructor
    · rw [inv_mul_le_iff₀ hpos] at hl; linarith
    · rw [le_inv_mul_iff₀ hpos] at hu; linarith

omit [Fintype ι] [LinearOrder ι]

/-- Theorem 1, Lemma 2 and Corollaries 3 and 4 of Ma and Zhang on MathOverflow 469781, over
`𝕜 = ℝ` or `ℂ`, in homogeneous form: for `x, y, z ∈ 𝕜ⁿ` with `⟪z, x⟫ = ⟪z, y⟫ = 0` (no normalization
of `z`, no condition on `x` and `y`), with `p_ij` the `2 × 2` and `q_ijk` the `3 × 3` minors over
increasing indices: `∑_{i<j<k} |q_ijk|² = ‖z‖² ∑_{i<j} |p_ij|²`; for every relation `F` on pairs,
read on increasing pairs, `‖z‖² ∑_{i<j, F} |p_ij|² ≤ ∑_{i<j<k meeting F} |q_ijk|²`; and for every
real weight array `a`, read on increasing pairs,
`∑ min(a_ij, a_ik, a_jk)|q_ijk|² ≤ ‖z‖² ∑ a_ij |p_ij|² ≤ ∑ max(a_ij, a_ik, a_jk)|q_ijk|²`. -/
theorem result {n : ℕ} (x y z : EuclideanSpace 𝕜 (Fin n))
    (hzx : inner 𝕜 z x = 0) (hzy : inner 𝕜 z y = 0) :
    (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        ‖Matrix.det !![x i, x j, x k; y i, y j, y k; z i, z j, z k]‖ ^ 2 else 0) =
      ‖z‖ ^ 2 * (∑ i, ∑ j, if i < j then ‖Matrix.det !![x i, x j; y i, y j]‖ ^ 2 else 0) ∧
    (∀ (F : Fin n → Fin n → Prop) [DecidableRel F],
      ‖z‖ ^ 2 * (∑ i, ∑ j, if i < j ∧ F i j then ‖Matrix.det !![x i, x j; y i, y j]‖ ^ 2 else 0) ≤
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k ∧ (F i j ∨ F i k ∨ F j k) then
          ‖Matrix.det !![x i, x j, x k; y i, y j, y k; z i, z j, z k]‖ ^ 2 else 0) ∧
    (∀ A : Fin n → Fin n → ℝ,
      (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then min (A i j) (min (A i k) (A j k)) *
          ‖Matrix.det !![x i, x j, x k; y i, y j, y k; z i, z j, z k]‖ ^ 2 else 0) ≤
        ‖z‖ ^ 2 * (∑ i, ∑ j, if i < j then A i j * ‖Matrix.det !![x i, x j; y i, y j]‖ ^ 2 else 0) ∧
      ‖z‖ ^ 2 * (∑ i, ∑ j, if i < j then A i j * ‖Matrix.det !![x i, x j; y i, y j]‖ ^ 2 else 0) ≤
        ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then max (A i j) (max (A i k) (A j k)) *
          ‖Matrix.det !![x i, x j, x k; y i, y j, y k; z i, z j, z k]‖ ^ 2 else 0) := by
  have hz : ‖z‖ ^ 2 = ∑ k, ‖z k‖ ^ 2 := EuclideanSpace.norm_sq_eq z
  have hzx' : ∑ k, conj (z k) * x k = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hzx
  have hzy' : ∑ k, conj (z k) * y k = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hzy
  have h := general (fun i => x i) (fun i => y i) (fun i => z i) hzx' hzy'
  simp only [pairMinor, tripleMinor, one_mul, ← hz] at h
  simp only [Matrix.det_fin_two_of]
  exact h

end D5.S3.Geometry.ProbabilityTransport.WeightedProjectionMinorsHermitian
