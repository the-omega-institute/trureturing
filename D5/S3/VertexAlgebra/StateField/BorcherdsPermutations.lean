/- GID: D5/S3/VertexAlgebra/StateField/BorcherdsPermutations
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/StateField/BorcherdsPermutations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite coefficient transpositions for the integer Borcherds defect. -/

import D5.S3.VertexAlgebra.StateFieldResidueReconstruction

/-! The indices `p`, `q`, and `r` are those of `x^p y^q (x-y)^r` in the
standard state-field Borcherds identity. The input is a family of bilinear modes,
so the same identities apply to sector products before assembling a vertex algebra. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

open scoped BigOperators VertexOperator
open StateFieldResidueReconstruction (integerBinomial epsilon)

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Integer modes with the convention `a_n b = μ n a b`. -/
abbrev Modes (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  ℤ → V →ₗ[ℂ] V →ₗ[ℂ] V

/-- The bilinear modes of a state-field map with the standard indexing. -/
def modesOfStateField (Y : V →ₗ[ℂ] VertexOperator ℂ V) : Modes V :=
  fun n => (LinearMap.proj n).comp (VertexOperator.ncoeff.comp Y)

variable (μ : Modes V)

/-- The divided powers of the state translation. -/
def dividedTranslation (T : Module.End ℂ V) (j : ℕ) : Module.End ℂ V :=
  (j.factorial : ℂ)⁻¹ • T ^ j

/-- Lower truncation of the series of each pair of states. -/
def LowerTruncated : Prop :=
  ∀ a b : V, ∃ N : ℤ, ∀ n ≥ N, μ n a b = 0

theorem lowerTruncated_modesOfStateField (Y : V →ₗ[ℂ] VertexOperator ℂ V) :
    LowerTruncated (modesOfStateField Y) := by
  intro a b
  refine ⟨-((HahnModule.of ℂ).symm (Y a b)).order, ?_⟩
  intro n hn
  exact VertexOperator.ncoeff_eq_zero_of_lt_order (Y a) n b (by omega)

/-- Coefficient skew for one ordered pair of states. -/
def SkewAt (T : Module.End ℂ V) (a b : V) : Prop :=
  ∀ n : ℤ, μ n a b = ∑ᶠ j : ℕ,
    epsilon (n + j + 1) • dividedTranslation T j (μ (n + j) b a)

/-- The state-translation law at each divided power and integer mode. -/
def DividedStateTranslation (T : Module.End ℂ V) : Prop :=
  ∀ (j : ℕ) (n : ℤ) (v : V),
    μ n (dividedTranslation T j v) =
      (((-1 : ℂ) ^ j) * integerBinomial n j) • μ (n - j) v

/-- The forward product in the Borcherds identity. -/
def product (a b c : V) (p q r : ℤ) : V :=
  ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial r i) •
    μ (p + r - i) a (μ (q + i) b c)

/-- The iterate in the Borcherds identity. -/
def iterate (a b c : V) (p q r : ℤ) : V :=
  ∑ᶠ i : ℕ, integerBinomial p i • μ (p + q - i) (μ (r + i) a b) c

/-- The forward product minus the signed reverse product and the iterate. -/
def defect (a b c : V) (p q r : ℤ) : V :=
  product μ a b c p q r - epsilon r • product μ b a c q p r - iterate μ a b c p q r

omit [Module ℂ V] in
private theorem support_subset_range {f : ℕ → V} {N : ℕ}
    (tail : ∀ i ≥ N, f i = 0) : Function.support f ⊆ Finset.range N := by
  intro i hi
  exact Finset.mem_range.mpr (Nat.lt_of_not_ge (fun h => hi (tail i h)))

omit [Module ℂ V] in
private theorem finsum_range {f : ℕ → V} {N : ℕ}
    (tail : ∀ i ≥ N, f i = 0) : (∑ᶠ i : ℕ, f i) = ∑ i ∈ Finset.range N, f i :=
  finsum_eq_sum_of_support_subset _ (support_subset_range tail)

private theorem offset_cutoff (h : LowerTruncated μ) (a b : V) (r : ℤ) :
    ∃ N : ℕ, ∀ i ≥ N, μ (r + (i : ℤ)) a b = 0 := by
  obtain ⟨k, hk⟩ := h a b
  exact ⟨(k - r).toNat, fun i hi => hk _ (by omega)⟩

/-- Vanishing of the defect is the standard state-field Borcherds identity,
including the finite-support requirements on each of its three summands. -/
theorem defect_eq_zero_iff_borcherds (trunc : LowerTruncated μ) (a b c : V) (p q r : ℤ) :
    defect μ a b c p q r = 0 ↔
      let left : ℕ → V := fun i => integerBinomial p i • μ (p + q - i) (μ (r + i) a b) c
      let first : ℕ → V := fun i =>
        ((-1 : ℂ)^i * integerBinomial r i) • μ (p + r - i) a (μ (q + i) b c)
      let second : ℕ → V := fun i =>
        ((-1 : ℂ)^i * integerBinomial r i) • (epsilon r • μ (q + r - i) b (μ (p + i) a c))
      Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
        Function.HasFiniteSupport second ∧
          (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ, ((-1 : ℂ)^i * integerBinomial r i) •
            (μ (p + r - i) a (μ (q + i) b c) - epsilon r • μ (q + r - i) b (μ (p + i) a c)) := by
  dsimp only
  obtain ⟨I, tailI⟩ := offset_cutoff μ trunc a b r
  obtain ⟨P, tailP⟩ := offset_cutoff μ trunc b c q
  obtain ⟨Q, tailQ⟩ := offset_cutoff μ trunc a c p
  let N := P + Q
  have leftFinite : Function.HasFiniteSupport (fun i : ℕ =>
      integerBinomial p i • μ (p + q - i) (μ (r + i) a b) c) :=
    (Finset.range I).finite_toSet.subset (support_subset_range
      (fun i hi => by rw [tailI i hi, map_zero, LinearMap.zero_apply, smul_zero]))
  have firstFinite : Function.HasFiniteSupport (fun i : ℕ =>
      ((-1 : ℂ)^i * integerBinomial r i) • μ (p + r - i) a (μ (q + i) b c)) :=
    (Finset.range P).finite_toSet.subset (support_subset_range
      (fun i hi => by rw [tailP i hi, map_zero, smul_zero]))
  have secondFinite : Function.HasFiniteSupport (fun i : ℕ =>
      ((-1 : ℂ)^i * integerBinomial r i) • (epsilon r • μ (q + r - i) b (μ (p + i) a c))) :=
    (Finset.range Q).finite_toSet.subset (support_subset_range
      (fun i hi => by rw [tailQ i hi, map_zero, smul_zero, smul_zero]))
  have products : product μ a b c p q r - epsilon r • product μ b a c q p r =
      ∑ᶠ i : ℕ, ((-1 : ℂ)^i * integerBinomial r i) •
        (μ (p + r - i) a (μ (q + i) b c) - epsilon r • μ (q + r - i) b (μ (p + i) a c)) := by
    unfold product
    rw [finsum_range (N := N) (fun i hi => by
          unfold N at hi; rw [tailP i (by omega), map_zero, smul_zero]),
        finsum_range (N := N) (fun i hi => by
          unfold N at hi; rw [tailQ i (by omega), map_zero, smul_zero]),
        finsum_range (N := N) (fun i hi => by
          unfold N at hi
          rw [tailP i (by omega), tailQ i (by omega), map_zero, map_zero, smul_zero, sub_zero,
            smul_zero]),
        Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_sub, smul_comm (epsilon r)]
  rw [defect, products, sub_eq_zero]
  simp only [leftFinite, firstFinite, secondFinite, true_and, iterate, eq_comm]

private theorem cast_choose (p : ℤ) (i : ℕ) :
    integerBinomial p i = Ring.choose (p : ℂ) i :=
  Ring.map_choose (Int.castRingHom ℂ) p i

private theorem reflect_choose (x : ℂ) (j : ℕ) :
    (-1 : ℂ) ^ j * Ring.choose x j = Ring.choose (-x + (j : ℂ) - 1) j := by
  have h := Ring.choose_neg (-x) j
  rw [neg_neg] at h
  rw [h]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num

private theorem sign_square (r : ℤ) : epsilon r * epsilon r = 1 := by
  rw [epsilon, ← mul_zpow]
  norm_num

private theorem diagonal (p q : ℤ) (l : ℕ) :
    (∑ i ∈ Finset.range (l + 1), ((-1 : ℂ) ^ i) * integerBinomial p i *
      integerBinomial (p + q - i) (l - i)) = integerBinomial q l := by
  simp only [cast_choose, Int.cast_sub, Int.cast_add, Int.cast_natCast]
  have vandermonde := Ring.add_choose_eq (R := ℂ)
    (r := (p : ℂ)) (s := -(p : ℂ) - (q : ℂ) + (l : ℂ) - 1) l (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
  have hs (i : ℕ) (hi : i ≤ l) :
      (-1 : ℂ) ^ l * ((-1 : ℂ) ^ i) = (-1 : ℂ) ^ (l - i) := by
    have hl : l = l - i + i := by omega
    conv_lhs => rw [hl]
    rw [pow_add, mul_assoc, ← mul_pow]
    simp
  calc
    _ = ∑ i ∈ Finset.range (l + 1),
        (-1 : ℂ) ^ l * (Ring.choose (p : ℂ) i *
          Ring.choose (-(p : ℂ) - (q : ℂ) + (l : ℂ) - 1) (l - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hb : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← show (-1 : ℂ) ^ (l - i) *
          Ring.choose ((p : ℂ) + (q : ℂ) - (i : ℂ)) (l - i) =
          Ring.choose (-(p : ℂ) - (q : ℂ) + (l : ℂ) - 1) (l - i) by
        rw [reflect_choose, Nat.cast_sub hb]
        congr 1
        ring, ← hs i hb]
      have square : (-1 : ℂ) ^ l * (-1 : ℂ) ^ l = 1 := by
        rw [← mul_pow]
        norm_num
      symm
      calc
        _ = ((-1 : ℂ) ^ l * (-1 : ℂ) ^ l) *
            ((-1 : ℂ) ^ i * Ring.choose (p : ℂ) i *
              Ring.choose ((p : ℂ) + (q : ℂ) - (i : ℂ)) (l - i)) := by ac_rfl
        _ = _ := by rw [square, one_mul]
    _ = (-1 : ℂ) ^ l * Ring.choose (-(q : ℂ) + (l : ℂ) - 1) l := by
      rw [← Finset.mul_sum, ← vandermonde]
      congr 2
      ring
    _ = _ := by
      rw [← reflect_choose, ← mul_assoc, ← mul_pow]
      norm_num

private theorem iterate_swap (h : LowerTruncated μ) {T : Module.End ℂ V}
    {a b : V} (skew : SkewAt μ T a b) (translate : DividedStateTranslation μ T)
    (c : V) (p q r : ℤ) :
    iterate μ a b c p q r = epsilon (r + 1) • iterate μ b a c q p r := by
  obtain ⟨N, tail⟩ := offset_cutoff μ h b a r
  have skew_range (i : ℕ) :
      μ (r + i) a b = ∑ j ∈ Finset.range (N - i),
        epsilon (r + i + j + 1) • dividedTranslation T j (μ (r + i + j) b a) := by
    rw [skew]
    apply finsum_range
    intro j hj
    rw [show r + (i : ℤ) + j = r + ((i + j : ℕ) : ℤ) by push_cast; ring,
      tail (i + j) (by omega), map_zero, smul_zero]
  have out (i : ℕ) (hi : N ≤ i) : μ (r + i) a b = 0 := by
    rw [skew_range, Nat.sub_eq_zero_of_le hi, Finset.range_zero, Finset.sum_empty]
  let f := fun l : ℕ => μ (p + q - l) (μ (r + l) b a) c
  have right_range : iterate μ b a c q p r =
      ∑ l ∈ Finset.range N, integerBinomial q l • f l := by
    unfold iterate
    rw [finsum_range (N := N) (fun i hi => by rw [tail i hi, map_zero, LinearMap.zero_apply,
      smul_zero])]
    simp only [f, add_comm q p]
  unfold iterate at *
  rw [right_range]
  rw [finsum_range (N := N) (fun i hi => by rw [out i hi, map_zero, LinearMap.zero_apply,
    smul_zero])]
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N - i),
        (epsilon (r + 1) * (((-1 : ℂ)^i) * integerBinomial p i *
          integerBinomial (p + q - i) j)) • f (i + j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [skew_range i, map_sum, LinearMap.sum_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [map_smul, LinearMap.smul_apply, smul_smul, f, Nat.cast_add]
      rw [translate j, LinearMap.smul_apply, smul_smul,
        show p + q - (i : ℤ) - j = p + q - ((i : ℤ) + j) by omega,
        show r + (i : ℤ) + j = r + ((i : ℤ) + j) by omega]
      congr 1
      have sign : epsilon (r + (i : ℤ) + j + 1) * (-1 : ℂ)^j =
          epsilon (r + 1) * (-1 : ℂ)^i := by
        unfold epsilon
        rw [show r + (i : ℤ) + j + 1 = (r + 1) + (i : ℤ) + j by omega,
          zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast, zpow_natCast,
          mul_assoc (((-1 : ℂ) ^ (r + 1)) * _),
          ← mul_pow]
        norm_num
      calc
        _ = (epsilon (r + (i : ℤ) + j + 1) * (-1 : ℂ)^j) *
            (integerBinomial p i * integerBinomial (p + q - i) j) := by ac_rfl
        _ = _ := by rw [sign]; ac_rfl
    _ = ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range (l + 1),
        (epsilon (r + 1) * (((-1 : ℂ)^i) * integerBinomial p i *
          integerBinomial (p + q - i) (l - i))) • f l := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    _ = _ := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      calc
        _ = epsilon (r + 1) •
            ∑ i ∈ Finset.range (l + 1), (((-1 : ℂ)^i) * integerBinomial p i *
              integerBinomial (p + q - i) (l - i)) • f l := by
          rw [Finset.smul_sum]
          simp only [smul_smul]
        _ = _ := by rw [← Finset.sum_smul, diagonal]

/-- Exchanging the first two states multiplies the defect by `(-1)^(r+1)`.
The only skew identity used is the one for the pair being exchanged. -/
theorem defect_swap_first (h : LowerTruncated μ) {T : Module.End ℂ V}
    {a b : V} (skew : SkewAt μ T a b) (translate : DividedStateTranslation μ T)
    (c : V) (p q r : ℤ) :
    defect μ a b c p q r = epsilon (r + 1) • defect μ b a c q p r := by
  have sign : epsilon (r + 1) = -epsilon r := by
    unfold epsilon
    rw [zpow_add₀ (by norm_num), zpow_one, mul_neg, mul_one]
  unfold defect
  rw [iterate_swap μ h skew translate, smul_sub, smul_sub, smul_smul, sign,
    neg_mul, sign_square]
  simp only [neg_smul, one_smul]
  abel

/-- Moving divided translation from the input of a mode to its output. -/
def DividedModeTranslation (T : Module.End ℂ V) (a : V) : Prop :=
  ∀ (n : ℤ) (h : ℕ) (v : V),
    μ n a (dividedTranslation T h v) = ∑ t ∈ Finset.range (h + 1),
      integerBinomial n t • dividedTranslation T (h - t) (μ (n - t) a v)

/-- The signed divided translation of a coefficient at the exchanged input. -/
def signedTranslation (T : Module.End ℂ V) (q : ℤ) (j : ℕ) : Module.End ℂ V :=
  epsilon (q + j + 1) • dividedTranslation T j

private theorem epsilon_add (n m : ℤ) : epsilon (n + m) = epsilon n * epsilon m :=
  zpow_add₀ (by norm_num) n m

private theorem epsilon_nat (i : ℕ) : epsilon (i : ℤ) = (-1 : ℂ)^i :=
  zpow_natCast _ _

private theorem epsilon_sub_nat (n : ℤ) (i : ℕ) :
    epsilon (n - i) = epsilon n * (-1 : ℂ)^i := by
  rw [sub_eq_add_neg, epsilon_add]
  unfold epsilon
  rw [zpow_neg, ← inv_zpow]
  have hs : (-1 : ℂ)⁻¹ = -1 := by norm_num
  rw [hs, zpow_natCast]

private theorem signed_diagonal (r p : ℤ) (l : ℕ) :
    (∑ i ∈ Finset.range (l + 1), (-1 : ℂ)^(l - i) * integerBinomial r i *
      integerBinomial (r + p - i) (l - i)) = (-1 : ℂ)^l * integerBinomial p l := by
  rw [← diagonal r p l, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hl : l = l - i + i := by have := Finset.mem_range.mp hi; omega
  rw [← mul_assoc, ← mul_assoc, show (-1 : ℂ)^l * (-1 : ℂ)^i = (-1 : ℂ)^(l - i) by
    conv_lhs => rw [hl]
    rw [pow_add, mul_assoc, ← mul_pow]
    simp]

omit [Module ℂ V] in
private theorem triangle_comm (N : ℕ) (f : ℕ → ℕ → V) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N - i), f i j) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (N - j), f i j := by
  have range_filter (i : ℕ) :
      Finset.range (N - i) = (Finset.range N).filter (fun j => i + j < N) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  simp_rw [range_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [add_comm]

private theorem product_swap_last (trunc : LowerTruncated μ) {T : Module.End ℂ V}
    {a b c : V} (skew : SkewAt μ T b c) (translate : DividedModeTranslation μ T a)
    (p q r : ℤ) :
    (∃ N : ℕ, ∀ j ≥ N, product μ a c b r (q + j) p = 0) ∧
    product μ a b c p q r =
      ∑ᶠ j : ℕ, signedTranslation T q j (product μ a c b r (q + j) p) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ trunc c b q
  let v := fun l j : ℕ => μ (p + r - l) a (μ (q + ((j + l : ℕ) : ℤ)) c b)
  let weight := fun i t : ℕ =>
    (-1 : ℂ)^t * integerBinomial r i * integerBinomial (p + r - i) t
  have skew_range (i : ℕ) :
      μ (q + i) b c = ∑ h ∈ Finset.range (N - i),
        epsilon (q + i + h + 1) • dividedTranslation T h (μ (q + i + h) c b) := by
    rw [skew]
    apply finsum_range
    intro h hh
    rw [show q + (i : ℤ) + h = q + ((i + h : ℕ) : ℤ) by push_cast; ring,
      tail (i + h) (by omega), map_zero, smul_zero]
  have forward_range : product μ a b c p q r =
      ∑ i ∈ Finset.range N, ((-1 : ℂ)^i * integerBinomial r i) •
        μ (p + r - i) a (μ (q + i) b c) := by
    unfold product
    apply finsum_range
    intro i hi
    rw [skew_range, Nat.sub_eq_zero_of_le hi, Finset.range_zero, Finset.sum_empty,
      map_zero, smul_zero]
  have reverse_range (j : ℕ) : product μ a c b r (q + j) p =
      ∑ l ∈ Finset.range (N - j), ((-1 : ℂ)^l * integerBinomial p l) • v l j := by
    unfold product
    rw [finsum_range (N := N - j) (fun l hl => by
      rw [show q + (j : ℤ) + l = q + ((j + l : ℕ) : ℤ) by push_cast; ring,
        tail (j + l) (by omega), map_zero, smul_zero])]
    simp only [v, add_comm r p, Nat.cast_add, add_assoc]
  have reverse_tail (j : ℕ) (hj : N ≤ j) : product μ a c b r (q + j) p = 0 := by
    rw [reverse_range, Nat.sub_eq_zero_of_le hj, Finset.range_zero, Finset.sum_empty]
  refine ⟨⟨N, reverse_tail⟩, ?_⟩
  rw [forward_range, finsum_range (N := N) (fun j hj => by rw [reverse_tail j hj, map_zero])]
  simp_rw [reverse_range]
  let F := fun i t j : ℕ => signedTranslation T q j (weight i t • v (i + t) j)
  calc
    _ = ∑ i ∈ Finset.range N, ∑ h ∈ Finset.range (N - i),
        ∑ t ∈ Finset.range (h + 1), F i t (h - t) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [skew_range, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [map_smul, translate, Finset.smul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hth : t ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      have sign : epsilon (q + (i : ℤ) + h + 1) =
          epsilon (q + ((h : ℤ) - t) + 1) * (-1 : ℂ)^(i+t) := by
        rw [show q + (i : ℤ) + h + 1 =
          (q + ((h : ℤ) - t) + 1) + (i + t : ℕ) by push_cast; ring,
          epsilon_add, epsilon_nat]
      simp only [F, signedTranslation, LinearMap.smul_apply, map_smul, smul_smul, weight,
        v, Nat.cast_add, Nat.cast_sub hth]
      rw [show p + r - (i : ℤ) - t = p + r - ((i : ℤ) + t) by omega,
        show q + ((h : ℤ) - t + ((i : ℤ) + t)) = q + i + h by omega,
        sign, pow_add]
      congr 1
      have square : (-1 : ℂ)^i * (-1 : ℂ)^i = 1 := by rw [← mul_pow]; norm_num
      calc
        _ = ((-1 : ℂ)^i * (-1 : ℂ)^i) *
            (epsilon (q + ((h : ℤ) - t) + 1) *
              ((-1 : ℂ)^t * integerBinomial r i * integerBinomial (p + r - i) t)) := by
          ac_rfl
        _ = _ := by rw [square, one_mul]; ac_rfl
    _ = ∑ i ∈ Finset.range N, ∑ t ∈ Finset.range (N - i),
        ∑ j ∈ Finset.range (N - (i + t)), F i t j := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [← Nat.sub_sub]
      exact Finset.sum_range_diag_flip (N - i) (F i)
    _ = ∑ l ∈ Finset.range N, ∑ j ∈ Finset.range (N - l),
        ∑ i ∈ Finset.range (l + 1), F i (l - i) j := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro l hl
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    _ = ∑ l ∈ Finset.range N, ∑ j ∈ Finset.range (N - l),
        signedTranslation T q j (((-1 : ℂ)^l * integerBinomial p l) • v l j) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ i ∈ Finset.range (l + 1),
            signedTranslation T q j (weight i (l - i) • v l j) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [F, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        _ = _ := by
          rw [← map_sum, ← Finset.sum_smul]
          congr 2
          simpa only [weight, add_comm p r] using signed_diagonal r p l
    _ = _ := by
      rw [triangle_comm]
      simp only [map_sum]

private theorem weighted_skew (trunc : LowerTruncated μ) {T : Module.End ℂ V}
    (q : ℤ) (a b : ℕ → V) (d : ℕ → ℤ) (w : ℕ → ℂ) (N : ℕ)
    (tail : ∀ i ≥ N, a i = 0 ∨ b i = 0) (skew : ∀ i, SkewAt μ T (a i) (b i)) :
    (∃ M : ℕ, ∀ j ≥ M,
      (∑ᶠ i : ℕ, (w i * epsilon (d i)) • μ (q + j + d i) (b i) (a i)) = 0) ∧
    (∑ᶠ i : ℕ, w i • μ (q + d i) (a i) (b i)) =
      ∑ᶠ j : ℕ, signedTranslation T q j
        (∑ᶠ i : ℕ, (w i * epsilon (d i)) • μ (q + j + d i) (b i) (a i)) := by
  classical
  choose cutoff hcutoff using fun i => offset_cutoff μ trunc (b i) (a i) (q + d i)
  let M := (Finset.range N).sup cutoff
  have cross_tail (i j : ℕ) (hi : i ∈ Finset.range N) (hj : M ≤ j) :
      μ (q + j + d i) (b i) (a i) = 0 := by
    rw [show q + (j : ℤ) + d i = q + d i + j by omega]
    exact hcutoff i j ((Finset.le_sup hi).trans hj)
  have inner_range (j : ℕ) :
      (∑ᶠ i : ℕ, (w i * epsilon (d i)) • μ (q + j + d i) (b i) (a i)) =
      ∑ i ∈ Finset.range N, (w i * epsilon (d i)) • μ (q + j + d i) (b i) (a i) := by
    apply finsum_range
    intro i hi
    rcases tail i hi with hz | hz <;> simp [hz]
  have outer_tail (j : ℕ) (hj : M ≤ j) :
      (∑ᶠ i : ℕ, (w i * epsilon (d i)) • μ (q + j + d i) (b i) (a i)) = 0 := by
    rw [inner_range]
    exact Finset.sum_eq_zero (fun i hi => by rw [cross_tail i j hi hj, smul_zero])
  refine ⟨⟨M, outer_tail⟩, ?_⟩
  rw [finsum_range (N := N) (fun i hi => by
      rcases tail i hi with hz | hz <;> simp [hz]),
    finsum_range (N := M) (fun j hj => by rw [outer_tail j hj, map_zero])]
  simp_rw [inner_range, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [skew i, finsum_range (N := M) (fun j hj => by
    rw [show q + d i + (j : ℤ) = q + j + d i by omega,
      cross_tail i j hi hj, map_zero, smul_zero]), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [signedTranslation, LinearMap.smul_apply, map_smul, smul_smul]
  rw [show q + d i + (j : ℤ) + 1 = (q + j + 1) + d i by omega,
    epsilon_add, show q + d i + (j : ℤ) = q + j + d i by omega]
  congr 1
  ac_rfl

private theorem signed_product (trunc : LowerTruncated μ) (a b c : V) (p q r : ℤ) :
    epsilon r • product μ a b c p q r =
      ∑ᶠ i : ℕ, (epsilon (r - i) * integerBinomial r i) •
        μ (p + r - i) a (μ (q + i) b c) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ trunc b c q
  unfold product
  rw [finsum_range (N := N) (fun i hi => by rw [tail i hi, map_zero, smul_zero]),
    finsum_range (N := N) (fun i hi => by rw [tail i hi, map_zero, smul_zero]),
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, epsilon_sub_nat, mul_assoc]

private theorem iterate_swap_last (trunc : LowerTruncated μ) {T : Module.End ℂ V}
    {a b c : V} {r : ℤ} (skew : ∀ i : ℕ, SkewAt μ T (μ (r + i) a b) c)
    (p q : ℤ) :
    (∃ N : ℕ, ∀ j ≥ N, epsilon p • product μ c a b (q + j) r p = 0) ∧
    iterate μ a b c p q r =
      ∑ᶠ j : ℕ, signedTranslation T q j (epsilon p • product μ c a b (q + j) r p) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ trunc a b r
  have h := weighted_skew μ trunc q (fun i => μ (r + i) a b) (fun _ => c)
    (fun i => p - i) (integerBinomial p) N (fun i hi => Or.inl (tail i hi)) skew
  simp_rw [signed_product μ trunc]
  simpa only [iterate, add_sub_assoc, add_comm p q, mul_comm (integerBinomial p _)] using h

private theorem reverse_swap_last (trunc : LowerTruncated μ) {T : Module.End ℂ V}
    {a b c : V} {p : ℤ} (skew : ∀ i : ℕ, SkewAt μ T b (μ (p + i) a c))
    (q r : ℤ) :
    (∃ N : ℕ, ∀ j ≥ N, iterate μ a c b r (q + j) p = 0) ∧
    epsilon r • product μ b a c q p r =
      ∑ᶠ j : ℕ, signedTranslation T q j (iterate μ a c b r (q + j) p) := by
  obtain ⟨N, tail⟩ := offset_cutoff μ trunc a c p
  have h := weighted_skew μ trunc q (fun _ => b) (fun i => μ (p + i) a c)
    (fun i => r - i) (fun i => epsilon (r - i) * integerBinomial r i) N
    (fun i hi => Or.inr (tail i hi)) skew
  have cancel (i : ℕ) :
      epsilon (r - i) * integerBinomial r i * epsilon (r - i) = integerBinomial r i := by
    rw [mul_comm (epsilon (r - i)) (integerBinomial r i), mul_assoc, sign_square, mul_one]
  simp only [cancel] at h
  rw [signed_product μ trunc]
  simpa only [iterate, ← add_sub_assoc, add_comm r (q + _)] using h

/-- Exchanging the last two states translates the permuted defects with
test indices `(r, q+j, p)`. The three skew hypotheses are local to the input
pair and the composite states that occur in the two Borcherds branches. -/
theorem defect_swap_last (trunc : LowerTruncated μ) {T : Module.End ℂ V}
    (a b c : V) (p q r : ℤ) (translate : DividedModeTranslation μ T a)
    (skewBC : SkewAt μ T b c)
    (skewIterate : ∀ i : ℕ, SkewAt μ T (μ (r + i) a b) c)
    (skewReverse : ∀ i : ℕ, SkewAt μ T b (μ (p + i) a c)) :
    Function.HasFiniteSupport (fun j : ℕ => defect μ a c b r (q + j) p) ∧
    defect μ a b c p q r =
      ∑ᶠ j : ℕ, signedTranslation T q j (defect μ a c b r (q + j) p) := by
  obtain ⟨⟨N, tailP⟩, hP⟩ := product_swap_last μ trunc skewBC translate p q r
  obtain ⟨⟨M, tailQ⟩, hI⟩ := iterate_swap_last μ trunc skewIterate p q
  obtain ⟨⟨K, tailI⟩, hQ⟩ := reverse_swap_last μ trunc skewReverse q r
  let B := N + M + K
  have tail (j : ℕ) (hj : B ≤ j) : defect μ a c b r (q + j) p = 0 := by
    unfold B at hj
    unfold defect
    rw [tailP j (by omega), tailQ j (by omega), tailI j (by omega)]
    simp
  refine ⟨(Finset.range B).finite_toSet.subset (support_subset_range tail), ?_⟩
  unfold defect
  rw [hP, hQ, hI]
  rw [finsum_range (N := B) (fun j hj => by
        unfold B at hj; rw [tailP j (by omega), map_zero]),
      finsum_range (N := B) (fun j hj => by
        unfold B at hj; rw [tailI j (by omega), map_zero]),
      finsum_range (N := B) (fun j hj => by
        unfold B at hj; rw [tailQ j (by omega), map_zero]),
      finsum_range (N := B) (fun j hj => by
        rw [show _ - _ - _ = (0 : V) from tail j hj, map_zero])]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_sub]
  abel

end

end D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
