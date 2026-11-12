/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.claim; result=D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.result; claim=D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.claim
   digest: A positive biased-cube mixture refutes sixth-order top pairing transfer. -/

/-
proof_shape: scalar_prod_diff_bound: bind-only (consumers: top_order_bound).
proof_shape: inj_sum_product_bound: bind-only (consumers: top_order_bound).
proof_shape: partialPairing_six_convolution: bind-only (consumers: model_unit_transfer).
proof_shape: sixth_four_defect_lower: bind-only (consumers: model_four_defect_lower).
proof_shape: transfer_error_small: bind-only (consumers: deviation_lower_bound).
proof_shape: sixth_defect_lower: bind-only (consumers: deviation_lower_bound).
proof_shape: moment_values: bind-only (consumers: distinct_bound, subset_unit_moment,
  distinct_pair_formula, result).
proof_shape: model_character: bind-only (consumers: result).
proof_shape: model_positive: bind-only (consumers: result).
proof_shape: distinct_bound: content.
proof_shape: subsetDistinct_univ: bind-only (consumers: top_order_bound).
proof_shape: subset_unit_moment: content.
proof_shape: distinct_pair_formula: content.
proof_shape: subset_pair_formula: bind-only (consumers: top_order_bound).
proof_shape: top_order_bound: content.
proof_shape: model_unit_transfer: bind-only (consumers: deviation_lower_bound).
proof_shape: model_unit_pair: bind-only (consumers: model_four_defect_lower).
proof_shape: model_four_defect_lower: bind-only (consumers: deviation_lower_bound).
proof_shape: deviation_lower_bound: content.
proof_shape: sixth_ratio_limit: bind-only (consumers: result).
proof_shape: result: content.
escape_witness: Uniform rank-one cancellation bounds the six-label distinct pairing
  defect by 720 N^2. The positive four-label defect propagated through the fifteen
  one-edge partial pairings forces the full sixth pairing defect above N^3. The
  positive mixture has L/H tending to zero and supplies the counterexample in result.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FifthOrderTopOnlyRefutation
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticFourthExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectInversion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PerfectPairingCount

/-! A positive finite mixture separating top distinct and full pairing defects. -/

open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Perturbing each factor of a product of three bounded scalars by at most one costs
at most three times the square of the common bound. -/
private theorem scalar_prod_diff_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.card = 3) (f g : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B)
    (hd : ∀ i ∈ s, |f i - g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ 3 * B ^ 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  have hm (x y : α) (hx : x ∈ ({a, b, c} : Finset α))
      (hy : y ∈ ({a, b, c} : Finset α)) (F G : α → ℝ)
      (hF : ∀ i ∈ ({a, b, c} : Finset α), |F i| ≤ B)
      (hG : ∀ i ∈ ({a, b, c} : Finset α), |G i| ≤ B) :
      |F x| * |G y| ≤ B ^ 2 := by
    nlinarith [mul_le_mul (hF x hx) (hG y hy) (abs_nonneg (G y)) hB]
  have ha : |(f a - g a) * f b * f c| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 1 * |f b| * |f c| := by gcongr; exact hd a (by simp)
      _ ≤ B ^ 2 := by simpa using hm b c (by simp) (by simp) f f hf hf
  have hb : |g a * (f b - g b) * f c| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |g a| * 1 * |f c| := by gcongr; exact hd b (by simp)
      _ ≤ B ^ 2 := by simpa using hm a c (by simp) (by simp) g f hg hf
  have hc : |g a * g b * (f c - g c)| ≤ B ^ 2 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |g a| * |g b| * 1 := by gcongr; exact hd c (by simp)
      _ ≤ B ^ 2 := by simpa using hm a b (by simp) (by simp) g g hg hg
  simp only [Finset.prod_insert (show a ∉ ({b, c} : Finset α) by simp [hab, hac]),
    Finset.prod_insert (show b ∉ ({c} : Finset α) by simp [hbc]), Finset.prod_singleton]
  have he : f a * (f b * f c) - g a * (g b * g c) =
      (f a - g a) * f b * f c + g a * (f b - g b) * f c +
        g a * g b * (f c - g c) := by ring
  rw [he]
  calc
    _ ≤ |(f a - g a) * f b * f c + g a * (f b - g b) * f c| +
        |g a * g b * (f c - g c)| := abs_add_le _ _
    _ ≤ (|(f a - g a) * f b * f c| + |g a * (f b - g b) * f c|) +
        |g a * g b * (f c - g c)| := by gcongr; exact abs_add_le _ _
    _ ≤ 3 * B ^ 2 := by linarith

/-- Removing noninjective assignments from a sixth-order product sum changes it by at
most thirty-six times the fifth power of the number of available labels. -/
private theorem inj_sum_product_bound (N : ℕ) (hN : 6 ≤ N)
    (g : Fin 6 → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |(∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) -
        ∏ i, ∑ d, g i d| ≤ 36 * (N : ℝ)^5 := by
  classical
  let all : Finset (Fin 6 → Fin N) := Finset.univ
  let good : Finset (Fin 6 → Fin N) := all.filter Function.Injective
  let bad : Finset (Fin 6 → Fin N) := all.filter (fun x => ¬Function.Injective x)
  have hsplit :
      (∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) +
        ∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i) =
        ∑ x : Fin 6 → Fin N, ∏ i, g i (x i) := by
    exact Finset.sum_filter_add_sum_filter_not _ Function.Injective _
  have hall : (∑ x : Fin 6 → Fin N, ∏ i, g i (x i)) = ∏ i, ∑ d, g i d := by
    rw [← Fintype.prod_sum]
  have hcardbad : (bad.card : ℝ) ≤ 36 * (N : ℝ)^5 := by
    have hcardgood : good.card = N.descFactorial 6 := by
      let e : {x : Fin 6 → Fin N // Function.Injective x} ≃ (Fin 6 ↪ Fin N) :=
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      have he := Fintype.card_congr e
      rw [Fintype.card_embedding_eq] at he
      simpa only [good, all, Fintype.card_subtype, Fintype.card_fin] using he
    have hcardall : all.card = N ^ 6 := by simp [all, Fintype.card_fun]
    have hdisj : Disjoint good bad := by
      apply Finset.disjoint_left.mpr
      intro x hxg hxb
      exact (Finset.mem_filter.mp hxb).2 (Finset.mem_filter.mp hxg).2
    have hunion : good ∪ bad = all := by
      ext x
      simp only [good, bad, all, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      tauto
    have hc : good.card + bad.card = all.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [hcardall, hcardgood] at hc
    have hcast : (N.descFactorial 6 : ℝ) + (bad.card : ℝ) = (N : ℝ)^6 := by
      exact_mod_cast hc
    have hNreal : (6 : ℝ) ≤ N := by exact_mod_cast hN
    have hlowerNat := Nat.pow_sub_le_descFactorial N 6
    rw [show N + 1 - 6 = N - 5 by omega] at hlowerNat
    have hlower : ((N : ℝ) - 5)^6 ≤ (N.descFactorial 6 : ℝ) := by
      have hcastLower : ((N - 5 : ℕ) : ℝ)^6 ≤ (N.descFactorial 6 : ℝ) := by
        exact_mod_cast hlowerNat
      simpa only [Nat.cast_sub (by omega : 5 ≤ N), Nat.cast_ofNat] using hcastLower
    have hp : |(N : ℝ)^6 - ((N : ℝ) - 5)^6| ≤ 30 * (N : ℝ)^5 := by
      have h := abs_pow_sub_pow_le (a := (N : ℝ)) (b := (N : ℝ) - 5) (n := 6)
      have hm : max |(N : ℝ)| |(N : ℝ) - 5| = (N : ℝ) := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith), max_eq_left]
        linarith
      rw [hm, show (N : ℝ) - ((N : ℝ) - 5) = 5 by ring] at h
      norm_num at h ⊢
      nlinarith [h]
    have hle := (le_abs_self ((N : ℝ)^6 - ((N : ℝ) - 5)^6)).trans hp
    nlinarith [show (0 : ℝ) ≤ (N : ℝ)^5 by positivity]
  have hbad :
      |∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i)| ≤
        36 * (N : ℝ)^5 := by
    calc
      _ ≤ ∑ x : Fin 6 → Fin N with ¬Function.Injective x, |∏ i, g i (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin 6 → Fin N with ¬Function.Injective x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hg i (x i))
      _ = (bad.card : ℝ) := by simp [bad, all]
      _ ≤ _ := hcardbad
  have he : (∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) -
      ∏ i, ∑ d, g i d =
      -(∑ x : Fin 6 → Fin N with ¬Function.Injective x, ∏ i, g i (x i)) := by
    rw [← hall]
    linarith
  rw [he, abs_neg]
  exact hbad

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- When defects vanish in orders at most two, a convolution on at most six labels
contains only its empty and single-edge contributions. -/
private theorem partialPairing_six_convolution (U : Finset α) (hU : U.card ≤ 6)
    (N : ℝ) (δ : Finset α → ℝ)
    (hsmall : ∀ V ⊆ U, V.card ≤ 2 → δ V = 0) :
    (∑ P : Finset (Finset α) with IsPartialPairing U P,
      N ^ P.card * δ (U \ pairingSupport P)) =
      δ U + N * ∑ e ∈ U.powersetCard 2, δ (U \ e) := by
  let S : Finset (Finset (Finset α)) := Finset.univ.filter (IsPartialPairing U)
  let S₁ := S.filter (fun P => P.card = 1)
  have hmem (P : Finset (Finset α)) : P ∈ S ↔ IsPartialPairing U P := by
    simp [S]
  have hmem₁ (P : Finset (Finset α)) : P ∈ S₁ ↔ IsPartialPairing U P ∧ P.card = 1 := by
    simp [S₁, S]
  have hsingleton (e : Finset α) : {e} ∈ S₁ ↔ e ∈ U.powersetCard 2 := by
    simp [hmem₁, IsPartialPairing, pairingSupport, Finset.mem_powersetCard, and_comm]
  have h0 : (∅ : Finset (Finset α)) ∈ S := by
    simp [S, IsPartialPairing, pairingSupport]
  have h01 : (∅ : Finset (Finset α)) ∉ S₁ := by simp [hmem₁]
  have hsub : insert ∅ S₁ ⊆ S := by
    intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact h0
    · exact (Finset.mem_filter.mp hP).1
  have hreduced : (∑ P ∈ S, N ^ P.card * δ (U \ pairingSupport P)) =
      ∑ P ∈ insert ∅ S₁, N ^ P.card * δ (U \ pairingSupport P) := by
    symm
    apply Finset.sum_subset hsub
    intro P hP hnot
    have hP' := (hmem P).1 hP
    have hcard : 2 ≤ P.card := by
      have hne : P ≠ ∅ := fun he => hnot (Finset.mem_insert.mpr (Or.inl he))
      have hneq : P.card ≠ 1 := fun hc => hnot
        (Finset.mem_insert.mpr (Or.inr ((hmem₁ P).2 ⟨hP', hc⟩)))
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    rw [hsmall (U \ pairingSupport P) Finset.sdiff_subset
      (by rw [(pairing_remainder_card U P hP').1]; omega), mul_zero]
  have hsingle : (∑ e ∈ U.powersetCard 2, N * δ (U \ e)) =
      ∑ P ∈ S₁, N ^ P.card * δ (U \ pairingSupport P) := by
    apply Finset.sum_nbij' (fun e => {e}) pairingSupport
    · intro e he
      exact (hsingleton e).2 he
    · intro P hP
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp ((hmem₁ P).1 hP).2
      simpa [pairingSupport] using (hsingleton e).1 hP
    · intro e he
      simp [pairingSupport]
    · intro P hP
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp ((hmem₁ P).1 hP).2
      simp [pairingSupport]
    · intro e he
      simp [pairingSupport]
  change (∑ P ∈ S, N ^ P.card * δ (U \ pairingSupport P)) = _
  rw [hreduced, Finset.sum_insert h01, ← hsingle, ← Finset.mul_sum]
  simp [pairingSupport]

/-- A quantitative lower bound for the four-label defect of the sixth-order model. -/
private theorem sixth_four_defect_lower (N : ℝ) (hN : 100 ≤ N) :
    N ^ 2 / 2 ≤ Real.sqrt 15 * (N * (N - 1) * (N - 2) * (N - 3)) / N ^ 2 -
      3 * (N - 1) ^ 2 := by
  have hpos : 0 < N := by linarith
  have hslo : (15 : ℝ) / 4 ≤ Real.sqrt 15 := by
    have hs : 0 ≤ Real.sqrt 15 := by positivity
    nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
  have hshi : Real.sqrt 15 ≤ (4 : ℝ) := by
    have hs : 0 ≤ Real.sqrt 15 := by positivity
    nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
  have hp : N ^ 4 - 6 * N ^ 3 ≤ N * (N - 1) * (N - 2) * (N - 3) := by
    nlinarith [sq_nonneg N]
  rw [le_sub_iff_add_le, le_div_iff₀ (sq_pos_of_pos hpos)]
  have hprod := mul_le_mul_of_nonneg_left hp (show 0 ≤ Real.sqrt 15 by positivity)
  have hlarge : (0 : ℝ) ≤ N ^ 4 - 6 * N ^ 3 := by
    nlinarith [show 0 ≤ N^3 * (N - 6) by exact mul_nonneg (pow_nonneg hpos.le 3) (by linarith)]
  have hlo := mul_le_mul_of_nonneg_right hslo hlarge
  have hnp : 0 ≤ N^3 * (N - 100) := mul_nonneg (pow_nonneg hpos.le 3) (by linarith)
  have hnp₂ : 0 ≤ N^2 * (N - 100) := mul_nonneg (sq_nonneg N) (by linarith)
  nlinarith [hprod, hlo, hnp, hnp₂, sq_nonneg N]

/-- The transfer error is at most twice the cubic scale once its coefficient is below the square root. -/
private theorem transfer_error_small (N K : ℝ) (hN : 1 ≤ N) (hK : K ≤ Real.sqrt N) :
    K * N ^ 3 * (Real.sqrt (1 / N) + 1 / N) ≤ 2 * N ^ 3 := by
  have hpos : 0 < N := by linarith
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 hpos
  have hsN : Real.sqrt N ≤ N := by
    exact (Real.sqrt_le_left hpos.le).2 (by nlinarith)
  have hKN : K ≤ N := hK.trans hsN
  have h1 : K / Real.sqrt N ≤ 1 := (div_le_one₀ hspos).2 hK
  have h2 : K / N ≤ 1 := (div_le_one₀ hpos).2 hKN
  calc
    _ = N ^ 3 * (K / Real.sqrt N + K / N) := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
      ring
    _ ≤ N ^ 3 * (1 + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = _ := by ring

/-- Positive one-edge defects dominate the bounded top-order and transfer errors. -/
private theorem sixth_defect_lower (N C δ₆ δ₄ E V : ℝ)
    (hN : 1 ≤ N) (hC : C ≤ N) (h6 : |δ₆| ≤ C * N ^ 2)
    (h4 : N ^ 2 / 2 ≤ δ₄) (hE : |E| ≤ 2 * N ^ 3)
    (hV : V = δ₆ + 15 * N * δ₄ + E) :
    N ^ 3 ≤ V := by
  have hn : 0 ≤ N := by linarith
  have h6lo := (abs_le.mp h6).1
  have hElo := (abs_le.mp hE).1
  have hCmul := mul_le_mul_of_nonneg_right hC (sq_nonneg N)
  have h4mul := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 15*N)
  nlinarith [pow_nonneg hn 3]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SixthOrderTopPairingRefutation

noncomputable section
set_option autoImplicit false

open D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FifthOrderTopOnlyRefutation

def claim : Prop :=
  ∀ (C : ℝ), 1 ≤ C → ∀ (D : ℕ → FifthData),
    (∀ n, (D n).ℓ 1 = 1) →
    (∀ n (y : (D n).A), 0 ≤ (D n).ℓ (y * y)) →
    (∀ n d, (D n).ℓ ((D n).Y d) = 0) →
    (∀ n d, (D n).Y d ^ 2 = (D n).a • (D n).Y d + (D n).b • 1) →
    (∀ n, (D n).L ≤ (D n).H) →
    (∀ n, 1 ≤ (D n).L) →
    (∀ n, |(D n).a| ≤ C * (D n).L) →
    (∀ n, |(D n).b| ≤ C * (D n).L) →
    (∀ n, (Fintype.card (D n).ι : ℝ) ≤ C * (D n).H) →
    (∀ n r, 2 ≤ r → r < 6 → ∀ (g : Fin r → (D n).ι → ℝ),
      (∀ i d, |g i d| ≤ 1) →
      |distinctIndexMoment (D n).ℓ (D n).Y g| ≤
        C * (Real.sqrt ((D n).H * (D n).L)) ^ r) →
    (∀ n (g : Fin 6 → (D n).ι → ℝ), (∀ i d, |g i d| ≤ 1) →
      |subsetDistinctMoment (D n).ℓ (D n).Y g Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetDistinctMoment (D n).ℓ (D n).Y g)| ≤
        C * (Real.sqrt ((D n).H * (D n).L)) ^ 6 / (D n).H) →
    Tendsto (fun n => (D n).L / (D n).H) atTop (𝓝 0) →
    Tendsto (fun n =>
      (subsetFamilyMoment (D n).ℓ (D n).Y (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (D n).ℓ (D n).Y (fun (_ : Fin 6) _ => (1 : ℝ)))) /
        (Real.sqrt ((D n).H * (D n).L)) ^ 6) atTop (𝓝 0)

private def zValue : Fin 3 → ℝ :=
  ![Real.sqrt (Real.sqrt 15), -Real.sqrt (Real.sqrt 15), 0]

private def zWeight : Fin 3 → ℝ :=
  ![1 / (2 * Real.sqrt 15), 1 / (2 * Real.sqrt 15), 1 - 1 / Real.sqrt 15]

private def moment (j : ℕ) : ℝ := ∑ z : Fin 3, zWeight z * zValue z ^ j

private def modelFunctional (N : ℕ) : ((Fin N → Bool) → ℝ) →ₗ[ℝ] ℝ :=
  mixtureFunctional N zValue zWeight

private lemma moment_values :
    moment 0 = 1 ∧ moment 1 = 0 ∧ moment 2 = 1 ∧
      moment 3 = 0 ∧ moment 4 = Real.sqrt 15 ∧ moment 5 = 0 ∧ moment 6 = 15 := by
  have hs : (Real.sqrt 15)^2 = (15 : ℝ) := by norm_num
  have hsp : 0 ≤ Real.sqrt 15 := by positivity
  have hc : (Real.sqrt (Real.sqrt 15))^2 = Real.sqrt 15 :=
    Real.sq_sqrt hsp
  norm_num [moment, zWeight, zValue, Fin.sum_univ_succ]
  all_goals field_simp [ne_of_gt (show (0 : ℝ) < Real.sqrt 15 by positivity)]
  all_goals ring_nf
  all_goals simp only [show (Real.sqrt (Real.sqrt 15)) ^ 4 =
      ((Real.sqrt (Real.sqrt 15)) ^ 2) ^ 2 by ring,
    show (Real.sqrt (Real.sqrt 15)) ^ 6 =
      ((Real.sqrt (Real.sqrt 15)) ^ 2) ^ 3 by ring, hc, hs]
  all_goals norm_num
  all_goals rw [show (Real.sqrt 15)^3 = (Real.sqrt 15)^2 * Real.sqrt 15 by ring, hs]
  all_goals ring

private lemma model_character (N : ℕ) (T : Finset (Fin N)) :
    modelFunctional N (∏ d ∈ T, modelY N d) =
      moment T.card / Real.sqrt N ^ T.card := by
  simpa only [modelFunctional, moment] using
    (mixture_character N zValue zWeight T)

private lemma model_positive (N : ℕ) (hN : 4 ≤ N) (F : (Fin N → Bool) → ℝ) :
    0 ≤ modelFunctional N (F * F) := by
  apply mixture_positive N zValue zWeight
  · intro z
    have hc : |Real.sqrt (Real.sqrt 15)| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]
      have hs4 : (Real.sqrt 15 : ℝ) ≤ 4 := by
        nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
      nlinarith [show (Real.sqrt (Real.sqrt 15))^2 = Real.sqrt 15 by
        exact Real.sq_sqrt (by positivity)]
    have hz : |zValue z| ≤ 2 := by fin_cases z <;> simp [zValue, hc]
    have hs : (2 : ℝ) ≤ Real.sqrt N := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).2
      exact_mod_cast hN
    exact hz.trans hs
  · intro z
    fin_cases z
    · norm_num [zWeight]
    · norm_num [zWeight]
    · have hs1 : (1 : ℝ) ≤ Real.sqrt 15 := by
        have hsp : (0 : ℝ) ≤ Real.sqrt 15 := by positivity
        nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num,
          hsp, sq_nonneg (Real.sqrt 15 - 1)]
      have hp : 0 < Real.sqrt 15 := by positivity
      have hi : 1 / Real.sqrt 15 ≤ (1 : ℝ) := (div_le_one₀ hp).2 hs1
      dsimp [zWeight]
      linarith
  · exact_mod_cast (show 0 < N by omega)

private lemma distinct_bound (N r : ℕ) (hN : 0 < N) (hr : 2 ≤ r) (hr6 : r < 6)
    (g : Fin r → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |distinctIndexMoment (modelFunctional N) (modelY N) g| ≤
      4 * Real.sqrt N ^ r := by
  classical
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hm : |moment r| ≤ 4 := by
    interval_cases r <;> norm_num [moment_values.2.2.1, moment_values.2.2.2.1,
      moment_values.2.2.2.2.1, moment_values.2.2.2.2.2.1]
    · rw [abs_of_nonneg (by positivity)]
      nlinarith [show (Real.sqrt 15)^2 = (15 : ℝ) by norm_num]
  have hsum : |∑ x : Fin r → Fin N with Function.Injective x, ∏ i, g i (x i)| ≤
      (N : ℝ)^r := by
    calc
      _ ≤ ∑ x : Fin r → Fin N with Function.Injective x, |∏ i, g i (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin r → Fin N with Function.Injective x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hg i (x i))
      _ ≤ ∑ _x : Fin r → Fin N, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = _ := by simp
  rw [modelFunctional, mixture_distinct_moments, ← moment, abs_mul, abs_div, abs_of_pos (pow_pos hs r)]
  calc
    _ ≤ (4 / Real.sqrt N ^ r) * (N : ℝ)^r :=
      mul_le_mul (div_le_div_of_nonneg_right hm (by positivity)) hsum
        (abs_nonneg _) (by positivity)
    _ = 4 * Real.sqrt N ^ r := by
      have he : (N : ℝ)^r = Real.sqrt N ^ r * Real.sqrt N ^ r := by
        rw [← mul_pow, ← pow_two, Real.sq_sqrt (by positivity)]
      rw [he]
      field_simp


private lemma subsetDistinct_univ {N : ℕ} (ℓ : ((Fin N → Bool) → ℝ) →ₗ[ℝ] ℝ)
    (Y : Fin N → (Fin N → Bool) → ℝ) (g : Fin 6 → Fin N → ℝ) :
    subsetDistinctMoment ℓ Y g (Finset.univ : Finset (Fin 6)) =
      distinctIndexMoment ℓ Y g := by
  classical
  let e : (Finset.univ : Finset (Fin 6)) ≃ Fin 6 :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [subsetDistinctMoment, ← retained_assignment_reindex ℓ Y Finset.univ g]
  convert assignment_moment_reindex ℓ Y e (fun i => g i.val) using 1
  unfold distinctIndexMoment
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

private lemma subset_unit_moment {k : ℕ} (N : ℕ) (U : Finset (Fin k)) :
    subsetDistinctMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U =
      (moment U.card / Real.sqrt N ^ U.card) * (N.descFactorial U.card : ℝ) := by
  classical
  have hc : (Finset.univ.filter (Function.Injective : (Fin (Fintype.card U) → Fin N) → Prop)).card =
      N.descFactorial (Fintype.card U) := by
    let e : {x : Fin (Fintype.card U) → Fin N // Function.Injective x} ≃ (Fin (Fintype.card U) ↪ Fin N) :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x, x.injective⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have he := Fintype.card_congr e
    rw [Fintype.card_embedding_eq] at he
    simpa only [Fintype.card_subtype, Fintype.card_fin] using he
  have hR : subsetDistinctMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U =
      distinctIndexMoment (modelFunctional N) (modelY N)
        (fun (_ : Fin (Fintype.card U)) (_ : Fin N) => (1 : ℝ)) := by
    unfold subsetDistinctMoment distinctIndexMoment
    simp only [Fintype.card_coe]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  rw [hR, modelFunctional, mixture_distinct_moments, ← moment]
  simp only [Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one, hc, Fintype.card_coe]

private lemma distinct_pair_formula (N : ℕ) (f h : Fin N → ℝ) :
    distinctIndexMoment (modelFunctional N) (modelY N) ![f, h] =
      (1 / (N : ℝ)) *
        ((∑ d, f d) * (∑ d, h d) - ∑ d, f d * h d) := by
  classical
  have hsum :
      (∑ x : Fin 2 → Fin N with Function.Injective x, ∏ i, ![f, h] i (x i)) =
        ∑ d, ∑ e with d ≠ e, f d * h e := by
    simpa [Fin.prod_univ_two] using (sum_two (fun d e => f d * h e))
  have hoff : (∑ d, ∑ e with d ≠ e, f d * h e) =
      (∑ d, f d) * (∑ e, h e) - ∑ d, f d * h d := by
    simpa [Finset.sum_filter, Fintype.sum_mul_sum] using
      (FiolArbitraryTreePair.sum_off_diagonal (fun d e => f d * h e))
  rw [modelFunctional, mixture_distinct_moments, ← moment, hsum, moment_values.2.2.1]
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)]
  rw [hoff]

private lemma subset_pair_formula (N : ℕ) (g : Fin 6 → Fin N → ℝ)
    (e : Finset (Fin 6)) (he : e.card = 2) :
    subsetDistinctMoment (modelFunctional N) (modelY N) g e =
      (1 / (N : ℝ)) *
        ((∏ i ∈ e, ∑ d, g i d) - ∑ d, ∏ i ∈ e, g i d) := by
  classical
  let v : e ≃ Fin 2 := Fintype.equivOfCardEq (by simpa using he)
  let q : Fin 2 → Fin N → ℝ := fun j => g (v.symm j).val
  have hR : subsetDistinctMoment (modelFunctional N) (modelY N) g e =
      distinctIndexMoment (modelFunctional N) (modelY N) q := by
    unfold subsetDistinctMoment
    rw [← retained_assignment_reindex (modelFunctional N) (modelY N) e g]
    convert assignment_moment_reindex (modelFunctional N) (modelY N) v
      (fun i => g i.val) using 1
    unfold distinctIndexMoment
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  rw [hR]
  have hq : q = ![q 0, q 1] := by funext j; fin_cases j <;> rfl
  rw [hq, distinct_pair_formula]
  have hp : (∏ i ∈ e, ∑ d, g i d) =
      (∑ d, q 0 d) * (∑ d, q 1 d) := by
    simp only [q]
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, ∑ d, g i.val d) =
        ∏ j : Fin 2, ∑ d, q j d := by
      apply Fintype.prod_equiv v
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ, Fin.prod_univ_two] using hprod
  have ht : (∑ d, ∏ i ∈ e, g i d) = ∑ d, q 0 d * q 1 d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, g i.val d) = ∏ j : Fin 2, q j d := by
      apply Fintype.prod_equiv v
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ, Fin.prod_univ_two] using hprod
  rw [← hp, ← ht]


private lemma top_order_bound (N : ℕ) (hN : 6 ≤ N)
    (g : Fin 6 → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |subsetDistinctMoment (modelFunctional N) (modelY N) g Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetDistinctMoment (modelFunctional N) (modelY N) g)| ≤
      720 * (N : ℝ)^2 := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hNs2 : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hNs6 : (Real.sqrt N)^6 = (N : ℝ)^3 := by
    calc
      _ = ((Real.sqrt N)^2)^3 := by ring
      _ = _ := by rw [hNs2]
  let A : Fin 6 → ℝ := fun i => ∑ d, g i d
  let a : Finset (Fin 6) → ℝ := fun e => (1 / (N : ℝ)) * ∏ i ∈ e, A i
  let R : Finset (Fin 6) → ℝ := subsetDistinctMoment (modelFunctional N) (modelY N) g
  have hA (i : Fin 6) : |A i| ≤ N := by
    calc
      _ ≤ ∑ d : Fin N, |g i d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun d _ => hg i d)
      _ = _ := by simp
  have ha (e : Finset (Fin 6)) (he : e.card = 2) : |a e| ≤ N := by
    dsimp only [a]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ)), Finset.abs_prod]
    calc
      _ ≤ (1 / (N : ℝ)) * ∏ _i ∈ e, (N : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA i)
      _ = _ := by simp only [Finset.prod_const, he]; field_simp [ne_of_gt hNp]
  have ht (e : Finset (Fin 6)) :
      |(1 / (N : ℝ)) * ∑ d, ∏ i ∈ e, g i d| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
    calc
      _ ≤ (1 / (N : ℝ)) * ∑ d : Fin N, |∏ i ∈ e, g i d| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (1 / (N : ℝ)) * ∑ _d : Fin N, (1 : ℝ) := by
        gcongr with d
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => hg i d)
      _ = _ := by simp [ne_of_gt hNp]
  have hRa (e : Finset (Fin 6)) (he : e.card = 2) : |R e - a e| ≤ 1 := by
    have heq : R e - a e = -(1 / (N : ℝ) * ∑ d, ∏ i ∈ e, g i d) := by
      dsimp only [R, a, A]
      rw [subset_pair_formula N g e he]
      ring
    rw [heq, abs_neg]
    exact ht e
  have hR (e : Finset (Fin 6)) (he : e.card = 2) : |R e| ≤ 2 * N := by
    calc
      _ = |R e - a e + a e| := by congr 1; ring
      _ ≤ |R e - a e| + |a e| := abs_add_le _ _
      _ ≤ 1 + N := add_le_add (hRa e he) (ha e he)
      _ ≤ _ := by linarith
  have hcount : ((Finset.univ : Finset (Finset (Finset (Fin 6)))).filter
      (IsPerfectPairing Finset.univ)).card = 15 := by
    rw [perfectPairingCount]
    norm_num [Nat.doubleFactorial]
  have hpoly : |finitePairingPolynomial Finset.univ R -
      finitePairingPolynomial Finset.univ a| ≤ 180 * (N : ℝ)^2 := by
    unfold finitePairingPolynomial
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ P : Finset (Finset (Fin 6)) with IsPerfectPairing Finset.univ P,
          |(∏ e ∈ P, R e) - ∏ e ∈ P, a e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _P : Finset (Finset (Fin 6)) with IsPerfectPairing Finset.univ _P,
          12 * (N : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro P hP
        have hp := (Finset.mem_filter.mp hP).2
        have hc := hp.card
        have hpc : P.card = 3 := by simp only [Finset.card_univ, Fintype.card_fin] at hc; omega
        have hb := scalar_prod_diff_bound P hpc R a (2 * N) (by positivity)
          (fun e he => hR e (hp.1.1 e he))
          (fun e he => (ha e (hp.1.1 e he)).trans (by linarith))
          (fun e he => hRa e (hp.1.1 e he))
        nlinarith [hb]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcount]; norm_num; ring
  have harank (e : Finset (Fin 6)) (he : e.card = 2) :
      a e = ∏ i ∈ e, A i / Real.sqrt N := by
    dsimp only [a]
    rw [Finset.prod_div_distrib, Finset.prod_const, he, hNs2]
    ring
  have hleading : finitePairingPolynomial Finset.univ a =
      (15 / Real.sqrt N ^ 6) * ∏ i, A i := by
    rw [finitePairingPolynomial_rankOne _ a (fun i => A i / Real.sqrt N) harank,
      hcount, Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
    ring
  have htop : |R Finset.univ - (15 / Real.sqrt N ^ 6) * ∏ i, A i| ≤
      540 * (N : ℝ)^2 := by
    have hi := inj_sum_product_bound N hN g hg
    have heq : R Finset.univ - (15 / Real.sqrt N ^ 6) * ∏ i, A i =
        (15 / Real.sqrt N ^ 6) *
          ((∑ x : Fin 6 → Fin N with Function.Injective x, ∏ i, g i (x i)) -
            ∏ i, ∑ d, g i d) := by
      dsimp only [R, A]
      rw [subsetDistinct_univ, modelFunctional, mixture_distinct_moments, ← moment, moment_values.2.2.2.2.2.2]
      ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 15 / Real.sqrt N ^ 6)]
    calc
      _ ≤ (15 / Real.sqrt N ^ 6) * (36 * (N : ℝ)^5) := by
        exact mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by rw [hNs6]; field_simp [ne_of_gt hNp]; ring
  change |R Finset.univ - finitePairingPolynomial Finset.univ R| ≤ _
  rw [← hleading] at htop
  have heq : R Finset.univ - finitePairingPolynomial Finset.univ R =
      (R Finset.univ - finitePairingPolynomial Finset.univ a) -
        (finitePairingPolynomial Finset.univ R - finitePairingPolynomial Finset.univ a) := by ring
  rw [heq]
  calc
    _ ≤ |R Finset.univ - finitePairingPolynomial Finset.univ a| +
        |finitePairingPolynomial Finset.univ R - finitePairingPolynomial Finset.univ a| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (R Finset.univ - finitePairingPolynomial Finset.univ a) 0
          (finitePairingPolynomial Finset.univ R - finitePairingPolynomial Finset.univ a)
    _ ≤ _ := by linarith [htop, hpoly]

-- DEVIATION

private lemma model_unit_transfer (N : ℕ) (hN : 4 ≤ N) :
    ∃ E : ℝ,
      subsetFamilyMoment (modelFunctional N) (modelY N)
          (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (modelFunctional N) (modelY N)
            (fun (_ : Fin 6) _ => (1 : ℝ))) =
        subsetPairingDefect (modelFunctional N) (modelY N)
            (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ +
          (N : ℝ) * ∑ e ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
            subsetPairingDefect (modelFunctional N) (modelY N)
              (fun (_ : Fin 6) _ => (1 : ℝ)) (Finset.univ \ e) + E ∧
      |E| ≤ pairingDefectConstant 6 4 * Real.sqrt N ^ 6 *
        (Real.sqrt (1 / (N : ℝ)) + 1 / N) := by
  classical
  have hunit : modelFunctional N 1 = 1 := by
    simpa only [Finset.prod_empty, Finset.card_empty, pow_zero, div_one, moment_values.1]
      using model_character N ∅
  have hcenter : ∀ d, modelFunctional N (modelY N d) = 0 := by
    intro d
    simpa only [Finset.prod_singleton, Finset.card_singleton, pow_one,
      moment_values.2.1, zero_div] using model_character N {d}
  have hquad : ∀ d, modelY N d ^ 2 = (0 : ℝ) • modelY N d + (1 : ℝ) • 1 := by
    intro d
    funext ω
    change sign (ω d)^2 = 0 * sign (ω d) + 1 * 1
    cases ω d <;> norm_num [sign]
  have hR : DisjointLabelMomentBound (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) _ => (1 : ℝ)) 4 (Real.sqrt ((N : ℝ) * 1)) := by
    intro r hr hr6 labels _ _
    simp only [Finset.prod_const_one, mul_one]
    have hb := distinct_bound N r (by omega) hr hr6 (fun _ _ => 1) (by simp)
    convert hb using 1
    congr 1
    unfold distinctIndexMoment
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  obtain ⟨E, _, hE, hb⟩ := quadratic_pairing_defect_transfer
    (modelFunctional N) (modelY N) (fun (_ : Fin 6) _ => (1 : ℝ))
    0 1 4 N 1 (by norm_num) (by exact_mod_cast (show 1 ≤ N by omega))
    (by norm_num) (by norm_num) (by norm_num) hquad hunit hcenter
    (by
      simp only [Fintype.card_fin]
      have hn : (0 : ℝ) ≤ N := by positivity
      linarith) (by simp) hR
  have hcollapse := partialPairing_six_convolution (Finset.univ : Finset (Fin 6))
    (by simp) (N : ℝ)
    (subsetPairingDefect (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) _ => (1 : ℝ)))
    (fun V _ hV => subset_pairing_defect_small (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) _ => (1 : ℝ)) hunit hcenter V hV)
  simp only [subsetWeightSum, indexSum, Finset.prod_const, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at hE
  rw [hcollapse] at hE
  refine ⟨E, ?_, ?_⟩
  · simpa only [subsetFamilyMoment, quadraticFamilyMoment] using hE
  · simpa only [mul_one] using hb

private lemma model_unit_pair {k : ℕ} (N : ℕ) (hN : 4 ≤ N)
    (e : Finset (Fin k)) (he : e.card = 2) :
    subsetDistinctMoment (modelFunctional N) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) e = (N : ℝ) - 1 := by
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hc : (N.descFactorial 2 : ℝ) = (N : ℝ) * (N - 1) := by
    norm_num [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  rw [subset_unit_moment, he, moment_values.2.2.1,
    Real.sq_sqrt (by positivity), hc]
  field_simp [hNz]

private lemma model_four_defect_lower (N : ℕ) (hN : 100 ≤ N)
    (U : Finset (Fin 6)) (hU : U.card = 4) :
    (N : ℝ) ^ 2 / 2 ≤ subsetPairingDefect (modelFunctional N) (modelY N)
      (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ)) U := by
  classical
  have hpoly : finitePairingPolynomial U
      (subsetDistinctMoment (modelFunctional N) (modelY N)
        (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ))) = 3 * ((N : ℝ) - 1)^2 := by
    rw [finitePairingPolynomial_const U _ ((N : ℝ) - 1)
      (fun e he => model_unit_pair N (by omega) e he), perfectPairingCount U]
    norm_num [hU, Nat.doubleFactorial]
  have hc : (N.descFactorial 4 : ℝ) =
      (N : ℝ) * (N - 1) * (N - 2) * (N - 3) := by
    norm_num [Nat.descFactorial_succ, Nat.cast_sub (by omega : 1 ≤ N),
      Nat.cast_sub (by omega : 2 ≤ N), Nat.cast_sub (by omega : 3 ≤ N)]
    ring
  have hs : Real.sqrt N ^ 4 = (N : ℝ)^2 := by
    calc
      _ = (Real.sqrt N ^ 2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  rw [subsetPairingDefect, hpoly, subset_unit_moment N U, hU,
    moment_values.2.2.2.2.1, hs, hc]
  convert sixth_four_defect_lower (N : ℝ) (by exact_mod_cast hN) using 1 <;> ring

private lemma deviation_lower_bound (N : ℕ) (hN : 1000 ≤ N)
    (hK : pairingDefectConstant 6 4 ≤ Real.sqrt N) :
    Real.sqrt N ^ 6 ≤
      subsetFamilyMoment (modelFunctional N) (modelY N)
          (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (modelFunctional N) (modelY N)
            (fun (_ : Fin 6) _ => (1 : ℝ))) := by
  classical
  obtain ⟨E, hid, hEb⟩ := model_unit_transfer N (by omega)
  have hs : Real.sqrt N ^ 6 = (N : ℝ)^3 := by
    calc
      _ = (Real.sqrt N ^ 2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have hEs : |E| ≤ 2 * (N : ℝ)^3 := by
    rw [hs] at hEb
    exact hEb.trans (transfer_error_small N (pairingDefectConstant 6 4)
      (by exact_mod_cast (show 1 ≤ N by omega)) hK)
  let Δ := subsetPairingDefect (modelFunctional N) (modelY N)
    (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ))
  let S := ∑ e ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, Δ (Finset.univ \ e)
  have hsum : 15 * (N : ℝ)^2 / 2 ≤ S := by
    calc
      _ = ∑ _e ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2, (N : ℝ)^2 / 2 := by
        norm_num [Finset.card_powersetCard, Nat.choose] <;> ring
      _ ≤ S := by
        apply Finset.sum_le_sum
        intro e he
        apply model_four_defect_lower N (by omega)
        have he' := Finset.mem_powersetCard.mp he
        rw [Finset.card_sdiff_of_subset he'.1]
        simp [he'.2]
  have h6 : |Δ Finset.univ| ≤ 720 * (N : ℝ)^2 := by
    simpa only [Δ, subsetPairingDefect] using
      top_order_bound N (by omega) (fun (_ : Fin 6) (_ : Fin N) => (1 : ℝ)) (by simp)
  have hv := sixth_defect_lower (N : ℝ) 720 (Δ Finset.univ) (S / 15) E
    (subsetFamilyMoment (modelFunctional N) (modelY N)
        (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
      finitePairingPolynomial Finset.univ
        (subsetFamilyMoment (modelFunctional N) (modelY N)
          (fun (_ : Fin 6) _ => (1 : ℝ))))
    (by exact_mod_cast (show 1 ≤ N by omega))
    (by exact_mod_cast (show 720 ≤ N by omega)) h6
    (by apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 15)).2; nlinarith)
    hEs (by dsimp only [Δ, S] at *; linarith [hid])
  simpa only [hs] using hv

private def sixthCounterData (offset n : ℕ) : FifthData where
  ι := Fin (n + offset)
  A := (Fin (n + offset) → Bool) → ℝ
  ℓ := modelFunctional (n + offset)
  Y := modelY (n + offset)
  a := 0
  b := 1
  H := ((n + offset : ℕ) : ℝ)
  L := 1

private lemma sixth_ratio_limit (offset : ℕ) :
    Tendsto (fun n : ℕ => (sixthCounterData offset n).L /
      (sixthCounterData offset n).H) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n + offset : ℕ) : ℝ)) atTop (𝓝 0)
  simp only [Nat.cast_add, one_div]
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (offset : ℝ) tendsto_natCast_atTop_atTop)


set_option backward.isDefEq.respectTransparency false in
/-- The positive biased-cube mixture refutes the sixth-order top-pairing implication. -/
theorem result : ¬ claim := by
  classical
  intro hclaim
  let K := pairingDefectConstant 6 4
  obtain ⟨offset, hoffset⟩ := exists_nat_ge (max (1000 : ℝ) (K^2))
  have hsize (n : ℕ) : (1000 : ℝ) ≤ ((n + offset : ℕ) : ℝ) := by
    have := (le_max_left (1000 : ℝ) (K^2)).trans hoffset
    push_cast at *
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hsizeNat (n : ℕ) : 1000 ≤ n + offset := by exact_mod_cast hsize n
  have hsqrt (n : ℕ) : K ≤ Real.sqrt ((n + offset : ℕ) : ℝ) := by
    have hKsq : K^2 ≤ ((n + offset : ℕ) : ℝ) := by
      have := (le_max_right (1000 : ℝ) (K^2)).trans hoffset
      push_cast at *
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    exact (le_abs_self K).trans ((Real.le_sqrt (abs_nonneg K) (by positivity)).2
      (by simpa only [sq_abs] using hKsq))
  let D := sixthCounterData offset
  have hone : ∀ n, (D n).ℓ 1 = 1 := by
    intro n
    dsimp only [D, sixthCounterData]
    simpa only [Finset.prod_empty, Finset.card_empty, pow_zero, div_one, moment_values.1]
      using model_character (n + offset) ∅
  have hpositive : ∀ n (y : (D n).A), 0 ≤ (D n).ℓ (y * y) := by
    intro n y
    exact model_positive (n + offset) (by have := hsizeNat n; omega) y
  have hcenter : ∀ n d, (D n).ℓ ((D n).Y d) = 0 := by
    intro n d
    dsimp only [D, sixthCounterData] at d ⊢
    simpa only [Finset.prod_singleton, Finset.card_singleton, pow_one,
      moment_values.2.1, zero_div] using model_character (n + offset) {d}
  have hquad : ∀ n d, (D n).Y d ^ 2 = (D n).a • (D n).Y d + (D n).b • 1 := by
    intro n d
    funext ω
    change sign (ω d)^2 = 0 * sign (ω d) + 1 * 1
    cases ω d <;> norm_num [sign]
  have hlower : ∀ n r, 2 ≤ r → r < 6 → ∀ (g : Fin r → (D n).ι → ℝ),
      (∀ i d, |g i d| ≤ 1) →
      |distinctIndexMoment (D n).ℓ (D n).Y g| ≤
        720 * Real.sqrt ((D n).H * (D n).L)^r := by
    intro n r hr hr6 g hg
    dsimp only [D, sixthCounterData] at g hg ⊢
    simp only [mul_one]
    exact (distinct_bound (n + offset) r (by have := hsizeNat n; omega) hr hr6 g hg).trans
      (by gcongr; norm_num)
  have htop : ∀ n (g : Fin 6 → (D n).ι → ℝ), (∀ i d, |g i d| ≤ 1) →
      |subsetDistinctMoment (D n).ℓ (D n).Y g Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetDistinctMoment (D n).ℓ (D n).Y g)| ≤
        720 * Real.sqrt ((D n).H * (D n).L)^6 / (D n).H := by
    intro n g hg
    dsimp only [D, sixthCounterData] at g hg ⊢
    simp only [mul_one]
    have hb := top_order_bound (n + offset) (by have := hsizeNat n; omega) g hg
    have hpos : (0 : ℝ) < ((n + offset : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n + offset by have := hsizeNat n; omega)
    have hs : Real.sqrt ((n + offset : ℕ) : ℝ)^6 = ((n + offset : ℕ) : ℝ)^3 := by
      calc
        _ = (Real.sqrt ((n + offset : ℕ) : ℝ)^2)^3 := by ring
        _ = _ := by rw [Real.sq_sqrt hpos.le]
    rw [hs]
    convert hb using 1 <;> field_simp [ne_of_gt hpos] <;> ring
  have hlimit := hclaim 720 (by norm_num) D hone hpositive hcenter hquad
    (by intro n; change (1 : ℝ) ≤ ((n + offset : ℕ) : ℝ); linarith [hsize n])
    (by intro n; exact le_refl 1)
    (by intro n; norm_num [D, sixthCounterData])
    (by intro n; norm_num [D, sixthCounterData])
    (by intro n
        change (Fintype.card (Fin (n + offset)) : ℝ) ≤
          720 * ((n + offset : ℕ) : ℝ)
        rw [Fintype.card_fin]
        have hn : (0 : ℝ) ≤ ((n + offset : ℕ) : ℝ) := by positivity
        linarith)
    hlower htop (sixth_ratio_limit offset)
  have hev := hlimit.eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hev
  have hb := deviation_lower_bound (n + offset) (hsizeNat n) (hsqrt n)
  have hspos : 0 < Real.sqrt ((n + offset : ℕ) : ℝ)^6 := by
    apply pow_pos
    apply Real.sqrt_pos.2
    exact_mod_cast (show 0 < n + offset by have := hsizeNat n; omega)
  have hl : (1 : ℝ) ≤
      (subsetFamilyMoment (D n).ℓ (D n).Y
          (fun (_ : Fin 6) _ => (1 : ℝ)) Finset.univ -
        finitePairingPolynomial Finset.univ
          (subsetFamilyMoment (D n).ℓ (D n).Y
            (fun (_ : Fin 6) _ => (1 : ℝ)))) /
        Real.sqrt ((D n).H * (D n).L)^6 := by
    dsimp only [D, sixthCounterData]
    simp only [mul_one]
    exact (le_div_iff₀ hspos).2 (by simpa only [one_mul] using hb)
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SixthOrderTopPairingRefutation
