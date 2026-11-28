/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global Hilbert gain reconstruction with an ordered triangle invariant. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.HilbertGlobalSubJungCertificate
import OmegaMath.Combinatorics.Graph.ChordalOrderedResidualExtension
import OmegaMath.Combinatorics.Graph.ChordalAbelianReduction
import OmegaMath.Combinatorics.Graph.HilbertWeightedEnergy
import OmegaMath.Combinatorics.Graph.HilbertWeightedTransfer
import OmegaMath.Combinatorics.Graph.HilbertPairCharges
import OmegaMath.Combinatorics.Graph.HilbertPrefixDeficit
import Mathlib.Algebra.Order.Chebyshev

/-! # Hilbert gain reconstruction below the Jung threshold -/

compile_only_with_mathlib

open scoped BigOperators

namespace SimpleGraph

open ChordalResidualExtension HilbertGlobalSubJungCertificate HilbertWeightedEnergy
open HilbertPairCharges (pairs)

universe u v

variable {V : Type u} {E : Type v} [Finite V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {G : SimpleGraph V}

private theorem scale_defect (C : ℝ) (hG : G.IsChordal)
    (fit : ∀ f : V → V → E, Skew f →
      (∀ i j k, Triangle G i j k → ‖holonomy f i j k‖ ≤ 1) →
      ∃ p : V → E, ∀ i j, G.Adj i j → ‖residual f p i j‖ ≤ C)
    (g : V → V → E) (D : ℝ) (hD : 0 ≤ D) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ D) :
    ∃ p : V → E, ∀ i j, G.Adj i j → ‖g i j + p i - p j‖ ≤ C * D := by
  by_cases h : D = 0
  · subst D
    obtain ⟨p, hp⟩ := GainReduction.integrate hG g (fun i j _ => hg i j)
      (fun i j k hij hjk hik =>
        sub_eq_zero.mp (norm_le_zero_iff.mp (ht i j k ⟨hij, hjk, hik⟩)))
    refine ⟨p, fun i j hij => ?_⟩
    rw [hp i j hij]
    have hzero : p j - p i + p i - p j = 0 := by abel
    simp [hzero]
  have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm h)
  let f (i j : V) := D⁻¹ • g i j
  have hf : Skew f := fun i j => by simp [f, hg i j, smul_neg]
  have hft (i j k : V) (hT : Triangle G i j k) : ‖holonomy f i j k‖ ≤ 1 := by
    simp only [holonomy, f, ← smul_add, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hD)]
    exact (mul_le_mul_of_nonneg_left (ht i j k hT) (inv_nonneg.mpr hD)).trans_eq
      (inv_mul_cancel₀ h)
  obtain ⟨p, hp⟩ := fit f hf hft
  refine ⟨fun i => D • p i, fun i j hij => ?_⟩
  have eq : g i j + D • p i - D • p j = D • residual f p i j := by
    simp only [ChordalResidualExtension.residual, f, smul_sub, smul_smul, mul_inv_cancel₀ h, one_smul]
    abel
  rw [eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hD, mul_comm C D]
  exact mul_le_mul_of_nonneg_left (hp i j hij) hpos.le

private theorem diagonal_credit {n N : ℕ} (hN : 1 ≤ N) (hn : n ≤ N)
    (p : Fin n → ℝ) (hp : ∑ i, p i = 1) :
    57 / (10 * (N : ℝ)) ≤ (57 / 10) * ∑ i, p i ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := p)
  rw [hp, one_pow, Finset.card_univ, Fintype.card_fin] at hcs
  have hcard : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_right hcard
    (Finset.sum_nonneg fun i _ => sq_nonneg (p i)))
  have hrec : 1 / (N : ℝ) ≤ ∑ i, p i ^ 2 := (div_le_iff₀ hN').2 (by linarith)
  calc
    _ = (57 / 10) * (1 / (N : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by norm_num)

private theorem sub_jung_comparisons :
    (241361 / 100000 : ℝ) < 2414 / 1000 ∧
      (2414 / 1000 : ℝ) < 1 + Real.sqrt 2 ∧
      (3 / 5000 : ℝ) < 1 + Real.sqrt 2 - 241361 / 100000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h := Real.sqrt_nonneg (2 : ℝ)
  have hstrict : (141421 / 100000 : ℝ) < Real.sqrt 2 := by
    by_contra! hn
    have hsq := pow_le_pow_left₀ h hn 2
    rw [hs] at hsq
    norm_num at hsq
  constructor
  · norm_num
  constructor <;> linarith

private theorem diagonal_sqrt_le_linear {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt ((241361 / 100000 : ℝ) ^ 2 - 57 / (10 * (N : ℝ))) ≤
      241361 / 100000 - 59 / (50 * (N : ℝ)) := by
  let R : ℝ := 241361 / 100000
  let x : ℝ := 1 / (N : ℝ)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0 : ℝ) < N := by linarith
  have h₀ : 0 ≤ x := div_nonneg zero_le_one hN₀.le
  have h₁ : x ≤ 1 := (div_le_one hN₀).mpr hN'
  have h₅₇ : (57 / (10 * (N : ℝ)) : ℝ) = (57 / 10 : ℝ) * x := by dsimp [x]; ring
  have h₅₉ : (59 / (50 * (N : ℝ)) : ℝ) = (59 / 50 : ℝ) * x := by dsimp [x]; ring
  rw [h₅₇, h₅₉]
  change Real.sqrt (R ^ 2 - (57 / 10) * x) ≤ R - (59 / 50) * x
  apply (Real.sqrt_le_iff).2
  constructor
  · dsimp [R]; linarith
  · have hc : 0 ≤ (57 / 10 : ℝ) - 2 * R * (59 / 50) := by norm_num [R]
    nlinarith [mul_nonneg hc h₀, sq_nonneg ((59 / 50 : ℝ) * x)]

private noncomputable def triangleInvariant (x y z t : E) : Prop :=
  F (inner ℝ x t / R) ≤ w * (r - ‖x‖ ^ 2) + (r - ‖y‖ ^ 2) + (r - ‖z‖ ^ 2)

private theorem reconstruct_with_credit (hG : G.IsChordal) (s : ℝ)
    (hs : 0 ≤ s) (sizeAllowed : ℕ → Prop)
    (hsize : ∀ S : Finset V, G.IsClique (S : Set V) → S.Nonempty → sizeAllowed (S.card - 1))
    (hcredit : ∀ n, sizeAllowed n → ∀ p : Fin n → ℝ,
      (∑ i, p i = 1) → s ≤ (57 / 10) * ∑ i, p i ^ 2)
    (place : ∀ n, ∀ (c : Fin n → E) (e : Fin n → Fin n → E), Skew e →
      (∀ i j, i < j → ‖e i j‖ ≤ R) →
      (∀ i j k, i < j → j < k → ‖holonomy e i j k‖ ≤ 1 ∧
        triangleInvariant (e i j) (e i k) (e j k) (holonomy e i j k)) →
      (∀ i j, i < j → ‖e i j - (c i - c j)‖ ≤ 1) →
      (∀ p : Fin n → ℝ, (∑ i, p i = 1) → s ≤ (57 / 10) * ∑ i, p i ^ 2) →
      ∃ z, (∀ i, ‖c i - z‖ ^ 2 ≤ r - s) ∧
        ∀ i j, i < j →
          triangleInvariant (e i j) (c i - z) (c j - z) (e i j - (c i - c j)))
    (g : V → V → E) (D : ℝ) (hD : 0 ≤ D) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ D) :
    ∃ p : V → E, ∀ i j, G.Adj i j → ‖g i j + p i - p j‖ ≤ Real.sqrt (r - s) * D := by
  apply scale_defect _ hG _ g D hD hg ht
  intro f hf hft
  apply reconstruct_ordered hG _ triangleInvariant sizeAllowed hsize _ f hf hft
  intro n hn c e he hedge hface hcurl
  have hR : 0 ≤ R := by rw [constants.1]; norm_num
  have hcap : Real.sqrt (r - s) ≤ R := by
    rw [← Real.sqrt_sq hR]
    apply Real.sqrt_le_sqrt
    rw [constants.2.1]
    linarith
  obtain ⟨z, hz, hzface⟩ := place n c e he
    (fun i j hij => (hedge i j hij).trans hcap) hface hcurl (hcredit n hn)
  exact ⟨z, fun i => by
    rw [← Real.sqrt_sq (norm_nonneg (c i - z))]
    exact Real.sqrt_le_sqrt (hz i), hzface⟩

private theorem mixture_credit (V A edgeDefect curlDefect meanEnergy curlEnergy charge bound : ℝ)
    (hA : 0 ≤ A) (he : 0 ≤ curlDefect)
    (varianceLoss : U - V = U * A + edgeDefect / a + curlDefect / b +
      nu0 * (curlEnergy + 2 * meanEnergy))
    (transfer : charge ≤ lambda * (edgeDefect + c * A) +
      2 * nu0 * meanEnergy + nu1 * curlEnergy + bound)
    (flat : c * I - c * K * A - gamma * I0 * curlEnergy ≤ 2 * edgeDefect)
    (baseline : U - r - rho * c * I / (2 * a) + bound ≤ 0) :
    V - r + charge ≤ -(57 / 10) * A := by
  have ha : 0 < a := lt_trans (by norm_num) numerical_conditions.1
  have hb : 0 < b := numerical_conditions.2.2.1
  have hρ : 0 ≤ rho := by norm_num [rho, Data.rho]
  have hLambda : lambda = (1 - rho) / a := constants.2.2.2.2.2.2.1
  have hν : nu1 = nu0 - rho * gamma * I0 / (2 * a) := constants.2.2.2.2.2.2.2.2
  have hcoef : 57 / 10 ≤ U - lambda * c - rho * c * K / (2 * a) :=
    le_of_lt numerical_conditions.2.2.2.2.2.2.2.2.2.2.2.1
  have hflat := mul_le_mul_of_nonneg_left flat (div_nonneg hρ (by positivity : 0 ≤ 2 * a))
  have hdiag := mul_le_mul_of_nonneg_right hcoef hA
  have hcurl : 0 ≤ curlDefect / b := div_nonneg he hb.le
  have hLambdae : edgeDefect / a - lambda * edgeDefect = rho / (2 * a) * (2 * edgeDefect) := by
    rw [hLambda]; field_simp; ring
  have hνe : nu0 * curlEnergy - nu1 * curlEnergy =
      rho / (2 * a) * (gamma * I0 * curlEnergy) := by
    rw [hν]; ring
  ring_nf at varianceLoss transfer baseline hflat hdiag hcurl hLambdae hνe ⊢
  linarith only [varianceLoss, transfer, baseline, hflat, hdiag, hcurl, hLambdae, hνe]

private theorem norm_le_of_sorted {n : ℕ} {f : Fin n → Fin n → E} (hf : Skew f)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ i j, i < j → ‖f i j‖ ≤ C) (i j : Fin n) : ‖f i j‖ ≤ C := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h i j hij
  · simpa [hf.diagonal] using hC
  · rw [hf j i, norm_neg]
    exact h j i hji

private theorem norm_holonomy_le_of_sorted {n : ℕ} {f : Fin n → Fin n → E} (hf : Skew f)
    (h : ∀ i j k, i < j → j < k → ‖holonomy f i j k‖ ≤ 1) (i j k : Fin n) :
    ‖holonomy f i j k‖ ≤ 1 := by
  have rot (a b c : Fin n) : ‖holonomy f a b c‖ = ‖holonomy f b c a‖ :=
    congrArg norm (holonomy_rotate f hf a b c).symm
  have swap (a b c : Fin n) : ‖holonomy f a b c‖ = ‖holonomy f b a c‖ := by
    have hh : holonomy f b a c = -holonomy f a b c := by
      unfold holonomy
      rw [hf a b]
      abel
    rw [hh, norm_neg]
  by_cases hij : i = j
  · subst j; norm_num [holonomy, hf.diagonal]
  by_cases hjk : j = k
  · subst k; norm_num [holonomy, hf.diagonal]
  by_cases hik : i = k
  · subst k; rw [rot]; norm_num [holonomy, hf.diagonal]
  rcases lt_or_gt_of_ne hij with hij | hji <;>
    rcases lt_or_gt_of_ne hjk with hjk | hkj <;>
    rcases lt_or_gt_of_ne hik with hik | hki
  · exact h i j k hij hjk
  · exact (lt_asymm (hij.trans hjk) hki).elim
  · rw [← rot k i j, swap k i j]
    exact h i k j hik hkj
  · rw [← rot k i j]
    exact h k i j hki hij
  · rw [swap i j k]
    exact h j i k hji hik
  · rw [rot]
    exact h j k i hjk hki
  · exact (lt_asymm (hkj.trans hji) hik).elim
  · rw [swap i j k, rot j i k, rot i k j]
    exact h k j i hkj hji

private theorem radius_pos : 0 < R := by norm_num [R, Data.R]

private theorem projection_abs {x : E} (hx : ‖x‖ ≤ R) (y : E) :
    |inner ℝ x y / R| ≤ ‖y‖ := by
  rw [abs_div, abs_of_pos radius_pos]
  exact (div_le_iff₀ radius_pos).2
    ((by simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) x y) :
      |inner ℝ x y| ≤ ‖x‖ * ‖y‖).trans (by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hx (norm_nonneg y)))

private theorem projection_upper {x y : E} (hy : ‖y‖ ≤ 1) :
    inner ℝ x y / R ≤ 1 - (r - ‖x‖ ^ 2) / (2 * r) := by
  have hinner : inner ℝ x y ≤ ‖x‖ := calc
    _ ≤ |inner ℝ x y| := le_abs_self _
    _ ≤ ‖x‖ * ‖y‖ := by simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x y
    _ ≤ ‖x‖ := by simpa using mul_le_mul_of_nonneg_left hy (norm_nonneg x)
  have h := div_le_div_of_nonneg_right hinner radius_pos.le
  apply h.trans
  rw [constants.2.1]
  suffices ‖x‖ / R ≤ (R ^ 2 + ‖x‖ ^ 2) / (2 * R ^ 2) by
    convert this using 1
    field_simp [radius_pos.ne']
    <;> ring
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos radius_pos _))).2
  have hdiv : ‖x‖ / R * (2 * R ^ 2) = 2 * ‖x‖ * R := by
    field_simp [radius_pos.ne']
    <;> ring
  rw [hdiv]
  nlinarith [sq_nonneg (R - ‖x‖)]

private theorem norm_sub_sq_le_two (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private noncomputable def deficit (x : E) : ℝ := r - ‖x‖ ^ 2

private noncomputable def alignment (x y : E) : ℝ := inner ℝ x y / R

private def newCurl {n : ℕ} (centers : Fin n → E) (f : Fin n → Fin n → E)
    (i j : Fin n) : E := f i j - (centers i - centers j)

private noncomputable def errorField {n : ℕ}
    (centers : Fin n → E) (f : Fin n → Fin n → E) (i j : Fin n) : E :=
  b • f i j + a • newCurl centers f i j

private theorem deficit_nonneg {x : E} (hx : ‖x‖ ≤ R) : 0 ≤ deficit x := by
  unfold deficit
  rw [constants.2.1]
  exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hx 2)

private theorem alignment_mem {x y : E} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ 1) :
    alignment x y ∈ Set.Icc (-1) 1 :=
  abs_le.mp ((projection_abs hx y).trans hy)

private theorem alignment_sq_le {x : E} (hx : ‖x‖ ≤ R) (y : E) :
    alignment x y ^ 2 ≤ ‖y‖ ^ 2 := by
  simpa only [alignment, sq_abs] using
    pow_le_pow_left₀ (abs_nonneg (alignment x y)) (projection_abs hx y) 2

private theorem error_skew {n : ℕ} {centers : Fin n → E} {f : Fin n → Fin n → E}
    (hf : Skew f) : Skew (errorField centers f) := by
  intro i j
  unfold errorField newCurl
  rw [hf i j]
  module

private theorem error_curl {n : ℕ} (centers : Fin n → E) (f : Fin n → Fin n → E)
    (i j k : Fin n) : holonomy (errorField centers f) i j k = holonomy f i j k := by
  rcases constants with ⟨_, _, _, hb, _⟩
  have hab : a + b = 1 := by linarith
  simp only [holonomy, errorField, newCurl]
  have split (x y : E) : b • x + a • (x - y) = x - a • y := by
    rw [smul_sub, ← add_sub_assoc, ← add_smul, add_comm b a, hab, one_smul]
  rw [split, split, split]
  rw [smul_sub, smul_sub, smul_sub]
  abel

private theorem alignment_add (x y z : E) :
    alignment x (y + z) = alignment x y + alignment x z := by
  simp only [alignment, inner_add_right, add_div]

private theorem alignment_sub (x y z : E) :
    alignment x (y - z) = alignment x y - alignment x z := by
  simp only [alignment, inner_sub_right, sub_div]

private theorem alignment_smul (x y : E) (q : ℝ) :
    alignment x (q • y) = q * alignment x y := by
  simp only [alignment, real_inner_smul_right, mul_div_assoc]

private theorem alignment_weighted_sum {n : ℕ} (x : E) (p : Fin n → ℝ) (g : Fin n → E) :
    alignment x (∑ k, p k • g k) = ∑ k, p k * alignment x (g k) := by
  simp only [alignment, inner_sum, real_inner_smul_right, Finset.sum_div, mul_div_assoc]

private theorem alignment_error {n : ℕ} (centers : Fin n → E) (f : Fin n → Fin n → E)
    (i j : Fin n) :
    alignment (f i j) (errorField centers f i j) =
      a * (1 + alignment (f i j) (newCurl centers f i j)) - a * (deficit (f i j) / r) := by
  rw [errorField, alignment_add, alignment_smul, alignment_smul]
  have hh : b / R = a / r := by norm_num [b, R, a, r, Data.b, Data.R, Data.a, Data.r]
  have hr : r ≠ 0 := by norm_num [r, Data.r, Data.R]
  simp only [alignment, real_inner_self_eq_norm_sq, deficit]
  have hs : b * (‖f i j‖ ^ 2 / R) = a * (‖f i j‖ ^ 2 / r) := by
    rw [show b * (‖f i j‖ ^ 2 / R) = (b / R) * ‖f i j‖ ^ 2 by ring, hh]
    ring
  rw [hs]
  field_simp [hr, radius_pos.ne']
  <;> ring

private theorem alignment_transfer {n : ℕ} (p : Fin n → ℝ) (hp : ∑ k, p k = 1)
    (centers : Fin n → E) (f : Fin n → Fin n → E) (hf : Skew f) (i j : Fin n) :
    let e := errorField centers f
    let M := rowMean p e
    let e₀ := centeredField p e
    let y := fun k => alignment (f i j) (holonomy f i j k)
    let z := ∑ k, p k * y k
    (z = a * (1 + alignment (f i j) (newCurl centers f i j)) - a * (deficit (f i j) / r)
        + alignment (f i j) (M j - M i)) ∧
      (∀ k, y k - z = alignment (f i j) (e₀ j k - e₀ i k)) := by
  dsimp only
  let e := errorField centers f
  let e₀ := centeredField p e
  let M := rowMean p e
  let x := f i j
  let y := fun k => alignment x (holonomy f i j k)
  let l := alignment x (e i j) + alignment x (M j - M i)
  have hsplit (k : Fin n) : y k = l + alignment x (e₀ j k - e₀ i k) := by
    have he : holonomy f i j k = e i j + (M j - M i) + (e₀ j k - e₀ i k) := by
      rw [← error_curl centers f i j k]
      change holonomy e i j k = _
      unfold holonomy e₀ centeredField
      dsimp only [M]
      abel
    change alignment x (holonomy f i j k) = _
    rw [he, alignment_add, alignment_add]
  have hmean : (∑ k, p k * y k) = l := by
    simp_rw [hsplit, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul,
      alignment_sub, mul_sub, Finset.sum_sub_distrib, ← alignment_weighted_sum]
    change l + (alignment x (rowMean p e₀ j) - alignment x (rowMean p e₀ i)) = _
    rw [rowMean_centeredField p hp e (error_skew hf), rowMean_centeredField p hp e (error_skew hf)]
    simp
  constructor
  · change (∑ k, p k * y k) = _
    rw [hmean]
    exact congrArg (fun u => u + alignment x (M j - M i)) (alignment_error centers f i j)
  · intro k
    change y k - (∑ k, p k * y k) = _
    rw [hmean, hsplit]
    ring

private theorem envelope_charge {n : ℕ} (p : Fin n → ℝ) (hp₀ : ∀ k, 0 ≤ p k)
    (hp : ∑ k, p k = 1) (centers : Fin n → E)
    (f : Fin n → Fin n → E) (hf : Skew f)
    (hedge : ∀ i j, ‖f i j‖ ≤ R)
    (hold : ∀ i j k, ‖holonomy f i j k‖ ≤ 1)
    (hface : ∀ i j k, i < j → j < k →
      triangleInvariant (f i j) (f i k) (f j k) (holonomy f i j k))
    (hnew : ∀ i j, i < j → ‖newCurl centers f i j‖ ≤ 1)
    (B : ℝ → ℝ)
    (henv : ∀ {θ t z y : ℝ}, θ ∈ Set.Icc 0 1 → t ∈ Set.Icc (-1) 1 →
      z ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 →
      F t ≤ B θ + nu0 * (z - a * (1 + t)) ^ 2 + θ * (nu1 * (y - z) ^ 2 + lambda * F y))
    (i j : Fin n) (hij : i < j) :
    let e := errorField centers f
    let M := rowMean p e
    let e₀ := centeredField p e
    let S := Finset.univ.filter (fun k => j ≤ k)
    F (alignment (f i j) (newCurl centers f i j)) - w * deficit (f i j) ≤
      B (∑ k ∈ S, p k) + 2 * nu0 * (‖M i‖ ^ 2 + ‖M j‖ ^ 2) +
      2 * nu1 * (∑ k ∈ S, p k * (‖e₀ i k‖ ^ 2 + ‖e₀ j k‖ ^ 2)) +
      lambda * (∑ k ∈ S, p k * (if k = j then c else deficit (f i k) + deficit (f j k))) := by
  dsimp only
  let e := errorField centers f
  let M := rowMean p e
  let e₀ := centeredField p e
  let S := Finset.univ.filter (fun k => j ≤ k)
  let d' (k : Fin n) := if k = j then c else deficit (f i k) + deficit (f j k)
  let x := f i j
  let d := deficit x
  let t := alignment x (newCurl centers f i j)
  let y (k : Fin n) := alignment x (holonomy f i j k)
  let z := ∑ k, p k * y k
  let θ := ∑ k ∈ S, p k
  have hθ : θ ∈ Set.Icc 0 1 :=
    ⟨Finset.sum_nonneg fun k _ => hp₀ k,
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun k _ _ => hp₀ k)).trans_eq hp⟩
  have ht := alignment_mem (hedge i j) (hnew i j hij)
  have hyl (k : Fin n) : -1 ≤ y k := (alignment_mem (hedge i j) (hold i j k)).1
  have hyr (k : Fin n) : y k ≤ 1 - d / (2 * r) := projection_upper (hold i j k)
  have hzl : -1 ≤ z := by
    calc
      -1 = ∑ k, p k * (-1) := by rw [← Finset.sum_mul, hp, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hyl k) (hp₀ k)
  have hzr : z ≤ 1 - d / (2 * r) := by
    calc
      _ ≤ ∑ k, p k * (1 - d / (2 * r)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hyr k) (hp₀ k)
      _ = _ := by rw [← Finset.sum_mul, hp, one_mul]
  have hF (k : Fin n) (hk : k ∈ S) : F (y k) ≤ d' k + w * d := by
    by_cases hkj : k = j
    · subst k
      have hzero : y j = 0 := by simp [y, alignment, holonomy, hf.diagonal]
      rw [hzero, F_zero]
      simpa only [d', if_pos rfl] using
        le_add_of_nonneg_right (mul_nonneg numerical_conditions.2.2.2.1.le (deficit_nonneg (hedge i j)))
    · have hjk : j < k := lt_of_le_of_ne (Finset.mem_filter.mp hk).2 (Ne.symm hkj)
      have hh := hface i j k hij hjk
      change F (y k) ≤ w * d + deficit (f i k) + deficit (f j k) at hh
      simpa only [d', if_neg hkj, add_comm, add_left_comm, add_assoc] using hh
  have hd' (k : Fin n) : 0 ≤ d' k := by
    unfold d'
    split_ifs
    · norm_num [c, Data.c]
    · exact add_nonneg (deficit_nonneg (hedge i k)) (deficit_nonneg (hedge j k))
  have hbgt : lambda * w + (2 * nu0 * (2 * a - 1) * (a - 1 / 2) + a * lambda * LF) / r ≤ w := by
    have hh := numerical_conditions.2.2.2.2.2.2.2.2.2.2.1
    convert hh using 1 <;> ring
  have hfLip (u v : ℝ) (_ : -1 ≤ u) (huv : u ≤ v) (_ : v ≤ 1) :
      F v ≤ F u + LF * (v - u) := by
    have hh := F_lipschitz.dist_le_mul v u
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr huv)] at hh
    have hh' : F v - F u ≤ LF * (v - u) := (le_abs_self _).trans hh
    linarith
  have ⟨hz, hyz⟩ := alignment_transfer p hp centers f hf i j
  change z = a * (1 + t) - a * (d / r) + alignment x (M j - M i) at hz
  change ∀ k, y k - z = alignment x (e₀ j k - e₀ i k) at hyz
  have hr : 0 < r := by norm_num [r, Data.r, Data.R]
  rcases numerical_conditions with
    ⟨ha, _, _, hw, _, hlambda, _, hnu0, hnu1, _, _⟩
  have hbase := HilbertWeightedTransfer.suffix_transfer S p y d'
    (fun k _ => hp₀ k) (fun k _ => hd' k) F B a r lambda nu0 nu1 w LF
    ha.le hr hlambda.le hnu0.le hnu1.le hw.le (by norm_num [LF]) hbgt hfLip d t z
    (deficit_nonneg (hedge i j)) ht.1 ht.2 hzl hzr
    (fun k _ => alignment_mem (hedge i j) (hold i j k)) hF hθ.2
    (fun u v hu₀ hu₁ hv₀ hv₁ => henv hθ ht ⟨hu₀, hu₁⟩ ⟨hv₀, hv₁⟩)
  have hm : z + a * (d / r) - a * (1 + t) = alignment x (M j - M i) := by
    rw [hz]
    ring
  have hmean := mul_le_mul_of_nonneg_left
    ((alignment_sq_le (hedge i j) (M j - M i)).trans (norm_sub_sq_le_two (M j) (M i))) hnu0.le
  have hcur (k : Fin n) : (y k - z) ^ 2 ≤ 2 * (‖e₀ i k‖ ^ 2 + ‖e₀ j k‖ ^ 2) := by
    rw [hyz k, add_comm]
    exact (alignment_sq_le (hedge i j) _).trans (norm_sub_sq_le_two _ _)
  have hs := Finset.sum_le_sum (s := S) fun k _ =>
    mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left (hcur k) hnu1.le) (lambda * d' k)) (hp₀ k)
  have hs' : (∑ k ∈ S, p k * (nu1 * (2 * (‖e₀ i k‖ ^ 2 + ‖e₀ j k‖ ^ 2)) + lambda * d' k)) =
      2 * nu1 * (∑ k ∈ S, p k * (‖e₀ i k‖ ^ 2 + ‖e₀ j k‖ ^ 2)) +
      lambda * (∑ k ∈ S, p k * d' k) := by
    simp_rw [show ∀ k, p k * (nu1 * (2 * (‖e₀ i k‖ ^ 2 + ‖e₀ j k‖ ^ 2)) + lambda * d' k) =
      (2 * nu1) * (p k * (‖e₀ i k‖ ^ 2 + ‖e₀ j k‖ ^ 2)) + lambda * (p k * d' k) by intro; ring,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hs'] at hs
  change F t - w * d ≤ B θ + 2 * nu0 * (‖M i‖ ^ 2 + ‖M j‖ ^ 2) + _ + _
  rw [hm] at hbase
  linarith

private theorem pair_sum_le {n : ℕ} {f g : Fin n → Fin n → ℝ}
    (h : ∀ i j, i < j → f i j ≤ g i j) : pairs f ≤ pairs g :=
  Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i hi => h i j (Finset.mem_filter.mp hi).2

private theorem split_companions {n : ℕ} (p : Fin n → ℝ) (d : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k => j ≤ k),
      p k * (if k = j then c else d i k + d j k)) =
        p j * c + ∑ k ∈ Finset.univ.filter (fun k => j < k), p k * (d i k + d j k) := by
  simp only [Finset.sum_filter]
  have hsplit (k : Fin n) :
      (if j ≤ k then p k * (if k = j then c else d i k + d j k) else 0) =
        (if k = j then p j * c else 0) + (if j < k then p k * (d i k + d j k) else 0) := by
    rcases lt_trichotomy j k with h | rfl | h
    · simp [h, h.le, h.ne.symm]
    · simp
    · simp [h, h.not_ge, h.not_gt, h.ne]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem charge_sum {n : ℕ} (p : Fin n → ℝ) (hp₀ : ∀ k, 0 ≤ p k)
    (hp : ∑ k, p k = 1) (x : Fin n → Fin n → ℝ)
    (hx : ∀ i j, x i j = x j i) (hx₀ : ∀ i j, 0 ≤ x i j) (hxz : ∀ i, x i i = 0)
    (hdegree : ∀ j, (∑ i, x i j) ≤ p j)
    (centers : Fin n → E) (f : Fin n → Fin n → E) (hf : Skew f)
    (hedge : ∀ i j, ‖f i j‖ ≤ R)
    (hold : ∀ i j k, ‖holonomy f i j k‖ ≤ 1)
    (hface : ∀ i j k, i < j → j < k →
      triangleInvariant (f i j) (f i k) (f j k) (holonomy f i j k))
    (hnew : ∀ i j, i < j → ‖newCurl centers f i j‖ ≤ 1) :
    let e := errorField centers f
    pairs (fun i j => x i j * (F (alignment (f i j) (newCurl centers f i j)) - w * deficit (f i j))) ≤
      lambda * (pairs (fun i j => p i * p j * deficit (f i j)) + c * ∑ i, p i ^ 2) +
      2 * nu0 * meanEnergy p e + nu1 * orderedEnergy p (centeredField p e) +
      (∫ θ in (0 : ℝ)..(1/2), envelope θ) := by
  dsimp only
  let e := errorField centers f
  let m (i : Fin n) := ‖rowMean p e i‖ ^ 2
  let e₀ := centeredField p e
  let ε (i j : Fin n) := ‖e₀ i j‖ ^ 2
  let d (i j : Fin n) := deficit (f i j)
  let threshold (j : Fin n) := ∑ k ∈ Finset.univ.filter (fun k => j ≤ k), p k
  let mass (j : Fin n) := ∑ i ∈ Finset.univ.filter (fun i => i < j), x i j
  let P (u : ℝ) := ∫ t in (0 : ℝ)..u, envelope t
  have hm₀ (j : Fin n) : 0 ≤ mass j := Finset.sum_nonneg fun i _ => hx₀ i j
  have hmp (j : Fin n) : mass j ≤ p j :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hx₀ i j)).trans (hdegree j)
  have hstep (l u : ℝ) (_hl : 0 ≤ l) (hle : l ≤ u) (_hu : u ≤ 1) :
      (u - l) * envelope u ≤ P u - P l := by
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (envelope_continuous.intervalIntegrable 0 l) (envelope_continuous.intervalIntegrable l u)
    have hb := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle intervalIntegrable_const
      (envelope_continuous.intervalIntegrable l u) (fun t ht => envelope_antitone ht.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hb
    dsimp [P]
    linarith
  have hmass : (∑ j, mass j) ≤ 1 / 2 := HilbertPairCharges.pair_mass_le_half p hp x hx hxz hdegree
  have hE : (∑ j, mass j * envelope (threshold j)) ≤ P (1/2) := by
    have h₁ := HilbertPairCharges.suffix_mass_le p mass hm₀ hmp hp.le envelope P
      (envelope_antitone.antitoneOn _) hstep
    have hz : P 0 = 0 := by simp [P]
    rw [hz, sub_zero] at h₁
    refine h₁.trans ?_
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (envelope_continuous.intervalIntegrable 0 (∑ j, mass j))
      (envelope_continuous.intervalIntegrable (∑ j, mass j) (1/2))
    have hh := intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) hmass envelope_nonneg
    dsimp [P]
    linarith
  have hM := HilbertPairCharges.prefix_incidence_le p x hx hx₀ hxz hdegree
    Finset.univ m (fun i _ => sq_nonneg _)
  change (∑ j, ∑ i, if i < j then x i j * (m i + m j) else 0) ≤ meanEnergy p e at hM
  have hM' : pairs (fun i j => x i j * (m i + m j)) ≤ meanEnergy p e := by
    simpa only [pairs, Finset.sum_filter] using hM
  have hD := HilbertPairCharges.suffix_companions_le p hp₀ x hx hx₀ hxz hdegree
    (· < ·) (fun h₁ h₂ => h₁.trans h₂) d (fun i k _ => deficit_nonneg (hedge i k))
  have hε := HilbertPairCharges.suffix_companions_le p hp₀ x hx hx₀ hxz hdegree
    (· ≤ ·) (fun h₁ h₂ => h₁.le.trans h₂) ε (fun i k _ => sq_nonneg _)
  have hεEq : (∑ k, ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), p i * p k * ε i k) =
      orderedEnergy p e₀ / 2 := by
    have he₀ : Skew e₀ := centeredField_skew p e (error_skew hf)
    have hz (i : Fin n) : ε i i = 0 := by
      simp [ε, he₀.diagonal]
    have hs (i j : Fin n) : p i * p j * ε i j = p j * p i * ε j i := by
      change p i * p j * ‖e₀ i j‖ ^ 2 = p j * p i * ‖e₀ j i‖ ^ 2
      simp [he₀ i j, mul_comm (p i) (p j)]
    have hh := HilbertPairCharges.twice_pairs (fun i j => p i * p j * ε i j) hs (by simp [hz])
    rw [show (∑ k, ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), p i * p k * ε i k) =
        pairs (fun i k => p i * p k * ε i k) by
      unfold pairs
      simp only [Finset.sum_filter]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by
        rcases lt_trichotomy i k with h | rfl | h
        · simp [h, h.le]
        · simp [hz]
        · simp [h.not_ge, h.not_gt]]
    rw [Finset.sum_comm] at hh
    change _ = orderedEnergy p e₀ at hh
    linarith
  rw [hεEq] at hε
  have hc₀ : 0 ≤ c := by norm_num [c, Data.c]
  have hdiag : (∑ j, mass j * (p j * c)) ≤ c * ∑ j, p j ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hh := mul_le_mul_of_nonneg_right (hmp j) (mul_nonneg (hp₀ j) hc₀)
    convert hh using 1 <;> ring
  have hpoint := pair_sum_le fun i j hij =>
    mul_le_mul_of_nonneg_left
      (envelope_charge p hp₀ hp centers f hf hedge hold hface hnew envelope
        (fun ht₀ ht hz hy => by
          have hh := scalar_envelope _ _ _ _ ht₀.1 ht hz hy
          linarith) i j hij) (hx₀ i j)
  change pairs (fun i j => x i j * (F (alignment (f i j) (newCurl centers f i j)) -
      w * d i j)) ≤ pairs (fun i j => x i j * (envelope (threshold j) +
      2 * nu0 * (m i + m j) +
      2 * nu1 * (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), p k * (ε i k + ε j k)) +
      lambda * (∑ k ∈ Finset.univ.filter (fun k => j ≤ k),
        p k * (if k = j then c else d i k + d j k)))) at hpoint
  let S (j : Fin n) := Finset.univ.filter fun k => j ≤ k
  let T (j : Fin n) := Finset.univ.filter fun k => j < k
  let em (i j : Fin n) := x i j * (m i + m j)
  let ec (i j : Fin n) := x i j * ∑ k ∈ S j, p k * (ε i k + ε j k)
  let dc (i j : Fin n) := x i j * ∑ k ∈ T j, p k * (d i k + d j k)
  let dt (i j : Fin n) := x i j * (p j * c)
  let sc (i j : Fin n) := x i j * envelope (threshold j)
  have combine (i j : Fin n) : x i j * (envelope (threshold j) +
      2 * nu0 * (m i + m j) + 2 * nu1 * (∑ k ∈ S j, p k * (ε i k + ε j k)) +
      lambda * (∑ k ∈ S j, p k * (if k = j then c else d i k + d j k))) =
      sc i j + (2 * nu0) * em i j + (2 * nu1) * ec i j + lambda * dt i j + lambda * dc i j := by
    rw [show (∑ k ∈ S j, p k * (if k = j then c else d i k + d j k)) =
        p j * c + ∑ k ∈ T j, p k * (d i k + d j k) from split_companions p d i j]
    dsimp only [sc, em, ec, dt, dc]
    ring
  rw [show _ = pairs (fun i j => sc i j + (2 * nu0) * em i j + (2 * nu1) * ec i j +
      lambda * dt i j + lambda * dc i j) from congrArg pairs (funext fun i => funext fun j => combine i j)] at hpoint
  have sum_add (f g : Fin n → Fin n → ℝ) :
      pairs (fun i j => f i j + g i j) = pairs f + pairs g := by
    simp only [pairs, Finset.sum_add_distrib]
  have sum_smul (c : ℝ) (f : Fin n → Fin n → ℝ) :
      pairs (fun i j => c * f i j) = c * pairs f := by
    simp only [pairs, Finset.mul_sum]
  simp only [sum_add, sum_smul] at hpoint
  have hel : pairs sc = ∑ j, mass j * envelope (threshold j) := by
    simp only [sc, mass, pairs, Finset.sum_mul]
  have hdl : pairs dt = ∑ j, mass j * (p j * c) := by
    simp only [dt, mass, pairs, Finset.sum_mul]
  rw [hel, hdl] at hpoint
  rcases numerical_conditions with ⟨_, _, _, _, _, hLambda, _, hnu0, hnu1, _⟩
  have h1M := mul_le_mul_of_nonneg_left (show pairs em ≤ meanEnergy p e from hM')
    (mul_nonneg (by norm_num) hnu0.le : 0 ≤ 2 * nu0)
  have h1ε := mul_le_mul_of_nonneg_left (show pairs ec ≤ orderedEnergy p e₀ / 2 from hε)
    (mul_nonneg (by norm_num) hnu1.le : 0 ≤ 2 * nu1)
  have h1D := mul_le_mul_of_nonneg_left (show pairs dc ≤
    pairs (fun i j => p i * p j * d i j) from hD) hLambda.le
  have h1d := mul_le_mul_of_nonneg_left hdiag hLambda.le
  dsimp only [P] at hE
  change _ ≤ lambda * (pairs (fun i j => p i * p j * d i j) + c * ∑ i, p i ^ 2) +
    2 * nu0 * meanEnergy p e + nu1 * orderedEnergy p e₀ + _
  linarith only [h1M, h1ε, h1D, h1d, hE, hpoint]


private theorem sum_fin_prefix {n m : ℕ} (hm : m ≤ n) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), f i.val) =
      ∑ i ∈ Finset.range m, f i := by
  symm
  refine Finset.sum_bij (fun i hi => (⟨i, (Finset.mem_range.mp hi).trans_le hm⟩ : Fin n))
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hi⟩)
    (fun _ _ _ _ h => congrArg Fin.val h) ?_ (fun _ _ => rfl)
  intro i hi
  exact ⟨i.val, Finset.mem_range.mpr (Finset.mem_filter.mp hi).2, Fin.ext rfl⟩

private theorem sum_fin_extend {n m : ℕ} (hm : m ≤ n) (f : Fin n → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), f i) =
      ∑ i ∈ Finset.range m, if h : i < n then f ⟨i, h⟩ else 0 := by
  rw [← sum_fin_prefix hm]
  exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]

private theorem flat_credit {n : ℕ} (p : Fin n → ℝ) (hp₀ : ∀ k, 0 ≤ p k)
    (hp : ∑ k, p k = 1) (centers : Fin n → E) (f : Fin n → Fin n → E)
    (hf : Skew f) (hedge : ∀ i j, ‖f i j‖ ≤ R)
    (hface : ∀ i j k, i < j → j < k →
      triangleInvariant (f i j) (f i k) (f j k) (holonomy f i j k)) :
    c * I - c * K * (∑ i, p i ^ 2) -
      gamma * I0 * orderedEnergy p (centeredField p (errorField centers f)) ≤
      2 * pairs (fun i j => p i * p j * deficit (f i j)) := by
  let p' (i : ℕ) := if hi : i < n then p ⟨i, hi⟩ else 0
  let d' (i j : ℕ) := if hi : i < n then if hj : j < n then deficit (f ⟨i, hi⟩ ⟨j, hj⟩) else 0 else 0
  let h' (i j k : ℕ) := if hi : i < n then if hj : j < n then if hk : k < n then
    alignment (f ⟨i, hi⟩ ⟨j, hj⟩) (holonomy f ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩) ^ 2 else 0 else 0 else 0
  let e := errorField centers f
  let e₀ := centeredField p e
  have hx (i j k : Fin n) : curl e₀ i j k = holonomy f i j k := by
    rw [show curl e₀ i j k = curl e i j k from curl_centeredField p e i j k]
    exact error_curl centers f i j k
  have hp' (m : ℕ) (hm : m ≤ n) : HilbertPrefixDeficit.prefixMass p' m =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), p i :=
    (sum_fin_extend hm p).symm
  have huniv : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i
    simp [i.isLt]
  have hsquares : HilbertPrefixDeficit.squares p' n = ∑ i, p i ^ 2 := by
    unfold HilbertPrefixDeficit.squares
    rw [← sum_fin_prefix (le_refl n), huniv]
    exact Finset.sum_congr rfl fun i _ => by simp [p', i.isLt]
  have hpairs : HilbertPrefixDeficit.pairs p' d' n =
      pairs (fun i j => p i * p j * deficit (f i j)) := by
    unfold HilbertPrefixDeficit.pairs pairs
    rw [← sum_fin_prefix (le_refl n), huniv]
    apply Finset.sum_congr rfl
    intro j _
    rw [← sum_fin_prefix j.isLt.le]
    exact Finset.sum_congr rfl fun i _ => by simp [p', d', i.isLt, j.isLt]
  have hprefix (m : ℕ) (hm : m ≤ n) : HilbertPrefixDeficit.triples p' h' m ≤
      HilbertPrefixDeficit.prefixMass p' m * orderedEnergy p e₀ := by
    let S : Finset (Fin n) := Finset.univ.filter (fun i => i.val < m)
    have hS : ∀ {i j : Fin n}, j ∈ S → i < j → i ∈ S :=
      fun {i j} hj hij => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (show i.val < j.val from hij).trans (Finset.mem_filter.mp hj).2⟩
    have hh := sorted_hodge_prefix p hp₀ S e₀ (centeredField_skew p e (error_skew hf))
    rw [hp' m hm]
    apply le_trans _ hh
    unfold HilbertPrefixDeficit.triples
    rw [← sum_fin_prefix hm]
    simp only [sortedTripleSum]
    have reverse_sums (g : Fin n → Fin n → Fin n → ℝ) :
        (∑ i, ∑ j, ∑ k, g i j k) = ∑ k, ∑ j, ∑ i, g i j k := by
      calc
        _ = ∑ j, ∑ i, ∑ k, g i j k := Finset.sum_comm
        _ = ∑ j, ∑ k, ∑ i, g i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [reverse_sums]
    simp only [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k ∈ S
    · simp only [show k.val < m from (Finset.mem_filter.mp hk).2, if_true]
      rw [← sum_fin_prefix k.isLt.le, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j < k
      · simp only [show j.val < k.val from hj, if_true]
        rw [← sum_fin_prefix j.isLt.le, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i < j
        · simp [show i.val < j.val from hi, hi, hj, hk, hS hk hj, hS (hS hk hj) hi,
            p', h', i.isLt, j.isLt, k.isLt]
          rw [hx]
          have h := mul_le_mul_of_nonneg_left (alignment_sq_le (hedge i j) (holonomy f i j k))
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hp₀ i)) (hp₀ j)) (hp₀ k))
          simpa only [mul_assoc] using h
        · simp [show ¬ i.val < j.val from hi, hi]
      · simp [show ¬ j.val < k.val from hj, hj]
    · have hkm : ¬ k.val < m := fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp [hkm, hk, mul_ite]
  have hF := HilbertPrefixDeficit.flat_triangle_deficit (p := p') (d := d') (h := h')
    (n := n) (H := orderedEnergy p e₀)
    (fun i hi => by simpa [p', hi] using hp₀ ⟨i, hi⟩)
    (by rw [hp' n le_rfl, huniv, hp])
    (fun i j hij hj => by
      have hi := hij.trans hj
      simpa [d', hi, hj] using deficit_nonneg (hedge ⟨i, hi⟩ ⟨j, hj⟩))
    (by
      unfold orderedEnergy
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (hp₀ i) (hp₀ j)) (sq_nonneg _))
    (fun i j k hij hjk hk => by
      have hj := hjk.trans hk
      have hi := hij.trans hj
      have hh := (F_parabola_le (alignment (f ⟨i, hi⟩ ⟨j, hj⟩)
        (holonomy f ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩))).trans
          (hface ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk)
      have hg : gamma = HilbertPrefixDeficit.gamma := by
        norm_num [gamma, Data.gamma, Data.q, Data.c, HilbertPrefixDeficit.gamma]
      rw [hg] at hh
      simpa [d', h', hi, hj, hk, c, w, Data.c, Data.w,
        Data.q, HilbertPrefixDeficit.c, HilbertPrefixDeficit.w, HilbertPrefixDeficit.gamma,
        triangleInvariant, alignment, deficit] using hh)
    hprefix
  rw [hsquares, hpairs] at hF
  have hI : HilbertPrefixDeficit.I = I := by
    norm_num [HilbertPrefixDeficit.I, I, Data.I, Data.v, Fin.sum_univ_succ]
  have hI0 : HilbertPrefixDeficit.I0 = I0 := by
    norm_num [HilbertPrefixDeficit.I0, I0, Data.I0, Data.v, Fin.sum_univ_succ]
  have hK : HilbertPrefixDeficit.K = K := by
    norm_num [HilbertPrefixDeficit.K, K, Data.K, Data.v, Fin.sum_univ_succ]
  have hc : HilbertPrefixDeficit.c = c := by norm_num [HilbertPrefixDeficit.c, c, Data.c]
  have hg : HilbertPrefixDeficit.gamma = gamma := by
    norm_num [HilbertPrefixDeficit.gamma, gamma, Data.gamma, Data.c, Data.q]
  rw [hI, hI0, hK, hc, hg] at hF
  exact hF

private theorem placement {n : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (centers : Fin n → E) (f : Fin n → Fin n → E) (hf : Skew f)
    (hedge : ∀ i j, i < j → ‖f i j‖ ≤ R)
    (hold : ∀ i j k, i < j → j < k → ‖holonomy f i j k‖ ≤ 1 ∧
      triangleInvariant (f i j) (f i k) (f j k) (holonomy f i j k))
    (hnew : ∀ i j, i < j → ‖newCurl centers f i j‖ ≤ 1)
    (hcredit : ∀ p : Fin n → ℝ, (∑ i, p i = 1) → s ≤ (57 / 10) * ∑ i, p i ^ 2) :
    ∃ z, (∀ i, ‖centers i - z‖ ^ 2 ≤ r - s) ∧
      ∀ i j, i < j → triangleInvariant (f i j) (centers i - z) (centers j - z) (newCurl centers f i j) := by
  classical
  let cost (i j : Fin n) := F (alignment (f i j) (newCurl centers f i j)) - w * deficit (f i j)
  let penalty (u : Fin n × Fin n) :=
    if u.1 < u.2 then cost u.1 u.2 else if u.2 < u.1 then cost u.2 u.1 else 0
  let q (u : Fin n × Fin n) (i : Fin n) : ℝ :=
    ((if i = u.1 then 1 else 0) + (if i = u.2 then 1 else 0)) / 2
  let offset (u : Fin n × Fin n) := s - r + penalty u / 2
  have hq (u : Fin n × Fin n) : ∑ i, q u i = 1 := by
    norm_num [q, add_div, ite_div, Finset.sum_add_distrib, Finset.sum_ite_eq']
  have hrow (u : Fin n × Fin n) (z : E) :
      (∑ i, q u i * ‖centers i - z‖ ^ 2) =
        (‖centers u.1 - z‖ ^ 2 + ‖centers u.2 - z‖ ^ 2) / 2 := by
    simp only [q, add_div, add_mul, Finset.sum_add_distrib, ite_div, zero_div, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  obtain ⟨z, hz⟩ := QuadraticRows.averaged_minimax centers q offset hq (by
    intro μ hμ₀ hμ
    let p := HilbertPairCharges.endpointWeight μ
    let x := HilbertPairCharges.edgeWeight μ
    have hp₀ := HilbertPairCharges.endpointWeight_nonneg μ hμ₀
    have hp := HilbertPairCharges.endpointWeight_sum μ hμ
    have hx := HilbertPairCharges.edgeWeight_symm μ
    have hx₀ := HilbertPairCharges.edgeWeight_nonneg μ hμ₀
    have hxz := HilbertPairCharges.edgeWeight_diag μ
    have hd := HilbertPairCharges.edgeWeight_degree μ hμ₀
    have hedge' := norm_le_of_sorted hf radius_pos.le hedge
    have hcurl := norm_holonomy_le_of_sorted hf (fun i j k hij hjk => (hold i j k hij hjk).1)
    have hface (i j k : Fin n) (hij : i < j) (hjk : j < k) :=
      (hold i j k hij hjk).2
    have hnewSkew : Skew (newCurl centers f) := by
      intro i j
      unfold newCurl
      rw [hf i j]
      abel
    have hnew' := norm_le_of_sorted hnewSkew (by norm_num) hnew
    have ht := charge_sum p hp₀ hp x hx hx₀ hxz hd centers f hf hedge' hcurl hface hnew
    have hflat := flat_credit p hp₀ hp centers f hf hedge' hface
    let e := errorField centers f
    let L := orderedDeficit p 1 (newCurl centers f) / 2
    let D := pairs (fun i j => p i * p j * deficit (f i j))
    have hL : 0 ≤ L := by
      apply div_nonneg _ (by norm_num)
      unfold orderedDeficit
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs
        · rfl
        · exact mul_nonneg (mul_nonneg (hp₀ i) (hp₀ j))
            (sub_nonneg.mpr (by simpa using pow_le_pow_left₀ (norm_nonneg _) (hnew' i j) 2))
    have hD : orderedDeficit p r f = 2 * D := by
      let d (i j : Fin n) := if i = j then 0 else p i * p j * deficit (f i j)
      have hh := HilbertPairCharges.twice_pairs d (fun i j => by
        simp [d, eq_comm, hf i j, deficit, mul_comm (p i) (p j)]) (by simp [d])
      rw [Finset.sum_comm] at hh
      have hEq : pairs d = D := le_antisymm
        (pair_sum_le fun i j hij => by simp [d, hij.ne])
        (pair_sum_le fun i j hij => by simp [d, hij.ne])
      rw [hEq] at hh
      exact hh.symm
    have hab : a + b = 1 := by norm_num [a, b, Data.a, Data.b, Data.R]
    have ha : a ≠ 0 := by norm_num [a, Data.a, Data.R]
    have hb : b ≠ 0 := (numerical_conditions.2.2.1).ne'
    have hcap : 2 * U = r / a + 1 / b := by norm_num [U, r, a, b, Data.U, Data.r, Data.a, Data.b, Data.R]
    have hv := variance_loss p hp centers f (newCurl centers f) hf hnewSkew
      (fun i j => by unfold newCurl; abel) a b (2 * U) r hab ha hb hcap
    rw [hD] at hv
    change (2 * U) / 2 - FiniteHilbertJung.variance centers p =
      (2 * U) / 2 * (∑ i, p i ^ 2) + (2 * D) / (2 * a) +
      orderedDeficit p 1 (newCurl centers f) / (2 * b) +
      (orderedEnergy p (centeredField p e) + 2 * meanEnergy p e) / (2 * a * b) at hv
    have hV : U - FiniteHilbertJung.variance centers p =
        U * (∑ i, p i ^ 2) + D / a + L / b +
          nu0 * (orderedEnergy p (centeredField p e) + 2 * meanEnergy p e) := by
      rw [constants.2.2.2.2.2.2.2.1]
      dsimp only [L, e]
      convert hv using 1 <;> ring
    have hmix := mixture_credit (FiniteHilbertJung.variance centers p) (∑ i, p i ^ 2)
      D L (meanEnergy p e) (orderedEnergy p (centeredField p e))
      (pairs fun i j => x i j * cost i j) _
      (Finset.sum_nonneg fun i _ => sq_nonneg _) hL hV ht hflat (closing_budget.le.trans (by norm_num))
    let z := FiniteHilbertJung.center centers p
    refine ⟨z, ?_⟩
    simp only [hrow, offset, mul_add, Finset.sum_add_distrib]
    have he := HilbertPairCharges.endpointWeight_mix μ (fun i => ‖centers i - z‖ ^ 2)
    have hpen := HilbertPairCharges.edgeWeight_mix μ cost
    have hz : (∑ i, p i * ‖centers i - z‖ ^ 2) = FiniteHilbertJung.variance centers p := by
      rw [FiniteHilbertJung.weighted_sq centers p hp]
      simp [z]
    rw [he, ← Finset.sum_mul, hμ, one_mul, hpen, hz]
    linarith [hcredit p hp])
  refine ⟨z, ?_, ?_⟩
  · intro i
    have h := hz (i, i)
    rw [hrow] at h
    dsimp only [offset] at h
    simp [penalty] at h
    linarith
  · intro i j hij
    have h := hz (i, j)
    rw [hrow] at h
    dsimp only [offset] at h
    simp only [penalty, hij, if_true, cost] at h
    unfold triangleInvariant alignment deficit at *
    linarith

/-- On every finite chordal graph, gains in any real inner product space admit
an edge error at most `241361/100000` times the triangle-defect budget.
This factor is strictly less than `2.414`, and its gap from `1 + √2` exceeds
`3/5000`. -/
theorem IsChordal.exists_hilbert_gain_potential_sub_jung (hG : G.IsChordal)
    (g : V → V → E) (D : ℝ) (hD : 0 ≤ D) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ D) :
    (∃ p : V → E, ∀ i j, G.Adj i j → ‖g i j + p i - p j‖ ≤ (241361 / 100000) * D) ∧
      ((241361 / 100000 : ℝ) < 2414 / 1000 ∧
      (2414 / 1000 : ℝ) < 1 + Real.sqrt 2 ∧
      (3 / 5000 : ℝ) < 1 + Real.sqrt 2 - 241361 / 100000) := by
  have h := reconstruct_with_credit hG 0 le_rfl (fun _ => True)
    (fun _ _ _ => trivial)
    (fun _ _ p _ => mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg (p i)))
    (fun _ => placement 0 le_rfl) g D hD hg ht
  rw [sub_zero, constants.2.1, Real.sqrt_sq radius_pos.le, constants.1] at h
  exact ⟨h, sub_jung_comparisons⟩

/-- The same triangle invariant gives a squared-radius credit of
`57/(10*N)` for every graph whose cliques have at most `N + 1` vertices. -/
theorem IsChordal.exists_hilbert_gain_potential_clique_credit
    (hG : G.IsChordal) (N : ℕ) (hN : 1 ≤ N)
    (hclique : ∀ S : Finset V, G.IsClique (S : Set V) → S.card ≤ N + 1)
    (g : V → V → E) (D : ℝ) (hD : 0 ≤ D) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ D) :
    (∃ p : V → E, ∀ i j, G.Adj i j →
      ‖g i j + p i - p j‖ ≤ Real.sqrt ((241361 / 100000 : ℝ) ^ 2 - 57 / (10 * (N : ℝ))) * D) ∧
      Real.sqrt ((241361 / 100000 : ℝ) ^ 2 - 57 / (10 * (N : ℝ))) ≤
        241361 / 100000 - 59 / (50 * (N : ℝ)) := by
  let s : ℝ := 57 / (10 * (N : ℝ))
  have hs : 0 ≤ s := by positivity
  have h := reconstruct_with_credit hG s hs (· ≤ N)
    (fun S hc _ => by have := hclique S hc; omega)
    (fun _ hn p hp => diagonal_credit hN hn p hp)
    (fun _ => placement s hs) g D hD hg ht
  rw [constants.2.1, constants.1] at h
  exact ⟨h, diagonal_sqrt_le_linear hN⟩

end SimpleGraph
