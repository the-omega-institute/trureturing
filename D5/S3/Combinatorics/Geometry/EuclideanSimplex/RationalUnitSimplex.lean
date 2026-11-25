/- GID: D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Classify dimensions admitting a full regular simplex on the rational unit sphere. -/

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Quaternion
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.LinearCombination

/-! The determinant obstruction and rational realizations of regular unit simplices. -/

namespace D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex

open Matrix
open scoped Quaternion

private def constantGram (n : ℕ) (c : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => if i = j then 1 else c)

private theorem det_constant_gram (n : ℕ) (c : ℚ) (hc : c ≠ 1) :
    (constantGram n c).det = (1 - c) ^ n * (1 + (n : ℚ) * (c / (1 - c))) := by
  let u : Fin n → ℚ := fun _ => 1
  let v : Fin n → ℚ := fun _ => c / (1 - c)
  have hn : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hv : (1 - c) * (c / (1 - c)) = c := by field_simp
  have h : constantGram n c = (1 - c) •
      (1 + replicateCol Unit u * replicateRow Unit v) := by
    ext i j
    by_cases hi : i = j
    · simp [constantGram, Matrix.mul_apply, u, v, hi, mul_add, hv]
    · simp [constantGram, Matrix.mul_apply, u, v, hi, hv]
  rw [h, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, u, v, mul_comm]

private theorem saturated_gram_determinant (n : ℕ) (hn : 0 < n) :
    (constantGram n (-(1 : ℚ) / n)).det =
      (1 + (1 : ℚ) / n) ^ n / ((n : ℚ) + 1) := by
  have hpos : (0 : ℚ) < n := by exact_mod_cast hn
  have hn0 : (n : ℚ) ≠ 0 := hpos.ne'
  have hp : (n : ℚ) + 1 ≠ 0 := by positivity
  have hc : -(1 : ℚ) / n ≠ 1 := by
    intro h
    have := (div_eq_iff hn0).mp h
    linarith
  rw [det_constant_gram _ _ hc]
  simp only [neg_div, sub_neg_eq_add]
  have ratio : 1 + (n : ℚ) * -(1 / (n : ℚ) / (1 + 1 / n)) =
      1 / ((n : ℚ) + 1) := by
      field_simp
      ring
  rw [ratio]
  exact (div_eq_mul_one_div _ _).symm

private theorem support_square_obstruction (n : ℕ) (hn : 0 < n)
    (V : Matrix (Fin n) (Fin n) ℚ)
    (h : Vᵀ * V = constantGram n (-(1 : ℚ) / n)) :
    (Odd n → IsSquare n) ∧ (Even n → IsSquare (n + 1)) := by
  have hn₀ : 0 < (n : ℚ) := by exact_mod_cast hn
  let factor : ℚ := 1 + 1 / (n : ℚ)
  have hfactor : 0 < factor := add_pos zero_lt_one (one_div_pos.mpr hn₀)
  have hdet : V.det * V.det = factor ^ n / ((n : ℚ) + 1) := by
    calc
      V.det * V.det = (Vᵀ * V).det := by rw [Matrix.det_mul, Matrix.det_transpose]
      _ = _ := h ▸ saturated_gram_determinant n hn
  have hs : IsSquare (factor ^ n / ((n : ℚ) + 1)) := ⟨V.det, hdet.symm⟩
  constructor
  · rintro ⟨k, hk⟩
    let value := factor ^ k
    have hpower : factor ^ n = value ^ 2 * factor := by
      change factor ^ n = (factor ^ k) ^ 2 * factor
      rw [hk, pow_succ, ← pow_mul, Nat.mul_comm 2 k]
    have hscale : factor ^ n / ((n : ℚ) + 1) = value ^ 2 / n := by
      rw [hpower]
      dsimp [factor]
      field_simp
    have hs' : IsSquare (value ^ 2 / (n : ℚ)) := hscale ▸ hs
    have hv : value ≠ 0 := pow_ne_zero k hfactor.ne'
    have cancel : (value ^ 2 / (value ^ 2 / (n : ℚ))) = (n : ℚ) := by
      field_simp [hv]
    exact Rat.isSquare_natCast_iff.mp (cancel ▸ (IsSquare.sq value).div hs')
  · rintro ⟨k, hk⟩
    let value := factor ^ k
    have hpower : factor ^ n = value ^ 2 := by
      change factor ^ n = (factor ^ k) ^ 2
      rw [hk, pow_two, ← pow_add]
    rw [hpower] at hs
    have hv : value ≠ 0 := pow_ne_zero k hfactor.ne'
    have cancel : (value ^ 2 / (value ^ 2 / ((n : ℚ) + 1))) = (n : ℚ) + 1 := by
      field_simp [hv]
    exact Rat.isSquare_natCast_iff.mp (by
      simpa using cancel ▸ (IsSquare.sq value).div hs)

private theorem normalized_saturated_gram (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : c ≠ 1)
    (V : Matrix (Fin n) (Fin (n + 1)) ℚ) (h : Vᵀ * V = constantGram (n + 1) c) :
    c = -(1 : ℚ) / n := by
  have hRank : (Vᵀ * V).rank ≤ n :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width Vᵀ)
  have hd : (Vᵀ * V).det = 0 := by
    by_contra hne
    have hfull := Matrix.rank_of_det_ne_zero hne
    simp only [Fintype.card_fin] at hfull
    omega
  rw [h, det_constant_gram _ _ hc, mul_eq_zero] at hd
  have hn₀ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc₀ : 1 - c ≠ 0 := sub_ne_zero.mpr hc.symm
  have hrelation := hd.resolve_left (pow_ne_zero _ hc₀)
  push_cast at hrelation
  have hv : c * (n : ℚ) = -1 := by
    field_simp at hrelation
    linarith
  exact (eq_div_iff hn₀).mpr hv

private theorem rational_full_simplex_necessary (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : c ≠ 1)
    (V : Matrix (Fin n) (Fin (n + 1)) ℚ) (h : Vᵀ * V = constantGram (n + 1) c) :
    (Odd n → IsSquare n) ∧ (Even n → IsSquare (n + 1)) := by
  let W := V.submatrix id Fin.castSucc
  have hc' := normalized_saturated_gram n hn c hc V h
  have hW : Wᵀ * W = constantGram n (-(1 : ℚ) / n) := by
    ext i j
    have hij := congrFun (congrFun h i.castSucc) j.castSucc
    change (Vᵀ * V) i.castSucc j.castSucc =
      (if i.castSucc = j.castSucc then (1 : ℚ) else c) at hij
    change (Vᵀ * V) i.castSucc j.castSucc =
      (if i = j then (1 : ℚ) else -(1 : ℚ) / n)
    simpa [Fin.castSucc_inj, hc'] using hij
  exact support_square_obstruction n hn W hW

private theorem rational_unit_reflection {ι : Type} [Fintype ι]
    (a b : ι → ℚ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) :
    ∃ f : (ι → ℚ) → (ι → ℚ), f a = b ∧ ∀ x y, f x ⬝ᵥ f y = x ⬝ᵥ y := by
  by_cases hab : a = b
  · exact ⟨id, hab, fun _ _ => rfl⟩
  let u := a - b
  let d := u ⬝ᵥ u
  have hd : d ≠ 0 := fun h => hab (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h))
  let coef := fun x : ι → ℚ => 2 * (u ⬝ᵥ x) / d
  let reflection := fun x : ι → ℚ => x - coef x • u
  have hdouble : d = 2 * (u ⬝ᵥ a) := by
    simp only [d, u, dotProduct_sub, sub_dotProduct, ha, hb, dotProduct_comm a b]
    ring
  refine ⟨reflection, ?_, ?_⟩
  · have hc : coef a = 1 := by
      dsimp only [coef]
      rw [← hdouble, div_self hd]
    rw [show reflection a = a - coef a • u from rfl, hc, one_smul]
    simp [u]
  · intro x y
    change (x - coef x • u) ⬝ᵥ (y - coef y • u) = x ⬝ᵥ y
    simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm x u]
    change x ⬝ᵥ y - coef x * (u ⬝ᵥ y) - coef y * (u ⬝ᵥ x - coef x * d) = x ⬝ᵥ y
    dsimp only [coef]
    field_simp [hd]
    ring

private def centerVertex {n : ℕ} (j i : Fin (n + 1)) : ℚ :=
  (if i = j then 1 else 0) - 1 / ((n : ℚ) + 1)

private theorem center_dot_ones (n : ℕ) (j : Fin (n + 1)) :
    (centerVertex j) ⬝ᵥ (fun _ => 1) = 0 := by
  have hp : (n : ℚ) + 1 ≠ 0 := by positivity
  simp [dotProduct, centerVertex, Finset.sum_sub_distrib]
  field_simp
  exact sub_self _

private theorem center_dot_center (n : ℕ) (j k : Fin (n + 1)) :
    centerVertex j ⬝ᵥ centerVertex k =
      (if j = k then (1 : ℚ) else 0) - 1 / ((n : ℚ) + 1) := by
  have hp : (n : ℚ) + 1 ≠ 0 := by positivity
  let t := 1 / ((n : ℚ) + 1)
  let u : Fin (n + 1) → ℚ := fun i => if i = j then 1 else 0
  let v : Fin (n + 1) → ℚ := fun i => if i = k then 1 else 0
  have hu : u ⬝ᵥ (fun _ => t) = t := by simp [u, dotProduct, ite_mul]
  have hv : (fun _ => t) ⬝ᵥ v = t := by simp [v, dotProduct, mul_ite]
  have huv : u ⬝ᵥ v = if j = k then 1 else 0 := by
    simp [u, v, dotProduct, eq_comm]
  have ht : (fun _ : Fin (n + 1) => t) ⬝ᵥ (fun _ => t) = t := by
    simp [dotProduct, t]
    field_simp
  change (u - fun _ => t) ⬝ᵥ (v - fun _ => t) = _
  simp only [dotProduct_sub, sub_dotProduct, hu, hv, huv, ht]
  ring

private def firstAxis (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  if i = 0 then 1 else 0

private theorem strip_normal (n : ℕ) (a : Fin (n + 1) → ℚ) (ha : a ⬝ᵥ a = 1) :
    ∃ g : (Fin (n + 1) → ℚ) → (Fin n → ℚ),
      ∀ x y, x ⬝ᵥ a = 0 → y ⬝ᵥ a = 0 → g x ⬝ᵥ g y = x ⬝ᵥ y := by
  have hAxis : firstAxis n ⬝ᵥ firstAxis n = 1 := by simp [firstAxis, dotProduct]
  obtain ⟨f, hf, hpreserve⟩ := rational_unit_reflection a (firstAxis n) ha hAxis
  have hcoord (x : Fin (n + 1) → ℚ) (hx : x ⬝ᵥ a = 0) : f x 0 = 0 := by
    have h := hpreserve x a
    rw [hf, hx] at h
    simpa [firstAxis, dotProduct, mul_ite] using h
  refine ⟨fun x i => f x i.succ, ?_⟩
  intro x y hx hy
  have h := hpreserve x y
  rwa [dotProduct, Fin.sum_univ_succ, hcoord x hx, zero_mul, zero_add] at h

private theorem restrict_scaled (n : ℕ) (hn : 0 < n)
    (g : (Fin (n + 1) → ℚ) → (Fin n → ℚ))
    (hg : ∀ x y, (fun _ => 1) ⬝ᵥ x = 0 → (fun _ => 1) ⬝ᵥ y = 0 →
      g x ⬝ᵥ g y = ((n : ℚ) + 1)/n * (x ⬝ᵥ y)) :
    ∃ p : Fin (n + 1) → Fin n → ℚ, ∀ j k,
      p j ⬝ᵥ p k = if j = k then 1 else -(1 : ℚ)/n := by
  refine ⟨fun j => g (centerVertex j), ?_⟩
  intro j k
  rw [hg _ _ ((dotProduct_comm _ _).trans (center_dot_ones n j))
    ((dotProduct_comm _ _).trans (center_dot_ones n k)), center_dot_center]
  have hcast : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsucc : (n : ℚ) + 1 ≠ 0 := by positivity
  split <;> field_simp <;> ring

private theorem remove_axis_from_similarity (n : ℕ) (s : ℚ) (hs : s ≠ 0)
    (f : (Fin (n + 1) → ℚ) → (Fin (n + 1) → ℚ))
    (hf : ∀ x y, f x ⬝ᵥ f y = (s ^ 2 / ((n : ℚ) + 1)) * (x ⬝ᵥ y)) :
    ∃ g : (Fin (n + 1) → ℚ) → (Fin n → ℚ),
      ∀ x y, (fun _ => 1) ⬝ᵥ x = 0 → (fun _ => 1) ⬝ᵥ y = 0 →
      g x ⬝ᵥ g y = (s ^ 2 / ((n : ℚ) + 1)) * (x ⬝ᵥ y) := by
  let ones : Fin (n + 1) → ℚ := fun _ => 1
  let a := s⁻¹ • f ones
  have hsucc : (n : ℚ) + 1 ≠ 0 := by positivity
  have ha : a ⬝ᵥ a = 1 := by
    rw [show a = s⁻¹ • f ones from rfl, smul_dotProduct, dotProduct_smul, hf]
    simp [smul_eq_mul, ones, dotProduct]
    field_simp
  have ha₀ : ∀ x, ones ⬝ᵥ x = 0 → f x ⬝ᵥ a = 0 := by
    intro x hx
    rw [show a = s⁻¹ • f ones from rfl, dotProduct_smul, hf, dotProduct_comm x ones, hx]
    simp
  obtain ⟨g, hg⟩ := strip_normal n a ha
  exact ⟨fun x => g (f x), fun x y hx hy => (hg _ _ (ha₀ x hx) (ha₀ y hy)).trans (hf _ _)⟩

private theorem block_similarity {ι : Type} [Fintype ι] (k d : ℕ)
    (hcard : Fintype.card ι = k * d) (scale : ℚ)
    (f : (Fin d → ℚ) → (Fin d → ℚ))
    (hf : ∀ x y, f x ⬝ᵥ f y = scale * (x ⬝ᵥ y)) :
    ∃ g : (ι → ℚ) → (ι → ℚ), ∀ x y, g x ⬝ᵥ g y = scale * (x ⬝ᵥ y) := by
  let e : ι ≃ Fin k × Fin d := Fintype.equivOfCardEq (by simpa using hcard)
  let G : (Fin k × Fin d → ℚ) → (Fin k × Fin d → ℚ) :=
    fun x p => f (fun i => x (p.1, i)) p.2
  have hG (x y : Fin k × Fin d → ℚ) : G x ⬝ᵥ G y = scale * (x ⬝ᵥ y) := by
    simp only [dotProduct, Fintype.sum_prod_type, G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact hf (fun i => x (j, i)) (fun i => y (j, i))
  refine ⟨fun x => G (x ∘ e.symm) ∘ e, ?_⟩
  intro x y
  rw [comp_equiv_dotProduct_comp_equiv, hG, comp_equiv_dotProduct_comp_equiv]

private theorem two_similarity (r : ℚ) :
    ∃ f : (Fin 2 → ℚ) → (Fin 2 → ℚ),
      ∀ x y, f x ⬝ᵥ f y = (r ^ 2 + 1) * (x ⬝ᵥ y) := by
  refine ⟨fun x => ![r * x 0 - x 1, x 0 + r * x 1], ?_⟩
  intro x y
  simp [dotProduct, Fin.sum_univ_two]
  ring

private theorem four_similarity (n : ℕ) :
    ∃ f : (Fin 4 → ℚ) → (Fin 4 → ℚ),
      ∀ x y, f x ⬝ᵥ f y = (n : ℚ) * (x ⬝ᵥ y) := by
  obtain ⟨r, s, t, u, hu⟩ := Nat.sum_four_squares n
  let a : ℍ[ℚ] := ⟨r, s, t, u⟩
  have ha : Quaternion.normSq a = (n : ℚ) := by
    have hcast := congrArg (fun v : ℕ => (v : ℚ)) hu
    push_cast at hcast
    simpa [a, Quaternion.normSq_def'] using hcast
  let Q : (Fin 4 → ℚ) → ℍ[ℚ] := fun x => ⟨x 0, x 1, x 2, x 3⟩
  let coords : ℍ[ℚ] → (Fin 4 → ℚ) := fun x => ![x.re, x.imI, x.imJ, x.imK]
  let f : (Fin 4 → ℚ) → (Fin 4 → ℚ) := fun x => coords (a * Q x)
  have hnorm (x : ℍ[ℚ]) : coords x ⬝ᵥ coords x = Quaternion.normSq x := by
    simp [dotProduct, coords, Fin.sum_univ_four, Quaternion.normSq_def', pow_two]
  have hinput (x : Fin 4 → ℚ) : Quaternion.normSq (Q x) = x ⬝ᵥ x := by
    simp [dotProduct, Q, Fin.sum_univ_four, Quaternion.normSq_def', pow_two]
  have hs (x : Fin 4 → ℚ) : f x ⬝ᵥ f x = (n : ℚ) * (x ⬝ᵥ x) := by
    rw [show f x = coords (a * Q x) from rfl, hnorm, map_mul, ha, hinput]
  have hadd (x y : Fin 4 → ℚ) : f (x + y) = f x + f y := by
    have hQ : Q (x + y) = Q x + Q y := by rfl
    change coords (a * Q (x + y)) = coords (a * Q x) + coords (a * Q y)
    rw [hQ, mul_add]
    funext i
    fin_cases i <;> rfl
  refine ⟨f, fun x y => ?_⟩
  have h := hs (x + y)
  rw [hadd] at h
  simp only [dotProduct_add, add_dotProduct, dotProduct_comm (f y) (f x),
    dotProduct_comm y x, hs] at h
  linarith only [h]

private theorem rational_simplex_of_odd_square (n : ℕ) (hn : 0 < n) (ho : Odd n)
    (hs : IsSquare n) :
    ∃ p : Fin (n + 1) → Fin n → ℚ, ∀ j k,
      p j ⬝ᵥ p k = if j = k then 1 else -(1 : ℚ)/n := by
  obtain ⟨m, hm⟩ := hs
  rw [← pow_two] at hm
  obtain ⟨k, hk⟩ := ho
  have hc : Fintype.card (Fin (n + 1)) = k.succ * 2 := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨T, hT⟩ := two_similarity (m : ℚ)
  obtain ⟨F, hF⟩ := block_similarity k.succ 2 hc ((m : ℚ) ^ 2 + 1) T hT
  have hmQ : (n : ℚ) = (m : ℚ)^2 := by exact_mod_cast hm
  have hn₀ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm₀ : (m : ℚ) ≠ 0 := by
    intro hz
    exact hn₀ (by simp [hmQ, hz])
  have hF' (x y : Fin (n + 1) → ℚ) :
      ((m : ℚ)⁻¹ • F x) ⬝ᵥ ((m : ℚ)⁻¹ • F y) =
      (((n : ℚ) + 1)^2/((n : ℚ) + 1)) * (x ⬝ᵥ y) / n := by
    rw [smul_dotProduct, dotProduct_smul, hF]
    simp only [smul_eq_mul]
    rw [hmQ]
    field_simp
  let normalized : (Fin (n + 1) → ℚ) → (Fin (n + 1) → ℚ) := fun x => (m : ℚ)⁻¹ • F x
  have hF'' : ∀ x y, normalized x ⬝ᵥ normalized y =
      (((n : ℚ) + 1)/(m : ℚ))^2 / ((n : ℚ) + 1) * (x ⬝ᵥ y) := by
    intro x y
    rw [show normalized x ⬝ᵥ normalized y = _ from hF' x y, hmQ]
    field_simp
  have hnormal : (n : ℚ) + 1 ≠ 0 := by positivity
  obtain ⟨G, hG⟩ := remove_axis_from_similarity n (((n : ℚ) + 1)/(m : ℚ))
    (div_ne_zero hnormal hm₀) normalized hF''
  apply restrict_scaled n hn G
  intro x y hx hy
  rw [hG x y hx hy]
  congr 1
  rw [hmQ]
  field_simp

private theorem rational_simplex_of_even_successor_square (n : ℕ) (hn : 0 < n) (he : Even n)
    (hs : IsSquare (n + 1)) :
    ∃ p : Fin (n + 1) → Fin n → ℚ, ∀ j k,
      p j ⬝ᵥ p k = if j = k then 1 else -(1 : ℚ)/n := by
  obtain ⟨m, hm⟩ := hs
  rw [← pow_two] at hm
  have hmOdd : Odd m := by
    have hodd : Odd (n + 1) := he.add_odd (by decide)
    rw [hm, pow_two] at hodd
    by_contra hnot
    have hmEven : Even m := (Nat.even_or_odd m).resolve_right hnot
    exact (Nat.not_odd_iff_even.mpr (hmEven.mul_right m)) hodd
  obtain ⟨a, ha⟩ := hmOdd
  have hprod : n = (a * (a + 1)) * 4 := by
    rw [ha] at hm
    nlinarith only [hm]
  have hc : Fintype.card (Fin n) = (a * (a + 1)) * 4 := by simpa using hprod
  obtain ⟨T, hT⟩ := four_similarity n
  obtain ⟨F, hF⟩ := block_similarity (a * (a + 1)) 4 hc (n : ℚ) T hT
  have hmQ : (n : ℚ) + 1 = (m : ℚ)^2 := by exact_mod_cast hm
  have hn₀ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnormal : (n : ℚ) + 1 ≠ 0 := by positivity
  have h1 : ∀ x y : Fin (n + 1) → ℚ, id x ⬝ᵥ id y = (m : ℚ)^2 / ((n : ℚ) + 1) * (x ⬝ᵥ y) := by
    intro x y
    rw [← hmQ, div_self hnormal, one_mul]
    rfl
  have hm₀ : (m : ℚ) ≠ 0 := by
    intro hmzero
    exact hnormal (by simp [hmQ, hmzero])
  obtain ⟨G, hG⟩ := remove_axis_from_similarity n m hm₀ id h1
  apply restrict_scaled n hn (fun x => ((m : ℚ)/n) • F (G x))
  intro x y hx hy
  rw [smul_dotProduct, dotProduct_smul, hF, hG x y hx hy, ← hmQ, div_self hnormal, one_mul]
  simp only [smul_eq_mul]
  rw [hmQ]
  field_simp

/-- The Euclidean unit sphere over the rationals contains a full regular simplex
exactly when the odd member of the pair n, n + 1 is a square. -/
theorem rational_unit_simplex_iff (n : ℕ) (hn : 0 < n) :
    (∃ c : ℚ, c ≠ 1 ∧ ∃ p : Fin (n + 1) → Fin n → ℚ, ∀ j k,
      p j ⬝ᵥ p k = if j = k then 1 else c) ↔
    (Odd n ∧ IsSquare n) ∨ (Even n ∧ IsSquare (n + 1)) := by
  constructor
  · rintro ⟨c, hc, p, hp⟩
    let V : Matrix (Fin n) (Fin (n + 1)) ℚ := Matrix.of fun i j => p j i
    have H : Vᵀ * V = constantGram (n + 1) c := by
      ext j k
      exact hp j k
    obtain ⟨hodd, heven⟩ := rational_full_simplex_necessary n hn c hc V H
    rcases Nat.even_or_odd n with he | ho
    · exact Or.inr ⟨he, heven he⟩
    · exact Or.inl ⟨ho, hodd ho⟩
  · intro hs
    have hpos : (0 : ℚ) < n := by exact_mod_cast hn
    refine ⟨-(1 : ℚ)/n, ne_of_lt (div_neg_of_neg_of_pos (by norm_num) hpos |>.trans zero_lt_one), ?_⟩
    rcases hs with ⟨ho, hs⟩ | ⟨he, hs⟩
    · exact rational_simplex_of_odd_square n hn ho hs
    · exact rational_simplex_of_even_successor_square n hn he hs

end D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex
