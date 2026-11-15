/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Every positive integral Huang nine-cube energy is at least three. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
import Batteries.Tactic.OpenPrivate

/-! A gap for positive integral energies of the original Huang nine-cube matrix. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q)
open private huangMatrix huangMatrix_symmetric huang_energy cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_support coeff matrix_coeff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

abbrev Q9 := BalancedCriticalSpectrum.Q 9

def energy (f : Q9 → ℤ) : ℝ :=
  (fun x => (f x : ℝ)) ⬝ᵥ ((3 : ℝ) • (fun x => (f x : ℝ)) -
    (huangMatrix 9).mulVec (fun x => (f x : ℝ)))

private def intCoeff (x y : Q9) : ℤ := Int.floor (huangMatrix 9 x y)

private def intA (f : Q9 → ℤ) : Q9 → ℤ :=
  fun x => ∑ y, intCoeff x y * f y

private def evenPart (f : Q9 → ℤ) : Q9 → ℤ :=
  fun x => if cubeParity x = false then f x else 0

private def oddPart (f : Q9 → ℤ) : Q9 → ℤ :=
  fun x => if cubeParity x = true then f x else 0

private def residual (f : Q9 → ℤ) : Q9 → ℤ :=
  fun x => 3 * evenPart f x - intA (oddPart f) x

private def castFn (f : Q9 → ℤ) : Q9 → ℝ := fun x => (f x : ℝ)

private def energyInt (f : Q9 → ℤ) : ℤ :=
  3 * ∑ x, f x ^ 2 - ∑ x, f x * intA f x

private theorem matrix_zero_of_not_adj (x y : Q9)
    (h : ¬ (hypercube 9).Adj x y) : huangMatrix 9 x y = 0 := by
  have ha := matrix_support x y
  rw [ite_eq_right h] at ha
  exact abs_eq_zero.mp ha

private theorem matrix_sign_of_adj (x y : Q9)
    (h : (hypercube 9).Adj x y) :
    huangMatrix 9 x y = 1 ∨ huangMatrix 9 x y = -1 := by
  have ha := matrix_support x y
  rw [ite_eq_left h] at ha
  exact eq_or_eq_neg_of_abs_eq ha

private theorem intCoeff_cast (x y : Q9) :
    (intCoeff x y : ℝ) = huangMatrix 9 x y := by
  classical
  by_cases h : (hypercube 9).Adj x y
  · rcases matrix_sign_of_adj x y h with hs | hs <;> norm_num [intCoeff, hs]
  · rw [intCoeff, matrix_zero_of_not_adj x y h]
    norm_num

private theorem intA_cast (f : Q9 → ℤ) (x : Q9) :
    (intA f x : ℝ) = (huangMatrix 9).mulVec (fun y => (f y : ℝ)) x := by
  classical
  simp only [intA, Int.cast_sum, Int.cast_mul, intCoeff_cast, Matrix.mulVec, dotProduct]

private theorem intA_sub (f g : Q9 → ℤ) : intA (f - g) = intA f - intA g := by
  classical
  funext x
  simp [intA, mul_sub, Finset.sum_sub_distrib]

private theorem intA_mul (c : ℤ) (f : Q9 → ℤ) :
    intA (fun x => c * f x) = fun x => c * intA f x := by
  classical
  funext x
  simp only [intA, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

private theorem huang_square (z : Q9 → ℝ) :
    (huangMatrix 9).mulVec ((huangMatrix 9).mulVec z) = (9 : ℝ) • z := by
  rw [matrix_coeff, matrix_coeff, (coeff 9).symm_apply_apply, Sensitivity.f_squared,
    map_smul]
  norm_num

private theorem intA_square (f : Q9 → ℤ) :
    intA (intA f) = fun x => 9 * f x := by
  funext x
  apply Int.cast_injective (α := ℝ)
  rw [intA_cast]
  have hfun : (fun y => (intA f y : ℝ)) =
      (huangMatrix 9).mulVec (fun y => (f y : ℝ)) := funext (intA_cast f)
  rw [hfun, huang_square]
  simp

private theorem parts_add (f : Q9 → ℤ) : evenPart f + oddPart f = f := by
  funext x
  cases h : cubeParity x <;> simp [evenPart, oddPart, h]

private theorem parts_orthogonal (f : Q9 → ℤ) (x : Q9) :
    evenPart f x * oddPart f x = 0 := by
  cases h : cubeParity x <;> simp [evenPart, oddPart, h]

private theorem matrix_zero_of_same_parity (x y : Q9)
    (h : cubeParity x = cubeParity y) : huangMatrix 9 x y = 0 := by
  apply matrix_zero_of_not_adj
  intro hadj
  exact cubeParity_ne_of_adj hadj h

private theorem intCoeff_zero_of_not_adj (x y : Q9)
    (h : ¬ (hypercube 9).Adj x y) : intCoeff x y = 0 := by
  apply Int.cast_injective (α := ℝ)
  simpa only [intCoeff_cast, Int.cast_zero] using matrix_zero_of_not_adj x y h

private theorem intCoeff_zero_of_same_parity (x y : Q9)
    (h : cubeParity x = cubeParity y) : intCoeff x y = 0 := by
  apply Int.cast_injective (α := ℝ)
  simpa only [intCoeff_cast, Int.cast_zero] using matrix_zero_of_same_parity x y h

private theorem intCoeff_sign_of_adj (x y : Q9)
    (h : (hypercube 9).Adj x y) : intCoeff x y = 1 ∨ intCoeff x y = -1 := by
  rcases matrix_sign_of_adj x y h with hs | hs
  · left
    apply Int.cast_injective (α := ℝ)
    simpa only [intCoeff_cast, Int.cast_one] using hs
  · right
    apply Int.cast_injective (α := ℝ)
    simpa only [intCoeff_cast, Int.cast_neg, Int.cast_one] using hs

private theorem intA_even_on_even (f : Q9 → ℤ) (x : Q9)
    (hx : cubeParity x = false) : intA (evenPart f) x = 0 := by
  classical
  unfold intA
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hy : cubeParity y = false
  · rw [intCoeff_zero_of_same_parity x y (hx.trans hy.symm)]
    simp
  · simp [evenPart, hy]

private theorem intA_odd_on_odd (f : Q9 → ℤ) (x : Q9)
    (hx : cubeParity x = true) : intA (oddPart f) x = 0 := by
  classical
  unfold intA
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hy : cubeParity y = true
  · rw [intCoeff_zero_of_same_parity x y (hx.trans hy.symm)]
    simp
  · simp [oddPart, hy]

private theorem even_self_zero (f : Q9 → ℤ) :
    castFn (evenPart f) ⬝ᵥ (huangMatrix 9).mulVec (castFn (evenPart f)) = 0 := by
  classical
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hpx : cubeParity x = false
  · have hz : (huangMatrix 9).mulVec (castFn (evenPart f)) x = 0 := by
      change (huangMatrix 9).mulVec (fun y => (evenPart f y : ℝ)) x = 0
      rw [← intA_cast]
      simp [intA_even_on_even f x hpx]
    rw [hz, mul_zero]
  · simp [castFn, evenPart, hpx]

private theorem odd_self_zero (f : Q9 → ℤ) :
    castFn (oddPart f) ⬝ᵥ (huangMatrix 9).mulVec (castFn (oddPart f)) = 0 := by
  classical
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hpx : cubeParity x = true
  · have hz : (huangMatrix 9).mulVec (castFn (oddPart f)) x = 0 := by
      change (huangMatrix 9).mulVec (fun y => (oddPart f y : ℝ)) x = 0
      rw [← intA_cast]
      simp [intA_odd_on_odd f x hpx]
    rw [hz, mul_zero]
  · simp [castFn, oddPart, hpx]

private theorem parts_cast_add (f : Q9 → ℤ) :
    castFn (evenPart f) + castFn (oddPart f) = castFn f := by
  funext x
  have h : evenPart f x + oddPart f x = f x := congrFun (parts_add f) x
  change (evenPart f x : ℝ) + (oddPart f x : ℝ) = (f x : ℝ)
  exact_mod_cast h

private theorem residual_cast (f : Q9 → ℤ) :
    castFn (residual f) =
      (3 : ℝ) • castFn (evenPart f) -
        (huangMatrix 9).mulVec (castFn (oddPart f)) := by
  funext x
  change ((3 * evenPart f x - intA (oddPart f) x : ℤ) : ℝ) =
    3 * (evenPart f x : ℝ) -
      (huangMatrix 9).mulVec (fun y => (oddPart f y : ℝ)) x
  push_cast
  rw [intA_cast]

private theorem energyInt_cast (f : Q9 → ℤ) :
    (energyInt f : ℝ) = energy f := by
  classical
  simp only [energyInt, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_sum,
    Int.cast_pow, intA_cast, energy, dotProduct, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private theorem residual_norm (f : Q9 → ℤ) :
    ∑ x, (residual f x : ℝ) ^ 2 = 3 * energy f := by
  let e : Q9 → ℝ := castFn (evenPart f)
  let o : Q9 → ℝ := castFn (oddPart f)
  have hsum : e + o = castFn f := by
    simpa [e, o] using parts_cast_add f
  have hee : e ⬝ᵥ (huangMatrix 9).mulVec e = 0 := by
    simpa [e] using even_self_zero f
  have hoo : o ⬝ᵥ (huangMatrix 9).mulVec o = 0 := by
    simpa [o] using odd_self_zero f
  have hsym : (huangMatrix 9).IsSymm :=
    Matrix.IsSymm.ext (fun x y => huangMatrix_symmetric y x)
  have hcross : e ⬝ᵥ (huangMatrix 9).mulVec o =
      o ⬝ᵥ (huangMatrix 9).mulVec e := by
    exact hsym.dotProduct_mulVec_comm (x := e) (y := o)
  have hcross' : (huangMatrix 9).mulVec o ⬝ᵥ e =
      e ⬝ᵥ (huangMatrix 9).mulVec o := dotProduct_comm _ _
  have horth : e ⬝ᵥ o = 0 := by
    rw [dotProduct]
    apply Finset.sum_eq_zero
    intro x hx
    dsimp only [e, o, castFn]
    exact_mod_cast parts_orthogonal f x
  have horth' : o ⬝ᵥ e = 0 := by rw [dotProduct_comm, horth]
  have ho_norm : (huangMatrix 9).mulVec o ⬝ᵥ
      (huangMatrix 9).mulVec o = 9 * (o ⬝ᵥ o) := by
    simpa only [dotProduct, ← pow_two, Nat.cast_ofNat] using huang_energy 9 o
  have hen : energy f = 3 * (e ⬝ᵥ e) + 3 * (o ⬝ᵥ o) -
      2 * (e ⬝ᵥ (huangMatrix 9).mulVec o) := by
    change castFn f ⬝ᵥ ((3 : ℝ) • castFn f -
      (huangMatrix 9).mulVec (castFn f)) = _
    rw [← hsum]
    simp only [dotProduct_sub, dotProduct_smul, Matrix.mulVec_add,
      add_dotProduct, dotProduct_add, smul_eq_mul]
    rw [horth, horth', hee, hoo, ← hcross]
    ring
  rw [show ∑ x, (residual f x : ℝ) ^ 2 =
      castFn (residual f) ⬝ᵥ castFn (residual f) by simp [castFn, dotProduct, pow_two]]
  rw [residual_cast]
  change ((3 : ℝ) • e - (huangMatrix 9).mulVec o) ⬝ᵥ
    ((3 : ℝ) • e - (huangMatrix 9).mulVec o) = _
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [hcross', ho_norm, hen]
  ring

private theorem intA_residual (f : Q9 → ℤ) :
    intA (residual f) =
      fun x => 3 * (intA (evenPart f) x - 3 * oddPart f x) := by
  change intA ((fun x => 3 * evenPart f x) - intA (oddPart f)) = _
  rw [intA_sub, intA_mul, intA_square]
  funext x
  simp only [Pi.sub_apply]
  ring

private def residualSupport (f : Q9 → ℤ) : Finset Q9 :=
  Finset.univ.filter (fun x => residual f x ≠ 0)

private theorem energyInt_one_or_two (f : Q9 → ℤ)
    (hpos : 0 < energy f) (hlt : energy f < 3) :
    energyInt f = 1 ∨ energyInt f = 2 := by
  have hpos' := hpos
  have hlt' := hlt
  rw [← energyInt_cast f] at hpos' hlt'
  have hpos'' : 0 < energyInt f := by exact_mod_cast hpos'
  have hlt'' : energyInt f < 3 := by exact_mod_cast hlt'
  omega

private theorem residual_support_nonempty (f : Q9 → ℤ)
    (hpos : 0 < energy f) : (residualSupport f).Nonempty := by
  classical
  by_contra hS
  have hS0 : residualSupport f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
  have hz (x : Q9) : residual f x = 0 := by
    by_contra hx
    have hxS : x ∈ residualSupport f := by
      simp [residualSupport, hx]
    rw [hS0] at hxS
    simp at hxS
  have hzero : ∑ x, (residual f x : ℝ) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [hz x]
  have : (0 : ℝ) = 3 * energy f := by
    rw [← residual_norm f, hzero]
  nlinarith

private theorem residual_support_card_le_six (f : Q9 → ℤ)
    (hpos : 0 < energy f) (hlt : energy f < 3) :
    (residualSupport f).card ≤ 6 := by
  classical
  let S := residualSupport f
  have hE := energyInt_one_or_two f hpos hlt
  have hsum : ∑ x, (residual f x : ℝ) ^ 2 = 3 * energy f := residual_norm f
  have hsum_le : ∑ x, (residual f x : ℝ) ^ 2 ≤ 6 := by
    rw [hsum, ← energyInt_cast f]
    rcases hE with hE | hE
    · rw [hE]
      norm_num
    · rw [hE]
      norm_num
  have hterm (x : Q9) (hx : x ∈ S) :
      (1 : ℝ) ≤ (residual f x : ℝ) ^ 2 := by
    have hne : residual f x ≠ 0 := by simpa [S, residualSupport] using (Finset.mem_filter.mp hx).2
    have hcases : residual f x ≤ -1 ∨ 1 ≤ residual f x := by omega
    rcases hcases with hneg | hpos'
    · have hneg' : (residual f x : ℝ) ≤ -1 := by exact_mod_cast hneg
      nlinarith
    · have hpos'' : (1 : ℝ) ≤ residual f x := by exact_mod_cast hpos'
      nlinarith
  have hcard_real : (S.card : ℝ) ≤ ∑ x ∈ S, (residual f x : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) = ∑ _x ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ S, (residual f x : ℝ) ^ 2 := by
        exact Finset.sum_le_sum fun x hx => hterm x hx
  have hsubset : ∑ x ∈ S, (residual f x : ℝ) ^ 2 ≤
      ∑ x, (residual f x : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x hx hxS
    positivity
  have hcard_real' : (S.card : ℝ) ≤ 6 := hcard_real.trans (hsubset.trans hsum_le)
  exact_mod_cast hcard_real'

private theorem residual_small_on_support (f : Q9 → ℤ)
    (hpos : 0 < energy f) (hlt : energy f < 3)
    {x : Q9} (hx : x ∈ residualSupport f) :
    -2 ≤ residual f x ∧ residual f x ≤ 2 := by
  have hE := energyInt_one_or_two f hpos hlt
  have hsum_le : ∑ z, (residual f z : ℝ) ^ 2 ≤ 6 := by
    rw [residual_norm f, ← energyInt_cast f]
    rcases hE with hE | hE
    · rw [hE]
      norm_num
    · rw [hE]
      norm_num
  have hterm : (residual f x : ℝ) ^ 2 ≤
      ∑ z, (residual f z : ℝ) ^ 2 := by
    exact Finset.single_le_sum (s := (Finset.univ : Finset Q9))
      (f := fun z : Q9 => (residual f z : ℝ) ^ 2)
      (fun z _ => sq_nonneg _) (Finset.mem_univ x)
  have hsq : (residual f x : ℝ) ^ 2 ≤ 6 := hterm.trans hsum_le
  have hne : residual f x ≠ 0 := (Finset.mem_filter.mp hx).2
  constructor
  · by_contra h
    have h' : residual f x ≤ -3 := by omega
    have h'' : (residual f x : ℝ) ≤ -3 := by exact_mod_cast h'
    nlinarith [sq_nonneg ((residual f x : ℝ) + 3)]
  · by_contra h
    have h' : 3 ≤ residual f x := by omega
    have h'' : (3 : ℝ) ≤ residual f x := by exact_mod_cast h'
    nlinarith [sq_nonneg ((residual f x : ℝ) - 3)]

open Classical in
private theorem residual_single_neighbor (f : Q9 → ℤ) {y x : Q9}
    (hfilter : (residualSupport f).filter
      (fun z => (hypercube 9).Adj y z) = {x}) :
    intA (residual f) y = intCoeff y x * residual f x := by
  classical
  unfold intA
  apply Finset.sum_eq_single x
  · intro z hz hzx
    by_cases hzS : z ∈ residualSupport f
    · have hzAdj : ¬ (hypercube 9).Adj y z := by
        intro hadj
        have hzF : z ∈ (residualSupport f).filter
            (fun w => (hypercube 9).Adj y w) :=
          Finset.mem_filter.mpr ⟨hzS, hadj⟩
        rw [hfilter] at hzF
        exact hzx (Finset.mem_singleton.mp hzF)
      rw [intCoeff_zero_of_not_adj y z hzAdj]
      simp
    · have hz0 : residual f z = 0 := by
        by_contra hz0
        exact hzS (by simp [residualSupport, hz0])
      simp [hz0]
  · simp

theorem three_le_energy (f : Q9 → ℤ) (hpos : 0 < energy f) :
    (3 : ℝ) ≤ energy f := by
  classical
  by_contra h
  have hlt : energy f < 3 := lt_of_not_ge h
  have hS : (residualSupport f).Nonempty := residual_support_nonempty f hpos
  have hcard : (residualSupport f).card ≤ 6 :=
    residual_support_card_le_six f hpos hlt
  obtain ⟨y, hy⟩ :=
    CubeSmallSupport.exists_unique_neighbor_of_card_le_six (n := 9) (by omega)
      (residualSupport f) hS hcard
  obtain ⟨x, hfilter⟩ := Finset.card_eq_one.mp hy
  have hxF : x ∈ (residualSupport f).filter
      (fun z => (hypercube 9).Adj y z) := by
    rw [hfilter]
    simp
  have hxS : x ∈ residualSupport f := (Finset.mem_filter.mp hxF).1
  have hxy : (hypercube 9).Adj y x := (Finset.mem_filter.mp hxF).2
  have hsmall := residual_small_on_support f hpos hlt hxS
  have hne : residual f x ≠ 0 := (Finset.mem_filter.mp hxS).2
  have hsingle := residual_single_neighbor f hfilter
  rw [intA_residual f] at hsingle
  change 3 * (intA (evenPart f) y - 3 * oddPart f y) =
    intCoeff y x * residual f x at hsingle
  rcases intCoeff_sign_of_adj y x hxy with hsign | hsign
  · rw [hsign] at hsingle
    omega
  · rw [hsign] at hsingle
    omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
