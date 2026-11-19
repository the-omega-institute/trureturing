/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFourCut
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFourCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Four-edge cuts of connected balanced cubic cube graphs have a small side. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
import Batteries.Tactic.OpenPrivate

/-! Four-edge cuts with at least three vertices on both sides are impossible. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap (Q9)
open private huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private intCoeff intA intA_sub intA_mul intA_square intA_cast intCoeff_cast
  intCoeff_zero_of_not_adj intCoeff_sign_of_adj energyInt energyInt_cast
  residual residual_norm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private exists_cut_energy from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeCut
open private lap delta intA_add_local intA_delta lap_mul energy_three_lap
  across across_subset across_lap mem_across_iff neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut

open Classical in
private theorem coeff_symm (x y : Q9) : intCoeff x y = intCoeff y x := by
  apply Int.cast_injective (α := ℝ)
  simpa only [intCoeff_cast] using huangMatrix_symmetric x y

open Classical in
private theorem row_pairing (f g : Q9 → ℤ) :
    (∑ x, f x * intA g x) = ∑ x, g x * intA f x := by
  simp only [intA, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [coeff_symm y x]
  ring

open Classical in
private theorem energy_nonneg (f : Q9 → ℤ) :
    0 ≤ HuangIntegralNormGap.energy f := by
  have hn : 0 ≤ ∑ x, (residual f x : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [residual_norm] at hn
  linarith

open Classical in
private theorem lap_sub (f g : Q9 → ℤ) : lap (f - g) = lap f - lap g := by
  funext x
  simp only [lap, intA_sub, Pi.sub_apply]
  ring

open Classical in
private theorem lap_negative_eigen (f : Q9 → ℤ) :
    intA (lap f) = fun x => -3 * lap f x := by
  have heq : lap f = (fun x => 3 * f x) - intA f := rfl
  rw [heq, intA_sub, intA_mul, intA_square]
  funext x
  simp only [Pi.sub_apply]
  ring

open Classical in
private theorem lap_square_sum (f : Q9 → ℤ) :
    ((∑ x, (lap f x) ^ 2 : ℤ) : ℝ) = 6 * HuangIntegralNormGap.energy f := by
  have hcross := row_pairing f (intA f)
  rw [intA_square] at hcross
  have hnorm : (∑ x, (intA f x) ^ 2) = 9 * ∑ x, f x ^ 2 := by
    calc
      (∑ x, (intA f x) ^ 2) = ∑ x, intA f x * intA f x := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = ∑ x, f x * (9 * f x) := hcross.symm
      _ = 9 * ∑ x, f x ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hi : (∑ x, (lap f x) ^ 2) = 6 * energyInt f := by
    calc
      (∑ x, (lap f x) ^ 2) =
          9 * (∑ x, f x ^ 2) - 6 * (∑ x, f x * intA f x) +
            ∑ x, (intA f x) ^ 2 := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        simp only [lap]
        ring
      _ = 6 * energyInt f := by rw [hnorm]; unfold energyInt; ring
  rw [hi]
  push_cast
  rw [energyInt_cast]


open Classical in
private theorem energy_variation (f : Q9 → ℤ) (s : ℤ) (y : Q9) :
    HuangIntegralNormGap.energy (f - fun x => s * delta y x) =
      HuangIntegralNormGap.energy f + 3 * (s : ℝ) ^ 2 -
        2 * (s : ℝ) * (lap f y : ℝ) := by
  have hdiag : intCoeff y y = 0 :=
    intCoeff_zero_of_not_adj y y ((hypercube 9).irrefl (v := y))
  have hcross : (∑ x, f x * intCoeff x y) = intA f y := by
    unfold intA
    apply Finset.sum_congr rfl
    intro x _
    rw [coeff_symm]
    ring
  have hi : energyInt (f - fun x => s * delta y x) =
      energyInt f + 3 * s ^ 2 - 2 * s * lap f y := by
    simp only [energyInt, intA_sub, intA_mul, intA_delta, Pi.sub_apply]
    have hnorm : (∑ x, (f x - s * delta y x) ^ 2) =
        (∑ x, f x ^ 2) - 2 * s * f y + s ^ 2 := by
      calc
        (∑ x, (f x - s * delta y x) ^ 2) =
            (∑ x, f x ^ 2) - 2 * s * (∑ x, f x * delta y x) +
              s ^ 2 * ∑ x, delta y x ^ 2 := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by simp [delta, mul_ite]
    have hprod :
        (∑ x, (f x - s * delta y x) * (intA f x - s * intCoeff x y)) =
          (∑ x, f x * intA f x) - 2 * s * intA f y := by
      calc
        _ = (∑ x, f x * intA f x) - s * (∑ x, f x * intCoeff x y) -
              s * (∑ x, delta y x * intA f x) +
                s ^ 2 * ∑ x, delta y x * intCoeff x y := by
          simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by rw [hcross]; simp [delta, ite_mul, hdiag]; ring
    rw [hnorm, hprod]
    simp only [lap]
    ring
  rw [← energyInt_cast, hi]
  push_cast
  rw [energyInt_cast]

open Classical in
private theorem lap_bound_two (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 4) (y : Q9) :
    -2 ≤ lap f y ∧ lap f y ≤ 2 := by
  have hp := energy_variation f 1 y
  have hm := energy_variation f (-1) y
  rw [he] at hp hm
  norm_num at hp hm
  have hnp := energy_nonneg (f - fun x => (1 : ℤ) * delta y x)
  have hnm := energy_nonneg (f - fun x => (-1 : ℤ) * delta y x)
  simp only [one_mul, neg_one_mul] at hnp hnm
  have hp3 : lap f y ≠ 3 := by
    intro h
    have henergy : HuangIntegralNormGap.energy (f - fun x => (1 : ℤ) * delta y x) = 1 := by
      rw [h] at hp
      norm_num at hp
      simpa only [one_mul] using hp
    have hgap := HuangIntegralNormGap.three_le_energy
      (f - fun x => (1 : ℤ) * delta y x) (by rw [henergy]; norm_num)
    rw [henergy] at hgap
    norm_num at hgap
  have hm3 : lap f y ≠ -3 := by
    intro h
    have henergy : HuangIntegralNormGap.energy (f - fun x => (-1 : ℤ) * delta y x) = 1 := by
      rw [h] at hm
      norm_num at hm
      simpa only [neg_one_mul] using hm
    have hgap := HuangIntegralNormGap.three_le_energy
      (f - fun x => (-1 : ℤ) * delta y x) (by rw [henergy]; norm_num)
    rw [henergy] at hgap
    norm_num at hgap
  have hpbound : (lap f y : ℝ) ≤ 7 / 2 := by linarith
  have hmbound : -(7 / 2 : ℝ) ≤ (lap f y : ℝ) := by linarith
  have hi : -3 ≤ lap f y ∧ lap f y ≤ 3 := by
    constructor <;> by_contra h
    · have h' : lap f y ≤ -4 := by omega
      have h'' : (lap f y : ℝ) ≤ -4 := by exact_mod_cast h'
      linarith
    · have h' : 4 ≤ lap f y := by omega
      have h'' : (4 : ℝ) ≤ (lap f y : ℝ) := by exact_mod_cast h'
      linarith
  omega

open Classical in
private theorem support_of_unit_lap (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 4)
    (hu : ∀ x, lap f x = 0 ∨ lap f x = 1 ∨ lap f x = -1) :
    (Finset.univ.filter (fun x => lap f x ≠ 0)).card = 24 := by
  have hn := lap_square_sum f
  rw [he] at hn
  norm_num at hn
  have hi : (∑ x, (lap f x) ^ 2 : ℤ) = 24 := by
    apply Int.cast_injective (α := ℝ)
    simpa using hn
  have hs : (∑ x, (lap f x) ^ 2 : ℤ) =
      ((Finset.univ.filter (fun x => lap f x ≠ 0)).card : ℤ) := by
    calc
      _ = ∑ x : Q9, if lap f x ≠ 0 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hu x with h | h | h <;> simp [h]
      _ = _ := by rw [← Finset.sum_filter]; simp
  rw [hs] at hi
  exact_mod_cast hi

open private matrix_flip_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

open Classical in
private theorem eigen_norm_six_dvd (w : Q9 → ℤ)
    (hw : intA w = fun x => 3 * w x) :
    (6 : ℤ) ∣ ∑ x, w x ^ 2 := by
  let z : Q9 → ℝ := fun x => (w x : ℝ)
  have hz : (huangMatrix 9).mulVec z = (3 : ℝ) • z := by
    funext x
    rw [← intA_cast]
    change (intA w x : ℝ) = 3 * (w x : ℝ)
    have h := congrFun hw x
    exact_mod_cast h
  have hsym : (huangMatrix 9).IsSymm :=
    Matrix.IsSymm.ext (fun x y => huangMatrix_symmetric y x)
  have hmove : z ⬝ᵥ (huangMatrix 9).mulVec (gamma (0 : Fin 9) z) =
      (3 : ℝ) * (z ⬝ᵥ gamma (0 : Fin 9) z) := by
    rw [hsym.dotProduct_mulVec_comm, hz]
    simp [dotProduct_comm]
  have ha := congrArg (fun v => z ⬝ᵥ v) (anticommutator (0 : Fin 9) z)
  rw [dotProduct_add, hmove, hz, map_smul, dotProduct_smul, dotProduct_smul] at ha
  have hi : (∑ x, w x ^ 2) = 3 * ∑ x, w x * w (flip x (0 : Fin 9)) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    have hg : z ⬝ᵥ gamma (0 : Fin 9) z =
        ∑ x, (w x : ℝ) * (w (flip x (0 : Fin 9)) : ℝ) := by
      simp only [dotProduct, gamma_apply, matrix_flip_zero, one_mul, z]
    have hn : z ⬝ᵥ z = ∑ x, (w x : ℝ) ^ 2 := by
      simp only [dotProduct, z, pow_two]
    rw [hg, hn] at ha
    simp only [smul_eq_mul] at ha
    linarith
  let L : Finset Q9 := Finset.univ.filter (fun x => x 0 = false)
  let R : Finset Q9 := Finset.univ.filter (fun x => x 0 = true)
  have hpair : (∑ x ∈ L, w x * w (flip x (0 : Fin 9))) =
      ∑ x ∈ R, w x * w (flip x (0 : Fin 9)) := by
    apply Finset.sum_bij (fun x _ => flip x (0 : Fin 9))
    · intro x hx
      have hx0 := (Finset.mem_filter.mp hx).2
      simp [R, hx0]
    · intro x _ y _ hxy
      have h := congrArg (fun a : Q9 => BalancedCriticalSpectrum.flip a (0 : Fin 9)) hxy
      simpa using h
    · intro y hy
      have hy0 := (Finset.mem_filter.mp hy).2
      exact ⟨flip y (0 : Fin 9), by simp [L, hy0], by simp⟩
    · intro x _
      simp [mul_comm]
  have hsplit : (∑ x, w x * w (flip x (0 : Fin 9))) =
      (∑ x ∈ L, w x * w (flip x (0 : Fin 9))) +
        ∑ x ∈ R, w x * w (flip x (0 : Fin 9)) := by
    have hu : L ∪ R = Finset.univ := by
      ext x
      cases hx : x 0 <;> simp [L, R, hx]
    have hd : Disjoint L R := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hx0 := (Finset.mem_filter.mp hx).2
      have hy0 := (Finset.mem_filter.mp hy).2
      simp_all
    rw [← Finset.sum_union hd, hu]
  refine ⟨∑ x ∈ L, w x * w (flip x (0 : Fin 9)), ?_⟩
  rw [hi, hsplit, ← hpair]
  ring

open Classical in
private theorem lap_two_shape (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 4) (y : Q9) (s : ℤ)
    (hs : s ^ 2 = 1) (hy : lap f y = 2 * s) :
    ∃ z : Q9, ∃ t : ℤ, t ^ 2 = 1 ∧ y ≠ z ∧
      intCoeff y z = s * t ∧ lap f z = 2 * t ∧
      lap f = lap ((fun x => s * delta y x) + fun x => t * delta z x) := by
  let f' : Q9 → ℤ := f - fun x => s * delta y x
  have he' : HuangIntegralNormGap.energy f' = 3 := by
    have hv := energy_variation f s y
    rw [he, hy] at hv
    have hsr : (s : ℝ) ^ 2 = 1 := by exact_mod_cast hs
    dsimp only [f']
    push_cast at hv
    nlinarith
  obtain ⟨z, t, ht, hshape⟩ := energy_three_lap f' he'
  have hfun : lap f' = lap (fun x => t * delta z x) := by
    rw [lap_mul]
    funext x
    rw [hshape x]
    simp only [lap, intA_delta, delta]
  have hl : lap f = lap ((fun x => s * delta y x) + fun x => t * delta z x) := by
    have hadd : lap ((fun x => s * delta y x) + fun x => t * delta z x) =
        lap (fun x => s * delta y x) + lap (fun x => t * delta z x) := by
      funext x
      simp only [lap, intA_add_local, Pi.add_apply]
      ring
    rw [hadd, ← hfun]
    dsimp only [f']
    rw [lap_sub]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hyy : intCoeff y y = 0 :=
    intCoeff_zero_of_not_adj y y ((hypercube 9).irrefl (v := y))
  have hyz : y ≠ z := by
    intro h
    subst z
    have h := congrFun hl y
    rw [hy] at h
    simp only [lap, intA_add_local, intA_mul, intA_delta, Pi.add_apply] at h
    simp only [delta, ite_true, hyy, mul_one, mul_zero, add_zero] at h
    have hst : s = -3 * t := by linarith
    rw [hst] at hs
    nlinarith [ht]
  have hcoeff : intCoeff y z = s * t := by
    have h := congrFun hl y
    rw [hy] at h
    simp only [lap, intA_add_local, intA_mul, intA_delta, Pi.add_apply] at h
    simp only [delta, ite_true, ite_false, hyz, hyy, mul_one, mul_zero, add_zero] at h
    have hc : t * intCoeff y z = s := by linarith
    calc
      intCoeff y z = t ^ 2 * intCoeff y z := by rw [ht]; ring
      _ = t * (t * intCoeff y z) := by ring
      _ = t * s := by rw [hc]
      _ = s * t := by ring
  have hzz : intCoeff z z = 0 :=
    intCoeff_zero_of_not_adj z z ((hypercube 9).irrefl (v := z))
  have hz : lap f z = 2 * t := by
    have h := congrFun hl z
    simp only [lap, intA_add_local, intA_mul, intA_delta, Pi.add_apply] at h
    simp only [delta, ite_true, ite_false, Ne.symm hyz, hzz, mul_one, mul_zero,
      zero_add, coeff_symm z y, hcoeff] at h
    have hmul : s * (s * t) = s ^ 2 * t := by ring
    rw [hmul, hs] at h
    change 3 * f z - intA f z = 2 * t
    linarith
  exact ⟨z, t, ht, hyz, hcoeff, hz, hl⟩

open Classical in
private theorem cut_card_erase (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hTC : T ⊆ C) (x : Q9) (hxT : x ∈ T) :
    (BalancedCubeCut.cutEdges C (T.erase x)).card +
        2 * ((C \ T).filter (fun y => (hypercube 9).Adj x y)).card =
      (BalancedCubeCut.cutEdges C T).card + 3 := by
  classical
  let U := T.erase x
  let R := C \ T
  let row := fun u : Q9 => (R.filter (fun y => (hypercube 9).Adj u y)).card
  have hxC : x ∈ C := hTC hxT
  have hxR : x ∉ R := by simp [R, hxT]
  have hcomp : C \ U = insert x R := by
    ext y
    by_cases hyx : y = x
    · subst y
      simp [U, R, hxC, hxT]
    · simp [U, R, Finset.mem_sdiff, Finset.mem_erase, hyx]
  have hcount :
      (∑ u ∈ U, if (hypercube 9).Adj u x then (1 : ℕ) else 0) =
        (U.filter (fun u => (hypercube 9).Adj x u)).card := by
    calc
      _ = ∑ u ∈ U, if (hypercube 9).Adj x u then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        have hs : (hypercube 9).Adj u x ↔ (hypercube 9).Adj x u :=
          ⟨fun h => h.symm, fun h => h.symm⟩
        rw [hs]
      _ = _ := by rw [← Finset.sum_filter]; simp
  have hnew : (BalancedCubeCut.cutEdges C U).card =
      (∑ u ∈ U, row u) +
        (U.filter (fun u => (hypercube 9).Adj x u)).card := by
    calc
      _ = ∑ u ∈ U, ((C \ U).filter (fun y => (hypercube 9).Adj u y)).card := by
        simp only [BalancedCubeCut.cutEdges, Finset.card_sigma]
      _ = ∑ u ∈ U, (row u + if (hypercube 9).Adj u x then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [hcomp]
        by_cases hux : (hypercube 9).Adj u x <;>
          simp [row, Finset.filter_insert, hux, hxR]
      _ = _ := by rw [Finset.sum_add_distrib, hcount]
  have hold : (∑ u ∈ U, row u) + row x =
      (BalancedCubeCut.cutEdges C T).card := by
    simpa only [U, BalancedCubeCut.cutEdges, Finset.card_sigma] using
      (Finset.sum_erase_add T row hxT)
  have hdisj : Disjoint
      (U.filter (fun y => (hypercube 9).Adj x y))
      (R.filter (fun y => (hypercube 9).Adj x y)) := by
    apply Finset.disjoint_left.mpr
    intro y hyU hyR
    have hyT : y ∈ T := (Finset.mem_erase.mp (Finset.mem_filter.mp hyU).1).2
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hyR).1).2 hyT
  have hsplit :
      U.filter (fun y => (hypercube 9).Adj x y) ∪
        R.filter (fun y => (hypercube 9).Adj x y) =
          C.filter (fun y => (hypercube 9).Adj x y) := by
    ext y
    simp only [U, R, Finset.mem_union, Finset.mem_filter,
      Finset.mem_erase, Finset.mem_sdiff]
    by_cases hyx : y = x
    · subst y
      simp
    · have hmem : y ∈ T → y ∈ C := fun hyT => hTC hyT
      tauto
  have hdegree :
      (U.filter (fun y => (hypercube 9).Adj x y)).card + row x = 3 := by
    have hcard := Finset.card_union_of_disjoint hdisj
    rw [hsplit, neighbor_card C hr x hxC] at hcard
    simpa only [row] using hcard.symm
  change (BalancedCubeCut.cutEdges C U).card + 2 * row x =
    (BalancedCubeCut.cutEdges C T).card + 3
  omega

open Classical in
private theorem bound_of_mem (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C)
    (hcut : (BalancedCubeCut.cutEdges C T).card = 4)
    (hT : 3 ≤ T.card) (hR : 3 ≤ (C \ T).card)
    (x : Q9) (hxT : x ∈ T) : (across C T x).card ≤ 1 := by
  classical
  let k := ((C \ T).filter (fun y => (hypercube 9).Adj x y)).card
  have hacross : (across C T x).card = k := by simp [across, hxT, k]
  have hk : k ≤ 3 := by
    have h := Finset.card_le_card (across_subset C T hTC x)
    rw [neighbor_card C hr x (hTC hxT), hacross] at h
    exact h
  have he := cut_card_erase C T hr hTC x hxT
  change (BalancedCubeCut.cutEdges C (T.erase x)).card + 2 * k =
    (BalancedCubeCut.cutEdges C T).card + 3 at he
  have hUC : T.erase x ⊆ C := fun _ hu => hTC (Finset.mem_erase.mp hu).2
  have herase : (T.erase x).card + 1 = T.card := Finset.card_erase_add_one hxT
  have hRsub : C \ T ⊆ C \ T.erase x := by
    intro y hy
    obtain ⟨hyC, hyT⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨hyC, fun h => hyT (Finset.mem_erase.mp h).2⟩
  have hRlarge : 3 ≤ (C \ T.erase x).card :=
    hR.trans (Finset.card_le_card hRsub)
  rw [hacross]
  by_contra hbound
  have hcases : k = 2 ∨ k = 3 := by omega
  rcases hcases with hk2 | hk3
  · have hthree : (BalancedCubeCut.cutEdges C (T.erase x)).card = 3 := by omega
    rcases BalancedCubeThreeCut.singleton_side_of_cut_card_eq_three
        C (T.erase x) hr hb hconn hUC hthree with hsingle | hsingle <;> omega
  · have hone : (BalancedCubeCut.cutEdges C (T.erase x)).card = 1 := by omega
    have hmin := BalancedCubeCut.three_le_cutEdges_card C (T.erase x)
      hr hb hUC (by omega)
    omega

open Classical in
private theorem cut_card_compl (C T : Finset Q9) (hTC : T ⊆ C) :
    (BalancedCubeCut.cutEdges C (C \ T)).card =
      (BalancedCubeCut.cutEdges C T).card := by
  classical
  have hdouble : C \ (C \ T) = T := by
    ext y
    have hmem : y ∈ T → y ∈ C := fun hy => hTC hy
    simp only [Finset.mem_sdiff]
    tauto
  apply Finset.card_bij
    (fun e _ => (⟨e.2, e.1⟩ : Sigma (fun _ : Q9 => Q9)))
  · intro e he
    change e ∈ (C \ T).sigma
      (fun a => (C \ (C \ T)).filter (fun b => (hypercube 9).Adj a b)) at he
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp he
    obtain ⟨hb, hab⟩ := Finset.mem_filter.mp hb
    rw [hdouble] at hb
    change (⟨e.2, e.1⟩ : Sigma (fun _ : Q9 => Q9)) ∈
      T.sigma (fun a => (C \ T).filter (fun b => (hypercube 9).Adj a b))
    exact Finset.mem_sigma.mpr ⟨hb, Finset.mem_filter.mpr ⟨ha, hab.symm⟩⟩
  · intro a _ b _ hab
    have hfirst : a.2 = b.2 := congrArg Sigma.fst hab
    have hsecond : a.1 = b.1 := congrArg (fun e : Sigma (fun _ : Q9 => Q9) => e.2) hab
    cases a
    cases b
    simp_all
  · intro e he
    change e ∈ T.sigma
      (fun a => (C \ T).filter (fun b => (hypercube 9).Adj a b)) at he
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp he
    obtain ⟨hb, hab⟩ := Finset.mem_filter.mp hb
    refine ⟨(⟨e.2, e.1⟩ : Sigma (fun _ : Q9 => Q9)), ?_, ?_⟩
    · change (⟨e.2, e.1⟩ : Sigma (fun _ : Q9 => Q9)) ∈
        (C \ T).sigma
          (fun a => (C \ (C \ T)).filter (fun b => (hypercube 9).Adj a b))
      apply Finset.mem_sigma.mpr
      refine ⟨hb, Finset.mem_filter.mpr ⟨?_, hab.symm⟩⟩
      simpa only [hdouble] using ha
    · cases e
      rfl

open Classical in
private theorem cut_matching (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C)
    (hcut : (BalancedCubeCut.cutEdges C T).card = 4)
    (hT : 3 ≤ T.card) (hR : 3 ≤ (C \ T).card) :
    ∀ x ∈ C, (across C T x).card ≤ 1 := by
  classical
  intro x hxC
  by_cases hxT : x ∈ T
  · exact bound_of_mem C T hr hb hconn hTC hcut hT hR x hxT
  · have hSC : C \ T ⊆ C := fun _ hy => (Finset.mem_sdiff.mp hy).1
    have hdouble : C \ (C \ T) = T := by
      ext y
      have hmem : y ∈ T → y ∈ C := fun hy => hTC hy
      simp only [Finset.mem_sdiff]
      tauto
    have hxS : x ∈ C \ T := Finset.mem_sdiff.mpr ⟨hxC, hxT⟩
    have hcutS : (BalancedCubeCut.cutEdges C (C \ T)).card = 4 :=
      (cut_card_compl C T hTC).trans hcut
    have hother : 3 ≤ (C \ (C \ T)).card := by simpa only [hdouble] using hT
    have hbound := bound_of_mem C (C \ T) hr hb hconn hSC hcutS hR hother x hxS
    have hacross : across C (C \ T) x = across C T x := by
      simp only [across, ite_eq_left hxS, ite_eq_right hxT, hdouble]
    simpa only [hacross] using hbound

open Classical in
private theorem unit_laplacian_of_cut_card_eq_four (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C)
    (hcut : (BalancedCubeCut.cutEdges C T).card = 4)
    (hT : 3 ≤ T.card) (hR : 3 ≤ (C \ T).card) :
    ∃ sigma : Q9 → ℝ, ∃ f h : Q9 → ℤ,
      IsSwitching C sigma ∧
      (fun x => (f x : ℝ)) = switchingVector T sigma ∧
      h = (fun x => 3 * f x - intA f x) ∧
      (∀ x, h x = 0 ∨ h x = 1 ∨ h x = -1) ∧
      (Finset.univ.filter (fun x => h x ≠ 0)).card = 24 ∧
      intA h = (fun x => -3 * h x) := by
  classical
  have hmatching := cut_matching C T hr hb hconn hTC hcut hT hR
  obtain ⟨sigma, hs⟩ := hb
  obtain ⟨f, hf, he⟩ := exists_cut_energy C T sigma hr hs hTC
  have he4 : HuangIntegralNormGap.energy f = 4 := by
    simpa [hcut] using he
  have habs : ∀ x ∈ C, |(lap f x : ℝ)| ≤ 1 := by
    intro x hx
    rw [across_lap C T sigma hr hs hTC f hf x hx]
    exact_mod_cast hmatching x hx
  obtain ⟨total, htotal, _⟩ :=
    exists_cut_energy C C sigma hr hs (by intro x hx; exact hx)
  have htotal_eigen : intA total = fun x => 3 * total x := by
    funext x
    apply Int.cast_injective (α := ℝ)
    have hx := congrFun (ambient_eigenvector (d := 3) C sigma hr hs) x
    rw [← htotal, ← intA_cast] at hx
    simpa only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat,
      Nat.cast_ofNat] using hx
  have htotal_zero : ∀ x, x ∉ C → total x = 0 := by
    intro x hx
    apply Int.cast_injective (α := ℝ)
    have h := congrFun htotal x
    simpa [switchingVector, hx] using h
  have hf_zero : ∀ x, x ∉ T → f x = 0 := by
    intro x hx
    apply Int.cast_injective (α := ℝ)
    have h := congrFun hf x
    simpa [switchingVector, hx] using h
  have hf_total : ∀ x, x ∈ T → f x = total x := by
    intro x hx
    apply Int.cast_injective (α := ℝ)
    have h₁ := congrFun hf x
    have h₂ := congrFun htotal x
    simp [switchingVector, hx, hTC hx] at h₁ h₂
    exact h₁.trans h₂.symm
  have hout : ∀ y (s : ℤ), s ^ 2 = 1 → lap f y = 2 * s → y ∉ C := by
    intro y s hs2 hy hyC
    have hl := habs y hyC
    rw [hy] at hl
    have hsign : s = 1 ∨ s = -1 := by
      have hprod : (s - 1) * (s + 1) = 0 := by nlinarith [hs2]
      rcases mul_eq_zero.mp hprod with hp | hm
      · left; omega
      · right; omega
    rcases hsign with rfl | rfl <;> norm_num at hl
  have hno_two : ∀ y (s : ℤ), s ^ 2 = 1 → lap f y ≠ 2 * s := by
    intro y s hs2 hy
    obtain ⟨z, t, ht2, hyz, _, hz, hshape⟩ := lap_two_shape f he4 y s hs2 hy
    have hyC := hout y s hs2 hy
    have hzC := hout z t ht2 hz
    have hfy : f y = 0 := hf_zero y (fun h => hyC (hTC h))
    have hfz : f z = 0 := hf_zero z (fun h => hzC (hTC h))
    have hty : total y = 0 := htotal_zero y hyC
    have htz : total z = 0 := htotal_zero z hzC
    let g : Q9 → ℤ := (fun x => s * delta y x) + fun x => t * delta z x
    let w₁ : Q9 → ℤ := f - g
    let w₂ : Q9 → ℤ := total - w₁
    have hw₁ : intA w₁ = fun x => 3 * w₁ x := by
      have hzero : lap w₁ = 0 := by
        change lap (f - g) = 0
        rw [lap_sub]
        change lap f - lap g = 0
        exact sub_eq_zero.mpr hshape
      funext x
      have hx := congrFun hzero x
      change 3 * w₁ x - intA w₁ x = 0 at hx
      linarith
    have hw₂ : intA w₂ = fun x => 3 * w₂ x := by
      change intA (total - w₁) = _
      rw [intA_sub, htotal_eigen, hw₁]
      funext x
      change 3 * total x - 3 * w₁ x = 3 * (total x - w₁ x)
      ring
    have hpoint : ∀ x : Q9,
        w₁ x ^ 2 + w₂ x ^ 2 = total x ^ 2 +
          (if x = y then 2 else 0) + (if x = z then 2 else 0) := by
      intro x
      by_cases hxy : x = y
      · subst x
        simp [w₁, w₂, g, delta, hfy, hty, hyz, hs2]
      · by_cases hxz : x = z
        · subst x
          simp [w₁, w₂, g, delta, hfz, htz, Ne.symm hyz, ht2]
        · have hg : g x = 0 := by simp [g, delta, hxy, hxz]
          by_cases hxT : x ∈ T
          · simp [w₁, w₂, hg, hf_total x hxT, hxy, hxz]
          · simp [w₁, w₂, hg, hf_zero x hxT, hxy, hxz]
    have hsum : (∑ x : Q9, w₁ x ^ 2) + (∑ x : Q9, w₂ x ^ 2) =
        (∑ x : Q9, total x ^ 2) + 4 := by
      calc
        _ = ∑ x : Q9, (w₁ x ^ 2 + w₂ x ^ 2) := (Finset.sum_add_distrib).symm
        _ = ∑ x : Q9, (total x ^ 2 +
            (if x = y then 2 else 0) + (if x = z then 2 else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hpoint x
        _ = _ := by simp only [Finset.sum_add_distrib]; simp; ring
    obtain ⟨a, ha⟩ := eigen_norm_six_dvd w₁ hw₁
    obtain ⟨b, hb'⟩ := eigen_norm_six_dvd w₂ hw₂
    obtain ⟨c, hc⟩ := eigen_norm_six_dvd total htotal_eigen
    omega
  have hu : ∀ x, lap f x = 0 ∨ lap f x = 1 ∨ lap f x = -1 := by
    intro x
    have hbound := lap_bound_two f he4 x
    have hp := hno_two x 1 (by norm_num)
    have hm := hno_two x (-1) (by norm_num)
    norm_num at hp hm
    omega
  exact ⟨sigma, f, lap f, hs, hf, rfl, hu,
    support_of_unit_lap f he4 hu, lap_negative_eigen f⟩

open Classical in
/-- Every actual four-edge cut has a side with at most two vertices. -/
theorem small_side_of_cut_card_eq_four (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C)
    (hcut : (BalancedCubeCut.cutEdges C T).card = 4) :
    T.card ≤ 2 ∨ (C \ T).card ≤ 2 := by
  by_contra hbad
  have hT : 3 ≤ T.card := by omega
  have hR : 3 ≤ (C \ T).card := by omega
  obtain ⟨sigma, f, h, _hs, _hf, _hh, hu, hsupp, heig⟩ :=
    unit_laplacian_of_cut_card_eq_four C T hr hb hconn hTC hcut hT hR
  exact HuangUnitSupportGap.no_unit_support_card_twenty_four h heig hu hsupp

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut
