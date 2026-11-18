/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeThreeCut
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeThreeCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Three-edge cuts of connected balanced cubic nine-cube graphs isolate a vertex. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeCut
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangMinimalResidual
import Batteries.Tactic.OpenPrivate

/-! Equality in the integral Huang energy gap forces a singleton side of an actual cut. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap (Q9)
open private huangMatrix cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private inside_equation switching_sq matrix_support from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private intCoeff intA evenPart oddPart residual parts_add intA_sub intA_mul
  intA_square intA_cast intCoeff_cast matrix_zero_of_not_adj intCoeff_zero_of_not_adj
  intA_residual residual_norm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private exists_cut_energy from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeCut

open Classical in
private def lap (f : Q9 → ℤ) (x : Q9) : ℤ := 3 * f x - intA f x

open Classical in
private def delta (y : Q9) (x : Q9) : ℤ := if x = y then 1 else 0

open Classical in
private theorem intA_add_local (f g : Q9 → ℤ) :
    intA (f + g) = intA f + intA g := by
  funext x
  simp [intA, mul_add, Finset.sum_add_distrib]

open Classical in
private theorem intA_delta (y : Q9) : intA (delta y) = fun x => intCoeff x y := by
  funext x
  simp [intA, delta, mul_ite]

open Classical in
private theorem lap_mul (c : ℤ) (f : Q9 → ℤ) :
    lap (fun x => c * f x) = fun x => c * lap f x := by
  funext x
  unfold lap
  rw [intA_mul]
  ring

open Classical in
private theorem lap_residual (f : Q9 → ℤ) :
    lap (residual f) = fun x => 3 * lap f x := by
  funext x
  have hf := congrFun (parts_add f) x
  have hAf := congrFun (congrArg intA (parts_add f)) x
  rw [intA_add_local] at hAf
  simp only [Pi.add_apply] at hf hAf
  have hAr := congrFun (intA_residual f) x
  unfold lap
  rw [hAr]
  change 3 * (3 * evenPart f x - intA (oddPart f) x) -
    3 * (intA (evenPart f) x - 3 * oddPart f x) = 3 * (3 * f x - intA f x)
  omega

open Classical in
private theorem lap_column (y : Q9) :
    lap (fun x => intCoeff x y) = fun x => -3 * lap (delta y) x := by
  have hAA := intA_square (delta y)
  rw [intA_delta] at hAA
  funext x
  have hx := congrFun hAA x
  have hd := congrFun (intA_delta y) x
  simp only [lap]
  rw [hx, hd]
  ring

open Classical in
private theorem energy_three_lap (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 3) :
    ∃ y : Q9, ∃ s : ℤ, s ^ 2 = 1 ∧
      ∀ x, lap f x = s * (3 * (if x = y then 1 else 0) - intCoeff x y) := by
  have hn : (∑ x, residual f x ^ 2) = (9 : ℤ) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [residual_norm, he]
    norm_num
  have hd : ∀ x, (3 : ℤ) ∣ intA (residual f) x := by
    intro x
    rw [intA_residual]
    exact dvd_mul_right 3 _
  rcases HuangMinimalResidual.classify_nine_residual (residual f) hn hd with
    ⟨y, s, hs, hr⟩ | ⟨y, s, hs, hr⟩
  · refine ⟨y, s, hs, ?_⟩
    have hr' : residual f = fun x => (3 * s) * delta y x := by
      rw [hr]
      funext x
      by_cases hx : x = y <;> simp [delta, hx]
    have hl := lap_residual f
    rw [hr', lap_mul] at hl
    intro x
    have hx := congrFun hl x
    have hdelta := congrFun (intA_delta y) x
    simp only [lap, delta] at hx
    rw [hdelta] at hx
    dsimp only [lap]
    nlinarith
  · refine ⟨y, -s, by simpa using hs, ?_⟩
    have hl := lap_residual f
    rw [hr, lap_mul, lap_column] at hl
    intro x
    have hx := congrFun hl x
    have hdelta := congrFun (intA_delta y) x
    simp only [lap] at hx
    rw [hdelta] at hx
    dsimp only [delta] at hx
    dsimp only [lap]
    nlinarith

open Classical in
private theorem signed_row (C S : Finset Q9) (sigma : Q9 → ℝ)
    (hs : IsSwitching C sigma) (hSC : S ⊆ C) (x : Q9) (hxC : x ∈ C) :
    sigma x * (huangMatrix 9).mulVec (switchingVector S sigma) x =
      ((S.filter (fun y => (hypercube 9).Adj x y)).card : ℝ) := by
  have hrestrict :
      (huangMatrix 9).mulVec (switchingVector S sigma) x =
        ∑ y ∈ S, huangMatrix 9 x y * sigma y := by
    rw [Matrix.mulVec, dotProduct]
    calc
      ∑ y, huangMatrix 9 x y * switchingVector S sigma y =
          ∑ y ∈ S, huangMatrix 9 x y * switchingVector S sigma y := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro y _ hy
        simp [switchingVector, hy]
      _ = ∑ y ∈ S, huangMatrix 9 x y * sigma y := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [switchingVector, hy]
  rw [hrestrict, Finset.mul_sum]
  calc
    ∑ y ∈ S, sigma x * (huangMatrix 9 x y * sigma y) =
        ∑ y ∈ S, if (hypercube 9).Adj x y then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : (hypercube 9).Adj x y
      · rw [ite_eq_left hxy, hs.2 x hxC y (hSC hy) hxy]
        calc
          sigma x * (sigma x * sigma y * sigma y) =
              sigma x ^ 2 * sigma y ^ 2 := by ring
          _ = 1 := by rw [switching_sq hs hxC, switching_sq hs (hSC hy)]; norm_num
      · simp [hxy, matrix_zero_of_not_adj x y hxy]
    _ = ((S.filter (fun y => (hypercube 9).Adj x y)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp

open Classical in
private def across (C T : Finset Q9) (x : Q9) : Finset Q9 :=
  if x ∈ T then (C \ T).filter (fun z => (hypercube 9).Adj x z)
  else T.filter (fun z => (hypercube 9).Adj x z)

open Classical in
private theorem across_subset (C T : Finset Q9) (hTC : T ⊆ C) (x : Q9) :
    across C T x ⊆ C.filter (fun z => (hypercube 9).Adj x z) := by
  intro z hz
  by_cases hx : x ∈ T
  · rw [across, ite_eq_left hx] at hz
    obtain ⟨hz, hxz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, hxz⟩
  · rw [across, ite_eq_right hx] at hz
    obtain ⟨hz, hxz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hTC hz, hxz⟩

open Classical in
private theorem across_lap (C T : Finset Q9) (sigma : Q9 → ℝ)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hTC : T ⊆ C)
    (f : Q9 → ℤ) (hf : (fun x => (f x : ℝ)) = switchingVector T sigma)
    (x : Q9) (hxC : x ∈ C) :
    |(lap f x : ℝ)| = ((across C T x).card : ℝ) := by
  have hl : (lap f x : ℝ) =
      3 * switchingVector T sigma x -
        (huangMatrix 9).mulVec (switchingVector T sigma) x := by
    simp only [lap, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, intA_cast]
    rw [congrFun hf x, hf]
  have hsplit : switchingVector C sigma =
      switchingVector T sigma + switchingVector (C \ T) sigma := by
    funext z
    by_cases hzT : z ∈ T
    · simp [switchingVector, hzT, hTC hzT]
    · by_cases hzC : z ∈ C <;> simp [switchingVector, hzT, hzC]
  by_cases hxT : x ∈ T
  · have hi := inside_equation C sigma hr hs hxC
    rw [hsplit, Matrix.mulVec_add] at hi
    have hl' : (lap f x : ℝ) =
        (huangMatrix 9).mulVec (switchingVector (C \ T) sigma) x := by
      rw [hl]
      simp only [Pi.add_apply] at hi
      have hz : switchingVector (C \ T) sigma x = 0 := by
        simp [switchingVector, hxT]
      rw [hz, add_zero] at hi
      norm_num only at hi
      linarith
    have hrow := signed_row C (C \ T) sigma hs
      (fun z hz => (Finset.mem_sdiff.mp hz).1) x hxC
    rw [← hl'] at hrow
    have hnonneg : (0 : ℝ) ≤
        (((C \ T).filter (fun z => (hypercube 9).Adj x z)).card : ℝ) := by positivity
    rcases hs.1 x hxC with hp | hm
    · rw [hp, one_mul] at hrow
      rw [hrow, abs_of_nonneg hnonneg]
      simp only [across, ite_eq_left hxT]
    · rw [hm, neg_one_mul] at hrow
      have hh : (lap f x : ℝ) =
          -((((C \ T).filter (fun z => (hypercube 9).Adj x z)).card : ℝ)) := by
        linarith
      rw [hh, abs_neg, abs_of_nonneg hnonneg]
      simp only [across, ite_eq_left hxT]
  · have hl' : (lap f x : ℝ) =
        -(huangMatrix 9).mulVec (switchingVector T sigma) x := by
      rw [hl]
      simp [switchingVector, hxT]
    have hrow := signed_row C T sigma hs hTC x hxC
    have hnonneg : (0 : ℝ) ≤
        ((T.filter (fun z => (hypercube 9).Adj x z)).card : ℝ) := by positivity
    rcases hs.1 x hxC with hp | hm
    · rw [hp, one_mul] at hrow
      rw [hl', hrow, abs_neg, abs_of_nonneg hnonneg]
      simp only [across, ite_eq_right hxT]
    · rw [hm, neg_one_mul] at hrow
      have hh : (lap f x : ℝ) =
          ((T.filter (fun z => (hypercube 9).Adj x z)).card : ℝ) := by
        linarith
      rw [hh, abs_of_nonneg hnonneg]
      simp only [across, ite_eq_right hxT]

open Classical in
private theorem mem_across_iff (C T : Finset Q9) (hTC : T ⊆ C) (x z : Q9) :
    z ∈ across C T x ↔
      z ∈ C ∧ (hypercube 9).Adj x z ∧ (x ∈ T ↔ z ∉ T) := by
  by_cases hx : x ∈ T
  · simp only [across, ite_eq_left hx, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  · simp only [across, ite_eq_right hx, Finset.mem_filter]
    constructor
    · rintro ⟨hz, hxz⟩
      exact ⟨hTC hz, hxz, by tauto⟩
    · rintro ⟨_, hxz, hop⟩
      exact ⟨by tauto, hxz⟩

open Classical in
private theorem neighbor_card (C : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (x : Q9) (hxC : x ∈ C) :
    (C.filter (fun z => (hypercube 9).Adj x z)).card = 3 := by
  let G := (hypercube 9).induce (C : Set Q9)
  let xC : (C : Set Q9) := ⟨x, hxC⟩
  have himage : (G.neighborFinset xC).image Subtype.val =
      C.filter (fun z => (hypercube 9).Adj x z) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
      have hadj : (hypercube 9).Adj x w.val :=
        (G.mem_neighborFinset xC w).mp hw
      exact Finset.mem_filter.mpr ⟨hwz ▸ w.property, hwz ▸ hadj⟩
    · intro hz
      obtain ⟨hzC, hxz⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_image.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
      apply (G.mem_neighborFinset xC ⟨z, hzC⟩).mpr
      exact hxz
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hr.degree_eq xC

open Classical in
private theorem cube_no_triangle (u v y : Q9)
    (huv : (hypercube 9).Adj u v) (hyu : (hypercube 9).Adj y u)
    (hyv : (hypercube 9).Adj y v) : False := by
  have huv' := cubeParity_ne_of_adj huv
  have hyu' := cubeParity_ne_of_adj hyu
  have hyv' := cubeParity_ne_of_adj hyv
  cases hy : cubeParity y <;> cases hu : cubeParity u <;>
    cases hv : cubeParity v <;> simp_all

open Classical in
private theorem walk_closed {V : Type*} {G : SimpleGraph V} (P : V → Prop)
    (hc : ∀ ⦃u v⦄, G.Adj u v → P u → P v)
    {u v : V} (p : G.Walk u v) : P u → P v := by
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (hc h hu)

open Classical in
/-- A three-edge actual cut in a connected balanced induced cubic nine-cube graph
has a singleton side. -/
theorem singleton_side_of_cut_card_eq_three (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : BalancedCriticalSpectrum.IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C)
    (hcut : (BalancedCubeCut.cutEdges C T).card = 3) :
    T.card = 1 ∨ (C \ T).card = 1 := by
  obtain ⟨sigma, hs⟩ := hb
  obtain ⟨f, hf, he⟩ := exists_cut_energy C T sigma hr hs hTC
  have he3 : HuangIntegralNormGap.energy f = 3 := by simpa [hcut] using he
  obtain ⟨y, s, hsquare, hshape⟩ := energy_three_lap f he3
  have habs (x : Q9) (hxC : x ∈ C) :
      |(lap f x : ℝ)| = ((across C T x).card : ℝ) :=
    across_lap C T sigma hr hs hTC f hf x hxC
  have hcutpos : 0 < (BalancedCubeCut.cutEdges C T).card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcutpos
  have he' := Finset.mem_sigma.mp he
  have huT : e.1 ∈ T := he'.1
  have hvfilter := Finset.mem_filter.mp he'.2
  have hvC : e.2 ∈ C := (Finset.mem_sdiff.mp hvfilter.1).1
  have hvT : e.2 ∉ T := (Finset.mem_sdiff.mp hvfilter.1).2
  have huv : (hypercube 9).Adj e.1 e.2 := hvfilter.2
  have huC : e.1 ∈ C := hTC huT
  have hvacross : e.2 ∈ across C T e.1 :=
    (mem_across_iff C T hTC e.1 e.2).mpr ⟨hvC, huv, by tauto⟩
  have huacross : e.1 ∈ across C T e.2 :=
    (mem_across_iff C T hTC e.2 e.1).mpr ⟨huC, huv.symm, by tauto⟩
  have hnonzero (x : Q9) (hxC : x ∈ C) (hn : (across C T x).Nonempty) :
      lap f x ≠ 0 := by
    intro hz
    have ha := habs x hxC
    have hp : 0 < (across C T x).card := Finset.card_pos.mpr hn
    rw [hz] at ha
    have hc : ((across C T x).card : ℝ) = 0 := by simpa using ha.symm
    have : (across C T x).card = 0 := by exact_mod_cast hc
    omega
  have hyC : y ∈ C := by
    by_contra hyC
    have huy : e.1 ≠ y := by intro h; exact hyC (h ▸ huC)
    have hvy : e.2 ≠ y := by intro h; exact hyC (h ▸ hvC)
    have huL := hnonzero e.1 huC ⟨e.2, hvacross⟩
    have hvL := hnonzero e.2 hvC ⟨e.1, huacross⟩
    have huyAdj : (hypercube 9).Adj e.1 y := by
      by_contra h
      have hz := hshape e.1
      rw [ite_eq_right huy, intCoeff_zero_of_not_adj e.1 y h] at hz
      simp only [mul_zero, sub_zero] at hz
      exact huL hz
    have hvyAdj : (hypercube 9).Adj e.2 y := by
      by_contra h
      have hz := hshape e.2
      rw [ite_eq_right hvy, intCoeff_zero_of_not_adj e.2 y h] at hz
      simp only [mul_zero, sub_zero] at hz
      exact hvL hz
    exact cube_no_triangle e.1 e.2 y huv huyAdj.symm hvyAdj.symm
  have hyy : intCoeff y y = 0 :=
    intCoeff_zero_of_not_adj y y ((hypercube 9).irrefl (v := y))
  have hLy : lap f y = 3 * s := by
    have h := hshape y
    simp only [ite_true, hyy, sub_zero, mul_one] at h
    linarith
  have hsign : s = 1 ∨ s = -1 := by
    have hz : (s - 1) * (s + 1) = 0 := by nlinarith [hsquare]
    rcases mul_eq_zero.mp hz with h | h
    · left; linarith
    · right; linarith
  have hyAcross : (across C T y).card = 3 := by
    have ha := habs y hyC
    rw [hLy] at ha
    rcases hsign with hp | hm
    · rw [hp] at ha
      norm_num at ha
      exact_mod_cast ha.symm
    · rw [hm] at ha
      norm_num at ha
      exact_mod_cast ha.symm
  have hallAcross : across C T y = C.filter (fun z => (hypercube 9).Adj y z) := by
    apply Finset.eq_of_subset_of_card_le (across_subset C T hTC y)
    exact le_of_eq ((neighbor_card C hr y hyC).trans hyAcross.symm)
  have hyNoSame (z : Q9) (hzC : z ∈ C) (hsame : z ∈ T ↔ y ∈ T) :
      ¬ (hypercube 9).Adj y z := by
    intro hyz
    have hz : z ∈ across C T y := by
      rw [hallAcross]
      exact Finset.mem_filter.mpr ⟨hzC, hyz⟩
    have hop := ((mem_across_iff C T hTC y z).mp hz).2.2
    tauto
  have hzeroAcross (x : Q9) (hxC : x ∈ C) (hxy : x ≠ y)
      (hsame : x ∈ T ↔ y ∈ T) : (across C T x).card = 0 := by
    have hn : ¬ (hypercube 9).Adj x y := by
      intro hxyAdj
      exact hyNoSame x hxC hsame hxyAdj.symm
    have hz : lap f x = 0 := by
      rw [hshape x, ite_eq_right hxy, intCoeff_zero_of_not_adj x y hn]
      ring
    have ha := habs x hxC
    rw [hz] at ha
    have hc : ((across C T x).card : ℝ) = 0 := by simpa using ha.symm
    exact_mod_cast hc
  have hsame_eq (x : Q9) (hxC : x ∈ C) (hsame : x ∈ T ↔ y ∈ T) : x = y := by
    by_contra hxy
    let G := (hypercube 9).induce (C : Set Q9)
    let P : {z : Q9 // z ∈ C} → Prop := fun z => (z.val ∈ T ↔ y ∈ T) ∧ z.val ≠ y
    have hclosed : ∀ ⦃u v : (C : Set Q9)⦄, G.Adj u v → P u → P v := by
      intro u v huv hu
      have huv' : (hypercube 9).Adj u.val v.val := huv
      have huSame : u.val ∈ T ↔ y ∈ T := hu.1
      have huNe : u.val ≠ y := hu.2
      have hcard := hzeroAcross u.val u.property huNe huSame
      have hvSame : v.val ∈ T ↔ y ∈ T := by
        by_contra hvSame
        have hop : u.val ∈ T ↔ v.val ∉ T := by tauto
        have hvAcross : v.val ∈ across C T u.val :=
          (mem_across_iff C T hTC u.val v.val).mpr ⟨v.property, huv', hop⟩
        have hempty := Finset.card_eq_zero.mp hcard
        rw [hempty] at hvAcross
        exact Finset.notMem_empty _ hvAcross
      have hvNe : v.val ≠ y := by
        intro hvy
        have hyu : (hypercube 9).Adj y u.val := by
          simpa only [hvy] using huv'.symm
        exact hyNoSame u.val u.property huSame hyu
      exact ⟨hvSame, hvNe⟩
    obtain ⟨p⟩ := hconn.preconnected ⟨x, hxC⟩ ⟨y, hyC⟩
    have hxP : P ⟨x, hxC⟩ := ⟨hsame, hxy⟩
    have hyP : P ⟨y, hyC⟩ := walk_closed P hclosed p hxP
    exact hyP.2 rfl
  by_cases hyT : y ∈ T
  · left
    have hsingle : T = {y} := by
      ext x
      constructor
      · intro hxT
        exact Finset.mem_singleton.mpr (hsame_eq x (hTC hxT) (by tauto))
      · intro hx
        have hxy := Finset.mem_singleton.mp hx
        simpa only [hxy] using hyT
    rw [hsingle]
    exact Finset.card_singleton y
  · right
    have hsingle : C \ T = {y} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxC, hxT⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_singleton.mpr (hsame_eq x hxC (by tauto))
      · intro hx
        have hxy := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_sdiff.mpr ⟨hyC, hyT⟩
    rw [hsingle]
    exact Finset.card_singleton y

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut
