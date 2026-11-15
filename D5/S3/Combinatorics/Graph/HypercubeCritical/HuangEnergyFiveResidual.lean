/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangEnergyFiveResidual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangEnergyFiveResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Integral Huang energy-five residuals are unit-valued or signed path Laplacians. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut
import Batteries.Tactic.OpenPrivate

/-! Classification of integral energy-five residuals for the original signed
Huang operator: either thirty unit coefficients, or the Laplacian of a coherently
signed three-vertex path. The proof also gives coefficient bounds and squared
norm fifteen on each original cube parity. This is a residual classification;
it does not settle energy-five cuts or the nine-cube problem. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangEnergyFiveResidual

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap (Q9)
open private intCoeff intA intA_sub intA_mul intCoeff_zero_of_not_adj
  intCoeff_sign_of_adj intCoeff_zero_of_same_parity evenPart oddPart parts_add from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private lap delta intA_add_local intA_delta lap_mul from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut
open private coeff_symm row_pairing energy_nonneg lap_sub lap_negative_eigen
  lap_square_sum energy_variation from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut
open private parts_eigen even_diff_of_parity_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private row_on_singleton from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangMinimalResidual

open Classical in
private theorem energy_zero_lap (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 0) : lap f = 0 := by
  have hn := lap_square_sum f
  rw [he] at hn
  norm_num at hn
  have hi : (∑ x, (lap f x) ^ 2 : ℤ) = 0 := by
    exact_mod_cast hn
  funext x
  have hx : (lap f x) ^ 2 ≤ ∑ y, (lap f y) ^ 2 :=
    Finset.single_le_sum (fun y _ => sq_nonneg (lap f y)) (Finset.mem_univ x)
  rw [hi] at hx
  change lap f x = 0
  nlinarith [sq_nonneg (lap f x)]

open Classical in
private theorem energy_five_bound (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 5) (y : Q9) :
    -2 ≤ lap f y ∧ lap f y ≤ 2 := by
  have hp := energy_variation f 1 y
  have hm := energy_variation f (-1) y
  rw [he] at hp hm
  norm_num at hp hm
  have hnp := energy_nonneg (f - fun x => (1 : ℤ) * delta y x)
  have hnm := energy_nonneg (f - fun x => (-1 : ℤ) * delta y x)
  simp only [one_mul, neg_one_mul] at hnp hnm
  have hi : -4 ≤ lap f y ∧ lap f y ≤ 4 := by
    constructor <;> by_contra h
    · have hz : lap f y ≤ -5 := by omega
      have hzr : (lap f y : ℝ) ≤ -5 := by exact_mod_cast hz
      linarith
    · have hz : 5 ≤ lap f y := by omega
      have hzr : (5 : ℝ) ≤ (lap f y : ℝ) := by exact_mod_cast hz
      linarith
  have hthree (s : ℤ) (hs : s ^ 2 = 1) (hy : lap f y = 3 * s) : False := by
    have hv := energy_variation f s y
    rw [he, hy] at hv
    have hsr : (s : ℝ) ^ 2 = 1 := by exact_mod_cast hs
    push_cast at hv
    have he' : HuangIntegralNormGap.energy (f - fun x => s * delta y x) = 2 := by
      nlinarith
    have hg := HuangIntegralNormGap.three_le_energy
      (f - fun x => s * delta y x) (by rw [he']; norm_num)
    rw [he'] at hg
    norm_num at hg
  have hfour (s : ℤ) (hs : s ^ 2 = 1) (hy : lap f y = 4 * s) : False := by
    have hv := energy_variation f s y
    rw [he, hy] at hv
    have hsr : (s : ℝ) ^ 2 = 1 := by exact_mod_cast hs
    push_cast at hv
    have he' : HuangIntegralNormGap.energy (f - fun x => s * delta y x) = 0 := by
      nlinarith
    have hz := congrFun (energy_zero_lap _ he') y
    rw [lap_sub] at hz
    change lap f y - lap (fun x => s * delta y x) y = 0 at hz
    rw [hy, lap_mul] at hz
    have hdiag : intCoeff y y = 0 :=
      intCoeff_zero_of_not_adj y y ((hypercube 9).irrefl (v := y))
    simp only [lap, intA_delta, delta, ite_true, mul_one, hdiag, sub_zero] at hz
    nlinarith
  have h3 : lap f y ≠ 3 := fun h => hthree 1 (by norm_num) (by simpa using h)
  have hn3 : lap f y ≠ -3 := fun h => hthree (-1) (by norm_num) (by simpa using h)
  have h4 : lap f y ≠ 4 := fun h => hfour 1 (by norm_num) (by simpa using h)
  have hn4 : lap f y ≠ -4 := fun h => hfour (-1) (by norm_num) (by simpa using h)
  omega

open Classical in
private theorem parity_norms (r : Q9 → ℤ)
    (heig : intA r = fun x => -3 * r x) (hnorm : (∑ x, r x ^ 2) = 30) :
    (∑ x, evenPart r x ^ 2) = 15 ∧ (∑ x, oddPart r x ^ 2) = 15 := by
  obtain ⟨he, ho⟩ := parts_eigen r heig
  have hp := row_pairing (evenPart r) (oddPart r)
  have hleft : (∑ x, evenPart r x * intA (oddPart r) x) =
      -3 * ∑ x, evenPart r x ^ 2 := by
    rw [ho, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hright : (∑ x, oddPart r x * intA (evenPart r) x) =
      -3 * ∑ x, oddPart r x ^ 2 := by
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hleft, hright] at hp
  have hsplit : (∑ x, evenPart r x ^ 2) + (∑ x, oddPart r x ^ 2) = 30 := by
    rw [← hnorm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    cases hx : cubeParity x <;> simp [evenPart, oddPart, hx]
  omega

open Classical in
/-- Energy five forces the sharp coefficient bound and equal original parity norms. -/
theorem energy_five_residual_invariants (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 5) :
    (∀ x, -2 ≤ lap f x ∧ lap f x ≤ 2) ∧
    (∑ x, (lap f x) ^ 2) = 30 ∧
    (∑ x, evenPart (lap f) x ^ 2) = 15 ∧
    (∑ x, oddPart (lap f) x ^ 2) = 15 := by
  have hn := lap_square_sum f
  rw [he] at hn
  norm_num at hn
  have hi : (∑ x, (lap f x) ^ 2 : ℤ) = 30 := by
    exact_mod_cast hn
  obtain ⟨heven, hodd⟩ := parity_norms (lap f) (lap_negative_eigen f) hi
  exact ⟨energy_five_bound f he, hi, heven, hodd⟩

open Classical in
private theorem unit_support_card (r : Q9 → ℤ)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (hnorm : (∑ x, r x ^ 2) = 30) :
    (Finset.univ.filter (fun x => r x ≠ 0)).card = 30 := by
  have hs : (∑ x, r x ^ 2 : ℤ) =
      ((Finset.univ.filter (fun x => r x ≠ 0)).card : ℤ) := by
    calc
      _ = ∑ x : Q9, if r x ≠ 0 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hu x with h | h | h <;> simp [h]
      _ = _ := by rw [← Finset.sum_filter]; simp
  omega

open Classical in
/-- A unit-valued energy-five residual has exactly thirty nonzero coefficients. -/
theorem energy_five_unit_support (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 5)
    (hu : ∀ x, lap f x = 0 ∨ lap f x = 1 ∨ lap f x = -1) :
    (Finset.univ.filter (fun x => lap f x ≠ 0)).card = 30 :=
  unit_support_card (lap f) hu (energy_five_residual_invariants f he).2.1

open Classical in
private theorem heavy_half_shape (q : Q9 → ℤ) (b : Bool)
    (hb : ∀ x, -2 ≤ q x ∧ q x ≤ 2)
    (hn : (∑ x, q x ^ 2) = 15)
    (hd : ∀ x, (3 : ℤ) ∣ intA q x)
    (hp : ∀ x, q x ≠ 0 → cubeParity x = b)
    (hh : ∃ x, q x = 2 ∨ q x = -2) :
    ∃ y z w : Q9, ∃ s : ℤ, s ^ 2 = 1 ∧
      (hypercube 9).Adj y z ∧ (hypercube 9).Adj y w ∧ z ≠ w ∧
      q = (fun x => s * intCoeff x y -
        3 * s * intCoeff z y * delta z x -
        3 * s * intCoeff w y * delta w x) := by
  let S := Finset.univ.filter (fun x => q x ≠ 0)
  let H := Finset.univ.filter (fun x => q x = 2 ∨ q x = -2)
  have hcount : (∑ x, q x ^ 2) = (S.card : ℤ) + 3 * (H.card : ℤ) := by
    have hlocal (x : Q9) : q x ^ 2 =
        (if q x ≠ 0 then (1 : ℤ) else 0) +
          3 * (if q x = 2 ∨ q x = -2 then (1 : ℤ) else 0) := by
      obtain ⟨hl, hu⟩ := hb x
      have hc : q x = -2 ∨ q x = -1 ∨ q x = 0 ∨ q x = 1 ∨ q x = 2 := by omega
      rcases hc with h | h | h | h | h <;> norm_num [h]
    simp_rw [hlocal, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [← Finset.sum_filter]
    simp [S, H]
  obtain ⟨a, ha⟩ := hh
  have haH : a ∈ H := by simp [H, ha]
  have haS : a ∈ S := by rcases ha with h | h <;> simp [S, h]
  have hHpos : 0 < H.card := Finset.card_pos.mpr ⟨a, haH⟩
  have hScard : S.card ≤ 12 := by omega
  have hno : ∀ y, (S.filter (fun x => (hypercube 9).Adj y x)).card ≠ 1 := by
    intro y hy
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hy
    have hxF : x ∈ S.filter (fun z => (hypercube 9).Adj y z) := by rw [hx]; simp
    have hxne : q x ≠ 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hxF).1).2
    have hxy := (Finset.mem_filter.mp hxF).2
    have hrow := row_on_singleton q (S := S) rfl hx
    obtain ⟨k, hk⟩ := hd y
    rw [hrow] at hk
    obtain ⟨hl, hu⟩ := hb x
    rcases intCoeff_sign_of_adj y x hxy with hc | hc <;> rw [hc] at hk <;> omega
  have heven : ∀ x ∈ S, ∀ y ∈ S,
      Even (Finset.univ.filter (fun i : Fin 9 => x i ≠ y i)).card := by
    intro x hx y hy
    exact even_diff_of_parity_eq x y
      ((hp x (Finset.mem_filter.mp hx).2).trans
        (hp y (Finset.mem_filter.mp hy).2).symm)
  obtain ⟨v, hv⟩ := CubeTwelveSupport.eq_neighbors_of_card_le_twelve
    S ⟨a, haS⟩ hScard hno heven
  have hS9 : S.card = 9 := by
    rw [hv, ← (hypercube 9).neighborFinset_eq_filter]
    exact (hypercube_regular 9).degree_eq v
  have hH2 : H.card = 2 := by omega
  obtain ⟨z, w, hzw, hH⟩ := Finset.card_eq_two.mp hH2
  have hheavy (x : Q9) : (q x = 2 ∨ q x = -2) ↔ x = z ∨ x = w := by
    have hm : x ∈ H ↔ x ∈ ({z, w} : Finset Q9) := by rw [hH]
    simpa [H] using hm
  let c : Q9 → ℤ := fun x => if q x = 2 then -1 else if q x = -2 then 1 else q x
  let d : Q9 → ℤ := fun x => if q x = 2 then 1 else if q x = -2 then -1 else 0
  have hcunit : ∀ x, c x = 0 ∨ c x = 1 ∨ c x = -1 := by
    intro x
    obtain ⟨hl, hu⟩ := hb x
    have hc : q x = -2 ∨ q x = -1 ∨ q x = 0 ∨ q x = 1 ∨ q x = 2 := by omega
    rcases hc with h | h | h | h | h <;> simp [c, h]
  have hcsq (x : Q9) : c x ^ 2 = if q x ≠ 0 then (1 : ℤ) else 0 := by
    obtain ⟨hl, hu⟩ := hb x
    have hc : q x = -2 ∨ q x = -1 ∨ q x = 0 ∨ q x = 1 ∨ q x = 2 := by omega
    rcases hc with h | h | h | h | h <;> norm_num [c, h]
  have hcn : (∑ x, c x ^ 2) = 9 := by
    simp_rw [hcsq]
    rw [← Finset.sum_filter]
    simpa [S] using congrArg (fun n : ℕ => (n : ℤ)) hS9
  have hdecomp : q = c + (fun x => 3 * d x) := by
    funext x
    obtain ⟨hl, hu⟩ := hb x
    have hc : q x = -2 ∨ q x = -1 ∨ q x = 0 ∨ q x = 1 ∨ q x = 2 := by omega
    rcases hc with h | h | h | h | h <;> norm_num [c, d, h]
  have hcd : ∀ x, (3 : ℤ) ∣ intA c x := by
    intro x
    obtain ⟨k, hk⟩ := hd x
    have heq := congrFun (congrArg intA hdecomp) x
    rw [intA_add_local, intA_mul] at heq
    change intA q x = intA c x + 3 * intA d x at heq
    refine ⟨k - intA d x, ?_⟩
    omega
  rcases HuangMinimalResidual.classify_nine_residual c hcn hcd with hc | hc
  · obtain ⟨y, s, hs, heq⟩ := hc
    have hy := congrFun heq y
    simp at hy
    rcases hcunit y with h | h | h <;> rw [h] at hy <;> nlinarith
  · obtain ⟨y, s, hs, heq⟩ := hc
    have hcz : c z ≠ 0 := by
      rcases (hheavy z).2 (Or.inl rfl) with h | h <;> simp [c, h]
    have hcw : c w ≠ 0 := by
      rcases (hheavy w).2 (Or.inr rfl) with h | h <;> simp [c, h]
    have hadj (x : Q9) (hx : c x ≠ 0) : (hypercube 9).Adj y x := by
      by_contra h
      have hz := intCoeff_zero_of_not_adj x y (fun ha => h ha.symm)
      apply hx
      rw [heq]
      simp [hz]
    refine ⟨y, z, w, s, hs, hadj z hcz, hadj w hcw, hzw, ?_⟩
    have hhc (x : Q9) (hx : q x = 2 ∨ q x = -2) : q x = -2 * c x := by
      rcases hx with h | h <;> norm_num [c, h]
    have hz := hhc z ((hheavy z).2 (Or.inl rfl))
    have hw := hhc w ((hheavy w).2 (Or.inr rfl))
    funext x
    have hloc : q x = c x - 3 * c z * delta z x - 3 * c w * delta w x := by
      by_cases hxz : x = z
      · subst x
        simp only [delta, ite_true, ite_false, hzw, mul_one, mul_zero, sub_zero]
        linarith
      · by_cases hxw : x = w
        · subst x
          simp only [delta, ite_true, ite_false, Ne.symm hzw, mul_one, mul_zero,
            sub_zero]
          linarith
        · have hx : ¬ (q x = 2 ∨ q x = -2) := by rw [hheavy]; simp [hxz, hxw]
          obtain ⟨h2, hn2⟩ := not_or.mp hx
          simp [c, delta, hxz, hxw, h2, hn2]
    simpa only [heq, mul_assoc] using hloc

open Classical in
private theorem eigen_eq_of_half (r t : Q9 → ℤ) (b : Bool)
    (hr : intA r = fun x => -3 * r x)
    (ht : intA t = fun x => -3 * t x)
    (hh : (fun x => if cubeParity x = b then r x else 0) =
      (fun x => if cubeParity x = b then t x else 0)) : r = t := by
  obtain ⟨hre, hro⟩ := parts_eigen r hr
  obtain ⟨hte, hto⟩ := parts_eigen t ht
  have he : evenPart r = evenPart t := by
    cases b
    · exact hh
    · have hodd : oddPart r = oddPart t := hh
      have ha := congrArg intA hodd
      rw [hro, hto] at ha
      funext x
      have hx := congrFun ha x
      change -3 * evenPart r x = -3 * evenPart t x at hx
      omega
  have ho : oddPart r = oddPart t := by
    have ha := congrArg intA he
    rw [hre, hte] at ha
    funext x
    have hx := congrFun ha x
    change -3 * oddPart r x = -3 * oddPart t x at hx
    omega
  calc
    r = evenPart r + oddPart r := (parts_add r).symm
    _ = evenPart t + oddPart t := by rw [he, ho]
    _ = t := parts_add t

open Classical in
/-- An energy-five residual is unit-valued on thirty vertices, or is the
Laplacian of a coherently signed three-vertex path. -/
theorem classify_energy_five_residual (f : Q9 → ℤ)
    (he : HuangIntegralNormGap.energy f = 5) :
    ((∀ x, lap f x = 0 ∨ lap f x = 1 ∨ lap f x = -1) ∧
      (Finset.univ.filter (fun x => lap f x ≠ 0)).card = 30) ∨
    (∃ y z w : Q9, ∃ s : ℤ, s ^ 2 = 1 ∧
      (hypercube 9).Adj y z ∧ (hypercube 9).Adj y w ∧ z ≠ w ∧
      lap f = lap (fun x => s * delta y x +
        s * intCoeff y z * delta z x + s * intCoeff y w * delta w x)) := by
  by_cases hu : ∀ x, lap f x = 0 ∨ lap f x = 1 ∨ lap f x = -1
  · exact Or.inl ⟨hu, energy_five_unit_support f he hu⟩
  obtain ⟨hb, hn, hne, hno⟩ := energy_five_residual_invariants f he
  push Not at hu
  obtain ⟨a, ha0, ha1, han1⟩ := hu
  have ha : lap f a = 2 ∨ lap f a = -2 := by have := hb a; omega
  let b := cubeParity a
  let q : Q9 → ℤ := fun x => if cubeParity x = b then lap f x else 0
  have hqb : ∀ x, -2 ≤ q x ∧ q x ≤ 2 := by
    intro x
    by_cases hx : cubeParity x = b
    · simpa [q, hx] using hb x
    · simp [q, hx]
  have hqn : (∑ x, q x ^ 2) = 15 := by
    cases hx : b
    · simpa [q, hx, evenPart] using hne
    · simpa [q, hx, oddPart] using hno
  obtain ⟨hre, hro⟩ := parts_eigen (lap f) (lap_negative_eigen f)
  have hqd : ∀ x, (3 : ℤ) ∣ intA q x := by
    intro x
    cases hx : b
    · have hq : q = evenPart (lap f) := by funext v; simp [q, hx, evenPart]
      rw [hq, hre]
      exact ⟨-oddPart (lap f) x, by ring⟩
    · have hq : q = oddPart (lap f) := by funext v; simp [q, hx, oddPart]
      rw [hq, hro]
      exact ⟨-evenPart (lap f) x, by ring⟩
  have hqp : ∀ x, q x ≠ 0 → cubeParity x = b := by
    intro x hx
    by_contra hp
    exact hx (by simp [q, hp])
  have hqh : ∃ x, q x = 2 ∨ q x = -2 := by
    refine ⟨a, ?_⟩
    simpa [q, b] using ha
  obtain ⟨y, z, w, s, hs, hyz, hyw, hzw, hshape⟩ :=
    heavy_half_shape q b hqb hqn hqd hqp hqh
  have hsn : s ≠ 0 := by intro h; simp [h] at hs
  have hcoeffz : intCoeff z y = 1 ∨ intCoeff z y = -1 :=
    intCoeff_sign_of_adj z y hyz.symm
  have hcoeffw : intCoeff w y = 1 ∨ intCoeff w y = -1 :=
    intCoeff_sign_of_adj w y hyw.symm
  have hqz : q z ≠ 0 := by
    have hz := congrFun hshape z
    simp only [delta, ite_true, ite_false, hzw, mul_one, mul_zero, sub_zero] at hz
    rcases hcoeffz with hc | hc <;> rw [hc] at hz <;> intro h <;> rw [h] at hz <;>
      apply hsn <;> omega
  have hqw : q w ≠ 0 := by
    have hw := congrFun hshape w
    simp only [delta, ite_true, ite_false, Ne.symm hzw, mul_one, mul_zero,
      sub_zero] at hw
    rcases hcoeffw with hc | hc <;> rw [hc] at hw <;> intro h <;> rw [h] at hw <;>
      apply hsn <;> omega
  have hzp := hqp z hqz
  have hwp := hqp w hqw
  have hyp : cubeParity y ≠ b := by
    intro h
    exact cubeParity_ne_of_adj hyz (h.trans hzp.symm)
  let g : Q9 → ℤ := fun x => (-s) * delta y x +
    (-s) * intCoeff y z * delta z x + (-s) * intCoeff y w * delta w x
  have hhalf : q = (fun x => if cubeParity x = b then lap g x else 0) := by
    funext x
    by_cases hx : cubeParity x = b
    · have hxy : x ≠ y := by intro h; subst x; exact hyp hx
      have hxz : intCoeff x z = 0 :=
        intCoeff_zero_of_same_parity x z (hx.trans hzp.symm)
      have hxw : intCoeff x w = 0 :=
        intCoeff_zero_of_same_parity x w (hx.trans hwp.symm)
      have hg : intA g x = (-s) * intCoeff x y +
          ((-s) * intCoeff y z) * intCoeff x z +
          ((-s) * intCoeff y w) * intCoeff x w := by
        change intA (((fun v => (-s) * delta y v) +
          (fun v => ((-s) * intCoeff y z) * delta z v)) +
          (fun v => ((-s) * intCoeff y w) * delta w v)) x = _
        simp only [intA_add_local, intA_mul, intA_delta, Pi.add_apply]
      rw [ite_eq_left hx]
      have hsh := congrFun hshape x
      rw [coeff_symm z y, coeff_symm w y] at hsh
      rw [hsh]
      change _ = 3 * g x - intA g x
      rw [hg, hxz, hxw]
      simp only [g, delta, ite_eq_right hxy]
      ring
    · simp [q, hx]
  refine Or.inr ⟨y, z, w, -s, by nlinarith, hyz, hyw, hzw, ?_⟩
  exact eigen_eq_of_half (lap f) (lap g) b (lap_negative_eigen f)
    (lap_negative_eigen g) hhalf

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangEnergyFiveResidual
