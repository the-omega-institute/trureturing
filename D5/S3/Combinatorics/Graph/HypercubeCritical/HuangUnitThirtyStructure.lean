/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Support degrees and the nonempty opposite-edge matching at unit norm thirty. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitNormThirty
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangEnergyFiveResidual
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import Batteries.Tactic.OpenPrivate

/-! Unit support thirty forces actual degrees three or five and an opposite edge. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyStructure

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open HuangIntegralNormGap (Q9)
open private intA intCoeff intA_sub intA_mul intA_square intCoeff_zero_of_not_adj
  intCoeff_sign_of_adj intCoeff_zero_of_same_parity intCoeff_cast evenPart oddPart from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private cubeParity cubeParity_ne_of_adj huangMatrix from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private parts_eigen unit_norm_eq_card no_singleton_row even_diff_of_parity_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
open private parity_norms from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangEnergyFiveResidual
open private delta intA_delta from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut
open private coeff_symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut
open private diff diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

open Classical in
private theorem neighbor_card_nine (y : Q9) :
    (Finset.univ.filter (fun x : Q9 => (hypercube 9).Adj y x)).card = 9 := by
  classical
  rw [← (hypercube 9).neighborFinset_eq_filter]
  exact (hypercube_regular 9).degree_eq y

open Classical in
private theorem indicator_card (P : Q9 → Prop) [DecidablePred P] :
    (∑ x, if P x then (1 : ℤ) else 0) =
      ((Finset.univ.filter P).card : ℤ) := by
  classical
  rw [← Finset.sum_filter]
  simp

open Classical in
private theorem common_neighbors_le_two (y z : Q9) (hyz : y ≠ z) :
    ((Finset.univ.filter (fun x : Q9 => (hypercube 9).Adj z x)).filter
      (fun x => (hypercube 9).Adj y x)).card ≤ 2 := by
  classical
  let C := (Finset.univ.filter (fun x : Q9 => (hypercube 9).Adj z x)).filter
    (fun x => (hypercube 9).Adj y x)
  by_cases hn : C.Nonempty
  · obtain ⟨w, hw⟩ := hn
    have hwy := (Finset.mem_filter.mp hw).2
    have hwz := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
    obtain ⟨i, hi⟩ := adjacent_exists_flip hwy
    have hd := diff_of_adj_flip (x := y) (z := z) hyz i (by
      rw [← hi]
      exact hwz.symm)
    have hsub : C ⊆ (diff y z).image (fun j => BalancedCriticalSpectrum.flip y j) := by
      intro u hu
      have huy := (Finset.mem_filter.mp hu).2
      have huz := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
      obtain ⟨j, hj⟩ := adjacent_exists_flip huy
      have hjd := diff_of_adj_flip (x := y) (z := z) hyz j (by
        rw [← hj]
        exact huz.symm)
      exact Finset.mem_image.mpr ⟨j, hjd.1, hj.symm⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq hd.2))
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change C.card ≤ 2
    simp [he]

private def centered (v : ℤ) : ℤ := if v = 2 then -1 else if v = -2 then 1 else v
private def correction (v : ℤ) : ℤ := if v = 2 then 1 else if v = -2 then -1 else 0

open Classical in
private theorem centered_eq (v : ℤ) : centered v = v - 3 * correction v := by
  unfold centered correction
  split_ifs <;> omega

open Classical in
private theorem selected_row (q : Q9 → ℤ) (b : Bool) (y : Q9) (eps : ℤ)
    (hu : ∀ x, q x = 0 ∨ q x = 1 ∨ q x = -1)
    (hp : ∀ x, q x ≠ 0 → cubeParity x = b)
    (hn : (∑ x, q x ^ 2) = 15)
    (hdiv : ∀ x, (3 : ℤ) ∣ intA q x)
    (hy : cubeParity y ≠ b) (heps : eps ^ 2 = 1)
    (hrow : intA q y = 3 * eps) :
    ((Finset.univ.filter (fun x => q x ≠ 0)).filter
      (fun x => (hypercube 9).Adj y x)).card = 3 ∨
    ((Finset.univ.filter (fun x => q x ≠ 0)).filter
      (fun x => (hypercube 9).Adj y x)).card = 5 := by
  classical
  have he : eps = 1 ∨ eps = -1 := by
    have : (eps - 1) * (eps + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  let t : Q9 → ℤ := fun x => eps * intCoeff x y
  let u : Q9 → ℤ := q - t
  let c : Q9 → ℤ := fun x => centered (u x)
  let d : Q9 → ℤ := fun x => correction (u x)
  let S := Finset.univ.filter (fun x => q x ≠ 0)
  let C := Finset.univ.filter (fun x => c x ≠ 0)
  let K := S.filter (fun x => (hypercube 9).Adj y x)
  let D := C.filter (fun x => (hypercube 9).Adj y x)
  have hcases (x : Q9) :
      (¬ (hypercube 9).Adj y x ∧ intCoeff x y = 0) ∨
      ((hypercube 9).Adj y x ∧ (intCoeff x y = 1 ∨ intCoeff x y = -1)) := by
    by_cases ha : (hypercube 9).Adj y x
    · exact Or.inr ⟨ha, intCoeff_sign_of_adj x y ha.symm⟩
    · exact Or.inl ⟨ha, intCoeff_zero_of_not_adj x y (fun h => ha h.symm)⟩
  have hcu : ∀ x, c x = 0 ∨ c x = 1 ∨ c x = -1 := by
    intro x
    rcases hcases x with ⟨ha, hc⟩ | ⟨ha, hc | hc⟩ <;>
      rcases hu x with hq | hq | hq <;> rcases he with he | he <;>
      norm_num [c, u, t, centered, hc, hq, he]
  have hcp : ∀ x ∈ C, cubeParity x = b := by
    intro x hx
    by_contra hxb
    have hq : q x = 0 := by
      by_contra hq
      exact hxb (hp x hq)
    have hxy : cubeParity x = cubeParity y := by
      cases hx' : cubeParity x <;> cases hy' : cubeParity y <;>
        cases hb : b <;> simp_all
    have hc : intCoeff x y = 0 := intCoeff_zero_of_same_parity x y hxy
    have hxne := (Finset.mem_filter.mp hx).2
    exact hxne (by simp [c, u, t, centered, hq, hc])
  have ht : intA t = fun x => 9 * eps * delta y x := by
    have heq : t = fun x => eps * intA (delta y) x := by
      rw [intA_delta]
    rw [heq, intA_mul, intA_square]
    funext x
    ring
  have hceq : c = u - fun x => 3 * d x := by
    funext x
    exact centered_eq (u x)
  have hcdiv : ∀ x, (3 : ℤ) ∣ intA c x := by
    intro x
    rw [hceq, intA_sub, intA_mul]
    change (3 : ℤ) ∣ intA u x - 3 * intA d x
    have hut : intA u x = intA q x - 9 * eps * delta y x := by
      change intA (q - t) x = _
      rw [intA_sub, ht]
      rfl
    rw [hut]
    exact dvd_sub (dvd_sub (hdiv x) (by use 3 * eps * delta y x; ring)) (dvd_mul_right _ _)
  have hlocal (x : Q9) :
      2 * c x ^ 2 + 3 * (if q x ≠ 0 ∧ (hypercube 9).Adj y x then (1 : ℤ) else 0) +
        eps * intCoeff x y * q x = 2 * q x ^ 2 + 2 * intCoeff x y ^ 2 := by
    rcases hcases x with ⟨ha, hc⟩ | ⟨ha, hc | hc⟩ <;>
      rcases hu x with hq | hq | hq <;> rcases he with he | he <;>
      norm_num [c, u, t, centered, ha, hc, hq, he]
  have hlocalD (x : Q9) :
      2 * (if c x ≠ 0 ∧ (hypercube 9).Adj y x then (1 : ℤ) else 0) +
        (if q x ≠ 0 ∧ (hypercube 9).Adj y x then (1 : ℤ) else 0) +
        eps * intCoeff x y * q x =
        2 * (if (hypercube 9).Adj y x then (1 : ℤ) else 0) := by
    rcases hcases x with ⟨ha, hc⟩ | ⟨ha, hc | hc⟩ <;>
      rcases hu x with hq | hq | hq <;> rcases he with he | he <;>
      norm_num [c, u, t, centered, ha, hc, hq, he]
  have hK : (∑ x, if q x ≠ 0 ∧ (hypercube 9).Adj y x then (1 : ℤ) else 0) =
      (K.card : ℤ) := by
    simpa only [K, S, Finset.filter_filter] using
      indicator_card (fun x => q x ≠ 0 ∧ (hypercube 9).Adj y x)
  have hD : (∑ x, if c x ≠ 0 ∧ (hypercube 9).Adj y x then (1 : ℤ) else 0) =
      (D.card : ℤ) := by
    simpa only [D, C, Finset.filter_filter] using
      indicator_card (fun x => c x ≠ 0 ∧ (hypercube 9).Adj y x)
  have hN : (∑ x : Q9, if (hypercube 9).Adj y x then (1 : ℤ) else 0) = 9 := by
    rw [indicator_card, neighbor_card_nine]
    norm_num
  have ha2 : (∑ x, intCoeff x y ^ 2) = (9 : ℤ) := by
    calc
      _ = ∑ x : Q9, if (hypercube 9).Adj y x then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hcases x with ⟨ha, hc⟩ | ⟨ha, hc | hc⟩ <;> simp [ha, hc]
      _ = 9 := hN
  have hsum : (∑ x, eps * intCoeff x y * q x) = 3 := by
    calc
      _ = eps * intA q y := by
        simp only [intA, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [coeff_symm x y]
        ring
      _ = 3 := by rw [hrow]; nlinarith
  have hcount : 2 * (C.card : ℤ) + 3 * (K.card : ℤ) = 45 := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hlocal x)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    rw [hK, hsum, ha2, hn, unit_norm_eq_card c hcu] at hh
    linarith
  have hdcount : 2 * (D.card : ℤ) + (K.card : ℤ) = 15 := by
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hlocalD x)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    rw [hD, hK, hsum, hN] at hh
    linarith
  have hklo : (3 : ℤ) ≤ K.card := by
    have hl : ∀ x, eps * intCoeff x y * q x ≤
        (if q x ≠ 0 ∧ (hypercube 9).Adj y x then (1 : ℤ) else 0) := by
      intro x
      rcases hcases x with ⟨ha, hc⟩ | ⟨ha, hc | hc⟩ <;>
        rcases hu x with hq | hq | hq <;> rcases he with he | he <;>
        norm_num [ha, hc, hq, he]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hl x)
    rwa [hsum, hK] at hh
  have hkhi : K.card ≤ 9 := by
    calc
      K.card ≤ (Finset.univ.filter (fun x : Q9 => (hypercube 9).Adj y x)).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      _ = 9 := neighbor_card_nine y
  have hnotlarge : ¬ 7 ≤ K.card := by
    intro hk7
    have hcsmall : C.card ≤ 12 := by omega
    have hcpos : 0 < C.card := by omega
    have hno := no_singleton_row c hcu hcdiv
    have heven : ∀ x ∈ C, ∀ z ∈ C,
        Even (Finset.univ.filter (fun i : Fin 9 => x i ≠ z i)).card := by
      intro x hx z hz
      exact even_diff_of_parity_eq x z ((hcp x hx).trans (hcp z hz).symm)
    obtain ⟨z, hz⟩ := CubeTwelveSupport.eq_neighbors_of_card_le_twelve
      C (Finset.card_pos.mp hcpos) hcsmall hno heven
    have hc9 : C.card = 9 := by rw [hz, neighbor_card_nine]
    have hk9 : K.card = 9 := by omega
    have hd3 : D.card = 3 := by omega
    by_cases hyz : y = z
    · have hd9 : D.card = 9 := by
        simp only [D, hz, ← hyz, Finset.filter_filter, and_self]
        exact neighbor_card_nine y
      omega
    · have hd2 : D.card ≤ 2 := by
        simpa only [D, hz] using common_neighbors_le_two y z hyz
      omega
  change K.card = 3 ∨ K.card = 5
  omega

open Classical in
private theorem support_degrees (r : Q9 → ℤ)
    (heig : intA r = fun x => -3 * r x)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (hcard : (Finset.univ.filter (fun x => r x ≠ 0)).card = 30) :
    ∀ y ∈ Finset.univ.filter (fun x => r x ≠ 0),
      ((Finset.univ.filter (fun x => r x ≠ 0)).filter
        (fun x => (hypercube 9).Adj y x)).card = 3 ∨
      ((Finset.univ.filter (fun x => r x ≠ 0)).filter
        (fun x => (hypercube 9).Adj y x)).card = 5 := by
  classical
  have hn : (∑ x, r x ^ 2) = 30 := by rw [unit_norm_eq_card r hu, hcard]; norm_num
  obtain ⟨hne, hno⟩ := parity_norms r heig hn
  obtain ⟨he, ho⟩ := parts_eigen r heig
  intro y hy
  have hyr : r y ≠ 0 := (Finset.mem_filter.mp hy).2
  have hyunit : r y = 1 ∨ r y = -1 := (hu y).resolve_left hyr
  have heps : (-r y) ^ 2 = 1 := by rcases hyunit with h | h <;> simp [h]
  have hqu (b : Bool) : ∀ x, (if cubeParity x = b then r x else 0) = 0 ∨
      (if cubeParity x = b then r x else 0) = 1 ∨
      (if cubeParity x = b then r x else 0) = -1 := by
    intro x
    by_cases hx : cubeParity x = b
    · simpa only [ite_eq_left hx] using hu x
    · simp [hx]
  have hqp (b : Bool) : ∀ x,
      (if cubeParity x = b then r x else 0) ≠ 0 → cubeParity x = b := by
    intro x hx
    by_contra hp
    simp [hp] at hx
  cases hpy : cubeParity y
  · have hrow : intA (oddPart r) y = 3 * (-r y) := by
      calc
        intA (oddPart r) y = -3 * r y := by
          simpa [evenPart, hpy] using congrFun ho y
        _ = 3 * (-r y) := by ring
    have hdiv : ∀ x, (3 : ℤ) ∣ intA (oddPart r) x := by
      intro x
      rw [congrFun ho x]
      exact ⟨-evenPart r x, by ring⟩
    have hh := selected_row (oddPart r) true y (-r y) (hqu true) (hqp true)
      hno hdiv (by simp [hpy]) heps hrow
    have hf : ((Finset.univ.filter (fun x => oddPart r x ≠ 0)).filter
        (fun x => (hypercube 9).Adj y x)) =
        ((Finset.univ.filter (fun x => r x ≠ 0)).filter
        (fun x => (hypercube 9).Adj y x)) := by
      ext x
      by_cases ha : (hypercube 9).Adj y x
      · have hp : cubeParity x = true := by
          have hn := cubeParity_ne_of_adj ha
          cases hx : cubeParity x <;> simp_all
        simp [oddPart, hp, ha]
      · simp [ha]
    rwa [hf] at hh
  · have hrow : intA (evenPart r) y = 3 * (-r y) := by
      calc
        intA (evenPart r) y = -3 * r y := by
          simpa [oddPart, hpy] using congrFun he y
        _ = 3 * (-r y) := by ring
    have hdiv : ∀ x, (3 : ℤ) ∣ intA (evenPart r) x := by
      intro x
      rw [congrFun he x]
      exact ⟨-oddPart r x, by ring⟩
    have hh := selected_row (evenPart r) false y (-r y) (hqu false) (hqp false)
      hne hdiv (by simp [hpy]) heps hrow
    have hf : ((Finset.univ.filter (fun x => evenPart r x ≠ 0)).filter
        (fun x => (hypercube 9).Adj y x)) =
        ((Finset.univ.filter (fun x => r x ≠ 0)).filter
        (fun x => (hypercube 9).Adj y x)) := by
      ext x
      by_cases ha : (hypercube 9).Adj y x
      · have hp : cubeParity x = false := by
          have hn := cubeParity_ne_of_adj ha
          cases hx : cubeParity x <;> simp_all
        simp [evenPart, hp, ha]
      · simp [ha]
    rwa [hf] at hh

open Classical in
private theorem opposite_count (r : Q9 → ℤ)
    (heig : intA r = fun x => -3 * r x)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (x : Q9) (hx : r x ≠ 0) :
    2 * ((((Finset.univ.filter (fun y => r y ≠ 0)).filter
      (fun y => (hypercube 9).Adj x y ∧ intCoeff x y * r x * r y = 1)).card : ℕ) : ℤ) + 3 =
      (((Finset.univ.filter (fun y => r y ≠ 0)).filter
        (fun y => (hypercube 9).Adj x y)).card : ℤ) := by
  classical
  have hxu : r x = 1 ∨ r x = -1 := (hu x).resolve_left hx
  have hlocal (y : Q9) :
      intCoeff x y * r x * r y =
        2 * (if r y ≠ 0 ∧ ((hypercube 9).Adj x y ∧ intCoeff x y * r x * r y = 1)
          then (1 : ℤ) else 0) -
        (if r y ≠ 0 ∧ (hypercube 9).Adj x y then (1 : ℤ) else 0) := by
    by_cases ha : (hypercube 9).Adj x y
    · rcases intCoeff_sign_of_adj x y ha with hc | hc <;>
        rcases hxu with hxx | hxx <;> rcases hu y with hyy | hyy | hyy <;>
        norm_num [ha, hc, hxx, hyy]
    · simp [ha, intCoeff_zero_of_not_adj x y ha]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => hlocal y)
  have he : (∑ y, intCoeff x y * r x * r y) = -3 := by
    calc
      _ = r x * intA r x := by
        simp only [intA, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = -3 := by
        rw [congrFun heig x]
        rcases hxu with h | h <;> simp [h]
  rw [he] at hs
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hO : (∑ y, if r y ≠ 0 ∧ ((hypercube 9).Adj x y ∧ intCoeff x y * r x * r y = 1)
      then (1 : ℤ) else 0) =
      (((Finset.univ.filter (fun y => r y ≠ 0)).filter
        (fun y => (hypercube 9).Adj x y ∧ intCoeff x y * r x * r y = 1)).card : ℤ) := by
    simpa only [Finset.filter_filter] using indicator_card
      (fun y => r y ≠ 0 ∧ ((hypercube 9).Adj x y ∧ intCoeff x y * r x * r y = 1))
  have hK : (∑ y, if r y ≠ 0 ∧ (hypercube 9).Adj x y then (1 : ℤ) else 0) =
      (((Finset.univ.filter (fun y => r y ≠ 0)).filter
        (fun y => (hypercube 9).Adj x y)).card : ℤ) := by
    simpa only [Finset.filter_filter] using indicator_card
      (fun y => r y ≠ 0 ∧ (hypercube 9).Adj x y)
  rw [hO, hK] at hs
  linarith

open Classical in
private theorem regular_of_neighbor_card (S : Finset Q9)
    (h : ∀ x ∈ S, (S.filter (fun y => (hypercube 9).Adj x y)).card = 3) :
    ((hypercube 9).induce (S : Set Q9)).IsRegularOfDegree 3 := by
  classical
  let G := (hypercube 9).induce (S : Set Q9)
  intro x
  have hi : (G.neighborFinset x).image Subtype.val =
      S.filter (fun y => (hypercube 9).Adj x.val y) := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_filter.mpr ⟨w.property, (G.mem_neighborFinset x w).mp hw⟩
    · intro hy
      obtain ⟨hyS, hxy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_image.mpr ⟨⟨y, hyS⟩, (G.mem_neighborFinset x ⟨y, hyS⟩).mpr hxy, rfl⟩
  have hc := h x.val x.property
  rw [← hi, Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

open Classical in
private theorem balanced_of_no_opposite (r : Q9 → ℤ)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (hno : ∀ x ∈ Finset.univ.filter (fun x => r x ≠ 0),
      ∀ y ∈ Finset.univ.filter (fun x => r x ≠ 0),
        (hypercube 9).Adj x y → intCoeff x y * r x * r y ≠ 1) :
    BalancedCriticalSpectrum.IsBalanced (Finset.univ.filter (fun x => r x ≠ 0)) := by
  classical
  let sigma : Q9 → ℝ := fun x => (if cubeParity x then -1 else 1) * (r x : ℝ)
  refine ⟨sigma, ?_, ?_⟩
  · intro x hx
    have hxu := (hu x).resolve_left (Finset.mem_filter.mp hx).2
    rcases hxu with h | h <;> cases hp : cubeParity x <;> simp [sigma, hp, h]
  · intro x hx y hy ha
    have hxu := (hu x).resolve_left (Finset.mem_filter.mp hx).2
    have hyu := (hu y).resolve_left (Finset.mem_filter.mp hy).2
    have hn := hno x hx y hy ha
    have hp := cubeParity_ne_of_adj ha
    have hc := intCoeff_sign_of_adj x y ha
    rw [← intCoeff_cast]
    rcases hc with hc | hc <;> rcases hxu with hxx | hxx <;>
      rcases hyu with hyy | hyy <;> cases hpx : cubeParity x <;>
      cases hpy : cubeParity y <;> norm_num [hc, hxx, hyy] at hn
    all_goals norm_num [hpx, hpy] at hp
    all_goals norm_num [sigma, hpx, hpy, hc, hxx, hyy]

open Classical in
/-- At support thirty the actual degrees are three or five, and the opposite
edges of the original FALSE-prefix Huang operator form a nonempty matching. -/
theorem structure_of_unit_negative_three_support_thirty (r : Q9 → ℤ)
    (heig : intA r = fun x => -3 * r x)
    (hu : ∀ x, r x = 0 ∨ r x = 1 ∨ r x = -1)
    (hcard : (Finset.univ.filter (fun x => r x ≠ 0)).card = 30) :
    let S := Finset.univ.filter (fun x => r x ≠ 0)
    (∀ x ∈ S, (S.filter (fun y => (hypercube 9).Adj x y)).card = 3 ∨
      (S.filter (fun y => (hypercube 9).Adj x y)).card = 5) ∧
    (∀ x ∈ S, (S.filter (fun y => (hypercube 9).Adj x y ∧
      intCoeff x y * r x * r y = 1)).card ≤ 1) ∧
    (∃ x ∈ S, ∃ y ∈ S, (hypercube 9).Adj x y ∧ intCoeff x y * r x * r y = 1) := by
  classical
  let S := Finset.univ.filter (fun x => r x ≠ 0)
  have hdeg := support_degrees r heig hu hcard
  refine ⟨hdeg, ?_, ?_⟩
  · intro x hx
    have hid := opposite_count r heig hu x (Finset.mem_filter.mp hx).2
    have hd := hdeg x hx
    rcases hd with hd | hd <;> rw [hd] at hid <;> omega
  · by_contra hn
    have hno : ∀ x ∈ S, ∀ y ∈ S, (hypercube 9).Adj x y →
        intCoeff x y * r x * r y ≠ 1 := by
      intro x hx y hy ha hs
      exact hn ⟨x, hx, y, hy, ha, hs⟩
    have hreg : ((hypercube 9).induce (S : Set Q9)).IsRegularOfDegree 3 := by
      apply regular_of_neighbor_card
      intro x hx
      have hz : S.filter (fun y => (hypercube 9).Adj x y ∧
          intCoeff x y * r x * r y = 1) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨hyS, ha, hs⟩ := Finset.mem_filter.mp hy
        exact hno x hx y hyS ha hs
      have hid := opposite_count r heig hu x (Finset.mem_filter.mp hx).2
      change 2 * ((S.filter (fun y => (hypercube 9).Adj x y ∧
        intCoeff x y * r x * r y = 1)).card : ℤ) + 3 =
        ((S.filter (fun y => (hypercube 9).Adj x y)).card : ℤ) at hid
      rw [hz] at hid
      exact_mod_cast (by simpa using hid.symm :
        ((S.filter (fun y => (hypercube 9).Adj x y)).card : ℤ) = 3)
    have hbal : BalancedCriticalSpectrum.IsBalanced S := balanced_of_no_opposite r hu hno
    have hne : S.Nonempty := Finset.card_pos.mp (by change 0 < (Finset.univ.filter _).card; omega)
    have hl := BalancedCubeLowerBound.forty_eight_le_card S hne hreg hbal
    change 48 ≤ (Finset.univ.filter (fun x => r x ≠ 0)).card at hl
    omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyStructure
