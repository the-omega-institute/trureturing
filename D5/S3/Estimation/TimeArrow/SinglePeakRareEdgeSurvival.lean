/- GID: D5/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SinglePeakRareEdgeSurvival
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Avoiding the rare opposite-to-peak edge gives an exact cubic survival recurrence. -/

import D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeSurvival
open Finset
open SinglePeakPathCurrent
private noncomputable def avoids {X : Type*} (chi : X -> Real) (z : X)
    (T : Nat) (x : Fin (T + 1) -> X) : Prop :=
  ∀ t : Fin T, ¬(region chi z (x t.castSucc) = Region.opposite ∧
    region chi z (x t.succ) = Region.peak)
private noncomputable def pathMass {X : Type*} [Fintype X]
    (chi : X -> Real) (z : X) (r q : Real) (T : Nat) (x : Fin (T + 1) -> X) : Real := by
  classical
  exact (1 / (Fintype.card X : Real)) *
      (∏ t : Fin T, kernel chi z r q (Fintype.card X) (x t.castSucc) (x t.succ)) *
      (if avoids chi z T x then 1 else 0)
/-- The uniform-start mass of paths of length `T` that have not traversed an
opposite-to-peak edge. -/
noncomputable def survival {X : Type*} [Fintype X]
    (chi : X -> Real) (z : X) (r q : Real) (T : Nat) : Real := by
  classical
  exact ∑ x : Fin (T + 1) -> X,
    (1 / (Fintype.card X : Real)) *
      (∏ t : Fin T, kernel chi z r q (Fintype.card X) (x t.castSucc) (x t.succ)) *
      (if avoids chi z T x then 1 else 0)
private noncomputable def endpointMass {X : Type*} [Fintype X]
    (chi : X -> Real) (z : X) (r q : Real) (T : Nat) (U : Region) : Real :=
  ∑ x : Fin (T + 1) -> X,
    pathMass chi z r q T x * if region chi z (x (Fin.last T)) = U then 1 else 0
private def regionSign : Region -> Real
  | Region.peak => 1
  | Region.bulk => 1
  | Region.opposite => -1
private def regionProfile (r q : Real) : Region -> Real
  | Region.peak => r
  | Region.bulk => -q
  | Region.opposite => 0
private def regionCount (M : Nat) : Region -> Real
  | Region.peak => 1
  | Region.bulk => (M : Real) - 1
  | Region.opposite => M
private noncomputable def killedKernel (N M : Nat) (r q : Real) (U V : Region) : Real :=
  if U = Region.opposite ∧ V = Region.peak then 0
  else regionCount M V * (1 + regionSign U * regionSign V * regionProfile r q U) / N
private noncomputable def killedStep (N M : Nat) (r q : Real)
    (f : Region -> Real) : Region -> Real
  | Region.peak =>
      f Region.peak * killedKernel N M r q Region.peak Region.peak +
        f Region.bulk * killedKernel N M r q Region.bulk Region.peak +
        f Region.opposite * killedKernel N M r q Region.opposite Region.peak
  | Region.bulk =>
      f Region.peak * killedKernel N M r q Region.peak Region.bulk +
        f Region.bulk * killedKernel N M r q Region.bulk Region.bulk +
        f Region.opposite * killedKernel N M r q Region.opposite Region.bulk
  | Region.opposite =>
      f Region.peak * killedKernel N M r q Region.peak Region.opposite +
        f Region.bulk * killedKernel N M r q Region.bulk Region.opposite +
        f Region.opposite * killedKernel N M r q Region.opposite Region.opposite
private noncomputable def transitionMass {X : Type*} [Fintype X]
    (chi : X -> Real) (z : X) (r q : Real) (x : X) (V : Region) : Real :=
  ∑ y : X,
    if ¬(region chi z x = Region.opposite ∧ region chi z y = Region.peak) ∧
        region chi z y = V then
      kernel chi z r q (Fintype.card X) x y
    else 0
/-- **Exact survival recurrence for the rare opposite-to-peak edge.** Under balanced signs and the
single-peak profile, the explicit avoiding-path mass has initial values `1`, `1-p`, `1-2p` and
satisfies the cubic recurrence with `p = 1/(2|X|)` and `epsilon = 1-r`. -/
theorem survival_recurrence {X : Type*} [Fintype X]
    (chi : X -> Real) (hchi : ∀ x, chi x = 1 ∨ chi x = -1)
    (z : X) (hz : chi z = 1) (r q : Real) (M : Nat)
    (hcard : Fintype.card X = 2 * M)
    (hplus : ((univ.filter fun x => chi x = 1).card) = M)
    (hM : 2 <= M) (hq : q = r / ((M : Real) - 1)) :
    survival chi z r q 0 = 1 ∧
      survival chi z r q 1 = 1 - 1 / (2 * (Fintype.card X : Real)) ∧
      survival chi z r q 2 = 1 - 2 * (1 / (2 * (Fintype.card X : Real))) ∧
      ∀ T : Nat, survival chi z r q (T + 3) = survival chi z r q (T + 2) -
        (1 / (2 * (Fintype.card X : Real))) * (1 - r) * survival chi z r q (T + 1) -
        (1 / (2 * (Fintype.card X : Real))) * r * survival chi z r q T := by
  have sign_eq_regionSign : ∀ (chi : X -> Real) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z x : X) (hz : chi z = 1), chi x = regionSign (region chi z x) := by
    intro chi hchi z x hz
    by_cases hx : x = z
    · simp [region, regionSign, hx, hz]
    · rcases hchi x with h | h
      · simp [region, regionSign, hx, h]
      · norm_num [region, regionSign, hx, h]
  have profile_eq_regionProfile : ∀ (chi : X -> Real) (z : X) (r q : Real) (x : X), profile chi z r q x = regionProfile r q (region chi z x) := by
    intro chi z r q x
    unfold profile
    rfl
  have region_card : ∀ (chi : X -> Real) (z : X) (hz : chi z = 1) (M : Nat) (hcard : Fintype.card X = 2 * M) (hplus : ((univ.filter fun x => chi x = 1).card) = M) (U : Region), (((univ.filter fun x => region chi z x = U).card : Nat) : Real) = regionCount M U := by
    intro chi z hz M hcard hplus U
    classical
    cases U with
    | peak =>
        have hset : univ.filter (fun x => region chi z x = Region.peak) = {z} := by
          ext x
          simp only [mem_filter, mem_univ, true_and, mem_singleton]
          by_cases hx : x = z
          · simp [region, hx]
          · by_cases hsign : chi x = 1 <;> simp [region, hx, hsign]
        simp [hset, regionCount]
    | bulk =>
        have hset : univ.filter (fun x => region chi z x = Region.bulk) =
            (univ.filter fun x => chi x = 1).erase z := by
          ext x
          simp only [mem_filter, mem_univ, true_and, mem_erase]
          by_cases hx : x = z
          · simp [region, hx, hz]
          · by_cases hsign : chi x = 1 <;> simp [region, hx, hsign]
        have hzmem : z ∈ (univ.filter fun x => chi x = 1) := by simp [hz]
        have hMpos : 1 <= M := by
          rw [← hplus]
          exact card_pos.mpr ⟨z, hzmem⟩
        rw [hset, card_erase_of_mem hzmem, hplus]
        rw [Nat.cast_sub hMpos]
        simp [regionCount]
    | opposite =>
        have hset : univ.filter (fun x => region chi z x = Region.opposite) =
            univ.filter (fun x => ¬chi x = 1) := by
          ext x
          simp only [mem_filter, mem_univ, true_and]
          by_cases hx : x = z
          · simp [region, hx, hz]
          · by_cases hsign : chi x = 1 <;> simp [region, hx, hsign]
        have hsplit := card_filter_add_card_filter_not (s := (univ : Finset X))
          (p := fun x => chi x = 1)
        rw [card_univ, hplus, hcard] at hsplit
        rw [hset]
        have : (univ.filter (fun x => ¬chi x = 1)).card = M := by omega
        rw [this]
        simp [regionCount]
  have sum_region_indicator : ∀ (chi : X -> Real) (z : X) (hz : chi z = 1) (M : Nat) (hcard : Fintype.card X = 2 * M) (hplus : ((univ.filter fun x => chi x = 1).card) = M) (U : Region) (c : Real), (∑ x : X, if region chi z x = U then c else 0) = regionCount M U * c := by
    intro chi z hz M hcard hplus U c
    classical
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul]
    rw [region_card chi z hz M hcard hplus U]
  have transitionMass_eq_killedKernel : ∀ (chi : X -> Real) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1) (r q : Real) (M : Nat) (hcard : Fintype.card X = 2 * M) (hplus : ((univ.filter fun x => chi x = 1).card) = M) (x : X) (V : Region), transitionMass chi z r q x V = killedKernel (Fintype.card X) M r q (region chi z x) V := by
    intro chi hchi z hz r q M hcard hplus x V
    classical
    unfold transitionMass killedKernel
    by_cases hbad : region chi z x = Region.opposite ∧ V = Region.peak
    · have hzero : ∀ y : X,
          (if ¬(region chi z x = Region.opposite ∧ region chi z y = Region.peak) ∧
              region chi z y = V then kernel chi z r q (Fintype.card X) x y else 0) = 0 := by
        intro y
        by_cases hy : region chi z y = V
        · simp [hbad.1, hbad.2, hy]
        · simp [hy]
      rw [if_pos hbad]
      exact sum_eq_zero fun y _ => hzero y
    · rw [if_neg hbad]
      have hpoint (y : X) :
          (if ¬(region chi z x = Region.opposite ∧ region chi z y = Region.peak) ∧
              region chi z y = V then kernel chi z r q (Fintype.card X) x y else 0) =
            if region chi z y = V then
              (1 + regionSign (region chi z x) * regionSign V *
                  regionProfile r q (region chi z x)) / Fintype.card X
            else 0 := by
        by_cases hy : region chi z y = V
        · have hnedge : ¬(region chi z x = Region.opposite ∧
              region chi z y = Region.peak) := by simpa [hy] using hbad
          simp only [hy, hnedge, true_and, if_true]
          rw [kernel, sign_eq_regionSign chi hchi z x hz,
            sign_eq_regionSign chi hchi z y hz, hy,
            profile_eq_regionProfile chi z r q x]
          simp [hbad]
        · simp [hy]
      simp_rw [hpoint]
      rw [sum_region_indicator chi z hz M hcard hplus V]
      ring
  have avoids_snoc : ∀ (chi : X -> Real) (z : X) (T : Nat) (x : Fin (T + 1) -> X) (y : X), avoids chi z (T + 1) (Fin.snoc x y) <-> avoids chi z T x ∧ ¬(region chi z (x (Fin.last T)) = Region.opposite ∧ region chi z y = Region.peak) := by
    intro chi z T x y
    unfold avoids
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, Fin.succ_castSucc]
  have endpointMass_succ_raw : ∀ (chi : X -> Real) (z : X) (r q : Real) (T : Nat) (V : Region), endpointMass chi z r q (T + 1) V = ∑ x : Fin (T + 1) -> X, pathMass chi z r q T x * transitionMass chi z r q (x (Fin.last T)) V := by
    intro chi z r q T V
    classical
    unfold endpointMass
    rw [← (Fin.snocEquiv (fun _ : Fin (T + 2) => X)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    unfold pathMass
    simp_rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, Fin.succ_castSucc,
      avoids_snoc]
    by_cases ha : avoids chi z T x
    · simp only [ha, true_and, if_true, transitionMass]
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      by_cases hv : region chi z y = V
      · by_cases hedge : region chi z (x (Fin.last T)) = Region.opposite ∧
            region chi z y = Region.peak
        · have hV : V = Region.peak := hv.symm.trans hedge.2
          simp [hv, hedge, hV]
        · simp [hv, hedge]
          ring_nf
      · simp [hv]
    · simp [ha]
  have sum_split_regions : ∀ (T : Nat) (rho : (Fin (T + 1) -> X) -> Region) (a : (Fin (T + 1) -> X) -> Real) (c : Region -> Real), (∑ x : Fin (T + 1) -> X, a x * c (rho x)) = (∑ x : Fin (T + 1) -> X, a x * if rho x = Region.peak then 1 else 0) * c Region.peak + (∑ x : Fin (T + 1) -> X, a x * if rho x = Region.bulk then 1 else 0) * c Region.bulk + (∑ x : Fin (T + 1) -> X, a x * if rho x = Region.opposite then 1 else 0) * c Region.opposite := by
    intro T rho a c
    classical
    rw [sum_mul, sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    cases hx : rho x <;> simp [hx]
  have endpointMass_succ : ∀ (chi : X -> Real) (hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (hz : chi z = 1) (r q : Real) (M : Nat) (hcard : Fintype.card X = 2 * M) (hplus : ((univ.filter fun x => chi x = 1).card) = M) (T : Nat), endpointMass chi z r q (T + 1) = killedStep (Fintype.card X) M r q (endpointMass chi z r q T) := by
    intro chi hchi z hz r q M hcard hplus T
    funext V
    rw [endpointMass_succ_raw]
    simp_rw [transitionMass_eq_killedKernel chi hchi z hz r q M hcard hplus]
    unfold killedStep endpointMass
    cases V <;>
      exact sum_split_regions T
        (fun x : Fin (T + 1) -> X => region chi z (x (Fin.last T)))
        (pathMass chi z r q T) (fun U => killedKernel (Fintype.card X) M r q U _)
  have survival_eq_total_endpointMass : ∀ (chi : X -> Real) (z : X) (r q : Real) (T : Nat), survival chi z r q T = endpointMass chi z r q T Region.peak + endpointMass chi z r q T Region.bulk + endpointMass chi z r q T Region.opposite := by
    intro chi z r q T
    classical
    unfold survival endpointMass pathMass
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    cases hx : region chi z (x (Fin.last T)) <;> simp [hx]
  have endpointMass_zero : ∀ (chi : X -> Real) (z : X) (hz : chi z = 1) (r q : Real) (M : Nat) (hcard : Fintype.card X = 2 * M) (hplus : ((univ.filter fun x => chi x = 1).card) = M) (U : Region), endpointMass chi z r q 0 U = regionCount M U / Fintype.card X := by
    intro chi z hz r q M hcard hplus U
    classical
    let e := Equiv.funUnique (Fin 1) X
    unfold endpointMass
    calc
      (∑ x : Fin 1 -> X,
          pathMass chi z r q 0 x * if region chi z (x (Fin.last 0)) = U then 1 else 0) =
          ∑ y : X, pathMass chi z r q 0 (e.symm y) *
            if region chi z ((e.symm y) (Fin.last 0)) = U then 1 else 0 := by
        apply Fintype.sum_equiv e
        intro x
        rw [e.symm_apply_apply]
      _ = ∑ y : X, (1 / (Fintype.card X : Real)) *
            (if region chi z y = U then 1 else 0) := by
        apply sum_congr rfl
        intro y _
        simp [pathMass, avoids, e]
      _ = (1 / (Fintype.card X : Real)) *
            (∑ y : X, if region chi z y = U then 1 else 0) := by rw [mul_sum]
      _ = regionCount M U / Fintype.card X := by
        rw [sum_region_indicator chi z hz M hcard hplus U]
        ring
  have killedStep_cubic : ∀ (N M : Nat) (r q : Real) (hM : 2 <= M) (hN : N = 2 * M) (hq : q = r / ((M : Real) - 1)) (f : Region -> Real), killedStep N M r q (killedStep N M r q (killedStep N M r q f)) = fun U => killedStep N M r q (killedStep N M r q f) U - (1 / (2 * (N : Real))) * (1 - r) * killedStep N M r q f U - (1 / (2 * (N : Real))) * r * f U := by
    intro N M r q hM hN hq f
    subst N
    rw [hq]
    have hM1 : (M : Real) - 1 ≠ 0 := by
      have hlt : (1 : Real) < M := by exact_mod_cast (show 1 < M by omega)
      linarith
    have hM1' : (-1 : Real) + M ≠ 0 := by
      intro h
      apply hM1
      linarith
    funext U
    cases U <;> simp [killedStep, killedKernel, regionCount, regionSign, regionProfile]
    all_goals
      push_cast [Nat.cast_sub (by omega : 1 <= M)]
      field_simp [hM1, hM1']
      ring
  classical
  let f0 := endpointMass chi z r q 0
  have hf0 : f0 = fun U => regionCount M U / Fintype.card X := by
    funext U
    exact endpointMass_zero chi z hz r q M hcard hplus U
  have hs (T : Nat) := endpointMass_succ chi hchi z hz r q M hcard hplus T
  have hpoly := killedStep_cubic (Fintype.card X) M r q hM hcard hq
  have hne : (Fintype.card X : Real) ≠ 0 := by
    rw [hcard]
    positivity
  have hM1 : (M : Real) - 1 ≠ 0 := by
    have hlt : (1 : Real) < M := by exact_mod_cast (show 1 < M by omega)
    linarith
  have hM1' : (-1 : Real) + M ≠ 0 := by
    intro h
    apply hM1
    linarith
  constructor
  · rw [survival_eq_total_endpointMass]
    change f0 Region.peak + f0 Region.bulk + f0 Region.opposite = 1
    rw [hf0, hcard]
    simp [regionCount]
    push_cast [Nat.cast_sub (by omega : 1 <= M)] at *
    field_simp [hM1, hM1']
    ring
  constructor
  · rw [survival_eq_total_endpointMass, hs 0]
    change (killedStep _ _ _ _ f0 Region.peak + killedStep _ _ _ _ f0 Region.bulk +
      killedStep _ _ _ _ f0 Region.opposite) = _
    rw [hf0, hcard, hq]
    simp [killedStep, killedKernel, regionCount, regionSign, regionProfile]
    push_cast [Nat.cast_sub (by omega : 1 <= M)]
    field_simp [hM1]
    ring
  constructor
  · rw [survival_eq_total_endpointMass, hs 1, hs 0]
    change (killedStep _ _ _ _ (killedStep _ _ _ _ f0) Region.peak +
      killedStep _ _ _ _ (killedStep _ _ _ _ f0) Region.bulk +
      killedStep _ _ _ _ (killedStep _ _ _ _ f0) Region.opposite) = _
    rw [hf0, hcard, hq]
    simp [killedStep, killedKernel, regionCount, regionSign, regionProfile]
    push_cast [Nat.cast_sub (by omega : 1 <= M)]
    field_simp [hM1, hM1']
    ring
  · intro T
    rw [survival_eq_total_endpointMass, survival_eq_total_endpointMass,
      survival_eq_total_endpointMass, survival_eq_total_endpointMass]
    have h1 := hs T
    have h2 := hs (T + 1)
    have h3 := hs (T + 2)
    simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3
    rw [h3, h2, h1]
    rw [hpoly (endpointMass chi z r q T)]
    ring
/-- The hypotheses are inhabited by four states with two positive and two negative signs. -/
example : ∃ (chi : Fin 4 -> Real) (z : Fin 4) (r q : Real) (M : Nat),
    (∀ x, chi x = 1 ∨ chi x = -1) ∧ chi z = 1 ∧
      Fintype.card (Fin 4) = 2 * M ∧
      ((univ.filter fun x => chi x = 1).card) = M ∧ 2 <= M ∧
      q = r / ((M : Real) - 1) := by
  let chi : Fin 4 -> Real := fun x => if x.val < 2 then 1 else -1
  refine ⟨chi, 0, 1 / 2, 1 / 2, 2, ?_⟩
  constructor
  · intro x
    fin_cases x <;> simp [chi]
  constructor
  · simp [chi]
  constructor
  · decide
  constructor
  · have hset : univ.filter (fun x : Fin 4 => chi x = 1) = {0, 1} := by
      ext x
      fin_cases x <;> norm_num [chi]
    rw [hset]
    decide
  constructor
  · omega
  · norm_num
#print axioms survival_recurrence
end D5.S3.Estimation.TimeArrow.SinglePeakRareEdgeSurvival
