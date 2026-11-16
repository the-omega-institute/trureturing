/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiveCut
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiveCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Nontrivial five-edge cuts force at least sixty-six vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangEnergyFiveResidual
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitNormThirty
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyGap
import Batteries.Tactic.OpenPrivate

/-! Nontrivial five-edge cuts in balanced cubic nine-cube graphs require sixty-six vertices. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiveCut

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap (Q9)
open private intA intCoeff intA_sub intA_mul intA_cast intCoeff_zero_of_not_adj
  intCoeff_zero_of_same_parity intCoeff_sign_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private exists_cut_energy from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeCut
open private lap delta across across_subset across_lap neighbor_card
  intA_add_local intA_delta from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeThreeCut
open private coeff_symm cut_card_erase cut_card_compl lap_sub lap_negative_eigen
  eigen_norm_six_dvd from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFourCut
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

open private thirty_six_le_support_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitThirtyGap

private theorem unit_of_square (a : ℤ) (ha : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
  have hh : (a - 1) * (a + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hh with h | h
  · left; omega
  · right; omega

open Classical in
private theorem bound_of_mem (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C) (hcut : (BalancedCubeCut.cutEdges C T).card = 5)
    (hT : 4 ≤ T.card) (hR : 4 ≤ (C \ T).card)
    (x : Q9) (hxT : x ∈ T) : (across C T x).card ≤ 1 := by
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
  have herase := Finset.card_erase_add_one hxT
  have hRsub : C \ T ⊆ C \ T.erase x := by
    intro y hy
    obtain ⟨hyC, hyT⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨hyC, fun h => hyT (Finset.mem_erase.mp h).2⟩
  have hRlarge := hR.trans (Finset.card_le_card hRsub)
  rw [hacross]
  by_contra hbound
  have hcases : k = 2 ∨ k = 3 := by omega
  rcases hcases with hk2 | hk3
  · have hfour : (BalancedCubeCut.cutEdges C (T.erase x)).card = 4 := by omega
    rcases BalancedCubeFourCut.small_side_of_cut_card_eq_four
      C (T.erase x) hr hb hconn hUC hfour with h | h <;> omega
  · have htwo : (BalancedCubeCut.cutEdges C (T.erase x)).card = 2 := by omega
    have hmin := BalancedCubeCut.three_le_cutEdges_card C (T.erase x)
      hr hb hUC (by omega)
    omega

open Classical in
private theorem cut_matching (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C) (hcut : (BalancedCubeCut.cutEdges C T).card = 5)
    (hT : 4 ≤ T.card) (hR : 4 ≤ (C \ T).card) :
    ∀ x ∈ C, (across C T x).card ≤ 1 := by
  have hdouble : C \ (C \ T) = T := by
    ext x
    have hm : x ∈ T → x ∈ C := fun h => hTC h
    simp only [Finset.mem_sdiff]
    tauto
  intro x hxC
  by_cases hxT : x ∈ T
  · exact bound_of_mem C T hr hb hconn hTC hcut hT hR x hxT
  · have hxR : x ∈ C \ T := Finset.mem_sdiff.mpr ⟨hxC, hxT⟩
    have hc : (BalancedCubeCut.cutEdges C (C \ T)).card = 5 := by
      rw [cut_card_compl C T hTC, hcut]
    have h := bound_of_mem C (C \ T) hr hb hconn Finset.sdiff_subset hc
      hR (by simpa [hdouble] using hT) x hxR
    simpa [across, hxT, hxR, hdouble] using h

open Classical in
private theorem support_bound (v : Q9 → ℤ) (S : Finset Q9)
    (y z w : Q9) (hv : ∀ x, x ∉ S → x ≠ y → x ≠ z → x ≠ w → v x = 0) :
    (Finset.univ.filter (fun x => v x ≠ 0)).card ≤ S.card + 3 := by
  have hsub : Finset.univ.filter (fun x => v x ≠ 0) ⊆
      insert y (insert z (insert w S)) := by
    intro x hx
    have hn := (Finset.mem_filter.mp hx).2
    by_contra h
    simp only [Finset.mem_insert, not_or] at h
    exact hn (hv x h.2.2.2 h.1 h.2.1 h.2.2.1)
  have hc := Finset.card_le_card hsub
  have h1 := Finset.card_insert_le y (insert z (insert w S))
  have h2 := Finset.card_insert_le z (insert w S)
  have h3 := Finset.card_insert_le w S
  omega

open Classical in
/-- For actual five-edge cuts with both sides of size at least four, a balanced
connected cubic induced nine-cube graph of order below sixty-six has a unit
integer Laplacian residual of support exactly thirty. -/
private theorem unit_laplacian_of_cut_card_eq_five_of_card_lt_sixty_six (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C) (hcut : (BalancedCubeCut.cutEdges C T).card = 5)
    (hT : 4 ≤ T.card) (hR : 4 ≤ (C \ T).card) (hsmall : C.card < 66) :
    ∃ sigma : Q9 → ℝ, ∃ f h : Q9 → ℤ,
      IsSwitching C sigma ∧
      (fun x => (f x : ℝ)) = switchingVector T sigma ∧
      h = (fun x => 3 * f x - intA f x) ∧
      (∀ x, h x = 0 ∨ h x = 1 ∨ h x = -1) ∧
      (Finset.univ.filter (fun x => h x ≠ 0)).card = 30 ∧
      intA h = (fun x => -3 * h x) := by
  have hmatching := cut_matching C T hr hb hconn hTC hcut hT hR
  obtain ⟨sigma, hs⟩ := hb
  obtain ⟨f, hf, he⟩ := exists_cut_energy C T sigma hr hs hTC
  have he5 : HuangIntegralNormGap.energy f = 5 := by simpa [hcut] using he
  have habs : ∀ x ∈ C, |(lap f x : ℝ)| ≤ 1 := by
    intro x hx
    rw [across_lap C T sigma hr hs hTC f hf x hx]
    exact_mod_cast hmatching x hx
  obtain ⟨total, htotal, _⟩ := exists_cut_energy C C sigma hr hs (by intro x hx; exact hx)
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
    simpa [switchingVector, hx] using congrFun htotal x
  have htotal_sign : ∀ x ∈ C, total x = 1 ∨ total x = -1 := by
    intro x hx
    have ht : (total x : ℝ) = sigma x := by
      simpa [switchingVector, hx] using congrFun htotal x
    rcases hs.1 x hx with hp | hm
    · left; exact_mod_cast ht.trans hp
    · right; exact_mod_cast ht.trans hm
  have hf_zero : ∀ x, x ∉ T → f x = 0 := by
    intro x hx
    apply Int.cast_injective (α := ℝ)
    simpa [switchingVector, hx] using congrFun hf x
  have hf_total : ∀ x, x ∈ T → f x = total x := by
    intro x hx
    apply Int.cast_injective (α := ℝ)
    have h1 := congrFun hf x
    have h2 := congrFun htotal x
    simp [switchingVector, hx, hTC hx] at h1 h2
    exact h1.trans h2.symm
  have hout : ∀ x (a : ℤ), a ^ 2 = 1 → lap f x = 2 * a → x ∉ C := by
    intro x a ha hl hx
    have hh := habs x hx
    rw [hl] at hh
    rcases unit_of_square a ha with rfl | rfl <;> norm_num at hh
  rcases HuangEnergyFiveResidual.classify_energy_five_residual f he5 with hunit | hpath
  · exact ⟨sigma, f, lap f, hs, hf, rfl, hunit.1, hunit.2, lap_negative_eigen f⟩
  · exfalso
    obtain ⟨y, z, w, s, hs2, hyz, hyw, hzw, hshape⟩ := hpath
    have hyz' : y ≠ z := hyz.ne
    have hyw' : y ≠ w := hyw.ne
    have hp : cubeParity z = cubeParity w := by
      have h1 := cubeParity_ne_of_adj hyz
      have h2 := cubeParity_ne_of_adj hyw
      cases hy : cubeParity y <;> cases hz : cubeParity z <;>
        cases hw : cubeParity w <;> simp_all
    have hzz : intCoeff z z = 0 :=
      intCoeff_zero_of_not_adj z z ((hypercube 9).irrefl (v := z))
    have hww : intCoeff w w = 0 :=
      intCoeff_zero_of_not_adj w w ((hypercube 9).irrefl (v := w))
    have hzw0 : intCoeff z w = 0 := intCoeff_zero_of_same_parity z w hp
    have hwz0 : intCoeff w z = 0 := by rw [coeff_symm]; exact hzw0
    let a : ℤ := s * intCoeff y z
    let b : ℤ := s * intCoeff y w
    have ha2 : a ^ 2 = 1 := by
      rcases intCoeff_sign_of_adj y z hyz with h | h <;> simp [a, h, hs2]
    have hb2 : b ^ 2 = 1 := by
      rcases intCoeff_sign_of_adj y w hyw with h | h <;> simp [b, h, hs2]
    let g : Q9 → ℤ := fun x => s * delta y x + a * delta z x + b * delta w x
    have hgA (x : Q9) : intA g x =
        s * intCoeff x y + a * intCoeff x z + b * intCoeff x w := by
      change intA (((fun v => s * delta y v) + (fun v => a * delta z v)) +
        (fun v => b * delta w v)) x = _
      simp only [intA_add_local, intA_mul, intA_delta, Pi.add_apply]
    have hshape' : lap f = lap g := hshape
    have hlz : lap f z = 2 * a := by
      rw [hshape']
      change 3 * g z - intA g z = 2 * a
      rw [hgA, hzz, hzw0, coeff_symm z y]
      simp only [g, delta, Ne.symm hyz', hzw, ite_false, ite_true, mul_zero,
        mul_one, zero_add, add_zero]
      dsimp [a]
      ring
    have hlw : lap f w = 2 * b := by
      rw [hshape']
      change 3 * g w - intA g w = 2 * b
      rw [hgA, hww, hwz0, coeff_symm w y]
      simp only [g, delta, Ne.symm hyw', Ne.symm hzw, ite_false, ite_true,
        mul_zero, mul_one, zero_add, add_zero]
      dsimp [b]
      ring
    have hzC := hout z a ha2 hlz
    have hwC := hout w b hb2 hlw
    have hfz := hf_zero z (fun h => hzC (hTC h))
    have hfw := hf_zero w (fun h => hwC (hTC h))
    have htz := htotal_zero z hzC
    have htw := htotal_zero w hwC
    let v1 : Q9 → ℤ := f - g
    let v2 : Q9 → ℤ := total - v1
    have hv1 : intA v1 = fun x => 3 * v1 x := by
      have hzero : lap v1 = 0 := by
        change lap (f - g) = 0
        rw [lap_sub]
        exact sub_eq_zero.mpr hshape'
      funext x
      have hx := congrFun hzero x
      change 3 * v1 x - intA v1 x = 0 at hx
      linarith
    have hv2 : intA v2 = fun x => 3 * v2 x := by
      change intA (total - v1) = _
      rw [intA_sub, htotal_eigen, hv1]
      funext x
      change 3 * total x - 3 * v1 x = 3 * (total x - v1 x)
      ring
    have hpoint (x : Q9) : v1 x ^ 2 + v2 x ^ 2 = total x ^ 2 +
        (if x = y then 2 + 2 * s * (total y - 2 * f y) else 0) +
        (if x = z then 2 else 0) + (if x = w then 2 else 0) := by
      by_cases hxy : x = y
      · subst x
        simp only [v1, v2, Pi.sub_apply, g, delta, ite_true, ite_false,
          hyz', hyw', mul_one, mul_zero, add_zero]
        have hsplit : f y = total y ∨ f y = 0 := by
          by_cases hyT : y ∈ T
          · exact Or.inl (hf_total y hyT)
          · exact Or.inr (hf_zero y hyT)
        rcases hsplit with hh | hh <;> rw [hh] <;> nlinarith [hs2]
      · by_cases hxz : x = z
        · subst x
          simp [v1, v2, g, delta, hfz, htz, Ne.symm hyz', hzw, ha2]
        · by_cases hxw : x = w
          · subst x
            simp [v1, v2, g, delta, hfw, htw, Ne.symm hyw', Ne.symm hzw, hb2]
          · have hg : g x = 0 := by simp [g, delta, hxy, hxz, hxw]
            by_cases hxT : x ∈ T
            · simp [v1, v2, hg, hf_total x hxT, hxy, hxz, hxw]
            · simp [v1, v2, hg, hf_zero x hxT, hxy, hxz, hxw]
    have hsum : (∑ x : Q9, v1 x ^ 2) + (∑ x : Q9, v2 x ^ 2) =
        (∑ x : Q9, total x ^ 2) + 6 + 2 * s * (total y - 2 * f y) := by
      calc
        _ = ∑ x : Q9, (v1 x ^ 2 + v2 x ^ 2) := Finset.sum_add_distrib.symm
        _ = ∑ x : Q9, (total x ^ 2 +
            (if x = y then 2 + 2 * s * (total y - 2 * f y) else 0) +
            (if x = z then 2 else 0) + (if x = w then 2 else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hpoint x
        _ = _ := by simp only [Finset.sum_add_distrib]; simp; ring
    have hyC : y ∉ C := by
      intro hyC
      obtain ⟨k1, hk1⟩ := eigen_norm_six_dvd v1 hv1
      obtain ⟨k2, hk2⟩ := eigen_norm_six_dvd v2 hv2
      obtain ⟨kt, hkt⟩ := eigen_norm_six_dvd total htotal_eigen
      have hySign := htotal_sign y hyC
      have hsSign := unit_of_square s hs2
      by_cases hyT : y ∈ T
      · rw [hf_total y hyT] at hsum
        rcases hySign with ht | ht <;> rcases hsSign with hh | hh <;>
          rw [ht, hh] at hsum <;> omega
      · rw [hf_zero y hyT] at hsum
        rcases hySign with ht | ht <;> rcases hsSign with hh | hh <;>
          rw [ht, hh] at hsum <;> omega
    have hgunit : ∀ x, g x = 0 ∨ g x = 1 ∨ g x = -1 := by
      intro x
      have ss := unit_of_square s hs2
      have aa := unit_of_square a ha2
      have bb := unit_of_square b hb2
      by_cases hxy : x = y
      · subst x
        simpa [g, delta, hyz', hyw'] using (Or.inr ss : s = 0 ∨ s = 1 ∨ s = -1)
      · by_cases hxz : x = z
        · subst x
          simpa [g, delta, Ne.symm hyz', hzw] using (Or.inr aa : a = 0 ∨ a = 1 ∨ a = -1)
        · by_cases hxw : x = w
          · subst x
            simpa [g, delta, Ne.symm hyw', Ne.symm hzw] using (Or.inr bb : b = 0 ∨ b = 1 ∨ b = -1)
          · left; simp [g, delta, hxy, hxz, hxw]
    have hgzero : ∀ x ∈ C, g x = 0 := by
      intro x hx
      have hxy : x ≠ y := fun h => hyC (h ▸ hx)
      have hxz : x ≠ z := fun h => hzC (h ▸ hx)
      have hxw : x ≠ w := fun h => hwC (h ▸ hx)
      simp [g, delta, hxy, hxz, hxw]
    have hvunit : (∀ x, v1 x = 0 ∨ v1 x = 1 ∨ v1 x = -1) ∧
        (∀ x, v2 x = 0 ∨ v2 x = 1 ∨ v2 x = -1) := by
      constructor <;> intro x
      · by_cases hxC : x ∈ C
        · rw [show v1 x = f x by simp [v1, hgzero x hxC]]
          by_cases hxT : x ∈ T
          · rw [hf_total x hxT]; exact Or.inr (htotal_sign x hxC)
          · exact Or.inl (hf_zero x hxT)
        · have hfx := hf_zero x (fun h => hxC (hTC h))
          rcases hgunit x with hh | hh | hh <;>
            simp [v1, hfx, hh]
      · by_cases hxC : x ∈ C
        · have hgx := hgzero x hxC
          by_cases hxT : x ∈ T
          · left; simp [v2, v1, hgx, hf_total x hxT]
          · have hfx := hf_zero x hxT
            simpa [v2, v1, hgx, hfx] using (Or.inr (htotal_sign x hxC) :
              total x = 0 ∨ total x = 1 ∨ total x = -1)
        · have hfx := hf_zero x (fun h => hxC (hTC h))
          have htx := htotal_zero x hxC
          simpa [v2, v1, hfx, htx] using hgunit x
    have hv1z : v1 z = -a := by simp [v1, g, delta, hfz, Ne.symm hyz', hzw]
    have hv2z : v2 z = a := by simp [v2, hv1z, htz]
    have hv1ne : v1 ≠ 0 := by
      intro hh
      have hz := congrFun hh z
      rw [hv1z] at hz
      change -a = 0 at hz
      nlinarith [ha2]
    have hv2ne : v2 ≠ 0 := by
      intro hh
      have hz := congrFun hh z
      rw [hv2z] at hz
      change a = 0 at hz
      nlinarith [ha2]
    have hl1 := thirty_six_le_support_card v1 hv1 hvunit.1 hv1ne
    have hl2 := thirty_six_le_support_card v2 hv2 hvunit.2 hv2ne
    have hb1 := support_bound v1 T y z w (by
      intro x hxT hxy hxz hxw
      simp [v1, hf_zero x hxT, g, delta, hxy, hxz, hxw])
    have hb2 := support_bound v2 (C \ T) y z w (by
      intro x hxR hxy hxz hxw
      have hgx : g x = 0 := by simp [g, delta, hxy, hxz, hxw]
      by_cases hxT : x ∈ T
      · simp [v2, v1, hgx, hf_total x hxT]
      · have hxC : x ∉ C := fun h => hxR (Finset.mem_sdiff.mpr ⟨h, hxT⟩)
        simp [v2, v1, hgx, hf_zero x hxT, htotal_zero x hxC])
    have hcard := Finset.card_sdiff_add_card_eq_card hTC
    omega

open Classical in
/-- An actual five-edge cut with at least four vertices on each side in a
connected balanced induced cubic nine-cube graph requires at least sixty-six
vertices. -/
theorem sixty_six_le_card_of_cut_card_eq_five (C T : Finset Q9)
    (hr : ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hconn : ((hypercube 9).induce (C : Set Q9)).Connected)
    (hTC : T ⊆ C) (hcut : (BalancedCubeCut.cutEdges C T).card = 5)
    (hT : 4 ≤ T.card) (hR : 4 ≤ (C \ T).card) : 66 ≤ C.card := by
  by_contra hn
  have hsmall : C.card < 66 := by omega
  obtain ⟨_sigma, _f, h, _hs, _hf, _heq, hu, hcard, heig⟩ :=
    unit_laplacian_of_cut_card_eq_five_of_card_lt_sixty_six
      C T hr hb hconn hTC hcut hT hR hsmall
  exact HuangUnitThirtyGap.no_unit_negative_three_support_thirty h heig hu hcard

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiveCut
