/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubeFiveNeighborGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubeFiveNeighborGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity, mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Five support neighbors force sixteen points for unit Huang rows divisible by three. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeTwelveSupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Batteries.Tactic.OpenPrivate

/-! Five support neighbors force at least sixteen support points. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubeFiveNeighborGap

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip)
open private intA intCoeff intCoeff_cast intCoeff_sign_of_adj
  intCoeff_zero_of_not_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private no_singleton_row intCoeff_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
open private directions mem_directions directions_card flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private flip_comm adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_symm diff_self from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
open private diff_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeTwelveSupport

private abbrev Q9 := Q 9
private abbrev Adj := (hypercube 9).Adj
private abbrev Pair := Fin 9 × Fin 9
private def cross (y : Q9) (a : Pair) : Q9 := flip (flip y a.1) a.2

open Classical in
private theorem diff_double (x : Q9) {i j : Fin 9} (hij : i ≠ j) :
    diff x (flip (flip x i) j) = {i, j} := by
  classical
  ext k
  simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hki : k = i
  · subst k
    cases h : x i <;> simp [BalancedCriticalSpectrum.flip, hij, h]
  · by_cases hkj : k = j
    · subst k
      cases h : x j <;> simp [BalancedCriticalSpectrum.flip, hki, h]
    · simp [BalancedCriticalSpectrum.flip, hki, hkj]

-- Two flips followed by an edge, outside the first neighborhood, have distance three.
open Classical in
private theorem cross_data {y z : Q9} {i j : Fin 9} (hij : i ≠ j)
    (hn : ¬ Adj y z) (ha : Adj (flip (flip y i) j) z) :
    (diff y z).card = 3 ∧ i ∈ diff y z ∧ j ∈ diff y z := by
  classical
  have hc : (diff (flip (flip y i) j) z).card = 1 := ha
  have hn' : (diff y z).card ≠ 1 := hn
  by_cases hi : i ∈ diff y z
  · have he := Finset.card_erase_add_one hi
    simp only [diff_flip, ite_eq_left hi] at hc
    by_cases hj : j ∈ diff y z
    · have hje : j ∈ (diff y z).erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
      have hf := Finset.card_erase_add_one hje
      rw [ite_eq_left hje] at hc
      exact ⟨by omega, hi, hj⟩
    · have hje : j ∉ (diff y z).erase i := fun h => hj (Finset.mem_erase.mp h).2
      rw [ite_eq_right hje, Finset.card_insert_of_notMem hje] at hc
      omega
  · simp only [diff_flip, ite_eq_right hi] at hc
    have he := Finset.card_insert_of_notMem hi
    by_cases hj : j ∈ diff y z
    · have hji : j ∈ insert i (diff y z) := Finset.mem_insert_of_mem hj
      have hf := Finset.card_erase_add_one hji
      rw [ite_eq_left hji] at hc
      omega
    · have hji : j ∉ insert i (diff y z) := by simp [hij.symm, hj]
      rw [ite_eq_right hji, Finset.card_insert_of_notMem hji] at hc
      omega

-- Among first neighbors, a cross row sees just its two coordinate endpoints.
open Classical in
private theorem first_neighbor {y z : Q9} {i j : Fin 9} (hij : i ≠ j)
    (hyz : Adj y z) (ha : Adj (flip (flip y i) j) z) :
    z = flip y i ∨ z = flip y j := by
  classical
  obtain ⟨k, rfl⟩ := adjacent_exists_flip hyz
  by_cases hki : k = i
  · subst k
    exact Or.inl rfl
  · have hne : flip y i ≠ flip y k := by
      intro h
      exact hki (flip_injective y h).symm
    have hk := (diff_of_adj_flip hne j ha).1
    have hd : diff (flip y i) (flip y k) = {i, k} := by
      have hs : diff y (flip y k) = {k} := by
        ext t
        simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        by_cases ht : t = k
        · subst t
          cases h : y k <;> simp [BalancedCriticalSpectrum.flip, h]
        · simp [BalancedCriticalSpectrum.flip, ht]
      simp only [diff_flip, hs, ite_eq_right (show i ∉ ({k} : Finset (Fin 9)) by
        simpa using Ne.symm hki)]
    rw [hd] at hk
    have hjk : j = k := by simpa [hij.symm] using hk
    subst k
    exact Or.inr rfl

open Classical in
private theorem row_two_zero (q : Q9 → ℤ)
    (hu : ∀ x, q x = 0 ∨ q x = 1 ∨ q x = -1)
    (hdiv : ∀ v, (3 : ℤ) ∣ intA q v)
    {v x z : Q9} (hxz : x ≠ z) (hx : q x ≠ 0) (hz : q z ≠ 0)
    (hvx : Adj v x) (hvz : Adj v z)
    (honly : ∀ w, q w ≠ 0 → Adj v w → w = x ∨ w = z) :
    intCoeff v x * q x + intCoeff v z * q z = 0 := by
  classical
  have hr : intA q v = intCoeff v x * q x + intCoeff v z * q z := by
    unfold intA
    have he : (∑ w : Q9, intCoeff v w * q w) =
        ∑ w ∈ ({x, z} : Finset Q9), intCoeff v w * q w := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      by_cases hq : q w = 0
      · simp [hq]
      · have hn : ¬ Adj v w := by
          intro ha
          have := honly w hq ha
          simp_all
        simp [intCoeff_zero_of_not_adj v w hn]
    rw [he]
    simp [hxz]
  obtain ⟨k, hk⟩ := hdiv v
  rw [hr] at hk
  rcases hu x with h | h | h <;> rcases hu z with h' | h' | h' <;>
    rcases intCoeff_sign_of_adj v x hvx with hc | hc <;>
    rcases intCoeff_sign_of_adj v z hvz with hd | hd <;>
    simp_all <;> omega

-- This uses the original signed operators, not balancedness of a selected square.
open Classical in
private theorem square_obstruction (q : Q9 → ℤ)
    (hu : ∀ x, q x = 0 ∨ q x = 1 ∨ q x = -1)
    (hdiv : ∀ v, (3 : ℤ) ∣ intA q v)
    {x : Q9} {j k : Fin 9} (hjk : j ≠ k)
    (hx : q x ≠ 0) (hz : q (flip (flip x j) k) ≠ 0)
    (hv : ∀ w, q w ≠ 0 → Adj (flip x j) w →
      w = x ∨ w = flip (flip x j) k)
    (hw : ∀ w, q w ≠ 0 → Adj (flip x k) w →
      w = x ∨ w = flip (flip x j) k) : False := by
  classical
  let z := flip (flip x j) k
  have hxz : x ≠ z := by
    intro h
    have hc := congrArg Finset.card (diff_double x hjk)
    change (diff x z).card = ({j, k} : Finset (Fin 9)).card at hc
    rw [← h, diff_self] at hc
    simp [hjk] at hc
  have hvx : Adj (flip x j) x := (BalancedCriticalSpectrum.flip_adj x j).symm
  have hwx : Adj (flip x k) x := (BalancedCriticalSpectrum.flip_adj x k).symm
  have hvz : Adj (flip x j) z := BalancedCriticalSpectrum.flip_adj _ k
  have hwz : Adj (flip x k) z := by
    dsimp [z]
    rw [flip_comm x j k]
    exact BalancedCriticalSpectrum.flip_adj _ j
  have hr := row_two_zero q hu hdiv hxz hx hz hvx hvz hv
  have hs := row_two_zero q hu hdiv hxz hx hz hwx hwz hw
  have hg := congrFun (BalancedCubeGirth.gamma_anticommute hjk
    (fun _ : Q9 => (1 : ℝ))) x
  simp only [BalancedCriticalSpectrum.gamma_apply, Pi.neg_apply, mul_one] at hg
  rw [flip_comm x k j] at hg
  have hg' : intCoeff (flip x j) x * intCoeff (flip x j) z =
      -(intCoeff (flip x k) x * intCoeff (flip x k) z) := by
    rw [intCoeff_symmetric (flip x j) x, intCoeff_symmetric (flip x k) x]
    apply Int.cast_injective (α := ℝ)
    simpa only [Int.cast_mul, Int.cast_neg, intCoeff_cast, z] using hg
  rcases hu x with h | h | h <;> rcases hu z with h' | h' | h' <;>
    rcases intCoeff_sign_of_adj _ _ hvx with ha | ha <;>
    rcases intCoeff_sign_of_adj _ _ hvz with hb | hb <;>
    rcases intCoeff_sign_of_adj _ _ hwx with hc | hc <;>
    rcases intCoeff_sign_of_adj _ _ hwz with hd | hd <;>
    simp_all

open Classical in
private theorem count_swap {α β : Type*} (A : Finset α) (B : Finset β)
    (P : α → β → Prop) :
    (∑ a ∈ A, (B.filter (P a)).card) =
      ∑ b ∈ B, (A.filter (fun a => P a b)).card := by
  classical
  simp only [Finset.card_filter]
  exact Finset.sum_comm

open Classical in
private theorem saturated {α : Type*} (A : Finset α) (f : α → ℕ) (c : ℕ)
    (hle : ∀ a ∈ A, f a ≤ c) (hs : (∑ a ∈ A, f a) = A.card * c) :
    ∀ a ∈ A, f a = c := by
  classical
  intro a ha
  by_contra hn
  have hlt : (∑ a ∈ A, f a) < ∑ _a ∈ A, c := by
    apply Finset.sum_lt_sum hle
    exact ⟨a, ha, by have := hle a ha; omega⟩
  simp only [Finset.sum_const, smul_eq_mul] at hlt
  omega

open Classical in
/-- A unit integral vector with all original Huang rows divisible by three has
at least sixteen support points if one row has five support neighbors. -/
theorem sixteen_le_support_card_of_neighbor_card_eq_five
    (q : Q9 → ℤ)
    (hu : ∀ x, q x = 0 ∨ q x = 1 ∨ q x = -1)
    (hdiv : ∀ v, (3 : ℤ) ∣ intA q v)
    (y : Q9)
    (hfive : ((Finset.univ.filter (fun x => q x ≠ 0)).filter
      (fun x => (hypercube 9).Adj y x)).card = 5) :
    16 ≤ (Finset.univ.filter (fun x => q x ≠ 0)).card := by
  classical
  let S : Finset Q9 := Finset.univ.filter (fun x => q x ≠ 0)
  let N := S.filter (Adj y)
  let T := S \ N
  let I := directions S y
  let J := Finset.univ \ I
  let W := I.product J
  let R := fun z : Q9 => W.filter (fun a => Adj (cross y a) z)
  let F := fun a : Pair => T.filter (Adj (cross y a))
  have hS : ∀ z, z ∈ S ↔ q z ≠ 0 := by simp [S]
  have hI : ∀ i, i ∈ I ↔ flip y i ∈ S := fun i => mem_directions S y i
  have hJ : ∀ j, j ∈ J ↔ j ∉ I := by simp [J]
  have hW : ∀ a : Pair, a ∈ W ↔ a.1 ∈ I ∧ a.2 ∈ J := by simp [W]
  have hne : ∀ a ∈ W, a.1 ≠ a.2 := by
    intro a ha he
    obtain ⟨hi, hj⟩ := (hW a).mp ha
    exact ((hJ _).mp hj) (he ▸ hi)
  have hIc : I.card = 5 := by
    rw [directions_card]
    exact hfive
  have hJc : J.card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hIc]
  have hWc : W.card = 20 := by simp [W, hIc, hJc]
  by_contra hbad
  change ¬ 16 ≤ S.card at hbad
  have hSc : S.card ≤ 15 := by omega
  have hNc : N.card = 5 := hfive
  have hTc : T.card ≤ 10 := by
    have hc := Finset.card_sdiff_add_card_inter S N
    have he : S ∩ N = N := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [he] at hc
    change T.card + N.card = S.card at hc
    omega
  have hT : ∀ z ∈ T, z ∈ S ∧ ¬ Adj y z := by
    intro z hz
    obtain ⟨hzS, hzN⟩ := Finset.mem_sdiff.mp hz
    exact ⟨hzS, fun ha => hzN (Finset.mem_filter.mpr ⟨hzS, ha⟩)⟩
  have hfirst : ∀ a ∈ W, ∀ z ∈ S, Adj (cross y a) z → Adj y z →
      z = flip y a.1 := by
    intro a ha z hz haz hyz
    rcases first_neighbor (hne a ha) hyz haz with h | h
    · exact h
    · have hj := (hW a).mp ha
      exact False.elim (((hJ _).mp hj.2) ((hI _).mpr (h ▸ hz)))
  have hpos : ∀ a ∈ W, 1 ≤ (F a).card := by
    intro a ha
    have hxS : flip y a.1 ∈ S := (hI _).mp ((hW a).mp ha).1
    have hax : Adj (cross y a) (flip y a.1) :=
      (BalancedCriticalSpectrum.flip_adj _ a.2).symm
    have hxmem : flip y a.1 ∈ S.filter (Adj (cross y a)) :=
      Finset.mem_filter.mpr ⟨hxS, hax⟩
    have hp := Finset.card_pos.mpr ⟨_, hxmem⟩
    have hn := no_singleton_row q hu hdiv (cross y a)
    change (S.filter (Adj (cross y a))).card ≠ 1 at hn
    have ht : 1 < (S.filter (Adj (cross y a))).card := by omega
    obtain ⟨z, hz, hzx⟩ := Finset.exists_mem_ne ht (flip y a.1)
    obtain ⟨hzS, haz⟩ := Finset.mem_filter.mp hz
    have hnz : ¬ Adj y z := fun hyz => hzx (hfirst a ha z hzS haz hyz)
    have hzT : z ∈ T := Finset.mem_sdiff.mpr
      ⟨hzS, fun h => hnz (Finset.mem_filter.mp h).2⟩
    have hpF : 0 < (F a).card := Finset.card_pos.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hzT, haz⟩⟩
    omega
  have hcap : ∀ z ∈ T, (R z).card ≤ 2 := by
    intro z hz
    by_cases hem : (R z).Nonempty
    · obtain ⟨a, ha⟩ := hem
      obtain ⟨haW, haz⟩ := Finset.mem_filter.mp ha
      have hd := cross_data (hne a haW) (hT z hz).2 haz
      let D := diff y z
      let A := D ∩ I
      let B := D ∩ J
      have hsub : R z ⊆ A.product B := by
        intro b hb
        obtain ⟨hbW, hbz⟩ := Finset.mem_filter.mp hb
        have hbD := cross_data (hne b hbW) (hT z hz).2 hbz
        exact Finset.mem_product.mpr
          ⟨Finset.mem_inter.mpr ⟨hbD.2.1, ((hW b).mp hbW).1⟩,
           Finset.mem_inter.mpr ⟨hbD.2.2, ((hW b).mp hbW).2⟩⟩
      have hdj : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        exact ((hJ i).mp (Finset.mem_inter.mp hj).2) (Finset.mem_inter.mp hi).2
      have huAB : A ∪ B = D := by
        ext i
        by_cases hi : i ∈ I <;> simp [A, B, J, hi]
      have hsum : A.card + B.card = 3 := by
        rw [← Finset.card_union_of_disjoint hdj, huAB]
        exact hd.1
      have hprod : A.card * B.card ≤ 2 := by
        have hA : A.card ≤ 3 := by omega
        interval_cases h : A.card <;> simp_all <;> omega
      exact (Finset.card_le_card hsub).trans (by simpa using hprod)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hem]
  have hswap : (∑ a ∈ W, (F a).card) = ∑ z ∈ T, (R z).card :=
    count_swap W T (fun a z => Adj (cross y a) z)
  have hlo : 20 ≤ ∑ a ∈ W, (F a).card := by
    calc
      20 = ∑ _a ∈ W, 1 := by simp [hWc]
      _ ≤ _ := Finset.sum_le_sum hpos
  have hhi : (∑ z ∈ T, (R z).card) ≤ 2 * T.card := by
    calc
      _ ≤ ∑ _z ∈ T, 2 := Finset.sum_le_sum hcap
      _ = _ := by simp [Nat.mul_comm]
  have htotal : (∑ a ∈ W, (F a).card) = 20 := by omega
  have hTc10 : T.card = 10 := by omega
  have hcol : ∀ z ∈ T, (R z).card = 2 := by
    apply saturated T (fun z => (R z).card) 2 hcap
    omega
  have hrow : ∀ a ∈ W, (F a).card = 1 := by
    intro a ha
    by_contra hn
    have hlt : (∑ _a ∈ W, 1) < ∑ a ∈ W, (F a).card := by
      apply Finset.sum_lt_sum hpos
      exact ⟨a, ha, by have := hpos a ha; omega⟩
    simp [hWc, htotal] at hlt
  have honly : ∀ a ∈ W, ∀ z ∈ T, Adj (cross y a) z →
      ∀ w, q w ≠ 0 → Adj (cross y a) w → w = flip y a.1 ∨ w = z := by
    intro a ha z hz haz w hw haw
    have hwS := (hS w).mpr hw
    by_cases hyw : Adj y w
    · exact Or.inl (hfirst a ha w hwS haw hyw)
    · right
      have hwT : w ∈ T := Finset.mem_sdiff.mpr
        ⟨hwS, fun h => hyw (Finset.mem_filter.mp h).2⟩
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (hrow a ha)
      have hwm : w ∈ F a := Finset.mem_filter.mpr ⟨hwT, haw⟩
      have hzm : z ∈ F a := Finset.mem_filter.mpr ⟨hz, haz⟩
      rw [hu] at hwm hzm
      exact (Finset.mem_singleton.mp hwm).trans (Finset.mem_singleton.mp hzm).symm
  have hsecond : ∀ z ∈ T, ∀ a ∈ R z, ∀ b ∈ R z, a.2 = b.2 := by
    intro z hz a ha b hb
    obtain ⟨haW, haz⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbW, hbz⟩ := Finset.mem_filter.mp hb
    by_contra hjk
    have hda := cross_data (hne a haW) (hT z hz).2 haz
    have hdb := cross_data (hne b hbW) (hT z hz).2 hbz
    have hei : a.1 = b.1 := by
      by_contra hi
      have hdsub : {a.1, a.2, b.1, b.2} ⊆ diff y z := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hda.2.1
        · exact hda.2.2
        · exact hdb.2.1
        · exact hdb.2.2
      have hab : a.1 ≠ b.2 := by
        intro he
        exact ((hJ _).mp ((hW b).mp hbW).2) (he ▸ ((hW a).mp haW).1)
      have hba : b.1 ≠ a.2 := by
        intro he
        exact ((hJ _).mp ((hW a).mp haW).2) (he ▸ ((hW b).mp hbW).1)
      have hc := Finset.card_le_card hdsub
      simp [hne a haW, hne b hbW, hi, hjk, hab, Ne.symm hba, hda.1] at hc
    let x := flip y a.1
    have hxS : x ∈ S := (hI _).mp ((hW a).mp haW).1
    have hxz : x ≠ z := by
      intro he
      exact (hT z hz).2 (he ▸ BalancedCriticalSpectrum.flip_adj y a.1)
    have hdj := diff_of_adj_flip hxz a.2 haz
    have hdk := diff_of_adj_flip hxz b.2 (by simpa [cross, ← hei] using hbz)
    have hdEq : diff x z = {a.2, b.2} := by
      have hs : {a.2, b.2} ⊆ diff x z := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hdj.1
        · exact hdk.1
      exact (Finset.eq_of_subset_of_card_le hs (by simp [hjk, hdj.2])).symm
    have hzEq : z = flip (flip x a.2) b.2 :=
      diff_injective (hdEq.trans (diff_double x hjk).symm)
    apply square_obstruction q hu hdiv hjk ((hS x).mp hxS)
      (by rw [← hzEq]; exact (hS z).mp (hT z hz).1)
    · intro w hw haw
      have hh := honly a haW z hz haz w hw haw
      simpa [x, hzEq] using hh
    · intro w hw hbw
      have hh := honly b hbW z hz hbz w hw (by simpa [cross, hei, x] using hbw)
      simpa [← hei, x, hzEq] using hh
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < J.card by omega)
  let V := W.filter (fun a => a.2 = j)
  have hVc : V.card = 5 := by
    have he : V = I.product {j} := by
      ext a
      constructor
      · intro ha
        obtain ⟨haW, haj⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_product.mpr
          ⟨((hW a).mp haW).1, Finset.mem_singleton.mpr haj⟩
      · intro ha
        obtain ⟨hai, haj⟩ := Finset.mem_product.mp ha
        have heq := Finset.mem_singleton.mp haj
        exact Finset.mem_filter.mpr
          ⟨(hW a).mpr ⟨hai, heq.symm ▸ hj⟩, heq⟩
    simp [he, hIc]
  let U := T.filter (fun z => ∃ a ∈ R z, a.2 = j)
  have hfiber : ∀ z ∈ T, (V.filter (fun a => Adj (cross y a) z)).card =
      if z ∈ U then 2 else 0 := by
    intro z hz
    by_cases hzU : z ∈ U
    · obtain ⟨_, a, ha, haj⟩ := Finset.mem_filter.mp hzU
      have he : V.filter (fun b => Adj (cross y b) z) = R z := by
        ext b
        constructor
        · intro hb
          obtain ⟨hbV, hbz⟩ := Finset.mem_filter.mp hb
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hbV).1, hbz⟩
        · intro hb
          obtain ⟨hbW, hbz⟩ := Finset.mem_filter.mp hb
          have hbj := (hsecond z hz b (Finset.mem_filter.mpr ⟨hbW, hbz⟩) a ha).trans haj
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hbW, hbj⟩, hbz⟩
      rw [he, hcol z hz, ite_eq_left hzU]
    · have he : V.filter (fun a => Adj (cross y a) z) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨haV, haz⟩ := Finset.mem_filter.mp ha
        obtain ⟨haW, haj⟩ := Finset.mem_filter.mp haV
        exact hzU (Finset.mem_filter.mpr
          ⟨hz, a, Finset.mem_filter.mpr ⟨haW, haz⟩, haj⟩)
      simp [he, hzU]
  have hfixed : 5 = 2 * U.card := by
    calc
      5 = ∑ a ∈ V, (F a).card := by
        calc
          5 = ∑ _a ∈ V, 1 := by simp [hVc]
          _ = _ := Finset.sum_congr rfl (fun a ha =>
            (hrow a (Finset.mem_filter.mp ha).1).symm)
      _ = ∑ z ∈ T, (V.filter (fun a => Adj (cross y a) z)).card :=
        count_swap V T (fun a z => Adj (cross y a) z)
      _ = ∑ z ∈ T, if z ∈ U then 2 else 0 := Finset.sum_congr rfl hfiber
      _ = 2 * U.card := by
        have hUT : T ∩ U = U :=
          Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
        simp [hUT, Nat.mul_comm]
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubeFiveNeighborGap
