/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4TightStarObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4TightStarObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Obstructions for the tight stars of the normalized K4 projection in Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import Mathlib.Combinatorics.SimpleGraph.Matching
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SingletonCutObstructions

/-! Singleton-cut obstructions for the normalized ten-pattern projection. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4TightStarObstruction

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open Q9FourFiberSpectrum (leftProjection)
open Q9TenPatternIncidence (tenProjection vertexCode midpointCode incidence potential endpoints midpoint_cut)
open scoped Matrix
open Q9SignedProjection (join fiber signedRow)
open Q9K4CutBalance
open private countIf label_contributions even_degree nonzero_iff_mem singletonSupport_card
  evenCount_eq_four_imp from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private flip_join_right from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private abs_prefixSign from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum

private theorem indicator_sum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ x, countIf (p x)) = ((univ.filter p).card : ℤ) := by
  simp [countIf]

private theorem occupied_mul_countIf (a : ℤ) (p : Prop) [Decidable p] :
    occupied a * countIf p = countIf (a ≠ 0 ∧ p) := by
  by_cases h : a = 0 <;> by_cases hp : p <;> simp [occupied, countIf, h, hp]

private theorem active_center_card (z : Q 9 → ℤ) (i : Fin 4) :
    activeCenters z i = ((univ.filter fun y =>
      evenLabel z i y ≠ 0 ∧ |cScaled z i y| = 3).card : ℤ) := by
  simp only [activeCenters, occupied_mul_countIf, indicator_sum]

private theorem partner_card (z : Q 9 → ℤ) (i : Fin 4) :
    activePartners z i = ((univ.filter fun y =>
      evenLabel z i y ≠ 0 ∧ (oddCount z y = 3 ∧ |cScaled z i y| ≠ 3)).card : ℤ) := by
  simp only [activePartners, occupied_mul_countIf, indicator_sum]

private theorem balanced_card (z : Q 9 → ℤ) (i : Fin 4) :
    activeBalanced z i = ((univ.filter fun y =>
      evenLabel z i y ≠ 0 ∧ oddCount z y = 4).card : ℤ) := by
  simp only [activeBalanced, occupied_mul_countIf, indicator_sum]

private theorem label_card (z : Q 9 → ℤ) (i : Fin 4) :
    labelCount z i = ((univ.filter fun y => evenLabel z i y ≠ 0).card : ℤ) := by
  simp only [labelCount, show ∀ a : ℤ, occupied a = countIf (a ≠ 0) from
    fun a => by by_cases h : a = 0 <;> simp [h, occupied, countIf], indicator_sum]

private theorem odd_cases {z : Q 9 → ℤ}
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (y : Q 5) : oddCount z y = 0 ∨ oddCount z y = 3 ∨ oddCount z y = 4 := by
  rcases hlocal y with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem sum_label_counts (z : Q 9 → ℤ) :
    (∑ i, labelCount z i) = ∑ y, evenCount (fun i => evenLabel z i y) := by
  simp only [labelCount, evenCount]
  exact sum_comm

private theorem singleton_zero_impossible {z : Q 9 → ℤ}
    (h24 : (∑ y, evenCount (fun i => evenLabel z i y)) = 24)
    (hpartner : ∀ i, activeBalanced z i ≤ 2 * activePartners z i)
    (hcount : ∀ i, labelCount z i = activeCenters z i + activePartners z i + activeBalanced z i)
    (hcenter : ∀ i, 3 * singletonCenters z i ≤ singletons z)
    (hs : singletons z = 0) : False := by
  have hthree (y : Q 5) : oddCount z y ≠ 3 := by
    have h := single_le_sum (f := fun y => countIf (oddCount z y = 3))
      (fun _ _ => by unfold countIf; split <;> omega) (mem_univ y)
    change _ ≤ singletons z at h
    intro hy
    simp [hy, hs, countIf] at h
  have hall (i : Fin 4) : labelCount z i = 0 := by
    have hl : activePartners z i = 0 := by simp [activePartners, countIf, hthree]
    have hm : activeCenters z i ≤ singletonCenters z i :=
      sum_le_sum (fun y _ => by unfold occupied countIf; split <;> split <;> omega)
    have hmn : 0 ≤ activeCenters z i := by rw [active_center_card]; positivity
    have hp : 0 ≤ activeBalanced z i := by rw [balanced_card]; positivity
    have := hpartner i
    have := hcount i
    have := hcenter i
    omega
  simpa [hall, h24] using sum_label_counts z

private theorem flip_inj {n : ℕ} (x : Q n) : Function.Injective (flip x) := by
  intro i j he
  by_contra hne
  have h := congrFun he i
  cases hx : x i <;> simp [BalancedCriticalSpectrum.flip, hne, hx] at h

private theorem card_ge_eight_of_suffix_degree_two {C : Finset (Q 9)} (hb : IsBalanced C)
    (a : Q 4) (P : Finset (Q 5)) (hne : P.Nonempty)
    (hmem : ∀ y ∈ P, join a y ∈ C)
    (hdeg : ∀ y ∈ P, ((univ : Finset (Fin 5)).filter fun d => flip y d ∈ P).card = 2) :
    8 ≤ P.card := by
  classical
  let G := (hypercube 5).induce (P : Set (Q 5))
  have degree_two (v : (P : Set (Q 5))) : G.degree v = 2 := by
    rw [← hdeg v v.property, ← SimpleGraph.card_neighborFinset_eq_degree]
    symm
    apply card_bij (fun d hd => ⟨flip v.val d, (mem_filter.mp hd).2⟩)
    · intro d hd
      exact (G.mem_neighborFinset _ _).mpr (BalancedCriticalSpectrum.flip_adj _ _)
    · intro d hd e he hh
      exact flip_inj v.val (congrArg Subtype.val hh)
    · intro w hw
      have hadj : (hypercube 5).Adj v.val w.val := (G.mem_neighborFinset _ _).mp hw
      obtain ⟨d, hd⟩ := adjacent_exists_flip hadj
      exact ⟨d, mem_filter.mpr ⟨mem_univ _, hd ▸ w.property⟩, Subtype.ext hd.symm⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [SimpleGraph.ncard_neighborSet, degree_two]
  obtain ⟨y, hy⟩ := hne
  let v : (P : Set (Q 5)) := ⟨y, hy⟩
  have hv : v ∈ (G.connectedComponentMk v).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hn : (G.neighborSet v).Nonempty := SimpleGraph.degree_pos_iff_nonempty.mp (by
    rw [degree_two]; decide)
  obtain ⟨p, hp, _⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  let F : G →g (hypercube 9).induce (C : Set (Q 9)) :=
    ⟨fun w => ⟨join a w.val, hmem w.val w.property⟩, by
      intro u w huw
      obtain ⟨d, hd⟩ := adjacent_exists_flip (show (hypercube 5).Adj u.val w.val from huw)
      change (hypercube 9).Adj (join a u.val) (join a w.val)
      rw [hd, ← flip_join_right]
      exact BalancedCriticalSpectrum.flip_adj _ _⟩
  have hF : Function.Injective F := by
    intro u w h
    apply Subtype.ext
    funext d
    have he := congrArg (fun x : (C : Set (Q 9)) => x.val (d.natAdd 4)) h
    simpa [F, join] using he
  have hcycle := hp.map hF
  have hg := SimpleGraph.le_egirth.mp (BalancedCubeGirth.eight_le_egirth C hb) _ _ hcycle
  have hlength : 8 ≤ p.length := by
    rw [SimpleGraph.Walk.length_map] at hg
    exact_mod_cast hg
  have ht := hp.isPath_tail.length_lt
  rw [SimpleGraph.Walk.length_tail] at ht
  have hcard : Fintype.card (P : Set (Q 5)) = P.card :=
    (Fintype.card_congr (Equiv.refl {x // x ∈ P})).trans (Fintype.card_coe P)
  rw [hcard] at ht
  omega

private theorem partner_cycle_bound {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hb : IsBalanced C)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0)
    (hdeg : ∀ i y, evenLabel z i y ≠ 0 →
      evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y)
    (i : Fin 4) (hp : activeBalanced z i = 0) (hl : 0 < activePartners z i) :
    8 ≤ activePartners z i := by
  let P := (univ : Finset (Q 5)).filter fun y =>
    evenLabel z i y ≠ 0 ∧ (oddCount z y = 3 ∧ |cScaled z i y| ≠ 3)
  have hP : activePartners z i = (P.card : ℤ) := partner_card z i
  have hPm (w : Q 5) : w ∈ P ↔
      evenLabel z i w ≠ 0 ∧ (oddCount z w = 3 ∧ |cScaled z i w| ≠ 3) := by simp [P]
  have hD (w : Q 5) : evenLabel z i w ≠ 0 → oddCount z w = 3 := by
    intro hw
    rcases odd_cases hlocal w with h | h | h
    · exact (hw (hzero w h i)).elim
    · exact h
    · have he : w ∈ univ.filter (fun w => evenLabel z i w ≠ 0 ∧ oddCount z w = 4) :=
          mem_filter.mpr ⟨mem_univ _, hw, h⟩
      have hc := card_pos.mpr ⟨w, he⟩
      rw [balanced_card] at hp
      omega
  have hcenter (w : Q 5) (hw : evenLabel z i w ≠ 0) (hc' : |cScaled z i w| = 3) :
      evenVerticalDegree z i w = 0 := by
    have h := (label_contributions (i := i) (hlocal w) (fun h => hzero w h i)).2.2
    simp [hw, hc', hD w hw, occupied, countIf] at h
    rw [hdeg i w hw, h]
    norm_num
  have hdegP (w : Q 5) (hw : w ∈ P) :
      ((univ : Finset (Fin 5)).filter fun d => flip w d ∈ P).card = 2 := by
    obtain ⟨ha, ho, hc'⟩ := (hPm w).mp hw
    have hprod := (label_contributions (i := i) (hlocal w) (fun h => hzero w h i)).2.2
    simp [ha, ho, hc', occupied, countIf] at hprod
    have he (d : Fin 5) : flip w d ∈ P ↔ evenLabel z i (flip w d) ≠ 0 := by
      refine ⟨fun hd => ((hPm _).mp hd).1, fun hd => (hPm _).mpr ⟨hd, hD _ hd, ?_⟩⟩
      intro hc''
      have hn := hcenter (flip w d) hd hc''
      have hterm := single_le_sum
        (f := fun t => occupied (evenLabel z i (flip (flip w d) t)))
        (fun _ _ => by unfold occupied; split <;> omega) (mem_univ d)
      change _ ≤ evenVerticalDegree z i (flip w d) at hterm
      simp [hn, ha, occupied] at hterm
    have h := hdeg i w ha
    rw [hprod] at h
    unfold evenVerticalDegree at h
    have hs' : (∑ d : Fin 5, occupied (evenLabel z i (flip w d))) =
        ((univ.filter fun d => flip w d ∈ P).card : ℤ) := by
      rw [← indicator_sum]
      apply sum_congr rfl
      intro d _
      by_cases hd : flip w d ∈ P
      · simp [hd, (he d).mp hd, countIf, occupied]
      · simp [hd, not_ne_iff.mp (mt (he d).mpr hd), countIf, occupied]
    omega
  have hnon : P.Nonempty := card_pos.mp (by omega)
  have hlarge := card_ge_eight_of_suffix_degree_two hb (pattern (vertexCode i)) P hnon
    (fun w hw => (nonzero_iff_mem hu hz _).mp ((hPm w).mp hw).1) hdegP
  omega

private theorem singleton_sixteen_impossible {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hb : IsBalanced C)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hc : ∀ i y, signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0)
    (hdeg : ∀ i y, evenLabel z i y ≠ 0 →
      evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y)
    (h24 : (∑ y, evenCount (fun i => evenLabel z i y)) = 24)
    (hcounts : ∀ i, labelCount z i = activeCenters z i + activePartners z i + activeBalanced z i ∧
      3 * activeCenters z i + activePartners z i + 2 * activeBalanced z i = 12 ∧
      activeCenters z i - activePartners z i = 4 * singletonCenters z i - singletons z)
    (hsb : 3 * singletons z + 4 * balancedCuts z = 48)
    (hs : singletons z = 16) : False := by
  have hb0 : balancedCuts z = 0 := by omega
  have hfour (y : Q 5) : oddCount z y ≠ 4 := by
    have h := single_le_sum (f := fun y => countIf (oddCount z y = 4))
      (fun _ _ => by unfold countIf; split <;> omega) (mem_univ y)
    change _ ≤ balancedCuts z at h
    intro hy
    simp [hy, hb0, countIf] at h
  have hp (i : Fin 4) : activeBalanced z i = 0 := by simp [activeBalanced, countIf, hfour]
  have hcut (i : Fin 4) (y : Q 5) :
      |cScaled z i y| ≤ 1 + 2 * countIf (|cScaled z i y| = 3) := by
    rcases hlocal y with ⟨hc0, _, _⟩ | ⟨j, sign, _, hcj, _⟩ | ⟨h, _⟩
    · rw [show cScaled z i y = 0 from hc0 i]; norm_num [countIf]
    · rw [show cScaled z i y = _ from hcj i]
      cases sign <;> by_cases hij : i = j <;> norm_num [hij, countIf]
    · exact (hfour y h).elim
  have hlabels (i : Fin 4) : labelCount z i = 4 := by
    obtain ⟨hn, hpair, hdiff⟩ := hcounts i
    rw [hp] at hn hpair
    have hinactive : activeCenters z i = singletonCenters z i - 1 := by omega
    obtain ⟨y, hy, hcy⟩ : ∃ y, evenLabel z i y = 0 ∧ |cScaled z i y| = 3 := by
      by_contra! h
      have he : activeCenters z i = singletonCenters z i := by
        apply sum_congr rfl
        intro y _
        by_cases hc' : |cScaled z i y| = 3
        · have he := fun hy => h y hy hc'
          simp [hc', show evenLabel z i y ≠ 0 from he, occupied, countIf]
        · simp [hc', countIf]
      omega
    have hself (d : Fin 5) : flip y d ≠ y := (hypercube 5).ne_of_adj
      (BalancedCriticalSpectrum.flip_adj y d) |>.symm
    have hnear : (∑ d : Fin 5, countIf (|cScaled z i (flip y d)| = 3)) + 1 ≤
        singletonCenters z i := by
      let D := (univ : Finset (Fin 5)).filter fun d => |cScaled z i (flip y d)| = 3
      let S := (univ : Finset (Q 5)).filter fun w => |cScaled z i w| = 3
      have hsub : D.image (flip y) ⊆ S.erase y := by
        intro w hw
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hw
        exact mem_erase.mpr ⟨hself d, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hd).2⟩⟩
      have hle := card_le_card hsub
      rw [card_image_of_injective _ (flip_inj y), card_erase_of_mem
        (show y ∈ S from mem_filter.mpr ⟨mem_univ _, hcy⟩)] at hle
      rw [singletonCenters, indicator_sum, indicator_sum]
      change (D.card : ℤ) + 1 ≤ (S.card : ℤ)
      have : 0 < S.card := card_pos.mpr ⟨y, mem_filter.mpr ⟨mem_univ _, hcy⟩⟩
      omega
    have hrow9 : |signedRow (cScaled z i) y| = 9 := by rw [hc, hy]; simp [abs_mul, hcy]
    have hrow_le : |signedRow (cScaled z i) y| ≤
        ∑ d : Fin 5, (1 + 2 * countIf (|cScaled z i (flip y d)| = 3)) := by
      unfold signedRow
      refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
      simpa [abs_mul, abs_prefixSign] using hcut i (flip y d)
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, mul_one, hrow9] at hrow_le
    have hsmall : activePartners z i ≤ 6 := by omega
    have hl0 : activePartners z i = 0 := by
      have hnon : 0 ≤ activePartners z i := by rw [partner_card]; positivity
      by_contra h
      have := partner_cycle_bound hb hu hz hlocal hzero hdeg i (hp i) (by omega)
      omega
    omega
  have h := sum_label_counts z
  simp [h24, hlabels] at h

private theorem singleton_centers_sum {z : Q 9 → ℤ}
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y)) :
    (∑ i, singletonCenters z i) = singletons z := by
  unfold singletonCenters singletons
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rcases hlocal y with ⟨hc, ho, _⟩ | ⟨i, sign, ho, hc, _⟩ | ⟨ho, hc, _⟩
  · simp [ho, hc, countIf]
  · have he (j : Fin 4) : |cScaled z j y| = 3 ↔ j = i := by
      rw [show cScaled z j y = _ from hc j]
      cases sign <;> by_cases h : j = i <;> norm_num [h]
    simp [ho, he, countIf]
  · have he (i : Fin 4) : |cScaled z i y| ≠ 3 := by
      rcases hc i with h | h <;> norm_num [show cScaled z i y = _ from h]
    simp [ho, he, countIf]

private theorem eight_label_counts {z : Q 9 → ℤ}
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hs : singletons z = 8)
    (hcounts : ∀ i, activeCenters z i ≤ singletonCenters z i ∧
      activeCenters z i - activePartners z i = 4 * singletonCenters z i - singletons z ∧
      activeBalanced z i = 6 - singletons z / 2 + 2 * (singletonCenters z i - activeCenters z i) ∧
      3 * singletonCenters z i ≤ singletons z ∧ activeBalanced z i ≤ 2 * activePartners z i) :
    ∀ i, singletonCenters z i = 2 ∧ activeCenters z i = 2 ∧
      activePartners z i = 2 ∧ activeBalanced z i = 2 := by
  have hsum := singleton_centers_sum hlocal
  have hall (i : Fin 4) : singletonCenters z i ≤ 2 := by
    have := (hcounts i).2.2.2.1
    omega
  have heq (i : Fin 4) : singletonCenters z i = 2 := by
    have h := sum_eq_zero_iff_of_nonneg (s := (univ : Finset (Fin 4)))
      (f := fun j => 2 - singletonCenters z j) (fun j _ => sub_nonneg.mpr (hall j))
    have h0 : (∑ j : Fin 4, (2 - singletonCenters z j)) = 0 := by
      simp [sum_sub_distrib, hsum, hs]
    have := h.mp h0 i (mem_univ i)
    omega
  intro i
  obtain ⟨hm, hdiff, hp, _, hbound⟩ := hcounts i
  have hi := heq i
  omega

private theorem active_centers_bound (z : Q 9 → ℤ) (i : Fin 4) :
    activeCenters z i ≤ singletonCenters z i :=
  sum_le_sum (fun _ _ => by unfold occupied countIf; split <;> split <;> omega)

private theorem twelve_label_counts {z : Q 9 → ℤ}
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hs : singletons z = 12) (hcenter : ∀ i, singletonCenters z i ≤ 3)
    (hsb : 3 * singletons z + 4 * balancedCuts z = 48)
    (hcounts : ∀ i, activeCenters z i - activePartners z i =
      4 * singletonCenters z i - singletons z ∧
      activeBalanced z i = 6 - singletons z / 2 + 2 * (singletonCenters z i - activeCenters z i)) :
    ∀ i, singletonCenters z i = 3 ∧ activeCenters z i = activePartners z i ∧
      (activeBalanced z i = 0 ∧ activePartners z i = 3 ∨ activeBalanced z i = 2) := by
  have hsum := singleton_centers_sum hlocal
  have heq (i : Fin 4) : singletonCenters z i = 3 := by
    have h := sum_eq_zero_iff_of_nonneg (s := (univ : Finset (Fin 4)))
      (f := fun j => 3 - singletonCenters z j) (fun j _ => sub_nonneg.mpr (hcenter j))
    have h0 : (∑ j : Fin 4, (3 - singletonCenters z j)) = 0 := by
      simp [sum_sub_distrib, hsum, hs]
    have := h.mp h0 i (mem_univ i)
    omega
  intro i
  have hbound : activeBalanced z i ≤ balancedCuts z :=
    sum_le_sum (fun _ _ => by unfold occupied countIf; split <;> split <;> omega)
  have hm := active_centers_bound z i
  have hi := heq i
  obtain ⟨hdiff, hp⟩ := hcounts i
  omega


open Q5SmallParitySupport (bitParity neighborParity oddNeighborImage)
open private direction_injective bitParity_flip evenWord evenWord_decode bitParity_xor
  translate mem_translate card_translate oddNeighborImage_translate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport

private theorem small_odd_image_bound (X : Finset (BitVec 5)) (p : Bool)
    (hp : ∀ x ∈ X, bitParity x = p) (hn : 1 ≤ X.card) (hc : X.card ≤ 3) :
    X.card + 4 ≤ (oddNeighborImage X).card := by
  have he (a b : BitVec 5) (h : bitParity b = bitParity a) :
      evenWord ((b ^^^ a).setWidth 4).toFin = b ^^^ a :=
    evenWord_decode _ (by simp [bitParity_xor, h])
  have hx (a x y : BitVec 5) : x ^^^ a = y ↔ x = y ^^^ a := by
    rw [← BitVec.xor_left_inj a (x := x) (y := y ^^^ a)]
    simp [BitVec.xor_assoc]
  have hcard : X.card = 1 ∨ X.card = 2 ∨ X.card = 3 := by omega
  rcases hcard with h | h | h
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h
    rw [card_singleton]
    have hnorm : translate a ({a} : Finset (BitVec 5)) = {0} := by
      ext x
      simp [mem_translate, hx]
    rw [← card_translate a (oddNeighborImage {a}), ← oddNeighborImage_translate, hnorm]
    decide
  · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h
    have hnorm : translate a ({a, b} : Finset (BitVec 5)) = {0, b ^^^ a} := by
      ext x
      simp [mem_translate, hx]
    rw [h, ← card_translate a (oddNeighborImage {a, b}), ← oddNeighborImage_translate, hnorm]
    have table : ∀ j : Fin 16, evenWord j ≠ 0 →
        6 ≤ (oddNeighborImage {0, evenWord j}).card := by decide
    have ht := table ((b ^^^ a).setWidth 4).toFin
    rw [he a b ((hp b (by simp)).trans (hp a (by simp)).symm)] at ht
    exact ht (by simpa [BitVec.xor_eq_zero_iff] using hab.symm)
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp h
    have hnorm : translate a ({a, b, c} : Finset (BitVec 5)) = {0, b ^^^ a, c ^^^ a} := by
      ext x
      simp [mem_translate, hx]
    rw [h, ← card_translate a (oddNeighborImage {a, b, c}), ← oddNeighborImage_translate, hnorm]
    have table : ∀ j k : Fin 16, evenWord j ≠ 0 → evenWord k ≠ 0 →
        evenWord j ≠ evenWord k → 7 ≤ (oddNeighborImage {0, evenWord j, evenWord k}).card := by
      decide +kernel
    have ht := table ((b ^^^ a).setWidth 4).toFin ((c ^^^ a).setWidth 4).toFin
    rw [he a b ((hp b (by simp)).trans (hp a (by simp)).symm),
      he a c ((hp c (by simp)).trans (hp a (by simp)).symm)] at ht
    exact ht (by simpa [BitVec.xor_eq_zero_iff] using hab.symm)
      (by simpa [BitVec.xor_eq_zero_iff] using hac.symm)
      (fun hh => hbc ((BitVec.xor_left_inj a).mp hh))

private abbrev paritySide (X : Finset (BitVec 5)) (p : Bool) :=
  X.filter fun x => bitParity x = p

private theorem neighborParity_from_side (X : Finset (BitVec 5)) (x : BitVec 5) :
    neighborParity X x = neighborParity (paritySide X (!bitParity x)) x := by
  have he (d : Fin 5) : (x ^^^ BitVec.twoPow 5 d.val) ∈ paritySide X (!bitParity x) ↔
      (x ^^^ BitVec.twoPow 5 d.val) ∈ X := by simp [bitParity_flip]
  unfold neighborParity
  simp only [show (1 : BitVec 5) = BitVec.twoPow 5 (0 : Fin 5).val from rfl,
    show (2 : BitVec 5) = BitVec.twoPow 5 (1 : Fin 5).val from rfl,
    show (4 : BitVec 5) = BitVec.twoPow 5 (2 : Fin 5).val from rfl,
    show (8 : BitVec 5) = BitVec.twoPow 5 (3 : Fin 5).val from rfl,
    show (16 : BitVec 5) = BitVec.twoPow 5 (4 : Fin 5).val from rfl, he]

private theorem odd_image_side (X : Finset (BitVec 5)) (p : Bool) :
    oddNeighborImage (paritySide X p) = paritySide (oddNeighborImage X) (!p) := by
  ext x
  simp only [Q5SmallParitySupport.mem_oddNeighborImage, mem_filter]
  by_cases h : bitParity x = !p
  · have hp : !bitParity x = p := by simp [h]
    simp [h, neighborParity_from_side X x, hp]
  · have hz (d : Fin 5) : (x ^^^ BitVec.twoPow 5 d.val) ∉ paritySide X p := by
      intro hx
      apply h
      have he := (mem_filter.mp hx).2
      rw [bitParity_flip] at he
      cases p <;> cases bitParity x <;> simp_all
    unfold neighborParity
    have h0 : x ^^^ 1 ∉ paritySide X p := hz 0
    have h1 : x ^^^ 2 ∉ paritySide X p := hz 1
    have h2 : x ^^^ 4 ∉ paritySide X p := hz 2
    have h3 : x ^^^ 8 ∉ paritySide X p := hz 3
    have h4 : x ^^^ 16 ∉ paritySide X p := hz 4
    simp only [h0, h1, h2, h3, h4, decide_false,
      Bool.xor_false, Bool.false_eq_true, h, and_false]

private theorem parity_card_split (X : Finset (BitVec 5)) :
    (paritySide X false).card + (paritySide X true).card = X.card := by
  simpa only [Bool.not_eq_false] using
    (card_filter_add_card_filter_not (s := X) (fun x => bitParity x = false))

private theorem quartet_one_parity {X : Finset (BitVec 5)}
    (hX : X.card = 4) (himage : (oddNeighborImage X).card = 8) :
    ∃ p : Bool, ∀ x ∈ X, bitParity x = p := by
  have hsum := parity_card_split X
  by_cases h0 : (paritySide X false).card = 0
  · refine ⟨true, fun x hx => ?_⟩
    cases he : bitParity x
    · have hm : x ∈ paritySide X false := mem_filter.mpr ⟨hx, he⟩
      simp [card_eq_zero.mp h0] at hm
    · rfl
  by_cases h1 : (paritySide X true).card = 0
  · refine ⟨false, fun x hx => ?_⟩
    cases he : bitParity x
    · rfl
    · have hm : x ∈ paritySide X true := mem_filter.mpr ⟨hx, he⟩
      simp [card_eq_zero.mp h1] at hm
  have hE := small_odd_image_bound (paritySide X false) false
    (fun _ hx => (mem_filter.mp hx).2) (by omega) (by omega)
  have hO := small_odd_image_bound (paritySide X true) true
    (fun _ hx => (mem_filter.mp hx).2) (by omega) (by omega)
  rw [odd_image_side] at hE hO
  simp only [Bool.not_true, Bool.not_false] at hE hO
  have hsum' := parity_card_split (oddNeighborImage X)
  omega


open private xor_table binary label_values local_pairing from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance

private abbrev suffixParity (y : Q 5) : Bool := bitParity ((cubeBitVec 5).symm y)

private theorem flip_word (x : BitVec 5) (d : Fin 5) :
    cubeBitVec 5 (x ^^^ BitVec.twoPow 5 d.val) = flip (cubeBitVec 5 x) d := by
  have hp : ∀ d : Fin 5, BitVec.twoPow 5 d.val = BitVec.ofNat 5 (2 ^ d.val) := by decide
  rw [hp, cubeBitVec_xor_single]
  rfl

private theorem suffixParity_flip (y : Q 5) (d : Fin 5) :
    suffixParity (flip y d) = !suffixParity y := by
  obtain ⟨x, rfl⟩ := (cubeBitVec 5).surjective y
  simp only [← flip_word, suffixParity, Equiv.symm_apply_apply, bitParity_flip]

private theorem even_occupation_parity {z : Q 9 → ℤ}
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0)
    (hdeg : ∀ i y, evenLabel z i y ≠ 0 →
      evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y)
    (h24 : (∑ y, evenCount (fun i => evenLabel z i y)) = 24) (p : Bool) :
    (∑ y : Q 5, if suffixParity y = p then evenCount (fun i => evenLabel z i y) else 0) = 12 := by
  let A : Q 5 → ℤ := fun y => evenCount (fun i => evenLabel z i y)
  let a : Fin 4 → Q 5 → ℤ := fun i y => occupied (evenLabel z i y)
  have hpoint (y : Q 5) :
      (∑ i, a i y * ∑ d : Fin 5, a i (flip y d)) = A y := by
    have ht (i : Fin 4) : a i y * (∑ d : Fin 5, a i (flip y d)) =
        3 * a i y - evenLabel z i y * cScaled z i y := by
      by_cases h : evenLabel z i y = 0
      · simp [a, occupied, h]
      · change a i y * evenVerticalDegree z i y = _
        simp [a, occupied, h, hdeg i y h]
    simp only [ht, sum_sub_distrib, ← mul_sum]
    have h := local_pairing (hlocal y)
    change (∑ i, evenLabel z i y * cScaled z i y) = if oddCount z y = 0 then 0 else 2 * A y at h
    by_cases ho : oddCount z y = 0
    · simp [a, A, evenCount, hzero y ho, occupied]
    · simp [ho] at h
      change 3 * A y - _ = A y
      omega
  let F (b : Bool) (y : Q 5) (i : Fin 4) (d : Fin 5) : ℤ :=
    if suffixParity y = b then a i y * a i (flip y d) else 0
  have hsum (b : Bool) :
      (∑ y, if suffixParity y = b then A y else 0) = ∑ d, ∑ i, ∑ y, F b y i d := by
    calc
      _ = ∑ y, ∑ i, ∑ d, F b y i d := by
        refine sum_congr rfl fun y _ => ?_
        rw [← hpoint]
        by_cases h : suffixParity y = b <;> simp [F, h, mul_sum]
      _ = ∑ i, ∑ y, ∑ d, F b y i d := sum_comm
      _ = ∑ i, ∑ d, ∑ y, F b y i d := sum_congr rfl fun _ _ => sum_comm
      _ = _ := sum_comm
  have hswap (i : Fin 4) (d : Fin 5) : (∑ y, F p y i d) = ∑ y, F (!p) y i d := by
    let e : Q 5 ≃ Q 5 := ⟨(flip · d), (flip · d), (BalancedCriticalSpectrum.flip_flip · d), (BalancedCriticalSpectrum.flip_flip · d)⟩
    apply Fintype.sum_equiv e
    intro y
    change F p y i d = F (!p) (flip y d) i d
    simp [F, suffixParity_flip, BalancedCriticalSpectrum.flip_flip, mul_comm]
  have heq : (∑ y, if suffixParity y = p then A y else 0) =
      ∑ y, if suffixParity y = !p then A y else 0 := by
    rw [hsum, hsum]
    exact sum_congr rfl (fun d _ => sum_congr rfl (fun i _ => hswap i d))
  have htotal : (∑ y, if suffixParity y = p then A y else 0) +
      (∑ y, if suffixParity y = !p then A y else 0) = 24 := by
    rw [← sum_add_distrib, ← h24]
    exact sum_congr rfl (fun y _ => by cases p <;> cases suffixParity y <;> simp [A])
  change (∑ y, if suffixParity y = p then A y else 0) = 12
  omega

private theorem twelve_center_four_impossible {z : Q 9 → ℤ}
    (hunit : ∀ i y, evenLabel z i y = 0 ∨ evenLabel z i y = 1 ∨ evenLabel z i y = -1)
    (hrows : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
      signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0)
    (htwo : ∀ y, evenCount (fun i => evenLabel z i y) = 0 ∨
      evenCount (fun i => evenLabel z i y) = 2)
    (hpar : ∀ p : Bool, (∑ y : Q 5, if suffixParity y = p then
      evenCount (fun i => evenLabel z i y) else 0) = 12)
    (i : Fin 4) (hs : singletons z = 12) (hn : labelCount z i = 4)
    (hm : activeCenters z i = 4) : False := by
  letI : Fintype (BitVec 5) := Fintype.ofEquiv (Q 5) (cubeBitVec 5).symm
  let X := univ.filter fun x : BitVec 5 => evenLabel z i (cubeBitVec 5 x) ≠ 0
  let M := X.filter fun x => |cScaled z i (cubeBitVec 5 x)| = 3
  let S := singletonSupport z
  have hX : X.card = 4 := by
    rw [label_card] at hn
    have h := Fintype.sum_equiv (cubeBitVec 5)
      (fun x => countIf (evenLabel z i (cubeBitVec 5 x) ≠ 0))
      (fun y => countIf (evenLabel z i y ≠ 0)) (fun _ => rfl)
    simp only [indicator_sum] at h
    change (X.card : ℤ) = _ at h
    exact_mod_cast h.trans hn
  have hM : M.card = 4 := by
    rw [active_center_card] at hm
    have h := Fintype.sum_equiv (cubeBitVec 5)
      (fun x => countIf (evenLabel z i (cubeBitVec 5 x) ≠ 0 ∧
        |cScaled z i (cubeBitVec 5 x)| = 3))
      (fun y => countIf (evenLabel z i y ≠ 0 ∧ |cScaled z i y| = 3)) (fun _ => rfl)
    simp only [indicator_sum] at h
    have hM' : M = univ.filter (fun x : BitVec 5 =>
        evenLabel z i (cubeBitVec 5 x) ≠ 0 ∧ |cScaled z i (cubeBitVec 5 x)| = 3) := by
      ext x
      simp [M, X, and_assoc]
    rw [← hM'] at h
    exact_mod_cast h.trans hm
  have hMX : M = X := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have hXS : X ⊆ S := by
    intro x hx
    have hc := (mem_filter.mp (show x ∈ M from hMX ▸ hx)).2
    rcases hlocal (cubeBitVec 5 x) with ⟨h0, _, _⟩ | ⟨_, _, h3, _⟩ | ⟨_, h4, _⟩
    · simp [show cScaled z i (cubeBitVec 5 x) = 0 from h0 i] at hc
    · simp only [S, singletonSupport, mem_filter, mem_univ, true_and]
      exact h3
    · rcases h4 i with h | h <;> norm_num [show cScaled z i (cubeBitVec 5 x) = _ from h] at hc
  have hodd : oddNeighborImage X = S \ X := by
    ext x
    rw [Q5SmallParitySupport.mem_oddNeighborImage]
    have hx (t : BitVec 5) : (occupied (evenLabel z i (cubeBitVec 5 t)) : ZMod 2) =
        binary (decide (t ∈ X)) := by
      by_cases h : evenLabel z i (cubeBitVec 5 t) = 0 <;> simp [binary, X, occupied, h]
    have hS : singletonIndicator z (cubeBitVec 5 x) = binary (decide (x ∈ S)) := by
      by_cases h : oddCount z (cubeBitVec 5 x) = 3 <;>
        simp [S, singletonSupport, singletonIndicator, binary, h]
    have hr := (singleton_parity_rows hunit hrows hlocal).1 i (cubeBitVec 5 x)
    simp only [← flip_word, hx, hS] at hr
    have ht : (∑ d : Fin 5, binary (decide (x ^^^ BitVec.twoPow 5 d.val ∈ X))) =
        binary (decide (x ∈ S \ X)) := by
      by_cases h : x ∈ X
      · have hs' : x ∈ S := hXS h
        simp only [h, hs', mem_sdiff, not_true_eq_false, and_false, decide_false,
          decide_true, binary, Bool.false_eq_true, ite_false, ite_true] at hr ⊢
        exact add_right_cancel (hr.trans (zero_add (1 : ZMod 2)).symm)
      · simpa only [h, mem_sdiff, not_false_eq_true, and_true, decide_false,
          binary, Bool.false_eq_true, ite_false, add_zero] using hr
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero] at ht
    have hf := xor_table _ _ _ _ _ _ (by simpa only [add_assoc] using ht)
    unfold neighborParity
    change (_ = true) ↔ x ∈ S \ X
    rw [show (decide (x ^^^ (1 : BitVec 5) ∈ X) ^^ decide (x ^^^ (2 : BitVec 5) ∈ X) ^^
      decide (x ^^^ (4 : BitVec 5) ∈ X) ^^ decide (x ^^^ (8 : BitVec 5) ∈ X) ^^
      decide (x ^^^ (16 : BitVec 5) ∈ X)) = decide (x ∈ S \ X) from hf.symm]
    exact decide_eq_true_iff
  have hS : S.card = 12 := by exact_mod_cast (singletonSupport_card z).trans hs
  have himage : (oddNeighborImage X).card = 8 := by rw [hodd, card_sdiff_of_subset hXS, hS, hX]
  obtain ⟨p, hp⟩ := quartet_one_parity hX himage
  let A (x : BitVec 5) := evenCount (fun j => evenLabel z j (cubeBitVec 5 x))
  have hsum := Fintype.sum_equiv (cubeBitVec 5)
    (fun x => if bitParity x = p then A x else 0)
    (fun y => if suffixParity y = p then evenCount (fun j => evenLabel z j y) else 0)
    (fun x => by simp [A, suffixParity])
  rw [hpar] at hsum
  have hterm (x : BitVec 5) : (if bitParity x = p then A x else 0) =
      2 * countIf (x ∈ X) := by
    by_cases hx : x ∈ X
    · have ha : evenLabel z i (cubeBitVec 5 x) ≠ 0 := (mem_filter.mp hx).2
      have hle : 1 ≤ A x := by
        have hi := single_le_sum (f := fun j => occupied (evenLabel z j (cubeBitVec 5 x)))
          (fun _ _ => by unfold occupied; split <;> omega) (mem_univ i)
        simpa [ha, A, evenCount, occupied] using hi
      have hA := htwo (cubeBitVec 5 x)
      change A x = 0 ∨ A x = 2 at hA
      have ha2 : A x = 2 := hA.resolve_left (by omega)
      simp [hp x hx, ha2, hx, countIf]
    by_cases hpx : bitParity x = p
    · have ha : evenLabel z i (cubeBitVec 5 x) = 0 := by
        by_contra hh
        exact hx (mem_filter.mpr ⟨mem_univ _, hh⟩)
      have hneigh (d : Fin 5) : evenLabel z i (flip (cubeBitVec 5 x) d) = 0 := by
        by_contra h
        have hm : x ^^^ BitVec.twoPow 5 d.val ∈ X :=
          mem_filter.mpr ⟨mem_univ _, by rwa [flip_word]⟩
        have hh := hp _ hm
        rw [bitParity_flip, hpx] at hh
        cases p <;> contradiction
      have hrow := (hrows i (cubeBitVec 5 x)).1
      have hc : cScaled z i (cubeBitVec 5 x) = 0 := by
        simpa [signedRow, hneigh, ha] using hrow
      have hA : A x = 0 := by
        rcases hlocal (cubeBitVec 5 x) with ⟨_, h, _⟩ |
          ⟨j, sign, _, hj, _⟩ | ⟨_, hj, _⟩
        · simp [A, evenCount, hzero _ h, occupied]
        · have hh : cScaled z i (cubeBitVec 5 x) = _ := hj i
          rw [hc] at hh
          cases sign <;> by_cases h : i = j <;> norm_num [h] at hh
        · rcases hj i with h | h <;> simp [hc] at h
      simp [hpx, hx, hA, countIf]
    · simp [hpx, hx, countIf]
  simp only [hterm, ← mul_sum, indicator_sum, filter_mem_eq_inter, univ_inter] at hsum
  omega


private theorem singleton_twelve_impossible {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hb : IsBalanced C)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrows : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
      signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0)
    (hdeg : ∀ i y, evenLabel z i y ≠ 0 →
      evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y)
    (h24 : (∑ y, evenCount (fun i => evenLabel z i y)) = 24)
    (htwo : ∀ y, evenCount (fun i => evenLabel z i y) = 0 ∨
      evenCount (fun i => evenLabel z i y) = 2)
    (hsb : 3 * singletons z + 4 * balancedCuts z = 48)
    (hcounts : ∀ i, labelCount z i = 6 + singletons z / 2 - 2 * singletonCenters z i ∧
      activeCenters z i - activePartners z i = 4 * singletonCenters z i - singletons z ∧
      activeBalanced z i = 6 - singletons z / 2 + 2 * (singletonCenters z i - activeCenters z i) ∧
      3 * singletonCenters z i ≤ singletons z)
    (hs : singletons z = 12) : False := by
  have hunit (i : Fin 4) (y : Q 5) :
      evenLabel z i y = 0 ∨ evenLabel z i y = 1 ∨ evenLabel z i y = -1 :=
    label_values hu hz (join (pattern (vertexCode i)) y)
  have hcenter (i : Fin 4) : singletonCenters z i ≤ 3 := by
    obtain ⟨hn, hdiff, hp, hbound⟩ := hcounts i
    by_contra h
    have hi : singletonCenters z i = 4 := by omega
    have hm := active_centers_bound z i
    have hl : 0 ≤ activePartners z i := by rw [partner_card]; positivity
    exact twelve_center_four_impossible hunit hrows hlocal hzero htwo
      (even_occupation_parity hlocal hzero hdeg h24) i hs (by omega) (by omega)
  have hp (i : Fin 4) : activeBalanced z i = 2 := by
    rcases (twelve_label_counts hlocal hs hcenter hsb
        (fun j => ⟨(hcounts j).2.1, (hcounts j).2.2.1⟩) i).2.2 with ⟨hp, hl⟩ | h
    · have hbnd := partner_cycle_bound hb hu hz hlocal hzero hdeg i hp (by omega)
      omega
    · exact h
  have htotal : (∑ i, activeBalanced z i) ≤ 2 * balancedCuts z := by
    unfold activeBalanced balancedCuts
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun y _ => ?_
    rw [← sum_mul]
    change evenCount (fun i => evenLabel z i y) * countIf (oddCount z y = 4) ≤
      2 * countIf (oddCount z y = 4)
    by_cases ho : oddCount z y = 4
    · rcases htwo y with h | h <;> simp [countIf, ho, h]
    · simp [countIf, ho]
  simp [hp] at htotal
  omega


open Q5SharedSixLeaves (degree)
open Q5SingletonCutObstructions (adjacent eight_point_dichotomy)
open private adjacent_flip degree_filter degree_mod_two sum_degree_swap degree_translate
  parallelCarrier translate_eq_parallelCarrier from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SingletonCutObstructions

private theorem parallel_external_edges (d : Fin 5) (x y : BitVec 5)
    (hx : x ∉ parallelCarrier d) (hy : y ∉ parallelCarrier d)
    (hx' : 0 < degree (parallelCarrier d) x) (hy' : 0 < degree (parallelCarrier d) y)
    (hxy : adjacent x y) : y = x ^^^ BitVec.twoPow 5 d.val := by
  change x ^^^ y ∈ ({1, 2, 4, 8, 16} : Finset (BitVec 5)) at hxy
  exact (show ∀ (d : Fin 5) (i j : Fin 32),
    BitVec.ofFin i ∉ parallelCarrier d → BitVec.ofFin j ∉ parallelCarrier d →
    0 < degree (parallelCarrier d) (BitVec.ofFin i) →
    0 < degree (parallelCarrier d) (BitVec.ofFin j) →
    BitVec.ofFin i ^^^ BitVec.ofFin j ∈ ({1, 2, 4, 8, 16} : Finset (BitVec 5)) →
    BitVec.ofFin j = BitVec.ofFin i ^^^ BitVec.twoPow 5 d.val by decide +kernel) d x.toFin y.toFin hx hy hx' hy' hxy

private theorem eight_fiber_geometry {S B : Finset (BitVec 5)}
    (hS : S.card = 8) (hB : B.card = 6) (hdis : Disjoint S B)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x)
    (hdeg : ∀ x ∈ S, degree S x + 2 * degree B x = 5) :
    ∃ d : Fin 5, (∀ x ∈ S, ∀ j : Fin 5, x ^^^ BitVec.twoPow 5 j.val ∈ S ↔ j = d) ∧
      (∑ x ∈ S, degree B x) = 16 ∧
      ∀ x ∈ B, ∀ y ∈ B, adjacent x y → y = x ^^^ BitVec.twoPow 5 d.val := by
  rcases eight_point_dichotomy hS hpar with
    ⟨d, hflip, hsingle, hcap, hhigh⟩ | ⟨p, _, _, _, _, _, hCp, hLp, hC, hL, hout⟩
  · have hcross : (∑ x ∈ S, degree B x) = 16 := by
      have h : (∑ x ∈ S, degree B x) = ∑ _x ∈ S, 2 :=
        sum_congr rfl fun x hx => by
          have hd := hdeg x hx
          have hs := hsingle x hx
          omega
      simpa [hS] using h
    have hbdegree : ∀ x ∈ B, degree S x = 0 ∨ degree S x = 2 ∨ degree S x = 4 := by
      intro x hx
      have hn : x ∉ S := fun hs => disjoint_left.mp hdis hs hx
      have h := hcap x hn
      have hp := degree_mod_two S x
      rw [← hpar] at hp
      simp [hn] at hp
      omega
    let H := B.filter fun x => degree S x = 4
    have hH : H.card ≤ 2 := hhigh B hdis
    have hweight : (∑ x ∈ B, (2 + (if degree S x = 4 then 2 else 0))) ≤ 16 := by
      rw [sum_add_distrib, sum_const_nat (fun _ _ => rfl), hB]
      have hsum : (∑ x ∈ B, if degree S x = 4 then 2 else 0) = 2 * H.card := by
        classical
        rw [← sum_filter]
        simp [H, Nat.mul_comm]
      omega
    have hbound (x : BitVec 5) (hx : x ∈ B) :
        degree S x ≤ 2 + (if degree S x = 4 then 2 else 0) := by
      rcases hbdegree x hx with h | h | h <;> simp [h]
    have hpos (x : BitVec 5) (hx : x ∈ B) : 0 < degree S x := by
      by_contra! h
      have hlt := sum_lt_sum hbound ⟨x, hx, by simp [show degree S x = 0 by omega]⟩
      rw [← sum_degree_swap, hcross] at hlt
      omega
    obtain ⟨w, hw, hw4⟩ : ∃ w ∈ B, degree S w = 4 := by
      by_contra! h
      have hsum : (∑ x ∈ B, degree S x) ≤ ∑ _x ∈ B, 2 := by
        exact sum_le_sum (fun x hx => by
          have := hbound x hx
          simpa [h x hx] using this)
      rw [← sum_degree_swap, hcross] at hsum
      simp [hB] at hsum
    have hnorm := translate_eq_parallelCarrier hS
      (fun x hx => (hflip x hx d).mpr rfl) (fun hwS => disjoint_left.mp hdis hwS hw) hw4
    refine ⟨d, hflip, hcross, fun x hx y hy hxy => ?_⟩
    have hx' : x ^^^ w ∉ parallelCarrier d := by
      rw [← hnorm]
      simp [show x ∉ S from fun h => disjoint_left.mp hdis h hx]
    have hy' : y ^^^ w ∉ parallelCarrier d := by
      rw [← hnorm]
      simp [show y ∉ S from fun h => disjoint_left.mp hdis h hy]
    have hxy' : adjacent (x ^^^ w) (y ^^^ w) := by
      have hxor : (x ^^^ w) ^^^ (y ^^^ w) = x ^^^ y := by
        simp only [BitVec.xor_assoc, BitVec.xor_comm w (y ^^^ w)]
        simp [← BitVec.xor_assoc]
      simpa only [adjacent, hxor] using hxy
    have h := parallel_external_edges d (x ^^^ w) (y ^^^ w) hx' hy'
      (by simpa [← hnorm, degree_translate, BitVec.xor_assoc] using hpos x hx)
      (by simpa [← hnorm, degree_translate, BitVec.xor_assoc] using hpos y hy) hxy'
    apply (BitVec.xor_left_inj w).mp
    simpa only [BitVec.xor_assoc, BitVec.xor_comm w (BitVec.twoPow 5 d.val)] using h
  · let E := paritySide S p
    let O := paritySide S (!p)
    have hpart : Disjoint E O := by
      rw [disjoint_left]
      intro x hx hy
      have he := (mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2
      cases p <;> contradiction
    have hunion : E ∪ O = S := by
      ext x
      cases p <;> cases hx : bitParity x <;> simp [E, O, hx]
    have hsum : (∑ x ∈ S, degree B x) = 14 := by
      rw [← hunion, sum_union hpart]
      have he : (∑ x ∈ E, degree B x) = ∑ _x ∈ E, 1 := by
        exact sum_congr rfl fun x hx => by
          have := hdeg x (mem_filter.mp hx).1
          have := hC x hx
          omega
      have ho : (∑ x ∈ O, degree B x) = ∑ _x ∈ O, 2 := by
        exact sum_congr rfl fun x hx => by
          have := hdeg x (mem_filter.mp hx).1
          have := hL x hx
          omega
      rw [he, ho]
      simp [E, O, hCp, hLp]
    have hsum' : (∑ x ∈ B, degree S x) ≤ ∑ _x ∈ B, 2 :=
      sum_le_sum fun x hx => hout x (fun h => disjoint_left.mp hdis h hx)
    rw [← sum_degree_swap, hsum] at hsum'
    simp [hB] at hsum'


open Q9FourFiberSpectrum (fiber_and_signedRow_supported)
open BalancedCriticalSpectrum (directionEdges directionEndpoints direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private selected_term incidence_laplacian sum_support point projectionCode from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
open private flip_join_left sign_join_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private signed_row_blocks transpose_mulVec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence

private abbrev oddLabel (z : Q 9 → ℤ) (y : Q 5) (e : Fin 6) : ℤ :=
  fiber z y (pattern (midpointCode e))

private def oddOverlap (z : Q 9 → ℤ) (y w : Q 5) : ℤ :=
  ∑ e, occupied (oddLabel z y e) * occupied (oddLabel z w e)

private theorem oddOverlap_comm (z : Q 9 → ℤ) (y w : Q 5) :
    oddOverlap z y w = oddOverlap z w y :=
  sum_congr rfl fun _ _ => mul_comm _ _

private theorem oddOverlap_zero {z : Q 9 → ℤ} {y w : Q 5} (hy : oddCount z y = 0) :
    oddOverlap z y w = 0 := by
  have hz (e : Fin 6) : occupied (oddLabel z y e) = 0 := by
    have h := single_le_sum (f := fun e => occupied (oddLabel z y e))
      (fun _ _ => by unfold occupied; split <;> omega) (mem_univ e)
    change _ ≤ oddCount z y at h
    unfold occupied at h ⊢
    split <;> omega
  simp [oddOverlap, hz]

open Classical in
private theorem overlap_le_endpoints {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) (d : Fin 5) :
    (∑ y, oddOverlap z y (flip y d)) ≤ 2 * (directionEdges C (d.natAdd 4) : ℤ) := by
  let g (u : Q 9) : ℤ := countIf (flip u (d.natAdd 4) ∈ C)
  have hg : (∑ u ∈ C, g u) = 2 * (directionEdges C (d.natAdd 4) : ℤ) := by
    simp only [g, countIf, sum_boole]
    change ((directionEndpoints C (d.natAdd 4)).card : ℤ) = _
    rw [endpoint_card_twice]
    push_cast
    rfl
  rw [← hg, ← sum_support hP g]
  refine sum_le_sum fun y _ => ?_
  rw [Fintype.sum_sum_type]
  have hm : (∑ e, if point y (Sum.inr e) ∈ C then g (point y (Sum.inr e)) else 0) =
      oddOverlap z y (flip y d) := by
    unfold oddOverlap
    refine sum_congr rfl fun e _ => ?_
    simp only [point, projectionCode, Sum.elim_inr, g, flip_join_right]
    let u := join (pattern (midpointCode e)) y
    let w := join (pattern (midpointCode e)) (flip y d)
    change (if u ∈ C then countIf (w ∈ C) else 0) = occupied (z u) * occupied (z w)
    by_cases hu' : u ∈ C
    · by_cases hw : w ∈ C
      · simp [hu', hw, occupied, countIf, (nonzero_iff_mem hu hz _).mpr hu',
          (nonzero_iff_mem hu hz _).mpr hw]
      · simp [hu', hw, occupied, countIf, hz _ hw]
    · simp [hu', hz _ hu', occupied]
  rw [hm]
  exact le_add_of_nonneg_left (sum_nonneg fun i _ => by
    simp only [g, countIf]
    by_cases h1 : point y (Sum.inl i) ∈ C <;>
      by_cases h2 : flip (point y (Sum.inl i)) (d.natAdd 4) ∈ C <;> simp [h1, h2])

open Classical in
private theorem odd_suffix_degree_sum {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (y : Q 5) :
    (∑ d : Fin 5, oddOverlap z y (flip y d)) =
      3 * oddCount z y - ∑ i, evenLabel z i y * cScaled z i y := by
  let f := fiber z y
  let a := fun i => evenLabel z i y
  let m := oddLabel z y
  have hf (x : Q 4) (hx : x ∉ tenProjection) := fiber_and_signedRow_supported hz hrow y
    (show x ∉ leftProjection C by rwa [hP])
  have ⟨_, hr⟩ := signed_row_blocks (fun x hx => (hf x hx).1)
  have hunit (e : Fin 6) : |m e| ≤ 1 := by
    rcases label_values hu hz (join (pattern (midpointCode e)) y) with h | h | h <;>
      norm_num [m, oddLabel, fiber, h]
  have hmid := (midpoint_cut (fun x hx => (hf x hx).1) (fun x hx => (hf x hx).2) hunit).1
  have hpair : (∑ e, m e * signedRow f (pattern (midpointCode e))) = ∑ i, a i * cScaled z i y := by
    calc
      _ = ∑ e, ∑ i, m e * (incidence i e * a i) := by
        refine sum_congr rfl fun e _ => ?_
        have hh : signedRow f (pattern (midpointCode e)) = (incidence.transpose *ᵥ a) e :=
          congrFun hr e
        rw [hh]
        simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, mul_sum]
      _ = ∑ i, a i * (incidence *ᵥ m) i := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        simp only [Matrix.mulVec_apply_eq_sum, mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      _ = _ := by
        change m = incidence.transpose *ᵥ potential f at hmid
        rw [hmid]
        simp only [incidence_laplacian, cScaled, f]
  have hp (e : Fin 6) :
      (∑ d : Fin 5, occupied (m e) * occupied (oddLabel z (flip y d) e)) =
        3 * occupied (m e) - m e * signedRow f (pattern (midpointCode e)) := by
    let x := pattern (midpointCode e)
    let u := join x y
    by_cases hmem : u ∈ C
    · have hdegree : (∑ j : Fin 9, occupied (z (flip u j))) = 3 := by
        have he (j : Fin 9) : occupied (z (flip u j)) = countIf (j ∈ directions C u) := by
          by_cases hh : flip u j ∈ C
          · simp [occupied, countIf, mem_directions, hh, (nonzero_iff_mem hu hz _).mpr hh]
          · simp [occupied, countIf, mem_directions, hh, hz _ hh]
        simp only [he, indicator_sum, filter_mem_eq_inter, univ_inter,
          regular_directions C hreg hmem, Nat.cast_ofNat]
      have hhor : (∑ j : Fin 4, occupied (z (flip u (j.castAdd 5)))) = m e * signedRow f x := by
        unfold signedRow
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        have hh := selected_term hreg hu hz hrow hmem (j.castAdd 5)
        simpa only [u, m, f, oddLabel, fiber, x, flip_join_left, sign_join_left] using hh.symm
      have hm : m e ≠ 0 := (nonzero_iff_mem hu hz u).mpr hmem
      rw [Fin.sum_univ_add (a := 4) (b := 5), hhor] at hdegree
      have hd : (∑ d : Fin 5, occupied (z (flip u (d.natAdd 4)))) =
          ∑ d : Fin 5, occupied (oddLabel z (flip y d) e) := by
        simp [u, x, flip_join_right, fiber]
      rw [hd] at hdegree
      have hocc : occupied (m e) = 1 := if_neg hm
      rw [hocc, mul_one]
      simp only [one_mul]
      change (∑ d : Fin 5, occupied (oddLabel z (flip y d) e)) = 3 - m e * signedRow f x
      omega
    · have hm : m e = 0 := hz u hmem
      simp [hm, occupied]
  unfold oddOverlap
  rw [sum_comm]
  change (∑ e, ∑ d : Fin 5, occupied (m e) * occupied (oddLabel z (flip y d) e)) =
    3 * (∑ e, occupied (m e)) - ∑ i, a i * cScaled z i y
  simp only [hp, sum_sub_distrib, ← mul_sum, hpair]


open private midpoint_scaled active_singleton_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance

private def starIndicator (i : Fin 4) (e : Fin 6) : ℤ :=
  countIf (i = (endpoints e).1 ∨ i = (endpoints e).2)

private def cutIndicator (p : Fin 4 → Bool) (e : Fin 6) : ℤ :=
  countIf (p (endpoints e).1 ≠ p (endpoints e).2)

private theorem star_overlap : ∀ i j : Fin 4, i ≠ j →
    (∑ e, starIndicator i e * starIndicator j e) = 1 := by decide +kernel

private theorem star_balanced_overlap : ∀ (i : Fin 4) (p : Fin 4 → Bool),
    (∑ e, cutIndicator p e) = 4 →
    (∑ e, starIndicator i e * cutIndicator p e) = 2 := by decide +kernel

private theorem odd_indicator_of_centers {z : Q 9 → ℤ} {y : Q 5}
    (hm : ∀ e, 4 * oddLabel z y e =
      cScaled z (endpoints e).1 y - cScaled z (endpoints e).2 y)
    (i : Fin 4) (s : Bool)
    (hc : ∀ j, cScaled z j y = (if s then 1 else -1) * (if j = i then 3 else -1)) (e : Fin 6) :
    occupied (oddLabel z y e) = starIndicator i e := by
  have h := hm e
  rw [hc, hc] at h
  by_cases hp : (endpoints e).1 = i <;> by_cases hq : (endpoints e).2 = i
  all_goals
    have hp' : (i = (endpoints e).1) ↔ (endpoints e).1 = i := eq_comm
    have hq' : (i = (endpoints e).2) ↔ (endpoints e).2 = i := eq_comm
    simp only [hp, hq, if_pos, if_neg, ite_true, ite_false] at h
    simp only [starIndicator, hp', hq', hp, hq, countIf]
  · have hn : ∀ e : Fin 6, (endpoints e).1 ≠ (endpoints e).2 := by decide
    exact (hn e (hp.trans hq.symm)).elim
  · cases s <;> simp at h <;> simp [occupied, show oddLabel z y e ≠ 0 by omega]
  · cases s <;> simp at h <;> simp [occupied, show oddLabel z y e ≠ 0 by omega]
  · simp at h
    simp [occupied, show oddLabel z y e = 0 by omega]

private theorem odd_indicator_of_balanced {z : Q 9 → ℤ} {y : Q 5}
    (hm : ∀ e, 4 * oddLabel z y e =
      cScaled z (endpoints e).1 y - cScaled z (endpoints e).2 y)
    (hc : ∀ j, cScaled z j y = 2 ∨ cScaled z j y = -2) (e : Fin 6) :
    occupied (oddLabel z y e) = cutIndicator (fun i => decide (cScaled z i y = 2)) e := by
  have h := hm e
  rcases hc (endpoints e).1 with h1 | h1 <;> rcases hc (endpoints e).2 with h2 | h2 <;>
    norm_num [h1, h2] at h <;>
    simp [occupied, h, cutIndicator, countIf, h1, h2] <;> omega

private theorem degree_as_directions (S : Finset (BitVec 5)) (x : BitVec 5) :
    degree S x = ((univ : Finset (Fin 5)).filter fun j =>
      x ^^^ BitVec.twoPow 5 j.val ∈ S).card := by
  rw [degree_filter]
  symm
  apply card_bij (fun j _ => x ^^^ BitVec.twoPow 5 j.val)
  · intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).2, (adjacent_flip _ _).mpr ⟨j, rfl⟩⟩
  · intro a _ b _ h
    have hpow := (BitVec.xor_right_inj x).mp h
    exact direction_injective hpow
  · intro w hw
    obtain ⟨j, hj⟩ := (adjacent_flip _ _).mp (mem_filter.mp hw).2
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, hj.symm ▸ (mem_filter.mp hw).1⟩, hj⟩

private def balancedSupport (z : Q 9 → ℤ) : Finset (BitVec 5) :=
  (univ : Finset (Fin 32)).map ⟨BitVec.ofFin, fun _ _ h => congrArg BitVec.toFin h⟩ |>.filter
    (fun x => oddCount z (cubeBitVec 5 x) = 4)

private theorem mem_balancedSupport {z : Q 9 → ℤ} {x : BitVec 5} :
    x ∈ balancedSupport z ↔ oddCount z (cubeBitVec 5 x) = 4 := by
  have hx : x ∈ (univ : Finset (Fin 32)).map
      ⟨BitVec.ofFin, fun _ _ h => congrArg BitVec.toFin h⟩ :=
    mem_map.mpr ⟨x.toFin, mem_univ _, rfl⟩
  simp [balancedSupport, hx]


open Classical in
private theorem eight_odd_direction {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0)
    (hdeg : ∀ i y, evenLabel z i y ≠ 0 →
      evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y)
    (h24 : (∑ y, evenCount (fun i => evenLabel z i y)) = 24)
    (h48 : (∑ y, oddCount z y) = 48)
    (hpar : ∀ x, decide (x ∈ singletonSupport z) = neighborParity (singletonSupport z) x)
    (hsb : 3 * singletons z + 4 * balancedCuts z = 48)
    (hs : singletons z = 8) (hcenters : ∀ i, activeCenters z i = singletonCenters z i) :
    ∃ d : Fin 5, (∑ y, oddOverlap z y (flip y d)) = 32 := by
  let S := singletonSupport z
  let B := balancedSupport z
  have hS (x : BitVec 5) : x ∈ S ↔ oddCount z (cubeBitVec 5 x) = 3 := by
    simp [S, singletonSupport]
  have hB (x : BitVec 5) : x ∈ B ↔ oddCount z (cubeBitVec 5 x) = 4 := mem_balancedSupport
  have hs8 : S.card = 8 := by exact_mod_cast (singletonSupport_card z).trans hs
  have hb6 : B.card = 6 := by
    let _ : Fintype (BitVec 5) := Fintype.ofEquiv (Q 5) (cubeBitVec 5).symm
    have h := Fintype.sum_equiv (cubeBitVec 5)
      (fun x => countIf (oddCount z (cubeBitVec 5 x) = 4))
      (fun y => countIf (oddCount z y = 4)) (fun _ => rfl)
    have hfil : (univ.filter (fun x : BitVec 5 => oddCount z (cubeBitVec 5 x) = 4)) = B := by
      ext x
      simp [hB x]
    rw [indicator_sum, hfil] at h
    change (B.card : ℤ) = balancedCuts z at h
    omega
  have hdis : Disjoint S B := by
    rw [disjoint_left]
    intro x hx hy
    have := (hS x).mp hx
    have := (hB x).mp hy
    omega
  have hmid (y : Q 5) (e : Fin 6) : 4 * oddLabel z y e =
      cScaled z (endpoints e).1 y - cScaled z (endpoints e).2 y := by
    have hf (x : Q 4) (hx : x ∉ tenProjection) := fiber_and_signedRow_supported hz hrow y
      (show x ∉ leftProjection C by rwa [hP])
    have hunit (e : Fin 6) : |oddLabel z y e| ≤ 1 := by
      rcases label_values hu hz (join (pattern (midpointCode e)) y) with h | h | h <;>
        norm_num [oddLabel, fiber, h]
    exact midpoint_scaled e (midpoint_cut (fun x hx => (hf x hx).1)
      (fun x hx => (hf x hx).2) hunit).1
  have hactive (i : Fin 4) (y : Q 5) (hy : |cScaled z i y| = 3) : evenLabel z i y ≠ 0 := by
    have hsum : (∑ w, (countIf (|cScaled z i w| = 3) -
        occupied (evenLabel z i w) * countIf (|cScaled z i w| = 3))) = 0 := by
      rw [sum_sub_distrib]
      change singletonCenters z i - activeCenters z i = 0
      rw [hcenters, sub_self]
    have h := (sum_eq_zero_iff_of_nonneg (fun w _ => by
      unfold occupied countIf
      split <;> try split <;> omega)).mp hsum y (mem_univ y)
    intro h0
    simp [h0, hy, countIf, occupied] at h
  have hstar (y : Q 5) (hy : oddCount z y = 3) : ∃ (i : Fin 4),
      evenLabel z i y ≠ 0 ∧ evenVerticalDegree z i y = 0 ∧
      (∀ e, occupied (oddLabel z y e) = starIndicator i e) ∧
      (evenCount (fun i => evenLabel z i y)) = 2 := by
    rcases hlocal y with ⟨_, h, _⟩ | ⟨i, sign, _, hc, ha⟩ | ⟨h, _, _⟩
    · omega
    · have hi : |cScaled z i y| = 3 := by
        rw [show cScaled z i y = _ from hc i]
        cases sign <;> norm_num
      have hn := hactive i y hi
      have hprod : evenLabel z i y * cScaled z i y = 3 := by
        simpa [countIf, occupied, hy, hi, hn] using
          (label_contributions (i := i) (hlocal y) (fun h => hzero y h i)).2.2
      refine ⟨i, hn, ?_, odd_indicator_of_centers (hmid y) i sign hc, ?_⟩
      · rw [hdeg i y hn, hprod]; norm_num
      · rcases ha with ha | ⟨k, hk, ha⟩
        · exact (hn (ha i)).elim
        · exact active_singleton_count sign hk ha
    · omega
  have hSS (y : Q 5) (d : Fin 5) (hy : oddCount z y = 3)
      (hw : oddCount z (flip y d) = 3) : oddOverlap z y (flip y d) = 1 := by
    obtain ⟨i, hi, hdeg0, hfirst, _⟩ := hstar y hy
    obtain ⟨j, hj, _, hsecond, _⟩ := hstar (flip y d) hw
    have hne : i ≠ j := by
      rintro rfl
      have h := single_le_sum (f := fun k => occupied (evenLabel z i (flip y k)))
        (fun _ _ => by unfold occupied; split <;> omega) (mem_univ d)
      change _ ≤ evenVerticalDegree z i y at h
      simp [hdeg0, hj, occupied] at h
    unfold oddOverlap
    simp only [hfirst, hsecond]
    exact star_overlap i j hne
  have hSB (y w : Q 5) (hy : oddCount z y = 3) (hw : oddCount z w = 4) :
      oddOverlap z y w = 2 := by
    obtain ⟨i, _, _, hi, _⟩ := hstar y hy
    rcases hlocal w with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, hc, _⟩
    · omega
    · omega
    · have hj := odd_indicator_of_balanced (hmid w) hc
      unfold oddOverlap
      simp only [hi, hj]
      apply star_balanced_overlap
      change (∑ e, _) = 4
      simpa only [oddCount, hj] using hw
  let W (x : BitVec 5) (d : Fin 5) := oddOverlap z (cubeBitVec 5 x) (flip (cubeBitVec 5 x) d)
  have hloc (x : BitVec 5) (hx : x ∈ S) : degree S x + 2 * degree B x = 5 := by
    let y := cubeBitVec 5 x
    have hy : oddCount z y = 3 := (hS x).mp hx
    obtain ⟨_, _, _, _, hp⟩ := hstar y hy
    have hsum := odd_suffix_degree_sum hreg hP hu hz hrow y
    rw [local_pairing (hlocal y), hp, hy] at hsum
    have hterm (d : Fin 5) : W x d =
        countIf (x ^^^ BitVec.twoPow 5 d.val ∈ S) + 2 * countIf (x ^^^ BitVec.twoPow 5 d.val ∈ B) := by
      simp only [countIf, hS, hB, flip_word]
      change W x d = (if oddCount z (flip y d) = 3 then 1 else 0) +
        2 * (if oddCount z (flip y d) = 4 then 1 else 0)
      rcases odd_cases hlocal (flip y d) with h | h | h
      · rw [show W x d = _ from oddOverlap_comm z y (flip y d), oddOverlap_zero h]
        norm_num [countIf, h]
      · have ho := hSS y d hy h
        simp [W, y, ho, countIf, h]
      · have ho := hSB y _ hy h
        simp [W, y, ho, countIf, h]
    change (∑ d, W x d) = _ at hsum
    simp only [hterm, sum_add_distrib, ← mul_sum, indicator_sum, ← degree_as_directions] at hsum
    norm_num at hsum
    exact_mod_cast hsum
  obtain ⟨d, hparallel, hcross, hbb⟩ := eight_fiber_geometry hs8 hb6 hdis hpar hloc
  let _ : Fintype (BitVec 5) := Fintype.ofEquiv (Q 5) (cubeBitVec 5).symm
  have htot : (∑ j : Fin 5, ∑ x : BitVec 5, W x j) = 96 := by
    have hswap (j : Fin 5) := Fintype.sum_equiv (cubeBitVec 5) (fun x => W x j)
      (fun y => oddOverlap z y (flip y j)) (fun _ => rfl)
    simp_rw [hswap]
    rw [sum_comm]
    simp_rw [odd_suffix_degree_sum hreg hP hu hz hrow, local_pairing (hlocal _)]
    have he (y : Q 5) : (if oddCount z y = 0 then 0 else 2 *
        evenCount (fun i => evenLabel z i y)) = 2 * evenCount (fun i => evenLabel z i y) := by
      by_cases h : oddCount z y = 0
      · simp [h, hzero y h, evenCount, occupied]
      · simp [h]
    simp only [he, sum_sub_distrib, ← mul_sum, h24, h48]
    decide
  let F (x : BitVec 5) (j : Fin 5) : ℤ :=
    countIf (x ∈ S ∧ x ^^^ BitVec.twoPow 5 j.val ∈ B)
  have hF : (∑ j : Fin 5, ∑ x : BitVec 5, F x j) = 16 := by
    rw [sum_comm]
    have hf (x : BitVec 5) : (∑ j, F x j) = if x ∈ S then (degree B x : ℤ) else 0 := by
      by_cases hx : x ∈ S
      · simp [F, countIf, hx, degree_as_directions]
      · simp [F, countIf, hx]
    simp_rw [hf, ← sum_filter, filter_mem_eq_inter, univ_inter]
    exact_mod_cast hcross
  have hFd (x : BitVec 5) : F x d = 0 := by
    by_cases hx : x ∈ S
    · have hm := (hparallel x hx d).mpr rfl
      have hn := fun hb => disjoint_left.mp hdis hm hb
      simp [F, countIf, hx, show _ ∉ B from hn]
    · simp [F, countIf, hx]
  have hswap (j : Fin 5) :
      (∑ x : BitVec 5, F (x ^^^ BitVec.twoPow 5 j.val) j) = ∑ x : BitVec 5, F x j := by
    let t (x : BitVec 5) := x ^^^ BitVec.twoPow 5 j.val
    have hi : Function.Involutive t := fun x => by simp [t, BitVec.xor_assoc]
    let e : BitVec 5 ≃ BitVec 5 := ⟨t, t, hi, hi⟩
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  have hother (j : Fin 5) (hj : j ≠ d) (x : BitVec 5) :
      W x j = 2 * (F x j + F (x ^^^ BitVec.twoPow 5 j.val) j) := by
    let v := x ^^^ BitVec.twoPow 5 j.val
    let y := cubeBitVec 5 x
    let w := cubeBitVec 5 v
    have hv : v ^^^ BitVec.twoPow 5 j.val = x := by simp [v, BitVec.xor_assoc]
    change oddOverlap z y (flip y j) = _
    rw [← flip_word]
    change oddOverlap z y w = _
    change _ = 2 * (countIf (x ∈ S ∧ v ∈ B) +
      countIf (v ∈ S ∧ v ^^^ BitVec.twoPow 5 j.val ∈ B))
    simp only [hv, countIf, hS x, hS v, hB x, hB v]
    change _ = 2 * ((if oddCount z y = 3 ∧ oddCount z w = 4 then 1 else 0) +
      (if oddCount z w = 3 ∧ oddCount z y = 4 then 1 else 0))
    rcases odd_cases hlocal y with hy | hy | hy <;>
      rcases odd_cases hlocal w with hw | hw | hw
    · simp [oddOverlap_zero hy, countIf, hy, hw]
    · simp [oddOverlap_zero hy, countIf, hy, hw]
    · simp [oddOverlap_zero hy, countIf, hy, hw]
    · rw [oddOverlap_comm, oddOverlap_zero hw]; norm_num [countIf, hy, hw]
    · have hx : x ∈ S := (hS x).mpr hy
      have hv' : v ∈ S := (hS v).mpr hw
      exact (hj ((hparallel x hx j).mp hv')).elim
    · simp [hSB y w hy hw, countIf, hy, hw]
    · rw [oddOverlap_comm, oddOverlap_zero hw]; norm_num [countIf, hy, hw]
    · rw [oddOverlap_comm, hSB w y hw hy]; norm_num [countIf, hy, hw]
    · have hv' := hbb x ((hB x).mpr hy) v ((hB v).mpr hw)
        ((adjacent_flip x v).mpr ⟨j, rfl⟩)
      exact (hj (direction_injective ((BitVec.xor_right_inj x).mp hv'))).elim
  have hdirection (j : Fin 5) (hj : j ≠ d) : (∑ x, W x j) = 4 * ∑ x, F x j := by
    simp only [hother j hj, ← mul_sum, sum_add_distrib, hswap]
    rw [show (∑ x, F x j) + (∑ x, F x j) = 2 * ∑ x, F x j by ring]
    ring
  have htail : (∑ j ∈ (univ : Finset (Fin 5)).erase d, ∑ x, W x j) = 64 := by
    calc
      _ = ∑ j ∈ (univ : Finset (Fin 5)).erase d, 4 * ∑ x, F x j :=
        sum_congr rfl fun j hj => hdirection j (mem_erase.mp hj).1
      _ = 4 * ∑ j ∈ (univ : Finset (Fin 5)).erase d, ∑ x, F x j := by rw [mul_sum]
      _ = _ := by
        have h := sum_erase_add (s := (univ : Finset (Fin 5))) (f := fun j => ∑ x, F x j) (mem_univ d)
        simp only [hFd, sum_const_zero, add_zero, hF] at h
        rw [h]
        decide
  have hmain := sum_erase_add (s := (univ : Finset (Fin 5))) (f := fun j => ∑ x, W x j) (mem_univ d)
  rw [htail, htot] at hmain
  refine ⟨d, ?_⟩
  have hsum := Fintype.sum_equiv (cubeBitVec 5) (fun x => W x d)
    (fun y => oddOverlap z y (flip y d)) (fun _ => rfl)
  rw [← hsum]
  omega


open Classical in
/-- A balanced cubic support with 72 vertices and the normalized K4 projection
cannot have at least 30 vertices in each of the four star halves. -/
theorem tight_stars_impossible {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalves : ∀ i, 30 ≤ (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card) :
    False := by
  obtain ⟨z, hu, hz, hrow, hc, hlocal, h24, h48, _, hzero, hpar, hsb, hcases, hlabels⟩ :=
    balanced_label_identities hsize hreg hb hP hhalves
  have hdeg := even_degree hreg hu hz hrow (fun i y => (hc i y).1)
  rcases hcases with h | h | h | h
  · exact (singleton_zero_impossible h24 (fun i => (hlabels i).2.2.2.2.2.2.2)
      (fun i => (hlabels i).1) (fun i => (hlabels i).2.2.2.2.2.2.1) h).elim
  · have hsz := eight_label_counts hlocal h (fun i =>
      ⟨active_centers_bound z i, (hlabels i).2.2.2.2.1,
        (hlabels i).2.2.2.2.2.1, (hlabels i).2.2.2.2.2.2.1, (hlabels i).2.2.2.2.2.2.2⟩)
    obtain ⟨d, hd⟩ := eight_odd_direction hreg hP hu hz hrow hlocal hzero hdeg h24 h48 hpar hsb h
      (fun i => (hsz i).2.1.trans (hsz i).1.symm)
    have he := overlap_le_endpoints hP hu hz d
    have hcount := direction_edge_count (d := 3) C hreg hb (d.natAdd 4)
    omega
  · obtain ⟨w, hwu, hwz, _, _, htwo, _⟩ := balanced_active_fibers hsize hreg hb hP hhalves
    have he (i : Fin 4) (y : Q 5) :
        occupied (evenLabel z i y) = occupied (evenLabel w i y) := by
      let u := join (pattern (vertexCode i)) y
      by_cases hm : u ∈ C
      · have h1 := (nonzero_iff_mem hu hz u).mpr hm
        have h2 := (nonzero_iff_mem hwu hwz u).mpr hm
        simp [occupied, show evenLabel z i y ≠ 0 from h1, show evenLabel w i y ≠ 0 from h2]
      · simp [occupied, show evenLabel z i y = 0 from hz u hm,
          show evenLabel w i y = 0 from hwz u hm]
    have htwo' (y : Q 5) : evenCount (fun i => evenLabel z i y) = 0 ∨
        evenCount (fun i => evenLabel z i y) = 2 := by
      simpa only [evenCount, he] using htwo y
    exact (singleton_twelve_impossible hb hu hz hc hlocal hzero
      (even_degree hreg hu hz hrow (fun i y => (hc i y).1)) h24 htwo' hsb
      (fun i => ⟨(hlabels i).2.1, (hlabels i).2.2.2.2.1, (hlabels i).2.2.2.2.2.1,
        (hlabels i).2.2.2.2.2.2.1⟩) h).elim
  · exact (singleton_sixteen_impossible hb hu hz (fun i y => (hc i y).2) hlocal hzero
      (even_degree hreg hu hz hrow (fun i y => (hc i y).1)) h24
      (fun i => ⟨(hlabels i).1, (hlabels i).2.2.2.1, (hlabels i).2.2.2.2.1⟩) hsb h).elim

#print axioms tight_stars_impossible

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4TightStarObstruction
