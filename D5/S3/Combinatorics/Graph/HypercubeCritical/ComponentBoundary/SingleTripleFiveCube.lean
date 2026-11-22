/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SingleTripleFiveCube
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SingleTripleFiveCube
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Rigidity of a balanced five-cube support with a single degree-three direction set. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-! The rigidity proof uses local saturation of the unsigned adjacency rows. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SingleTripleFiveCube

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced gamma)
open BalancedCubeGirth
  (adjacent_exists_flip flip_comm no_selected_square three_directions_distinct
    three_step_first_direction_eq)
open BalancedCubeComponentBoundary
  (directions mem_directions directions_card flip_injective flip_three_swap)

attribute [local instance] Classical.propDecidable

private abbrev adj {n : ℕ} := (hypercube n).Adj

private def neighbors {n : ℕ} (U : Finset (Q n)) (x : Q n) : Finset (Q n) :=
  U.filter (adj x)

private theorem mem_neighbors {n : ℕ} {U : Finset (Q n)} {x y : Q n} :
    y ∈ neighbors U x ↔ y ∈ U ∧ adj x y :=
  Finset.mem_filter

private def High {n : ℕ} (U : Finset (Q n)) (x : Q n) : Prop :=
  (directions U x).card = 3

private def Near {n : ℕ} (U : Finset (Q n)) (x : Q n) : Prop :=
  ∃ y ∈ neighbors U x, High U y

private theorem direction_of_mem {n : ℕ} {U : Finset (Q n)} {T : Finset (Fin n)}
    {x : Q n} (ht : directions U x = T) (i : Fin n) :
    flip x i ∈ U ↔ i ∈ T := by
  rw [← ht, mem_directions]

private theorem next_outside {n : ℕ} {U : Finset (Q n)} {T : Finset (Fin n)}
    (hb : IsBalanced U) {x : Q n} (hx : x ∈ U) (ht : directions U x = T)
    {i j : Fin n} (hij : i ≠ j) (hi : i ∈ T) (hijU : flip (flip x i) j ∈ U) :
    j ∉ T := by
  intro hj
  exact no_selected_square hb hij hx ((direction_of_mem ht i).mpr hi)
    ((direction_of_mem ht j).mpr hj) hijU

private theorem high_separation {n : ℕ} {U : Finset (Q n)} {T : Finset (Fin n)}
    (hb : IsBalanced U)
    (ht : ∀ x ∈ U, High U x → directions U x = T) :
    (∀ x ∈ U, High U x → ¬ Near U x) ∧
    (∀ x y z, x ∈ U → High U x → z ∈ U → High U z → y ∈ U →
      adj x y → adj y z → x = z) ∧
    (∀ x y, x ∈ U → y ∈ U → Near U x → Near U y → ¬ adj x y) := by
  have one : ∀ x ∈ U, High U x → ¬ Near U x := by
    intro x hx hX hn
    obtain ⟨z, hzN, hZ⟩ := hn
    obtain ⟨hz, hxz⟩ := mem_neighbors.mp hzN
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxz
    have hi : i ∈ T := (direction_of_mem (ht x hx hX) i).mp hz
    have hc : T.card = 3 := by rw [← ht x hx hX]; exact hX
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) i
    exact next_outside hb hx (ht x hx hX) hji.symm hi
      ((direction_of_mem (ht (flip x i) hz hZ) j).mpr hj) hj
  have two : ∀ x y z, x ∈ U → High U x → z ∈ U → High U z → y ∈ U →
      adj x y → adj y z → x = z := by
    intro x y z hx hX hz hZ hy hxy hyz
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
    obtain ⟨j, rfl⟩ := adjacent_exists_flip hyz
    by_cases hij : i = j
    · subst j
      rw [BalancedCriticalSpectrum.flip_flip]
    · have hi : i ∈ T := (direction_of_mem (ht x hx hX) i).mp hy
      have hj : j ∈ T := (direction_of_mem (ht _ hz hZ) j).mp (by simpa using hy)
      exact (next_outside hb hx (ht x hx hX) hij hi hz hj).elim
  refine ⟨one, two, ?_⟩
  intro y z hy hz hyN hzN hyz
  obtain ⟨x, hxN, hX⟩ := hyN
  obtain ⟨w, hwN, hW⟩ := hzN
  obtain ⟨hx, hyx⟩ := mem_neighbors.mp hxN
  obtain ⟨hw, hzw⟩ := mem_neighbors.mp hwN
  obtain ⟨i, rfl⟩ := adjacent_exists_flip hyx.symm
  obtain ⟨b, rfl⟩ := adjacent_exists_flip hyz
  obtain ⟨j, rfl⟩ := adjacent_exists_flip hzw
  have hib : i ≠ b := by
    rintro rfl
    exact one x hx hX ⟨_, mem_neighbors.mpr ⟨hw,
      by simpa only [BalancedCriticalSpectrum.flip_flip] using hzw⟩, hW⟩
  have hbj : b ≠ j := by
    rintro rfl
    have hY : High U (flip x i) := by simpa only [BalancedCriticalSpectrum.flip_flip] using hW
    exact one x hx hX ⟨_, mem_neighbors.mpr ⟨hy, flip_adj x i⟩, hY⟩
  have hij := three_directions_distinct hb hib hbj hx hy hz hw
  have hj : j ∈ T := (direction_of_mem (ht _ hw hW) j).mp (by simpa using hz)
  have hXj := (direction_of_mem (ht x hx hX) j).mpr hj
  have hi : i ∈ T := (direction_of_mem (ht x hx hX) i).mp hy
  have hr := flip_three_swap x i b j
  have hrU : flip (flip (flip x j) b) i ∈ U := hr ▸ hw
  have hmid : flip (flip x j) b ∈ U := by
    simpa only [BalancedCriticalSpectrum.flip_flip] using
      (direction_of_mem (ht _ hrU (hr ▸ hW)) i).mpr hi
  exact hij (three_step_first_direction_eq hb hib hbj hbj.symm hib.symm
    hx hy hz hw hXj hmid hrU hr)

private def row {n : ℕ} (U : Finset (Q n)) (f : Q n → ℝ) (x : Q n) : ℝ :=
  ∑ y ∈ neighbors U x, f y

private theorem row_pairing {n : ℕ} (U : Finset (Q n)) (f g : Q n → ℝ) :
    (∑ x ∈ U, f x * row U g x) = ∑ x ∈ U, g x * row U f x := by
  simp only [row, neighbors, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [show adj y x ↔ adj x y from ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩, mul_comm]

private theorem row_eq_of_le {n : ℕ} {U : Finset (Q n)} {f g : Q n → ℝ} {r : ℝ}
    (hpos : ∀ x ∈ U, 0 < f x) (hf : ∀ x ∈ U, row U f x = r * f x)
    (hg : ∀ x ∈ U, row U g x ≤ r * g x) :
    ∀ x ∈ U, row U g x = r * g x := by
  have hsum : (∑ x ∈ U, f x * row U g x) = ∑ x ∈ U, f x * (r * g x) := by
    rw [row_pairing]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hf x hx]
    ring
  intro x hx
  apply le_antisymm (hg x hx)
  by_contra! hlt
  exact (ne_of_lt (Finset.sum_lt_sum
    (fun y hy => mul_le_mul_of_nonneg_left (hg y hy) (hpos y hy).le)
    ⟨x, hx, mul_lt_mul_of_pos_left hlt (hpos x hx)⟩)) hsum

private theorem neighbors_card {n : ℕ} (U : Finset (Q n)) (x : Q n) :
    (neighbors U x).card = (directions U x).card :=
  (directions_card U x).symm

private theorem forced_layers {n : ℕ} {U : Finset (Q n)} {T : Finset (Fin n)}
    (hb : IsBalanced U) (hdeg : ∀ x ∈ U, (directions U x).card ≤ 3)
    (ht : ∀ x ∈ U, High U x → directions U x = T)
    {f : Q n → ℝ} (hpos : ∀ x ∈ U, 0 < f x)
    (hf : ∀ x ∈ U, row U f x = Real.sqrt 5 * f x) :
    (∀ x ∈ U, Near U x → ∃ y z, High U y ∧ ¬ High U z ∧ ¬ Near U z ∧
      neighbors U x = {y, z}) ∧
    (∀ x ∈ U, ¬ High U x → ¬ Near U x →
      (neighbors U x).card = 2 ∧ ∀ y ∈ neighbors U x, Near U y) := by
  obtain ⟨hone, htwo, hthree⟩ := high_separation hb ht
  let r := Real.sqrt 5
  have hr : r ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : 2 < r := by nlinarith
  let w : Q n → ℝ := fun x => if High U x then 3 else if Near U x then r else 2
  have w_high {x : Q n} (hx : High U x) : w x = 3 := by simp [w, hx]
  have w_near {x : Q n} (hx : x ∈ U) (hn : Near U x) : w x = r := by
    simp [w, show ¬ High U x from fun h => hone x hx h hn, hn]
  have w_far {x : Q n} (hX : ¬ High U x) (hn : ¬ Near U x) : w x = 2 := by
    simp [w, hX, hn]
  have high_for_near (x : Q n) (hn : Near U x) : ∃ y ∈ neighbors U x, High U y := hn
  have near_data {x y : Q n} (hx : x ∈ U) (hyN : y ∈ neighbors U x)
      (hY : High U y) :
      (neighbors U x).card ≤ 2 ∧ ∀ z ∈ (neighbors U x).erase y, ¬ High U z ∧ ¬ Near U z := by
    have hn : Near U x := ⟨y, hyN, hY⟩
    have hd := hdeg x hx
    rw [← neighbors_card] at hd
    have hnot : (neighbors U x).card ≠ 3 := fun h => hone x hx
      (by rwa [neighbors_card] at h) hn
    refine ⟨by omega, ?_⟩
    intro z hz
    obtain ⟨hzy, hzN⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzU, hxz⟩ := mem_neighbors.mp hzN
    obtain ⟨hyU, hxy⟩ := mem_neighbors.mp hyN
    exact ⟨fun hZ => hzy (htwo z x y hzU hZ hyU hY hx hxz.symm hxy),
      fun hzNear => hthree x z hx hzU hn hzNear hxz⟩
  have near_row {x y : Q n} (hx : x ∈ U) (hy : y ∈ neighbors U x) (hY : High U y) :
      row U w x = 3 + ((neighbors U x).erase y).card * 2 := by
    have h := (near_data hx hy hY).2
    unfold row
    rw [← Finset.sum_erase_add _ _ hy, w_high hY]
    have hs : (∑ z ∈ (neighbors U x).erase y, w z) =
        ∑ _z ∈ (neighbors U x).erase y, (2 : ℝ) :=
      Finset.sum_congr rfl (fun z hz => w_far (h z hz).1 (h z hz).2)
    rw [hs]
    simp [add_comm]
  have far_data {x : Q n} (hx : x ∈ U) (hX : ¬ High U x) (hn : ¬ Near U x) :
      (neighbors U x).card ≤ 2 ∧ ∀ y ∈ neighbors U x, ¬ High U y ∧ w y ≤ r := by
    have hd := hdeg x hx
    rw [← neighbors_card] at hd
    refine ⟨by
      have hnot : (neighbors U x).card ≠ 3 := fun h => hX (by rwa [neighbors_card] at h)
      omega, ?_⟩
    intro y hy
    have hY : ¬ High U y := fun h => hn ⟨y, hy, h⟩
    refine ⟨hY, ?_⟩
    by_cases hyN : Near U y
    · rw [w_near (mem_neighbors.mp hy).1 hyN]
    · rw [w_far hY hyN]
      exact hr2.le
  have card_real {m : ℕ} (hm : m ≤ 2) : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have far_bound {x : Q n} (hx : x ∈ U) (hX : ¬ High U x) (hn : ¬ Near U x) :
      row U w x ≤ ((neighbors U x).card : ℝ) * r := by
    calc
      row U w x ≤ ∑ _y ∈ neighbors U x, r :=
        Finset.sum_le_sum (fun y hy => (far_data hx hX hn).2 y hy |>.2)
      _ = _ := by simp
  have hbound (x : Q n) (hx : x ∈ U) : row U w x ≤ r * w x := by
    by_cases hX : High U x
    · have hcard : (neighbors U x).card = 3 := (neighbors_card U x).trans hX
      have hs : row U w x = ∑ _y ∈ neighbors U x, r := by
        apply Finset.sum_congr rfl
        intro y hy
        obtain ⟨hyU, hxy⟩ := mem_neighbors.mp hy
        exact w_near hyU ⟨x, mem_neighbors.mpr ⟨hx, hxy.symm⟩, hX⟩
      rw [hs, w_high hX]
      simp [hcard, mul_comm]
    · by_cases hn : Near U x
      · obtain ⟨y, hy, hY⟩ := high_for_near x hn
        have hc := (near_data hx hy hY).1
        have he := Finset.card_erase_add_one hy
        have hh : ((neighbors U x).erase y).card ≤ 1 := by omega
        have hh' : (((neighbors U x).erase y).card : ℝ) ≤ 1 := by exact_mod_cast hh
        rw [near_row hx hy hY, w_near hx hn, ← pow_two, hr]
        linarith
      · rw [w_far hX hn, mul_comm r]
        exact (far_bound hx hX hn).trans
          (mul_le_mul_of_nonneg_right (card_real (far_data hx hX hn).1) hr0)
  have heq := row_eq_of_le hpos hf hbound
  constructor
  · intro x hx hn
    obtain ⟨y, hy, hY⟩ := high_for_near x hn
    have h := heq x hx
    rw [near_row hx hy hY, w_near hx hn, ← pow_two, hr] at h
    have he : (((neighbors U x).erase y).card : ℝ) = 1 := by linarith
    have he' : ((neighbors U x).erase y).card = 1 := by exact_mod_cast he
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp he'
    have hzmem : z ∈ (neighbors U x).erase y := by simp [hz]
    obtain ⟨hZ, hzN⟩ := (near_data hx hy hY).2 z hzmem
    refine ⟨y, z, hY, hZ, hzN, ?_⟩
    rw [← Finset.insert_erase hy, hz]
  · intro x hx hX hn
    have h := heq x hx
    rw [w_far hX hn, mul_comm r] at h
    have hle := far_bound hx hX hn
    have hc' : (2 : ℝ) ≤ (neighbors U x).card :=
      le_of_mul_le_mul_right (h ▸ hle) (by linarith)
    have hc : 2 ≤ (neighbors U x).card := by exact_mod_cast hc'
    have hcard := le_antisymm (far_data hx hX hn).1 hc
    refine ⟨hcard, ?_⟩
    intro y hy
    by_contra hyN
    have hs : row U w x < ∑ _y ∈ neighbors U x, r :=
      Finset.sum_lt_sum (fun z hz => (far_data hx hX hn).2 z hz |>.2)
        ⟨y, hy, by rw [w_far ((far_data hx hX hn).2 y hy).1 hyN]; exact hr2⟩
    simp [hcard, h] at hs


private theorem step_from_high {n : ℕ} {U : Finset (Q n)} {T : Finset (Fin n)}
    (hb : IsBalanced U)
    (ht : ∀ x ∈ U, High U x → directions U x = T)
    (pairs : ∀ x ∈ U, Near U x → ∃ y z, High U y ∧ ¬ High U z ∧ ¬ Near U z ∧
      neighbors U x = {y, z})
    {x y : Q n} (hx : x ∈ U) (hX : High U x) (hy : y ∈ U) (hxy : adj x y)
    (i : Fin n) (he : y = flip x i) :
    ∃ b ∉ T, ¬ High U (flip y b) ∧ ¬ Near U (flip y b) ∧
      neighbors U y = {x, flip y b} := by
  have hxN : x ∈ neighbors U y := mem_neighbors.mpr ⟨hx, hxy.symm⟩
  obtain ⟨u, z, hU, hZ, hzN, hp⟩ := pairs y hy ⟨x, hxN, hX⟩
  rw [hp] at hxN
  have hxu : x = u := by
    rcases Finset.mem_insert.mp hxN with h | h
    · exact h
    · exact (hZ ((Finset.mem_singleton.mp h) ▸ hX)).elim
  subst u
  have hz : z ∈ neighbors U y := by rw [hp]; simp
  obtain ⟨hzU, hyz⟩ := mem_neighbors.mp hz
  obtain ⟨b, rfl⟩ := adjacent_exists_flip hyz
  have hi : i ∈ T := (direction_of_mem (ht _ hx hX) i).mp (he ▸ hy)
  have hib : i ≠ b := by
    rintro rfl
    exact hZ (by simpa only [he, BalancedCriticalSpectrum.flip_flip] using hX)
  exact ⟨b, next_outside hb hx (ht _ hx hX) hib hi (he ▸ hzU), hZ, hzN, hp⟩

private theorem outward_path {n : ℕ} {U : Finset (Q n)} {T : Finset (Fin n)}
    (hb : IsBalanced U)
    (ht : ∀ x ∈ U, High U x → directions U x = T)
    (pairs : ∀ x ∈ U, Near U x → ∃ y z, High U y ∧ ¬ High U z ∧ ¬ Near U z ∧
      neighbors U x = {y, z})
    (middle : ∀ x ∈ U, ¬ High U x → ¬ Near U x →
      (neighbors U x).card = 2 ∧ ∀ y ∈ neighbors U x, Near U y)
    {x : Q n} (hx : x ∈ U) (hX : High U x) {i : Fin n} (hi : i ∈ T) :
    ∃ b ∉ T, ∃ c ∉ T, ∃ j ∈ T, b ≠ c ∧
      let p := flip x i
      let m := flip p b
      let q := flip m c
      let y := flip q j
      p ∈ U ∧ m ∈ U ∧ q ∈ U ∧ y ∈ U ∧ High U y ∧
        neighbors U p = {x, m} ∧ neighbors U m = {p, q} ∧ neighbors U q = {m, y} := by
  let p := flip x i
  have hp : p ∈ U := (direction_of_mem (ht x hx hX) i).mpr hi
  obtain ⟨b, hbT, hM, hmN, hpair⟩ := step_from_high hb ht pairs hx hX hp (flip_adj x i) i rfl
  let m := flip p b
  have hm : m ∈ U := (mem_neighbors.mp (show m ∈ neighbors U p by rw [hpair]; simp [m])).1
  have hpN : p ∈ neighbors U m := mem_neighbors.mpr ⟨hp, (flip_adj p b).symm⟩
  obtain ⟨hc, hnear⟩ := middle m hm hM hmN
  have hc' : ((neighbors U m).erase p).card = 1 := by
    have := Finset.card_erase_add_one hpN
    omega
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc'
  have hqN : q ∈ (neighbors U m).erase p := by simp [hq]
  obtain ⟨hqp, hqm⟩ := Finset.mem_erase.mp hqN
  have hmPair : neighbors U m = {p, q} := by rw [← Finset.insert_erase hpN, hq]
  have hqNear := hnear q hqm
  obtain ⟨hqU, hmq⟩ := mem_neighbors.mp hqm
  obtain ⟨c, rfl⟩ := adjacent_exists_flip hmq
  have hbc : b ≠ c := by
    intro he
    apply hqp
    simp [m, he]
  obtain ⟨y, z, hY, hZ, _, hqPair⟩ := pairs _ hqU hqNear
  have hmQ : m ∈ neighbors U (flip m c) :=
    mem_neighbors.mpr ⟨hm, (flip_adj m c).symm⟩
  have hmz : m = z := by
    rw [hqPair] at hmQ
    rcases Finset.mem_insert.mp hmQ with h | h
    · exact (hM (show High U m from h.symm ▸ hY)).elim
    · exact Finset.mem_singleton.mp h
  subst z
  have hyQ : y ∈ neighbors U (flip m c) := by rw [hqPair]; simp
  obtain ⟨hy, hqy⟩ := mem_neighbors.mp hyQ
  obtain ⟨j, rfl⟩ := adjacent_exists_flip hqy
  have hj : j ∈ T :=
    (direction_of_mem (ht _ hy hY) j).mp (by simpa only [BalancedCriticalSpectrum.flip_flip] using hqU)
  have hjc : j ≠ c := by
    rintro rfl
    exact hM (by simpa only [BalancedCriticalSpectrum.flip_flip] using hY)
  have hcT : c ∉ T :=
    next_outside hb hy (ht _ hy hY) hjc hj
      (by simpa only [BalancedCriticalSpectrum.flip_flip] using hm)
  exact ⟨b, hbT, c, hcT, j, hj, hbc, hp, hm, hqU, hy, hY, hpair, hmPair,
    by rw [hqPair, Finset.pair_comm]⟩


private theorem no_high_two_triple {n : ℕ} {U : Finset (Q n)} {T : Finset (Fin n)}
    (hb : IsBalanced U) (ht : ∀ x ∈ U, High U x → directions U x = T)
    {x : Q n} (hx : x ∈ U) (hX : High U x)
    {i j : Fin n} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j)
    (hy : flip (flip x i) j ∈ U) : False :=
  next_outside hb hx (ht x hx hX) hij hi hy hj

private theorem pair_in_triple {T : Finset (Fin 5)} (hT : T.card = 3)
    {i j k l : Fin 5} (hi : i ∈ T) (hj : j ∈ T) (hk : k ∈ T) (hl : l ∈ T)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    l = i ∨ l = j ∨ l = k := by
  have ht : ({k, i, j} : Finset (Fin 5)) = T :=
    Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hk (Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)))
      (by simp [hT, hki, hkj, hij])
  simpa [← ht, or_left_comm, or_comm] using hl

private theorem endpoint_dirs_eq {U : Finset (Q 5)} {T : Finset (Fin 5)}
    (hb : IsBalanced U) (ht : ∀ x ∈ U, High U x → directions U x = T)
    (hT : T.card = 3) (v : Q 5)
    (hit : ∀ k ∈ T, ∃ l ∈ T, flip (flip v k) l ∈ U ∧ High U (flip (flip v k) l))
    {i j : Fin 5} (hi : i ∈ T) (hj : j ∈ T)
    (hy : flip (flip v i) j ∈ U) : i = j := by
  by_contra hij
  have hn : ¬ T ⊆ ({i, j} : Finset (Fin 5)) := by
    intro hs
    have hc := Finset.card_le_card hs
    simp [hT, hij] at hc
  obtain ⟨k, hk, hkij⟩ := Finset.not_subset.mp hn
  have hkne : k ≠ i ∧ k ≠ j := by simpa using hkij
  obtain ⟨l, hl, hz, hZ⟩ := hit k hk
  rcases pair_in_triple hT hi hj hk hl hij hkne.1 hkne.2 with hl | hl | hl
  · subst l
    have he : flip (flip (flip (flip v k) i) k) j = flip (flip v i) j := by
      rw [flip_comm (flip v k) i k, BalancedCriticalSpectrum.flip_flip]
    exact no_high_two_triple hb ht hz hZ hk hj hkne.2 (he.symm ▸ hy)
  · subst l
    have he : flip (flip (flip (flip v k) j) k) i = flip (flip v i) j := by
      rw [flip_comm (flip v k) j k, BalancedCriticalSpectrum.flip_flip, flip_comm]
    exact no_high_two_triple hb ht hz hZ hk hi hkne.1 (he.symm ▸ hy)
  · subst l
    rw [BalancedCriticalSpectrum.flip_flip] at hz hZ
    exact no_high_two_triple hb ht hz hZ hi hj hij hy

private theorem flip_middle_pair {n : ℕ} (x : Q n) (i b c : Fin n) :
    flip (flip (flip x i) b) c = flip (flip (flip x b) c) i := by
  rw [flip_comm x i b, flip_comm (flip x b) i c]

private theorem oriented_word_sign {n : ℕ} {U : Finset (Q n)}
    {s : Q n → ℝ} (hs : BalancedCriticalSpectrum.IsSwitching U s)
    {x : Q n} {i b c : Fin n} (hib : i ≠ b) (hic : i ≠ c)
    (hx : x ∈ U) (hp : flip x i ∈ U) (hm : flip (flip x i) b ∈ U)
    (hq : flip (flip (flip x b) c) i ∈ U) (hy : flip (flip x b) c ∈ U) :
    gamma b (gamma c (fun _ => 1)) x = s x * s (flip (flip x b) c) := by
  have h := TwentyPointEightWord.word_switching hs x [i, b, c, i] (by
    intro z hz
    simp only [List.scanl_cons, List.scanl_nil, List.mem_cons, List.not_mem_nil, or_false,
      flip_middle_pair x i b c, BalancedCriticalSpectrum.flip_flip] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact hx
    · exact hp
    · exact hm
    · exact hq
    · exact hy)
  have hg (z : Q n → ℝ) : gamma i (gamma b (gamma c (gamma i z))) =
      gamma b (gamma c z) := by
    rw [BalancedCubeGirth.gamma_anticommute hib, BalancedCubeGirth.gamma_anticommute hic,
      map_neg, neg_neg, TwentyPointEightWord.gamma_square]
  simpa [TwentyPointEightWord.wordGamma, hg, flip_middle_pair x i b c] using h


private def NormalPath (U : Finset (Q 5)) (x : Q 5) (i b c : Fin 5) : Prop :=
  let y := flip (flip x b) c
  let p := flip x i
  let m := flip p b
  let q := flip y i
  p ∈ U ∧ m ∈ U ∧ q ∈ U ∧
    neighbors U p = {x, m} ∧ neighbors U m = {p, q} ∧ neighbors U q = {m, y}

private theorem all_paths_same_order {U : Finset (Q 5)} {T : Finset (Fin 5)}
    {x : Q 5} {b c : Fin 5} (hb : IsBalanced U) (hx : x ∈ U)
    (hbT : b ∉ T) (hcT : c ∉ T) (hbc : b ≠ c)
    (hy : flip (flip x b) c ∈ U)
    (hpaths : ∀ i ∈ T, NormalPath U x i b c ∨ NormalPath U x i c b)
    {k : Fin 5} (hk : k ∈ T) (hpath : NormalPath U x k b c) :
    ∀ i ∈ T, NormalPath U x i b c := by
  obtain ⟨s, hs⟩ := hb
  have sign {i a d : Fin 5} (hi : i ∈ T) (ha : a ∉ T) (hd : d ∉ T)
      (hy' : flip (flip x a) d ∈ U) (hp : NormalPath U x i a d) :
      gamma a (gamma d (fun _ => 1)) x = s x * s (flip (flip x a) d) :=
    oriented_word_sign hs (fun h => ha (h ▸ hi)) (fun h => hd (h ▸ hi)) hx
      hp.1 hp.2.1 hp.2.2.1 hy'
  have hsign := sign hk hbT hcT hy hpath
  have hsx : s x ≠ 0 := by
    rcases hs.1 x hx with h | h <;> rw [h] <;> norm_num
  have hsy : s (flip (flip x b) c) ≠ 0 := by
    rcases hs.1 _ hy with h | h <;> rw [h] <;> norm_num
  intro i hi
  rcases hpaths i hi with hp | hp
  · exact hp
  · have hy' := flip_comm x b c ▸ hy
    have hsign' := sign hi hcT hbT hy' hp
    rw [flip_comm x c b] at hsign'
    have h := congrFun (BalancedCubeGirth.gamma_anticommute hbc (fun _ => 1)) x
    simp only [Pi.neg_apply, hsign, hsign'] at h
    exact (mul_ne_zero hsx hsy (by linarith)).elim

private theorem closed_of_paths {U : Finset (Q 5)} {T : Finset (Fin 5)}
    (hc : ((hypercube 5).induce (U : Set (Q 5))).Connected)
    {x : Q 5} {b c : Fin 5} (hx : x ∈ U)
    (htx : directions U x = T) (hty : directions U (flip (flip x b) c) = T)
    (hpaths : ∀ i ∈ T, NormalPath U x i b c) :
    ∀ z ∈ U, z = x ∨ z = flip (flip x b) c ∨
      ∃ i ∈ T, z = flip x i ∨ z = flip (flip x i) b ∨ z = flip (flip (flip x b) c) i := by
  let y := flip (flip x b) c
  let P : Q 5 → Prop := fun z => z = x ∨ z = y ∨
    ∃ i ∈ T, z = flip x i ∨ z = flip (flip x i) b ∨ z = flip y i
  have step (u v : Q 5) (hu : P u) (hv : v ∈ neighbors U u) : P v := by
    rcases hu with rfl | rfl | ⟨i, hi, rfl | rfl | rfl⟩
    · obtain ⟨j, rfl⟩ := adjacent_exists_flip (mem_neighbors.mp hv).2
      exact Or.inr (Or.inr ⟨j, (direction_of_mem htx j).mp (mem_neighbors.mp hv).1, Or.inl rfl⟩)
    · obtain ⟨j, rfl⟩ := adjacent_exists_flip (mem_neighbors.mp hv).2
      exact Or.inr (Or.inr ⟨j, (direction_of_mem hty j).mp (mem_neighbors.mp hv).1,
        Or.inr (Or.inr rfl)⟩)
    · have hp := (hpaths i hi).2.2.2.1
      rw [hp] at hv
      rcases Finset.mem_insert.mp hv with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inl (Finset.mem_singleton.mp h))⟩)
    · have hp := (hpaths i hi).2.2.2.2.1
      rw [hp] at hv
      rcases Finset.mem_insert.mp hv with h | h
      · exact Or.inr (Or.inr ⟨i, hi, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inr (Finset.mem_singleton.mp h))⟩)
    · have hp := (hpaths i hi).2.2.2.2.2
      rw [hp] at hv
      rcases Finset.mem_insert.mp hv with h | h
      · exact Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inl h)⟩)
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp h))
  let u : (U : Set (Q 5)) := ⟨x, hx⟩
  have reach (v : (U : Set (Q 5)))
      (hwalk : Relation.ReflTransGen (((hypercube 5).induce (U : Set (Q 5))).Adj) u v) :
      P v.val := by
    induction hwalk with
    | refl => exact Or.inl rfl
    | @tail a v _ hab ih => exact step a.val v.val ih (mem_neighbors.mpr ⟨v.property, hab⟩)
  intro z hz
  exact reach ⟨z, hz⟩ ((SimpleGraph.reachable_iff_reflTransGen u ⟨z, hz⟩).mp
    (hc.preconnected u ⟨z, hz⟩))


private theorem card_of_normal_form {U : Finset (Q 5)} {T : Finset (Fin 5)}
    (hT : T.card = 3) (x : Q 5) {b c : Fin 5}
    (hbc : b ≠ c) (hb : b ∉ T) (hc : c ∉ T)
    (hm : ∀ z : Q 5, z ∈ U ↔ z = x ∨ z = flip (flip x b) c ∨
      ∃ i ∈ T, z = flip x i ∨ z = flip (flip x i) b ∨ z = flip (flip (flip x b) c) i) :
    U.card = 11 := by
  let y := flip (flip x b) c
  let L := insert x (T.image (flip x))
  let M := T.image (fun i => flip (flip x i) b)
  let R := insert y (T.image (flip y))
  have card_end (v : Q 5) : (insert v (T.image (flip v))).card = 4 := by
    have hv : v ∉ T.image (flip v) := by
      rintro hv
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hv
      exact (flip_adj v i).ne he.symm
    rw [Finset.card_insert_of_notMem hv, Finset.card_image_of_injective _ (flip_injective v), hT]
  have card_mid : M.card = 3 := by
    rw [Finset.card_image_of_injective, hT]
    intro i j he
    exact flip_injective x (by simpa using congrArg (fun z : Q 5 => BalancedCriticalSpectrum.flip z b) he)
  have hL {z : Q 5} (hz : z ∈ L) : z b = x b ∧ z c = x c := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨rfl, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hbi : b ≠ i := fun h => hb (h ▸ hi)
      have hci : c ≠ i := fun h => hc (h ▸ hi)
      simp [BalancedCriticalSpectrum.flip, hbi, hci]
  have hM {z : Q 5} (hz : z ∈ M) : z b = !x b ∧ z c = x c := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hbi : b ≠ i := fun h => hb (h ▸ hi)
    have hci : c ≠ i := fun h => hc (h ▸ hi)
    simp [BalancedCriticalSpectrum.flip, hbi, hci, hbc.symm]
  have hR {z : Q 5} (hz : z ∈ R) : z c = !x c := by
    have hy : y c = !x c := by simp [y, BalancedCriticalSpectrum.flip, hbc.symm]
    rcases Finset.mem_insert.mp hz with he | hz
    · exact he.symm ▸ hy
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hci : c ≠ i := fun h => hc (h ▸ hi)
      simpa [BalancedCriticalSpectrum.flip, hci] using hy
  have bool_ne (a : Bool) : a ≠ !a := by cases a <;> decide
  have hLM : Disjoint L M := by
    apply Finset.disjoint_left.mpr
    intro z hz hm
    exact bool_ne _ ((hL hz).1.symm.trans (hM hm).1)
  have hLR : Disjoint (L ∪ M) R := by
    apply Finset.disjoint_left.mpr
    intro z hz hr
    have he : z c = x c := (Finset.mem_union.mp hz).elim (fun hl => (hL hl).2) (fun hm => (hM hm).2)
    exact bool_ne _ (he.symm.trans (hR hr))
  have hU : U = L ∪ M ∪ R := by
    ext z
    rw [hm]
    simp only [L, M, R, y, Finset.mem_union, Finset.mem_insert, Finset.mem_image]
    aesop
  rw [hU, Finset.card_union_of_disjoint hLR, Finset.card_union_of_disjoint hLM,
    show L.card = 4 from card_end x, card_mid, show R.card = 4 from card_end y]

/-- A connected balanced induced subcubic support in the five-cube, with common
degree-three directions and positive row eigenvalue square root of five, consists
of three four-edge paths with one common order of the complementary directions. -/
theorem eleven_vertex_normal_form (U : Finset (Q 5)) (T : Finset (Fin 5))
    (hc : ((hypercube 5).induce (U : Set (Q 5))).Connected)
    (hb : IsBalanced U) (hdeg : ∀ x ∈ U, (directions U x).card ≤ 3)
    (ht : ∀ x ∈ U, (directions U x).card = 3 → directions U x = T)
    (f : Q 5 → ℝ) (hpos : ∀ x ∈ U, 0 < f x)
    (hf : ∀ x ∈ U, (∑ y ∈ U.filter ((hypercube 5).Adj x), f y) = Real.sqrt 5 * f x) :
    ∃ x : Q 5, ∃ b c : Fin 5, b ≠ c ∧ (Finset.univ \ T : Finset (Fin 5)) = {b, c} ∧
      let y := flip (flip x b) c
      directions U x = T ∧ directions U y = T ∧ U.card = 11 ∧
      ∀ z : Q 5, z ∈ U ↔ z = x ∨ z = y ∨
        ∃ i ∈ T, z = flip x i ∨ z = flip (flip x i) b ∨ z = flip y i := by
  obtain ⟨pairs, middle⟩ := forced_layers hb hdeg ht hpos hf
  have high_exists : ∃ x ∈ U, High U x := by
    by_contra! h
    obtain ⟨v⟩ := hc.nonempty
    have hn (z : Q 5) : ¬ Near U z := by
      rintro ⟨y, hy, hY⟩
      exact h y (mem_neighbors.mp hy).1 hY
    obtain ⟨hd, hN⟩ := middle v.val v.property (h _ v.property) (hn _)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (neighbors U v.val).card)
    exact hn y (hN y hy)
  obtain ⟨x, hx, hX⟩ := high_exists
  have htx := ht x hx hX
  have hT : T.card = 3 := by rw [← htx]; exact hX
  have hcompl : (Finset.univ \ T : Finset (Fin 5)).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), hT]
    decide
  obtain ⟨b, c, hbc, hbcT⟩ := Finset.card_eq_two.mp hcompl
  have compl (a : Fin 5) : a ∉ T ↔ a = b ∨ a = c := by
    have hm : a ∈ (Finset.univ \ T : Finset (Fin 5)) ↔ a ∉ T := by simp
    rw [hbcT] at hm
    simpa using hm.symm
  have hbT := (compl b).mpr (Or.inl rfl)
  have hcT := (compl c).mpr (Or.inr rfl)
  have ord {a d : Fin 5} (ha : a ∉ T) (hd : d ∉ T) (had : a ≠ d) :
      (a = b ∧ d = c) ∨ (a = c ∧ d = b) := by
    rcases (compl a).mp ha with rfl | rfl <;>
      rcases (compl d).mp hd with rfl | rfl <;> simp_all
  let y := flip (flip x b) c
  have endpoint {i a d j : Fin 5} (ho : (a = b ∧ d = c) ∨ (a = c ∧ d = b)) :
      flip (flip (flip (flip x i) a) d) j = flip (flip y i) j := by
    rw [flip_middle_pair x i a d]
    rcases ho with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · rw [ha, hd]
    · rw [ha, hd, flip_comm x c b]
  have hit (i : Fin 5) (hi : i ∈ T) :
      ∃ j ∈ T, flip (flip y i) j ∈ U ∧ High U (flip (flip y i) j) := by
    obtain ⟨a, ha, d, hd, j, hj, had, _, _, _, hmem, hhigh, _⟩ :=
      outward_path hb ht pairs middle hx hX hi
    rw [endpoint (ord ha hd had)] at hmem hhigh
    exact ⟨j, hj, hmem, hhigh⟩
  have paths (i : Fin 5) (hi : i ∈ T) : y ∈ U ∧ High U y ∧
      (NormalPath U x i b c ∨ NormalPath U x i c b) := by
    obtain ⟨a, ha, d, hd, j, hj, had, hp, hm, hq, hmem, hhigh, hpPair, hmPair, hqPair⟩ :=
      outward_path hb ht pairs middle hx hX hi
    have ho := ord ha hd had
    have hij := endpoint_dirs_eq hb ht hT y hit hi hj (by rwa [← endpoint ho])
    subst j
    rw [endpoint ho, BalancedCriticalSpectrum.flip_flip] at hmem hhigh
    refine ⟨hmem, hhigh, ?_⟩
    have path : NormalPath U x i a d := by
      rw [flip_middle_pair x i a d] at hq hmPair hqPair
      rw [BalancedCriticalSpectrum.flip_flip] at hqPair
      exact ⟨hp, hm, hq, hpPair, hmPair, hqPair⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl path
    · exact Or.inr path
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have close {a d : Fin 5} (had : a ≠ d)
      (hadT : (Finset.univ \ T : Finset (Fin 5)) = {a, d})
      (ha : a ∉ T) (hd : d ∉ T)
      (hy : flip (flip x a) d ∈ U) (hY : High U (flip (flip x a) d))
      (hs : ∀ i ∈ T, NormalPath U x i a d ∨ NormalPath U x i d a)
      (hkPath : NormalPath U x k a d) : ∃ x : Q 5, ∃ b c : Fin 5,
        b ≠ c ∧ (Finset.univ \ T : Finset (Fin 5)) = {b, c} ∧
        let y := flip (flip x b) c
        directions U x = T ∧ directions U y = T ∧ U.card = 11 ∧
        ∀ z : Q 5, z ∈ U ↔ z = x ∨ z = y ∨
          ∃ i ∈ T, z = flip x i ∨ z = flip (flip x i) b ∨ z = flip y i := by
    have hall := all_paths_same_order hb hx ha hd had hy hs hk hkPath
    have hty := ht _ hy hY
    have hiff (z : Q 5) : z ∈ U ↔ z = x ∨ z = flip (flip x a) d ∨
        ∃ i ∈ T, z = flip x i ∨ z = flip (flip x i) a ∨ z = flip (flip (flip x a) d) i := by
      refine ⟨closed_of_paths hc hx htx hty hall z, ?_⟩
      rintro (rfl | rfl | ⟨i, hi, rfl | rfl | rfl⟩)
      · exact hx
      · exact hy
      · exact (hall i hi).1
      · exact (hall i hi).2.1
      · exact (hall i hi).2.2.1
    exact ⟨x, a, d, had, hadT, htx, hty, card_of_normal_form hT x had ha hd hiff, hiff⟩
  obtain ⟨hy, hY, hp | hp⟩ := paths k hk
  · exact close hbc hbcT hbT hcT hy hY (fun i hi => (paths i hi).2.2) hp
  · rw [Finset.pair_comm] at hbcT
    have hswap := flip_comm x b c
    exact close hbc.symm hbcT hcT hbT (hswap ▸ hy) (hswap ▸ hY)
      (fun i hi => ((paths i hi).2.2).symm) hp

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SingleTripleFiveCube.eleven_vertex_normal_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms eleven_vertex_normal_form

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SingleTripleFiveCube
