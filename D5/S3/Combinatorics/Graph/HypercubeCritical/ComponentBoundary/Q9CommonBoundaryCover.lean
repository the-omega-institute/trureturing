/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: At most three parallel covers per support on a common boundary edge of the nine-cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-! Four parallel covers of a common boundary edge force either too many
directions at a selected edge or a negative closed walk in the other support. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CommonBoundaryCover

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj gamma IsBalanced)
open BalancedCubeGirth (gamma_anticommute no_selected_square)
open BalancedCubeComponentBoundary
  (directions regular_directions exterior_even neighbor_card_add_le_six)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (mem_directions directions_card)
open TwentyPointEightWord (wordGamma gamma_square word_switching)
open BalancedCriticalSpectrum (switching_sq)

set_option maxRecDepth 4096 in
private theorem no_negative_eight_walk {n : ℕ} {D : Finset (Q n)}
    (hb : IsBalanced D) (x : Q n) {i j k l : Fin n}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (hwalk : ∀ y ∈ [l, k, i, j, k, l, i, j].scanl flip x, y ∈ D)
    (hclosed : [l, k, i, j, k, l, i, j].foldl flip x = x) : False := by
  obtain ⟨sigma, hs⟩ := hb
  have hx := hwalk x (by simp [List.scanl_cons])
  let one : Q n → ℝ := fun _ => 1
  have hpositive : wordGamma [l, k, i, j, k, l, i, j] one x = 1 := calc
    _ = sigma x * sigma ([l, k, i, j, k, l, i, j].foldl flip x) :=
      word_switching hs x _ hwalk
    _ = sigma x * sigma x := congrArg (fun y => sigma x * sigma y) hclosed
    _ = 1 := by simpa only [pow_two] using switching_sq hs hx
  have hconj (a : Fin n) (hai : a ≠ i) (haj : a ≠ j) (z : Q n → ℝ) :
      gamma a (gamma i (gamma j (gamma a z))) = gamma i (gamma j z) := by
    calc
      _ = -gamma i (gamma a (gamma j (gamma a z))) := gamma_anticommute hai _
      _ = _ := by rw [gamma_anticommute haj (gamma a z), gamma_square, map_neg, neg_neg]
  have hnegative : gamma l (gamma k (gamma i (gamma j
      (gamma k (gamma l (gamma i (gamma j one))))))) = -one := by
    rw [hconj k hki hkj, hconj l hli hlj,
      gamma_anticommute hij.symm (gamma j one), map_neg, gamma_square, gamma_square]
  have hword : wordGamma [l, k, i, j, k, l, i, j] one = -one := by
    simpa only [wordGamma, List.foldr_cons, List.foldr_nil] using hnegative
  have hsign : wordGamma [l, k, i, j, k, l, i, j] one x = -1 := congrFun hword x
  exact (by norm_num : (-1 : ℝ) ≠ 1) (hsign.symm.trans hpositive)

private theorem direction_avoids_cover {C D : Finset (Q 9)}
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    {A : Finset (Fin 9)} {x : Q 9} {p a : Fin 9}
    (hcover : ∀ r ∈ A, flip x r ∈ C)
    (ha : a ∈ directions D (flip x p)) : a ∉ A := by
  intro haA
  apply hcross _ (hcover a haA) _ ((mem_directions _ _ _).mp ha)
  rw [flip_comm x p a]
  exact flip_adj _ _

open Classical in
private theorem shared_direction_impossible {C D : Finset (Q 9)}
    (hrD : ((hypercube 9).induce (D : Set _)).IsRegularOfDegree 3)
    (hbD : IsBalanced D)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    {v : Q 9} {k p : Fin 9} {A : Finset (Fin 9)} (hA : A.card = 4)
    (hcover : ∀ a ∈ A, flip v a ∈ C) (hcover' : ∀ a ∈ A, flip (flip v k) a ∈ C)
    (hvD : v ∉ D) (hwD : flip v k ∉ D)
    (hpA : p ∉ A) (hp : flip v p ∈ D) (hp' : flip (flip v k) p ∈ D) : False := by
  let U := directions D (flip v p)
  let V := directions D (flip (flip v k) p)
  have hedge : flip (flip v p) k = flip (flip v k) p := flip_comm v p k
  have hpK : flip (flip v p) k ∈ D := by rwa [hedge]
  have hmeet : U ∩ V = {k} := by
    ext a
    rw [Finset.mem_inter, Finset.mem_singleton]
    change a ∈ directions D (flip v p) ∧ a ∈ directions D (flip (flip v k) p) ↔ a = k
    simp only [mem_directions]
    constructor
    · rintro ⟨ha, ha'⟩
      by_contra hne
      exact no_selected_square hbD (fun he => hne he.symm) hp hpK ha (by rwa [hedge])
    · rintro rfl
      rw [← hedge, BalancedCriticalSpectrum.flip_flip]
      exact ⟨hpK, hp⟩
  have hU := regular_directions D hrD hp
  have hV := regular_directions D hrD hp'
  have hUV : (U ∪ V).card = 5 := by
    have h := Finset.card_union_add_card_inter U V
    rw [hmeet, Finset.card_singleton] at h
    change U.card = 3 at hU
    change V.card = 3 at hV
    omega
  have hdisj : Disjoint (insert p A) (U ∪ V) := by
    apply Finset.disjoint_left.mpr
    intro a ha haUV
    rcases Finset.mem_union.mp haUV with haU | haV
    · rcases Finset.mem_insert.mp ha with rfl | haA
      · exact hvD (by
          simpa only [BalancedCriticalSpectrum.flip_flip] using (mem_directions _ _ _).mp haU)
      · exact direction_avoids_cover hcross hcover haU haA
    · rcases Finset.mem_insert.mp ha with rfl | haA
      · exact hwD (by
          simpa only [BalancedCriticalSpectrum.flip_flip] using (mem_directions _ _ _).mp haV)
      · exact direction_avoids_cover hcross hcover' haV haA
  have hle : ((insert p A) ∪ (U ∪ V)).card ≤ 9 := by
    simpa using Finset.card_le_card (Finset.subset_univ ((insert p A) ∪ (U ∪ V)))
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hpA, hA, hUV] at hle
  omega

open Classical in
private theorem forced_direction {C D : Finset (Q 9)}
    (hrD : ((hypercube 9).induce (D : Set _)).IsRegularOfDegree 3)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    {x : Q 9} {k p : Fin 9} {A : Finset (Fin 9)}
    (hA : A.card = 4) (hcover : ∀ a ∈ A, flip x a ∈ C)
    (hx : x ∉ D) (hp : flip x p ∈ D) (hpA : p ∉ A)
    (hkA : k ∉ A) (hkp : k ≠ p) (hmissing : flip (flip x p) k ∉ D)
    {q : Fin 9} (hqp : q ≠ p) (hqk : q ≠ k) (hqA : q ∉ A) :
    flip (flip x p) q ∈ D := by
  let B := (Finset.univ : Finset (Fin 9)) \ insert k (insert p A)
  have hsubset : directions D (flip x p) ⊆ B := by
    intro a ha
    have haA := direction_avoids_cover hcross hcover ha
    have hap : a ≠ p := by
      rintro rfl
      exact hx (by
        simpa only [BalancedCriticalSpectrum.flip_flip] using (mem_directions _ _ _).mp ha)
    have hak : a ≠ k := fun he => hmissing (he ▸ (mem_directions _ _ _).mp ha)
    simp [B, hap, hak, haA]
  have hcard : B.card = 3 := by
    have hk : k ∉ insert p A := by simp [hkp, hkA]
    simp [B, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_insert_of_notMem hk, Finset.card_insert_of_notMem hpA, hA]
  have heq := Finset.eq_of_subset_of_card_le hsubset
    (by rw [hcard, regular_directions D hrD hp])
  apply (mem_directions _ _ _).mp
  rw [heq]
  simp [B, hqp, hqk, hqA]

open Classical in
/-- On an exterior cube edge meeting both balanced cubic supports at both ends,
at most three directions translate the edge into the first support.
Exchanging the supports gives the same bound for the second support. -/
theorem cover_card_le_three
    (C D : Finset (Q 9))
    (hrC : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set _)).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdisj : Disjoint C D)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (v : Q 9) (k : Fin 9)
    (hvC : v ∉ C) (hvD : v ∉ D) (hwC : flip v k ∉ C) (hwD : flip v k ∉ D)
    (hvCpos : 0 < (directions C v).card) (hvDpos : 0 < (directions D v).card)
    (hwCpos : 0 < (directions C (flip v k)).card)
    (hwDpos : 0 < (directions D (flip v k)).card) :
    (directions C v ∩ directions C (flip v k)).card ≤ 3 := by
  let w := flip v k
  let A := directions C v ∩ directions C w
  change A.card ≤ 3
  by_contra hbad
  have endpoint (x : Q 9) (hxC : x ∉ C) (hxD : x ∉ D)
      (hxCpos : 0 < (directions C x).card) (hxDpos : 0 < (directions D x).card)
      (hsub : A ⊆ directions C x) : A.card = 4 ∧ (directions D x).card = 2 := by
    have hsum := neighbor_card_add_le_six C D hrC hrD hbC hbD hdisj hcross x hxC hxD
      (by rwa [← directions_card]) (by rwa [← directions_card])
    rw [← directions_card, ← directions_card] at hsum
    obtain ⟨d, hd⟩ := exterior_even D hrD hbD x hxD
    have hle := Finset.card_le_card hsub
    omega
  have ⟨hA, hvTwo⟩ := endpoint v hvC hvD hvCpos hvDpos Finset.inter_subset_left
  have ⟨_, hwTwo⟩ := endpoint w hwC hwD hwCpos hwDpos Finset.inter_subset_right
  have hcover (a : Fin 9) (ha : a ∈ A) : flip v a ∈ C :=
    (mem_directions _ _ _).mp (Finset.mem_inter.mp ha).1
  have hcover' (a : Fin 9) (ha : a ∈ A) : flip w a ∈ C :=
    (mem_directions _ _ _).mp (Finset.mem_inter.mp ha).2
  have havoid {x : Q 9} (hc : ∀ a ∈ A, flip x a ∈ C) {p : Fin 9}
      (hp : flip x p ∈ D) : p ∉ A :=
    fun h => Finset.disjoint_left.mp hdisj (hc p h) hp
  have hsep : Disjoint (directions D v) (directions D w) := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hpD := (mem_directions _ _ _).mp hp
    exact shared_direction_impossible hrD hbD hcross hA hcover hcover' hvD hwD
      (havoid hcover hpD) hpD ((mem_directions _ _ _).mp hp')
  obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp hvTwo
  have hi : i ∈ directions D v := by simp [hpair]
  have hj : j ∈ directions D v := by simp [hpair]
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (show 0 < (directions D w).card by omega)
  have hiD := (mem_directions _ _ _).mp hi
  have hjD := (mem_directions _ _ _).mp hj
  have hlD := (mem_directions _ _ _).mp hl
  have hkA : k ∉ A := fun h => hwC (hcover k h)
  have hki : k ≠ i := by rintro rfl; exact hwD hiD
  have hkj : k ≠ j := by rintro rfl; exact hwD hjD
  have hkl : k ≠ l := by
    rintro rfl
    exact hvD (by simpa only [w, BalancedCriticalSpectrum.flip_flip] using hlD)
  have hli : l ≠ i := by rintro rfl; exact Finset.disjoint_left.mp hsep hi hl
  have hlj : l ≠ j := by rintro rfl; exact Finset.disjoint_left.mp hsep hj hl
  have forceV {p q : Fin 9} (hp : p ∈ directions D v) (hkp : k ≠ p)
      (hqp : q ≠ p) (hqk : q ≠ k) (hqA : q ∉ A) : flip (flip v p) q ∈ D := by
    have hpD := (mem_directions _ _ _).mp hp
    refine forced_direction hrD hcross hA hcover hvD hpD (havoid hcover hpD)
      hkA hkp ?_ hqp hqk hqA
    rw [flip_comm v p k]
    exact fun h => Finset.disjoint_left.mp hsep hp ((mem_directions _ _ _).mpr h)
  have forceW {q : Fin 9} (hql : q ≠ l) (hqk : q ≠ k) (hqA : q ∉ A) :
      flip (flip w l) q ∈ D := by
    refine forced_direction hrD hcross hA hcover' hwD hlD (havoid hcover' hlD)
      hkA hkl ?_ hql hqk hqA
    rw [flip_comm w l k, BalancedCriticalSpectrum.flip_flip v k]
    exact fun h => Finset.disjoint_left.mp hsep ((mem_directions _ _ _).mpr h) hl
  have hiA := havoid hcover hiD
  have hjA := havoid hcover hjD
  have hlA := havoid hcover' hlD
  have hilD := forceV hi hki hli hkl.symm hlA
  have hjlD := forceV hj hkj hlj hkl.symm hlA
  have hjiD := forceV hj hkj hij hki.symm hiA
  have hliD := forceW hli.symm hki.symm hiA
  have hljD := forceW hlj.symm hkj.symm hjA
  -- The forced edges trace the word l, k, i, j, k, l, i, j.
  have hstep₂ : flip (flip (flip v i) l) k = flip (flip w l) i := by
    rw [flip_comm (flip v i) l k, flip_comm v i k]
    exact flip_comm w i l
  have hstep₅ : flip (flip (flip w l) j) k = flip (flip v j) l := by
    rw [flip_comm (flip w l) j k, flip_comm w l k]
    simp only [w, BalancedCriticalSpectrum.flip_flip]
    exact flip_comm v l j
  have hstep₈ : flip (flip (flip v j) i) j = flip v i := by
    rw [flip_comm (flip v j) i j, BalancedCriticalSpectrum.flip_flip]
  apply no_negative_eight_walk hbD (flip v i) hij hki hkj hli hlj
  · intro y hy
    simp only [List.scanl_cons, List.scanl_nil, hstep₂, hstep₅, hstep₈,
      BalancedCriticalSpectrum.flip_flip, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals assumption
  · simp only [List.foldl_cons, List.foldl_nil, hstep₂, hstep₅, hstep₈,
      BalancedCriticalSpectrum.flip_flip]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CommonBoundaryCover
