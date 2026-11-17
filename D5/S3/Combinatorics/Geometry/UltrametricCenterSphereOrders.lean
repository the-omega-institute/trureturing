/- GID: D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: The possible orders for prescribed ultrametric center sphere counts follow a divisor recurrence. -/

import D5.S3.Combinatorics.Geometry.UltrametricConstantJoin
import Mathlib.Data.Fintype.EquivFin

/-! Theorem 1.2 of the pinned written proof of #29039. -/

noncomputable section

namespace UltrametricCenterSphereOrders

open Metric
open scoped BigOperators
open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

/-- A sum of a nonempty finite sequence. Indices distinguish repeated summands. -/
def PositiveSum (A : Set ℕ) (t : ℕ) : Prop :=
  ∃ k : ℕ, ∃ s : Fin (k + 1) → ℕ, (∀ j, s j ∈ A) ∧ (∑ j, s j) = t

/-- Candidate orders at each level of the sphere count sequence. -/
def orders (b : ℕ → ℕ) : ℕ → Set ℕ
  | 0 => {1}
  | i + 1 => {n | ∃ t, PositiveSum (orders b i) t ∧ t ∣ b (i + 1) ∧ n = b (i + 1) + t}

theorem orders_pos (b : ℕ → ℕ) (i : ℕ) {n : ℕ} (hn : n ∈ orders b i) : 0 < n := by
  induction i generalizing n with
  | zero =>
    simp [orders] at hn
    omega
  | succ i ih =>
    obtain ⟨t, ⟨k, s, hs, rfl⟩, _, rfl⟩ := hn
    have hp := ih (hs 0)
    have hle : s 0 ≤ ∑ j, s j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ 0)
    omega

/-- The divisor search is bounded by the positive sphere count. -/
theorem mem_orders_succ_iff_bounded (b : ℕ → ℕ) (i n : ℕ) (hb : 0 < b (i + 1)) :
    n ∈ orders b (i + 1) ↔
      ∃ t, 0 < t ∧ t ≤ b (i + 1) ∧ PositiveSum (orders b i) t ∧
        t ∣ b (i + 1) ∧ n = b (i + 1) + t := by
  constructor
  · rintro ⟨t, hsum, hd, hn⟩
    obtain ⟨k, s, hs, hst⟩ := hsum
    have hp := orders_pos b i (hs 0)
    have hle : s 0 ≤ ∑ j, s j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ 0)
    exact ⟨t, by omega, Nat.le_of_dvd hb hd, ⟨k, s, hs, hst⟩, hd, hn⟩
  · rintro ⟨t, _, _, hs, hd, hn⟩
    exact ⟨t, hs, hd, hn⟩

variable {X : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]

omit [MetricSpace X] [IsUltrametricDist X] in
/-- Count a partition by its actual pieces, and retain representatives and coverage. -/
private theorem partition_card {S : Set X} (hS : S.Nonempty) (B : X → Set X)
    (hself : ∀ x ∈ S, x ∈ B x)
    (hsub : ∀ x ∈ S, B x ⊆ S)
    (heq : ∀ x ∈ S, ∀ y ∈ B x, B y = B x) :
    ∃ k : ℕ, ∃ p : Fin (k + 1) → X,
      (∀ j, p j ∈ S) ∧ (∀ y ∈ S, ∃ j, y ∈ B (p j)) ∧
      (∑ j, Nat.card (B (p j))) = Nat.card S := by
  classical
  let I := Set.range (fun x : S => B x.val)
  let f : S → I := fun x => ⟨B x.val, ⟨x, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨s, x, rfl⟩
    exact ⟨x, rfl⟩
  let p : I → S := fun j => Classical.choose (hf j)
  have hp (j : I) : f (p j) = j := Classical.choose_spec (hf j)
  have : Finite I := Finite.of_surjective f hf
  let _ : Fintype I := Fintype.ofFinite I
  have : Nonempty I := ⟨f ⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  let e : I ≃ Fin (k + 1) := Fintype.equivFinOfCardEq hk
  have hmem (x : S) (j : I) : f x = j ↔ x.val ∈ B (p j).val := by
    constructor
    · intro h
      have h' : B x.val = B (p j).val := congrArg Subtype.val (h.trans (hp j).symm)
      exact h' ▸ hself x.val x.property
    · intro h
      exact (Subtype.ext (heq _ (p j).property _ h)).trans (hp j)
  let g (j : I) : {x : S // f x = j} ≃ B (p j).val :=
    { toFun := fun x => ⟨x.val.val, (hmem x.val j).mp x.property⟩
      invFun := fun y =>
        let x : S := ⟨y.val, hsub _ (p j).property y.property⟩
        ⟨x, (hmem x j).mpr y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨k, fun j => (p (e.symm j)).val, fun j => (p (e.symm j)).property, ?_, ?_⟩
  · intro y hy
    exact ⟨e (f ⟨y, hy⟩), by simpa using (hmem ⟨y, hy⟩ (f ⟨y, hy⟩)).mp rfl⟩
  · calc
      _ = ∑ j : I, Nat.card (B (p j).val) := e.symm.sum_comp _
      _ = ∑ j : I, Nat.card {x : S // f x = j} :=
        Finset.sum_congr rfl (fun j _ => (Nat.card_congr (g j)).symm)
      _ = Nat.card (Σ j : I, {x : S // f x = j}) := Nat.card_sigma.symm
      _ = Nat.card S := Nat.card_congr (Equiv.sigmaFiberEquiv f)

/-- The lower closed balls partition a strict upper ball. -/
theorem lower_closedBalls {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) (x : X) :
    ∃ k : ℕ, ∃ p : Fin (k + 1) → X,
      (∀ j, p j ∈ ball x s) ∧ (∀ y ∈ ball x s, ∃ j, y ∈ closedBall (p j) r) ∧
      (∑ j, Nat.card (closedBall (p j) r)) = Nat.card (ball x s) := by
  refine partition_card ⟨x, mem_ball_self (hr.trans_lt hrs)⟩ (fun y => closedBall y r)
    (fun _ _ => mem_closedBall_self hr) ?_ ?_
  · intro y hy z hz
    exact (IsUltrametricDist.dist_triangle_max z y x).trans_lt
      (max_lt (lt_of_le_of_lt hz hrs) hy)
  · intro y _ z hz
    exact (IsUltrametricDist.closedBall_eq_of_mem hz).symm

omit [IsUltrametricDist X] in
/-- The strict ball through a point is the part of its closed ball outside its sphere. -/
theorem closedBall_card_eq {x : X} {s : ℝ} :
    Nat.card (closedBall x s) = Nat.card (sphere x s) + Nat.card (ball x s) := by
  simp only [Nat.card_coe_set_eq]
  rw [← closedBall_sdiff_ball]
  exact (Set.ncard_sdiff_add_ncard_of_subset ball_subset_closedBall).symm

private theorem ball_card_dvd_sphere_card {s : ℝ} (hs : 0 < s) (x : X) (b : ℕ)
    (hc : ∀ y : X, Nat.card (sphere y s) = b) : Nat.card (ball x s) ∣ b := by
  obtain ⟨k, p, hp, _, hsum⟩ :=
    partition_card (S := closedBall x s) ⟨x, mem_closedBall_self hs.le⟩ (fun y => ball y s)
      (fun _ _ => mem_ball_self hs)
      (fun y hy z hz => (IsUltrametricDist.dist_triangle_max z y x).trans
        (max_le (le_of_lt hz) hy))
      (fun _ _ _ hz => (IsUltrametricDist.ball_eq_of_mem hz).symm)
  have he (j : Fin (k + 1)) : Nat.card (ball (p j) s) = Nat.card (ball x s) := by
    have h := closedBall_card_eq (x := p j) (s := s)
    rw [← IsUltrametricDist.closedBall_eq_of_mem (hp j), hc] at h
    rw [closedBall_card_eq (x := x) (s := s), hc] at h
    omega
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  change (k + 1) * Nat.card (ball x s) = Nat.card (closedBall x s) at hsum
  rw [closedBall_card_eq, hc, Nat.add_mul, Nat.one_mul] at hsum
  exact ⟨k, by rw [Nat.mul_comm]; omega⟩

private theorem radii_mono {c : ℕ → ℝ} {h : ℕ} (hc : ∀ i < h, c i < c (i + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ h) : c i ≤ c j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hc j (by omega)).le

/-- Every closed ball at a prescribed level has an order in the recurrence. -/
theorem closedBall_order (c : ℕ → ℝ) (b : ℕ → ℕ) (h : ℕ) (hc0 : c 0 = 0)
    (hc : ∀ i < h, c i < c (i + 1))
    (hb : ∀ i ≤ h, ∀ x : X, Nat.card (sphere x (c i)) = b i) (x : X) :
    Nat.card (closedBall x (c h)) ∈ orders b h := by
  induction h generalizing x with
  | zero => simp [hc0, orders]
  | succ i ih =>
    have hr : 0 ≤ c i := by
      rw [← hc0]
      exact radii_mono hc (Nat.zero_le _) (Nat.le_succ _)
    have hlt := hc i (Nat.lt_succ_self i)
    obtain ⟨k, p, _, _, hsum⟩ := lower_closedBalls hr hlt x
    refine ⟨Nat.card (ball x (c (i + 1))), ⟨k, fun j => Nat.card (closedBall (p j) (c i)),
      fun j => ih (fun l hl => hc l (by omega)) (fun l hl => hb l (by omega)) (p j), hsum⟩,
      ball_card_dvd_sphere_card (hr.trans_lt hlt) x _ (hb _ le_rfl), ?_⟩
    rw [closedBall_card_eq, hb _ le_rfl]

/-- The maximum distance in a finite nonempty ultrametric is central. -/
private theorem exists_central_bound [Nonempty X] :
    ∃ d ∈ center X, ∀ x y : X, dist x y ≤ d := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (X × X))
    (fun q => dist q.1 q.2) Finset.univ_nonempty
  have hd (x y : X) : dist x y ≤ dist p.1 p.2 := hp (x, y) (Finset.mem_univ _)
  refine ⟨dist p.1 p.2, ⟨dist_nonneg, fun x => ?_⟩, hd⟩
  have hh := IsUltrametricDist.dist_triangle_max p.1 x p.2
  rcases le_max_iff.mp hh with hh | hh
  · exact ⟨p.1, (hd _ _).antisymm hh⟩
  · rw [dist_comm x p.2] at hh
    exact ⟨p.2, (hd _ _).antisymm hh⟩

/-- Necessity for the whole space, including the singleton case and zero count. -/
theorem necessary [Nonempty X] (c : ℕ → ℝ) (b : ℕ → ℕ) (h : ℕ) (hc0 : c 0 = 0)
    (hc : ∀ i < h, c i < c (i + 1))
    (hcenter : center X = c '' Set.Iic h)
    (hb : ∀ i ≤ h, ∀ x : X, Nat.card (sphere x (c i)) = b i) :
    b 0 = 1 ∧ Nat.card X ∈ orders b h := by
  let x : X := Classical.choice inferInstance
  have hzero := hb 0 (Nat.zero_le _) x
  simp [hc0] at hzero
  refine ⟨hzero.symm, ?_⟩
  obtain ⟨d, hd, hbound⟩ := exists_central_bound (X := X)
  rw [hcenter] at hd
  obtain ⟨j, hj, rfl⟩ := hd
  have ht : closedBall x (c h) = Set.univ :=
    Set.eq_univ_of_forall fun y => (hbound y x).trans (radii_mono hc hj le_rfl)
  have ho := closedBall_order c b h hc0 hc hb x
  simpa [ht, Nat.card_coe_set_eq] using ho


/-- At level `h`, only central radii through `h` and auxiliary radii
from gaps below `h` may occur. Gap `i` lies between `c i` and `c (i+1)`. -/
def allowed (c u v : ℕ → ℝ) (h : ℕ) : Set ℝ :=
  (c '' Set.Iic h) ∪ ((u '' Set.Iio h) ∪ (v '' Set.Iio h))

/-- A realization includes the original center predicate and every pointwise count. -/
structure Model (c : ℕ → ℝ) (b : ℕ → ℕ) (u v : ℕ → ℝ) (h n : ℕ) where
  carrier : Type
  [metric : MetricSpace carrier]
  [ultra : IsUltrametricDist carrier]
  [finite : Finite carrier]
  [nonempty : Nonempty carrier]
  order_eq : Nat.card carrier = n
  center_eq : center carrier = c '' Set.Iic h
  counts : ∀ i ≤ h, ∀ x : carrier, Nat.card (sphere x (c i)) = b i
  distances : ∀ x y : carrier, dist x y ∈ allowed c u v h

private theorem allowed_le {c u v : ℕ → ℝ} {h : ℕ}
    (hc : ∀ i < h, c i < c (i + 1))
    (hg : ∀ i < h, c i < u i ∧ u i < v i ∧ v i < c (i + 1))
    {d : ℝ} (hd : d ∈ allowed c u v h) : d ≤ c h := by
  rcases hd with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact radii_mono hc hj le_rfl
  · exact ((hg j hj).2.1.trans (hg j hj).2.2).le.trans (radii_mono hc hj le_rfl)
  · exact (hg j hj).2.2.le.trans (radii_mono hc hj le_rfl)

private theorem allowed_step (c u v : ℕ → ℝ) (i : ℕ) :
    allowed c u v i ⊆ allowed c u v (i + 1) := by
  rintro d (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact Or.inl ⟨j, (show j ≤ i from hj).trans (Nat.le_succ _), rfl⟩
  · exact Or.inr (Or.inl ⟨j, (show j < i from hj).trans (Nat.lt_succ_self _), rfl⟩)
  · exact Or.inr (Or.inr ⟨j, (show j < i from hj).trans (Nat.lt_succ_self _), rfl⟩)

open ConstantCrossDistance

private theorem join_dist_cases {ι : Type} (Y : ι → Type)
    [∀ i, MetricSpace (Y i)] [∀ i, IsUltrametricDist (Y i)]
    (a : ℝ) (ha : 0 < a) (hb : ∀ i (x y : Y i), dist x y ≤ a)
    (p q : Join Y a ha hb) :
    dist p q = a ∨ ∃ (i : ι) (x y : Y i), dist p q = dist x y := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    exact Or.inr ⟨i, x, y, dist_same Y a ha hb i x y⟩
  · exact Or.inl (dist_cross Y a ha hb h x y)

private def realize_step (c : ℕ → ℝ) (b : ℕ → ℕ) (u v : ℕ → ℝ) (i k l : ℕ)
    (hc0 : c 0 = 0) (hc : ∀ j < i + 1, c j < c (j + 1))
    (hg : ∀ j < i + 1, c j < u j ∧ u j < v j ∧ v j < c (j + 1))
    (hb : ∀ j ≤ i + 1, 0 < b j)
    (s : Fin (l + 1) → ℕ) (t : ℕ) (hst : ∑ j, s j = t)
    (hbk : b (i + 1) = t * k) (hk : 0 < k)
    (M : ∀ j, Model c b u v i (s j)) : Model c b u v (i + 1) (b (i + 1) + t) := by
  classical
  let Y (j : Fin (l + 1)) := (M j).carrier
  letI (j : Fin (l + 1)) : MetricSpace (Y j) := (M j).metric
  letI (j : Fin (l + 1)) : IsUltrametricDist (Y j) := (M j).ultra
  letI (j : Fin (l + 1)) : Finite (Y j) := (M j).finite
  let a (g : Fin (k + 1)) : ℝ := if g = 0 then u i else v i
  have hgap := hg i (Nat.lt_succ_self _)
  have hac (g) : c i < a g := by
    dsimp [a]
    split
    · exact hgap.1
    · exact hgap.1.trans hgap.2.1
  have hat (g) : a g < c (i + 1) := by
    dsimp [a]
    split
    · exact hgap.2.1.trans hgap.2.2
    · exact hgap.2.2
  have hci : 0 ≤ c i := by
    rw [← hc0]
    exact radii_mono hc (Nat.zero_le _) (Nat.le_succ _)
  have ha (g) : 0 < a g := hci.trans_lt (hac g)
  have hdist (j : Fin (l + 1)) (x y : Y j) : dist x y ≤ c i :=
    allowed_le (fun j hj => hc j (by omega)) (fun j hj => hg j (by omega))
      ((M j).distances x y)
  have hinner (g) : ∀ j (x y : Y j), dist x y ≤ a g :=
    fun j x y => (hdist j x y).trans (hac g).le
  let G (g : Fin (k + 1)) := Join Y (a g) (ha g) (hinner g)
  have houter (g) (p q : G g) : dist p q < c (i + 1) := by
    rcases join_dist_cases Y (a g) (ha g) (hinner g) p q with he | ⟨j, x, y, he⟩
    · exact he.symm ▸ hat g
    · rw [he]
      exact (hdist j x y).trans_lt (hc i (Nat.lt_succ_self _))
  have hbouter (g) (p q : G g) : dist p q ≤ c (i + 1) := (houter g p q).le
  have htop : 0 < c (i + 1) := hci.trans_lt (hc i (Nat.lt_succ_self _))
  let Z := Join G (c (i + 1)) htop hbouter
  let y0 : Y 0 := Classical.choice (M 0).nonempty
  have hgcard (g : Fin (k + 1)) : Nat.card (G g) = t := by
    rw [card_join_sum]
    exact (Finset.sum_congr rfl (fun j _ => (M j).order_eq)).trans hst
  have hzcard : Nat.card Z = b (i + 1) + t := by
    rw [card_join_sum]
    simp only [hgcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (k + 1) * t = b (i + 1) + t
    rw [Nat.add_mul, Nat.one_mul, hbk, Nat.mul_comm k]
  have hcounts (j : ℕ) (hj : j ≤ i + 1) (z : Z) :
      Nat.card (sphere z (c j)) = b j := by
    rcases z with ⟨g, ⟨q, x⟩⟩
    by_cases hj' : j ≤ i
    · have hle := radii_mono hc hj' (Nat.le_succ _)
      rw [sphere_card G (c (i + 1)) htop hbouter g _ ((hle.trans_lt
        (hc i (Nat.lt_succ_self _))).ne)]
      rw [sphere_card Y (a g) (ha g) (hinner g) q _ ((hle.trans_lt (hac g)).ne)]
      exact (M q).counts j hj' x
    · have hjtop : j = i + 1 := by omega
      subst j
      rw [sphere_top_card G (c (i + 1)) htop hbouter houter g _, hzcard, hgcard]
      omega
  have hzcenter : center Z = c '' Set.Iic (i + 1) := by
    ext d
    constructor
    · intro hd
      by_cases hdt : d = c (i + 1)
      · exact ⟨i + 1, Set.mem_Iic.mpr le_rfl, hdt.symm⟩
      · have hformula := ConstantCrossDistance.center_eq G (c (i + 1)) htop hbouter houter
        have hgcent : 0 ≤ d ∧ ∀ g, d ∈ center (G g) := by
          rw [hformula] at hd
          rcases hd with hd | hd
          · exact ⟨hd.1, hd.2.2⟩
          · exact (hdt hd.1).elim
        let g1 : Fin (k + 1) := ⟨1, by omega⟩
        have hg10 : g1 ≠ 0 := by intro he; have := congrArg Fin.val he; simp [g1] at this
        have hdiff : a 0 ≠ a g1 := by simpa [a, hg10] using hgap.2.1.ne
        have hchoose : ∃ g, d ≠ a g := by
          by_cases h0 : d = a 0
          · exact ⟨g1, h0.trans_ne hdiff⟩
          · exact ⟨0, h0⟩
        obtain ⟨g, hda⟩ := hchoose
        have hym := ((mem_center_iff Y (a g) (ha g) (hinner g) hda).mp (hgcent.2 g)).2 0
        have hm := (M (0 : Fin (l + 1))).center_eq
        change center (Y 0) = c '' Set.Iic i at hm
        rw [hm] at hym
        have hsmall : d ∈ c '' Set.Iic i := hym
        obtain ⟨j, hj, rfl⟩ := hsmall
        exact ⟨j, (show j ≤ i from hj).trans (Nat.le_succ _), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, fun x => ?_⟩
      · rw [← hc0]
        exact radii_mono hc (Nat.zero_le _) hj
      · have hp : 0 < Nat.card (sphere x (c j)) := (hcounts j hj x).symm ▸ hb j hj
        obtain ⟨y⟩ := (Nat.card_pos_iff.mp hp).1
        exact ⟨y.val, y.property⟩
  refine { carrier := Z
           metric := inferInstance
           ultra := inferInstance
           finite := inferInstance
           nonempty := ⟨⟨0, ⟨0, y0⟩⟩⟩
           order_eq := hzcard
           center_eq := hzcenter
           counts := hcounts
           distances := ?_ }
  intro p q
  rcases join_dist_cases G (c (i + 1)) htop hbouter p q with he | ⟨g, x, y, he⟩
  · exact Or.inl ⟨i + 1, Set.mem_Iic.mpr le_rfl, he.symm⟩
  · rw [he]
    rcases join_dist_cases Y (a g) (ha g) (hinner g) x y with hd | ⟨j, x', y', hd⟩
    · rw [hd]
      by_cases h : g = 0
      · exact Or.inr (Or.inl ⟨i, Nat.lt_succ_self _, by simp [a, h]⟩)
      · exact Or.inr (Or.inr ⟨i, Nat.lt_succ_self _, by simp [a, h]⟩)
    · rw [hd]
      exact allowed_step c u v i ((M j).distances x' y')

/-- Every candidate order is realizable for every selection of pairs in the gaps. -/
theorem sufficient (c : ℕ → ℝ) (b : ℕ → ℕ) (u v : ℕ → ℝ) (h n : ℕ)
    (hc0 : c 0 = 0) (hc : ∀ i < h, c i < c (i + 1))
    (hg : ∀ i < h, c i < u i ∧ u i < v i ∧ v i < c (i + 1))
    (hb0 : b 0 = 1) (hb : ∀ i ≤ h, 0 < b i)
    (hn : n ∈ orders b h) : Nonempty (Model c b u v h n) := by
  classical
  induction h generalizing n with
  | zero =>
    have hn' : n = 1 := by simpa [orders] using hn
    subst n
    have hdist (x y : PUnit) : dist x y = 0 := by rw [Subsingleton.elim x y, dist_self]
    refine ⟨{ carrier := PUnit
              metric := inferInstance
              ultra := ⟨fun _ _ _ => by simp⟩
              finite := inferInstance
              nonempty := inferInstance
              order_eq := by simp
              center_eq := ?_
              counts := ?_
              distances := fun x y => Or.inl ⟨0, Set.mem_Iic.mpr le_rfl, by rw [hc0, hdist]⟩ }⟩
    · ext d
      constructor
      · intro hd
        obtain ⟨y, hy⟩ := hd.2 PUnit.unit
        exact ⟨0, Set.mem_Iic.mpr le_rfl, by rw [hc0, ← hy, hdist]⟩
      · rintro ⟨j, hj, rfl⟩
        have h : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        rw [hc0]
        exact ⟨le_rfl, fun x => ⟨x, dist_self x⟩⟩
    · intro j hj x
      have h : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      simp [hc0, hb0]
  | succ i ih =>
    obtain ⟨t, ⟨l, s, hs, hst⟩, ⟨k, hbk⟩, rfl⟩ := hn
    have hk : 0 < k := by
      have hp := hb (i + 1) le_rfl
      by_contra! h
      have he : k = 0 := by omega
      simp [hbk, he] at hp
    let M (j : Fin (l + 1)) : Model c b u v i (s j) :=
      Classical.choice (ih (s j) (fun j hj => hc j (by omega))
        (fun j hj => hg j (by omega)) (fun j hj => hb j (by omega)) (hs j))
    exact ⟨realize_step c b u v i k l hc0 hc hg hb s t hst hbk hk M⟩

/-- Exact classification of orders with arbitrary prescribed auxiliary gap radii.
If the zero count differs from one, the right hand side is false. -/
theorem possible_orders_iff (c : ℕ → ℝ) (b : ℕ → ℕ) (u v : ℕ → ℝ) (h n : ℕ)
    (hc0 : c 0 = 0) (hc : ∀ i < h, c i < c (i + 1))
    (hg : ∀ i < h, c i < u i ∧ u i < v i ∧ v i < c (i + 1))
    (hb : ∀ i ≤ h, 0 < b i) :
    Nonempty (Model c b u v h n) ↔ b 0 = 1 ∧ n ∈ orders b h := by
  constructor
  · rintro ⟨M⟩
    have := @necessary M.carrier M.metric M.ultra M.finite M.nonempty
      c b h hc0 hc M.center_eq M.counts
    simpa only [M.order_eq] using this
  · rintro ⟨hb0, hn⟩
    exact sufficient c b u v h n hc0 hc hg hb0 hb hn

/-- Exact classification without a distance support restriction. For the converse,
one can take the points at one-third and two-thirds of every gap. -/
theorem possible_orders_unrestricted_iff (c : ℕ → ℝ) (b : ℕ → ℕ) (h n : ℕ)
    (hc0 : c 0 = 0) (hc : ∀ i < h, c i < c (i + 1))
    (hb : ∀ i ≤ h, 0 < b i) :
    (∃ (X : Type) (m : MetricSpace X),
      letI := m
      IsUltrametricDist X ∧ Finite X ∧ Nonempty X ∧ Nat.card X = n ∧
        center X = c '' Set.Iic h ∧ (∀ i ≤ h, ∀ x : X, Nat.card (sphere x (c i)) = b i)) ↔
      b 0 = 1 ∧ n ∈ orders b h := by
  constructor
  · rintro ⟨X, m, hU, hF, hN, hX, hC, hB⟩
    rw [← hX]
    exact @necessary X m hU hF hN c b h hc0 hc hC hB
  · rintro ⟨hb0, hn⟩
    let u (i : ℕ) := (2 * c i + c (i + 1)) / 3
    let v (i : ℕ) := (c i + 2 * c (i + 1)) / 3
    have hg (i : ℕ) (hi : i < h) : c i < u i ∧ u i < v i ∧ v i < c (i + 1) := by
      have hlt := hc i hi
      dsimp [u, v]
      constructor
      · linarith
      · constructor <;> linarith
    obtain ⟨M⟩ := (possible_orders_iff c b u v h n hc0 hc hg hb).mpr ⟨hb0, hn⟩
    exact ⟨M.carrier, M.metric, M.ultra, M.finite, M.nonempty, M.order_eq, M.center_eq, M.counts⟩

end UltrametricCenterSphereOrders
