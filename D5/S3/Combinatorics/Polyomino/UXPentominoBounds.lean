/- GID: D5/S3/Combinatorics/Polyomino/UXPentominoBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Polyomino/UXPentominoBounds
   mirror-E: none(waiver:universal-pentomino-bound)
   anchors: []
   utility: none
   digest: Exact lower bounds on square-grid boards containing U or X pentomino translates. -/

import D5.S3.Combinatorics.Polyomino.LPolyominoSkippedSequence

/-! The two outer columns of U, or of X in the coordinates `(x+y,y)`,
give lower bounds on board area by counting the two column parities separately. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory (Point)
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates (squareGrid)
open D5.S3.Combinatorics.Polyomino.LPolyominoSkippedSequence (instances IsPolyomino a)

namespace D5.S3.Combinatorics.Polyomino.UXPentominoBounds

/-- The bottom row and the two upturned arms of U. -/
def U : Finset Point := {(0, 0), (-1, 0), (-1, 1), (1, 0), (1, 1)}

/-- The center and its four edge neighbors. -/
def X : Finset Point := {(0, 0), (-1, 0), (0, -1), (1, 0), (0, 1)}

private theorem square_of_two_counts {m n r s : ℕ} (hnm : n ≤ m)
    (hm : 4 * m ≤ r ^ 2) (hn : 4 * n ≤ s ^ 2) (hd : m ≤ n + s + 1) :
    8 * (m + n) ≤ (r + s) ^ 2 + 4 := by
  by_cases hrs : r ≤ s
  · have hsq := Nat.mul_le_mul (show 2 * r ≤ r + s by omega)
        (show 2 * r ≤ r + s by omega)
    nlinarith only [hsq, hm, hnm]
  by_cases heq : r = s + 1
  · subst r
    nlinarith only [hm, hn]
  · have hsq := Nat.mul_le_mul (show 2 * s + 2 ≤ r + s by omega)
        (show 2 * s + 2 ≤ r + s by omega)
    nlinarith only [hsq, hn, hd]

private theorem board_slack {m n r s B C : ℕ} (hmpos : 0 < m) (hnm : n ≤ m)
    (hm : 4 * m ≤ r ^ 2) (hn : 4 * n ≤ s ^ 2)
    (hzero : n = 0 → s = 0)
    (hcenter : m ≤ B) (hfirst : m + r + 1 ≤ C) (hsecond : 0 < n → n + s + 1 ≤ B) :
    m + n + 2 ≤ B + C ∧ 8 * (m + n) ≤ (B + C - (m + n) - 2) ^ 2 + 4 := by
  let t := max s (m - n - 1)
  have ht : t + n + 1 ≤ B := by
    by_cases hz : n = 0
    · have hs := hzero hz
      dsimp [t]
      omega
    · have hs := hsecond (by omega)
      dsimp [t]
      omega
  have hnt : 4 * n ≤ t ^ 2 := hn.trans (Nat.pow_le_pow_left (le_max_left _ _) _)
  have hd : m ≤ n + t + 1 := by
    have hmt : m - n - 1 ≤ t := le_max_right _ _
    omega
  have hr : r + t ≤ B + C - (m + n) - 2 := by omega
  exact ⟨by omega, (square_of_two_counts hnm hm hnt hd).trans
    (Nat.add_le_add_right (Nat.pow_le_pow_left hr _) _)⟩

/-- A finite column profile can pay for both outside arms of a maximum column.
Other columns pay for just the arm directed away from that maximum. -/
private theorem sum_arm_columns (anchors board : Finset ℤ) (q h : ℤ → ℕ)
    (hleft : ∀ x ∈ anchors, x - 1 ∈ board ∧ q x + 1 ≤ h (x - 1))
    (hright : ∀ x ∈ anchors, x + 1 ∈ board ∧ q x + 1 ≤ h (x + 1))
    {peak : ℤ} (hpeak : peak ∈ anchors) :
    (∑ x ∈ anchors, q x) + anchors.card + q peak + 1 ≤ ∑ x ∈ board, h x := by
  classical
  let arm := fun x : ℤ => if x < peak then x - 1 else x + 1
  have hinj : Function.Injective arm := by
    intro x y hxy
    dsimp [arm] at hxy
    split at hxy <;> split at hxy <;> omega
  have hmem : ∀ x ∈ anchors, arm x ∈ board ∧ q x + 1 ≤ h (arm x) := by
    intro x hx
    unfold arm
    split
    · exact hleft x hx
    · exact hright x hx
  have hmiss : peak - 1 ∉ anchors.image arm := by
    rintro h
    obtain ⟨x, _, hx⟩ := mem_image.mp h
    dsimp [arm] at hx
    split at hx <;> omega
  have hsub : insert (peak - 1) (anchors.image arm) ⊆ board := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact (hleft peak hpeak).1
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact (hmem y hy).1
  have hsum : (∑ x ∈ anchors, (q x + 1)) ≤ ∑ x ∈ anchors.image arm, h x := by
    rw [sum_image hinj.injOn]
    exact sum_le_sum fun x hx => (hmem x hx).2
  rw [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, mul_one] at hsum
  have harea := sum_le_sum_of_subset (f := h) hsub
  rw [sum_insert hmiss] at harea
  have hp := (hleft peak hpeak).2
  omega

private theorem parity_profile_slack (anchors board : Finset ℤ) (q h : ℤ → ℕ)
    (hcenter : ∀ x ∈ anchors, x ∈ board ∧ q x ≤ h x)
    (hleft : ∀ x ∈ anchors, x - 1 ∈ board ∧ q x + 1 ≤ h (x - 1))
    (hright : ∀ x ∈ anchors, x + 1 ∈ board ∧ q x + 1 ≤ h (x + 1))
    (hpos : 0 < ∑ x ∈ anchors, q x) :
    (∑ x ∈ anchors, q x) + 2 ≤ ∑ x ∈ board, h x ∧
      8 * (∑ x ∈ anchors, q x) ≤
        ((∑ x ∈ board, h x) - (∑ x ∈ anchors, q x) - 2) ^ 2 + 4 := by
  let part := fun (s : Finset ℤ) (e : ℤ) => s.filter (fun x => x % 2 = e)
  let A := fun e => ∑ x ∈ part anchors e, q x
  let B := fun e => ∑ x ∈ part board e, h x
  have hpartition (s : Finset ℤ) (f : ℤ → ℕ) :
      (∑ x ∈ part s 0, f x) + (∑ x ∈ part s 1, f x) = ∑ x ∈ s, f x := by
    have hodd : s.filter (fun x => x % 2 ≠ 0) = part s 1 := by
      ext x
      simp only [part, mem_filter]
      exact and_congr_right fun _ => by omega
    rw [← hodd]
    exact sum_filter_add_sum_filter_not _ _ _
  have hcent (e : ℤ) : A e ≤ B e := by
    calc
      A e ≤ ∑ x ∈ part anchors e, h x :=
        sum_le_sum fun x hx => (hcenter x (mem_filter.mp hx).1).2
      _ ≤ B e := sum_le_sum_of_subset fun x hx => by
        obtain ⟨hx, he⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨(hcenter x hx).1, he⟩
  have harm (e : ℤ) (he : e = 0 ∨ e = 1) :
      ∃ r : ℕ, 4 * A e ≤ r ^ 2 ∧ (A e = 0 → r = 0) ∧
        (0 < A e → A e + r + 1 ≤ B (1 - e)) := by
    by_cases hz : A e = 0
    · exact ⟨0, by simp [hz], fun _ => rfl, by omega⟩
    have hne : (part anchors e).Nonempty := by
      by_contra hn
      have hf := not_nonempty_iff_eq_empty.mp hn
      exact hz (by simp [A, hf])
    obtain ⟨peak, hpeak, hmax⟩ := (part anchors e).exists_max_image q hne
    refine ⟨(part anchors e).card + q peak, ?_, by omega, fun _ => ?_⟩
    · have hrect : A e ≤ (part anchors e).card * q peak := by
        calc
          A e ≤ ∑ x ∈ part anchors e, q peak := sum_le_sum hmax
          _ = _ := by simp
      have hsq := two_mul_le_add_sq (part anchors e).card (q peak)
      nlinarith only [hrect, hsq]
    · rw [← Nat.add_assoc]
      apply sum_arm_columns (part anchors e) (part board (1 - e)) q h
      · intro x hx
        obtain ⟨hx, hxe⟩ := mem_filter.mp hx
        have heq : x % 2 = e := hxe
        exact ⟨mem_filter.mpr ⟨(hleft x hx).1, by
          rcases he with rfl | rfl <;> omega⟩, (hleft x hx).2⟩
      · intro x hx
        obtain ⟨hx, hxe⟩ := mem_filter.mp hx
        have heq : x % 2 = e := hxe
        exact ⟨mem_filter.mpr ⟨(hright x hx).1, by
          rcases he with rfl | rfl <;> omega⟩, (hright x hx).2⟩
      · exact hpeak
  obtain ⟨r, hr, hrzero, hrarm⟩ := harm 0 (Or.inl rfl)
  obtain ⟨s, hs, hszero, hsarm⟩ := harm 1 (Or.inr rfl)
  have ha : A 0 + A 1 = ∑ x ∈ anchors, q x := hpartition anchors q
  have hb : B 0 + B 1 = ∑ x ∈ board, h x := hpartition board h
  have hrarm' : 0 < A 0 → A 0 + r + 1 ≤ B 1 := hrarm
  have hsarm' : 0 < A 1 → A 1 + s + 1 ≤ B 0 := hsarm
  rw [← ha, ← hb]
  by_cases hle : A 1 ≤ A 0
  · exact board_slack (by omega) hle hr hs hszero (hcent 0) (hrarm' (by omega)) hsarm'
  · rw [add_comm (A 0), add_comm (B 0)]
    exact board_slack (by omega) (by omega) hs hr hrzero (hcent 1) (hsarm' (by omega)) hrarm'

private def fiber (column : Point →+ ℤ) (P : Finset Point) (x : ℤ) : Finset Point :=
  P.filter fun p => column p = x

private theorem arm_fiber_bound (column : Point →+ ℤ) (S P : Finset Point)
    {x : ℤ} (hx : x ∈ S.image column) {offset step : Point}
    (hstep : column step = 0) (hup : 0 < step.2)
    (hbase : ∀ p ∈ S, offset + p ∈ P) (htop : ∀ p ∈ S, (offset + step) + p ∈ P) :
    x + column offset ∈ P.image column ∧
      (fiber column S x).card + 1 ≤ (fiber column P (x + column offset)).card := by
  classical
  let F := fiber column S x
  obtain ⟨p, hpS, hpx⟩ := mem_image.mp hx
  have hF : F.Nonempty := ⟨p, mem_filter.mpr ⟨hpS, hpx⟩⟩
  obtain ⟨top, htopF, hmax⟩ := F.exists_max_image Prod.snd hF
  obtain ⟨htopS, htopx⟩ := mem_filter.mp htopF
  let lift := fun p : Point => offset + p
  let extra := (offset + step) + top
  have hinj : Function.Injective lift := fun _ _ h => add_left_cancel h
  have he : column extra = x + column offset := by
    simp only [extra, map_add, hstep, zero_add, htopx, add_comm]
  have hextra : extra ∉ F.image lift := by
    rintro hm
    obtain ⟨v, hv, hve⟩ := mem_image.mp hm
    have hcmp := hmax v hv
    have hcoords := congrArg Prod.snd hve
    simp only [lift, extra, Prod.snd_add] at hcoords
    omega
  have hsub : insert extra (F.image lift) ⊆ fiber column P (x + column offset) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_filter.mpr ⟨htop top htopS, he⟩
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
      obtain ⟨huS, hux⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨hbase u huS, by simp [lift, hux, add_comm]⟩
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hextra, card_image_of_injective _ hinj] at hcard
  exact ⟨mem_image.mpr ⟨extra, htop top htopS, he⟩, hcard⟩

private theorem board_bound_of_arms (column : Point →+ ℤ) (P S : Finset Point)
    {left right step : Point} (hl : column left = -1) (hr : column right = 1)
    (hs : column step = 0) (hup : 0 < step.2) (hS : S ⊆ P)
    (hlower : ∀ p ∈ S, left + p ∈ P) (hupper : ∀ p ∈ S, (left + step) + p ∈ P)
    (hrlower : ∀ p ∈ S, right + p ∈ P) (hrupper : ∀ p ∈ S, (right + step) + p ∈ P)
    (hpos : 0 < S.card) :
    S.card + 2 ≤ P.card ∧ 8 * S.card ≤ (P.card - S.card - 2) ^ 2 + 4 := by
  classical
  let q := fun x => (fiber column S x).card
  let h := fun x => (fiber column P x).card
  have hA : S.card = ∑ x ∈ S.image column, q x := card_eq_sum_card_image column S
  have hB : P.card = ∑ x ∈ P.image column, h x := card_eq_sum_card_image column P
  have hcenter : ∀ x ∈ S.image column, x ∈ P.image column ∧ q x ≤ h x := by
    intro x hx
    refine ⟨image_subset_image hS hx, card_le_card ?_⟩
    intro p hp
    obtain ⟨hpS, hpx⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hS hpS, hpx⟩
  rw [hA, hB]
  apply parity_profile_slack _ _ q h hcenter
  · intro x hx
    simpa only [q, h, hl, sub_eq_add_neg] using
      arm_fiber_bound column S P hx hs hup hlower hupper
  · intro x hx
    simpa only [q, h, hr] using arm_fiber_bound column S P hx hs hup hrlower hrupper
  · exact hA ▸ hpos

private theorem mem_instances_iff {P p : Finset Point} (hzero : (0 : Point) ∈ p) (v : Point) :
    v ∈ instances P p ↔ ∀ c ∈ p, c + v ∈ P := by
  classical
  unfold instances
  refine ⟨fun hv => (mem_filter.mp hv).2, fun h => mem_filter.mpr ⟨?_, h⟩⟩
  have hv : v ∈ P := by simpa only [zero_add] using h 0 hzero
  exact mem_biUnion.mpr ⟨v, hv, mem_image.mpr ⟨0, hzero, sub_zero v⟩⟩

private theorem instance_cells {P p : Finset Point} {v : Point} (hv : v ∈ instances P p) :
    ∀ c ∈ p, c + v ∈ P := by
  classical
  unfold instances at hv
  exact (mem_filter.mp hv).2

/-- The exact quadratic lower bound, valid even for boards with gaps or multiple components. -/
theorem u_card_bound (P : Finset Point) (hpos : 0 < (instances P U).card) :
    (instances P U).card + 2 ≤ P.card ∧
      8 * (instances P U).card ≤ (P.card - (instances P U).card - 2) ^ 2 + 4 := by
  let column : Point →+ ℤ := AddMonoidHom.fst ℤ ℤ
  apply board_bound_of_arms column P (instances P U)
    (left := (-1, 0)) (right := (1, 0)) (step := (0, 1)) rfl rfl rfl (by decide)
  · intro p hp
    simpa only [zero_add] using instance_cells hp (0 : Point) (by decide)
  · exact fun p hp => instance_cells hp (-1, 0) (by decide)
  · intro p hp
    rw [show ((-1, 0) : Point) + (0, 1) = (-1, 1) by decide]
    exact instance_cells hp (-1, 1) (by decide)
  · exact fun p hp => instance_cells hp (1, 0) (by decide)
  · exact fun p hp => instance_cells hp (1, 1) (by decide)
  · exact hpos

/-- The same lower bound in the integer columns (x+y) of an X board. -/
theorem x_card_bound (P : Finset Point) (hpos : 0 < (instances P X).card) :
    (instances P X).card + 2 ≤ P.card ∧
      8 * (instances P X).card ≤ (P.card - (instances P X).card - 2) ^ 2 + 4 := by
  let column : Point →+ ℤ := AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ
  apply board_bound_of_arms column P (instances P X)
    (left := (0, -1)) (right := (1, 0)) (step := (-1, 1)) rfl rfl rfl (by decide)
  · intro p hp
    simpa only [zero_add] using instance_cells hp (0 : Point) (by decide)
  · exact fun p hp => instance_cells hp (0, -1) (by decide)
  · intro p hp
    rw [show ((0, -1) : Point) + (-1, 1) = (-1, 0) by decide]
    exact instance_cells hp (-1, 0) (by decide)
  · exact fun p hp => instance_cells hp (1, 0) (by decide)
  · exact fun p hp => instance_cells hp (0, 1) (by decide)
  · exact hpos

private def stack (columns : Finset ℤ) (height : ℤ → ℕ) : Finset Point :=
  columns.biUnion fun x => (range (height x)).image fun y : ℕ => (x, (y : ℤ))

private theorem mem_stack {columns : Finset ℤ} {height : ℤ → ℕ} {x y : ℤ} :
    (x, y) ∈ stack columns height ↔ x ∈ columns ∧ 0 ≤ y ∧ y < (height x : ℤ) := by
  constructor
  · rintro hp
    obtain ⟨c, hc, hmem⟩ := mem_biUnion.mp hp
    obtain ⟨k, hk, hxy⟩ := mem_image.mp hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
    exact ⟨hc, by omega, by exact_mod_cast mem_range.mp hk⟩
  · rintro ⟨hx, hy, hlt⟩
    exact mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨y.toNat, mem_range.mpr (by omega),
      Prod.ext rfl (Int.toNat_of_nonneg hy)⟩⟩

private theorem card_stack (columns : Finset ℤ) (height : ℤ → ℕ) :
    (stack columns height).card = ∑ x ∈ columns, height x := by
  unfold stack
  rw [card_biUnion]
  · apply sum_congr rfl
    intro x _
    rw [card_image_of_injective _ (fun a b hab => by
      have h : (a : ℤ) = (b : ℤ) := congrArg Prod.snd hab
      exact_mod_cast h), card_range]
  · intro x _ y _ hxy
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨_, _, hp'⟩ := mem_image.mp hp
    obtain ⟨_, _, hq'⟩ := mem_image.mp hq
    exact hxy ((congrArg Prod.fst hp').trans (congrArg Prod.fst hq').symm)

private def diagonalColumn : Point →+ ℤ :=
  AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ

private theorem stacked_isPolyomino (P : Finset Point) (hP : IsPolyomino P) :
    IsPolyomino (stack (P.image diagonalColumn) (fun x => (fiber diagonalColumn P x).card)) := by
  let height := fun x => (fiber diagonalColumn P x).card
  let columns := P.image diagonalColumn
  let Q := stack columns height
  let adj := fun p q : Point => p ∈ Q ∧ q ∈ Q ∧ squareGrid.Adj p q
  have hbottom : ∀ p ∈ P, (diagonalColumn p, 0) ∈ Q := by
    intro p hp
    have hpos : 0 < height (diagonalColumn p) :=
      card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, rfl⟩⟩
    exact mem_stack.mpr ⟨mem_image_of_mem _ hp, le_rfl, by exact_mod_cast hpos⟩
  have hpaths : ∀ p q : Point, ∀ hp : Relation.ReflTransGen
      (fun a b => a ∈ P ∧ b ∈ P ∧ squareGrid.Adj a b) p q,
      Relation.ReflTransGen adj (diagonalColumn p, 0) (diagonalColumn q, 0) := by
    intro p q path
    induction path with
    | refl => exact .refl
    | @tail b c _ hab ih =>
      refine ih.tail ⟨hbottom _ hab.1, hbottom _ hab.2.1, ?_⟩
      have hedge := hab.2.2
      change (b.1 + 1 = c.1 ∧ b.2 = c.2) ∨ (c.1 + 1 = b.1 ∧ b.2 = c.2) ∨
        (b.2 + 1 = c.2 ∧ b.1 = c.1) ∨ (c.2 + 1 = b.2 ∧ b.1 = c.1) at hedge
      have hstep : diagonalColumn b + 1 = diagonalColumn c ∨
          diagonalColumn c + 1 = diagonalColumn b := by
        change b.1 + b.2 + 1 = c.1 + c.2 ∨ c.1 + c.2 + 1 = b.1 + b.2
        omega
      exact hstep.elim (fun h => Or.inl ⟨h, rfl⟩) (fun h => Or.inr (Or.inl ⟨h, rfl⟩))
  have hvert : ∀ x ∈ columns, ∀ k : ℕ, k < height x →
      Relation.ReflTransGen adj (x, 0) (x, (k : ℤ)) ∧
        Relation.ReflTransGen adj (x, (k : ℤ)) (x, 0) := by
    intro x hx k
    induction k with
    | zero => intro _; exact ⟨.refl, .refl⟩
    | succ k ih =>
      intro hk
      have ha : (x, (k : ℤ)) ∈ Q := mem_stack.mpr ⟨hx, by omega, by omega⟩
      have hb : (x, ((k + 1 : ℕ) : ℤ)) ∈ Q := mem_stack.mpr ⟨hx, by omega, by omega⟩
      have edge : squareGrid.Adj (x, (k : ℤ)) (x, ((k + 1 : ℕ) : ℤ)) :=
        Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))
      obtain ⟨hup, hdown⟩ := ih (by omega)
      exact ⟨hup.tail ⟨ha, hb, edge⟩, hdown.head ⟨hb, ha, edge.symm⟩⟩
  obtain ⟨p, hp⟩ := hP.1
  refine ⟨⟨(diagonalColumn p, 0), hbottom p hp⟩, ?_⟩
  rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy'
  obtain ⟨hx, hy, hlt⟩ := mem_stack.mp hxy
  obtain ⟨hx', hy', hlt'⟩ := mem_stack.mp hxy'
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hx
  obtain ⟨c', hc', rfl⟩ := mem_image.mp hx'
  have hylt : y.toNat < height (diagonalColumn c) := by
    exact_mod_cast (show (y.toNat : ℤ) < (height (diagonalColumn c) : ℤ) by
      rw [Int.toNat_of_nonneg hy]; exact hlt)
  have hylt' : y'.toNat < height (diagonalColumn c') := by
    exact_mod_cast (show (y'.toNat : ℤ) < (height (diagonalColumn c') : ℤ) by
      rw [Int.toNat_of_nonneg hy']; exact hlt')
  have hu := (hvert _ (mem_image_of_mem diagonalColumn hc) y.toNat hylt).2
  have hv := (hvert _ (mem_image_of_mem diagonalColumn hc') y'.toNat hylt').1
  rw [Int.toNat_of_nonneg hy] at hu
  rw [Int.toNat_of_nonneg hy'] at hv
  exact hu.trans ((hpaths c c' (hP.2 c hc c' hc')).trans hv)

private theorem card_instances_stack (anchors board : Finset ℤ) (q h : ℤ → ℕ)
    (hcenter : ∀ x ∈ anchors, x ∈ board ∧ q x ≤ h x)
    (hleft : ∀ x ∈ anchors, x - 1 ∈ board ∧ q x + 1 ≤ h (x - 1))
    (hright : ∀ x ∈ anchors, x + 1 ∈ board ∧ q x + 1 ≤ h (x + 1)) :
    (∑ x ∈ anchors, q x) ≤ (instances (stack board h) U).card := by
  rw [← card_stack]
  apply card_le_card
  rintro ⟨x, y⟩ hy
  obtain ⟨hx, hy0, hyq⟩ := mem_stack.mp hy
  have hc := hcenter x hx
  have hl := hleft x hx
  have hr := hright x hx
  apply (mem_instances_iff (by decide : (0 : Point) ∈ U) (x, y)).mpr
  intro c hcU
  simp only [U, mem_insert, mem_singleton] at hcU
  rcases hcU with rfl | rfl | rfl | rfl | rfl
  · rw [show ((0, 0) : Point) = 0 by rfl, zero_add]
    exact mem_stack.mpr ⟨hc.1, hy0, by omega⟩
  · refine mem_stack.mpr ⟨?_, ?_, ?_⟩
    · simpa only [Prod.fst_add, Prod.fst, sub_eq_add_neg, add_comm] using hl.1
    · change 0 ≤ 0 + y
      omega
    · change 0 + y < (h (-1 + x) : ℤ)
      rw [show -1 + x = x - 1 by omega]
      omega
  · refine mem_stack.mpr ⟨?_, ?_, ?_⟩
    · simpa only [Prod.fst_add, Prod.fst, sub_eq_add_neg, add_comm] using hl.1
    · change 0 ≤ 1 + y
      omega
    · change 1 + y < (h (-1 + x) : ℤ)
      rw [show -1 + x = x - 1 by omega]
      omega
  · refine mem_stack.mpr ⟨?_, ?_, ?_⟩
    · simpa only [Prod.fst_add, Prod.fst, add_comm] using hr.1
    · change 0 ≤ 0 + y
      omega
    · change 0 + y < (h (1 + x) : ℤ)
      rw [add_comm 1 x]
      omega
  · refine mem_stack.mpr ⟨?_, ?_, ?_⟩
    · simpa only [Prod.fst_add, Prod.fst, add_comm] using hr.1
    · change 0 ≤ 1 + y
      omega
    · change 1 + y < (h (1 + x) : ℤ)
      rw [add_comm 1 x]
      omega

/-- Diagonal column compression turns an X board into a connected U board
of exactly the same area with at least as many translation anchors. -/
theorem u_board_of_x_board (P : Finset Point) (hP : IsPolyomino P) :
    ∃ Q : Finset Point, IsPolyomino Q ∧ (instances P X).card ≤ (instances Q U).card ∧
      Q.card = P.card := by
  let S := instances P X
  let q := fun x => (fiber diagonalColumn S x).card
  let h := fun x => (fiber diagonalColumn P x).card
  have hS : S ⊆ P := by
    intro p hp
    simpa only [zero_add] using instance_cells hp (0 : Point) (by decide)
  refine ⟨stack (P.image diagonalColumn) h, stacked_isPolyomino P hP, ?_, ?_⟩
  · change S.card ≤ _
    rw [card_eq_sum_card_image diagonalColumn S]
    apply card_instances_stack (S.image diagonalColumn) (P.image diagonalColumn) q h
    · intro x hx
      refine ⟨image_subset_image hS hx, card_le_card ?_⟩
      intro p hp
      obtain ⟨hpS, hpx⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hS hpS, hpx⟩
    · intro x hx
      have hlower : ∀ p ∈ S, (0, -1) + p ∈ P :=
        fun p hp => instance_cells hp (0, -1) (by decide)
      have hupper : ∀ p ∈ S, ((0, -1) + (-1, 1)) + p ∈ P := by
        intro p hp
        rw [show ((0, -1) : Point) + (-1, 1) = (-1, 0) by decide]
        exact instance_cells hp (-1, 0) (by decide)
      simpa only [q, h, show diagonalColumn (0, -1) = -1 by decide, sub_eq_add_neg] using
        arm_fiber_bound diagonalColumn S P hx (step := (-1, 1)) rfl (by decide) hlower hupper
    · intro x hx
      have hlower : ∀ p ∈ S, (1, 0) + p ∈ P :=
        fun p hp => instance_cells hp (1, 0) (by decide)
      have hupper : ∀ p ∈ S, ((1, 0) + (-1, 1)) + p ∈ P := by
        intro p hp
        rw [show ((1, 0) : Point) + (-1, 1) = (0, 1) by decide]
        exact instance_cells hp (0, 1) (by decide)
      simpa only [q, h, show diagonalColumn (1, 0) = 1 by decide] using
        arm_fiber_bound diagonalColumn S P hx (step := (-1, 1)) rfl (by decide) hlower hupper
  · rw [card_stack]
    exact (card_eq_sum_card_image diagonalColumn P).symm

private def checkerRect (w h : ℕ) : Finset (ℕ × ℕ) :=
  (range w ×ˢ range h).filter fun p => p.1 % 2 = p.2 % 2

private theorem mem_checkerRect {w h u v : ℕ} :
    (u, v) ∈ checkerRect w h ↔ u < w ∧ v < h ∧ u % 2 = v % 2 := by
  simp only [checkerRect, mem_filter, mem_product, mem_range, and_assoc]

private def parityRect (w h e : ℕ) : Finset (ℕ × ℕ) :=
  (range ((w + 1 - e) / 2) ×ˢ range ((h + 1 - e) / 2)).image
    fun p => (2 * p.1 + e, 2 * p.2 + e)

private theorem mem_parityRect {w h e u v : ℕ} (he : e ≤ 1) :
    (u, v) ∈ parityRect w h e ↔ u < w ∧ v < h ∧ u % 2 = e ∧ v % 2 = e := by
  constructor
  · rintro hm
    obtain ⟨⟨i, j⟩, hij, huv⟩ := mem_image.mp hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
    obtain ⟨hi, hj⟩ := mem_product.mp hij
    simp only [mem_range] at hi hj
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro ⟨hu, hv, hue, hve⟩
    refine mem_image.mpr ⟨(u / 2, v / 2), mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · apply mem_range.mpr
      omega
    · apply mem_range.mpr
      omega
    · exact Prod.ext (by dsimp; omega) (by dsimp; omega)

private theorem card_checkerRect (w h : ℕ) :
    (checkerRect w h).card = ((w + 1) / 2) * ((h + 1) / 2) + (w / 2) * (h / 2) := by
  have hunion : checkerRect w h = parityRect w h 0 ∪ parityRect w h 1 := by
    ext ⟨u, v⟩
    simp only [mem_checkerRect, mem_union, mem_parityRect (by decide : 0 ≤ 1),
      mem_parityRect (by decide : 1 ≤ 1)]
    omega
  have hd : Disjoint (parityRect w h 0) (parityRect w h 1) := by
    apply disjoint_left.mpr
    rintro ⟨u, v⟩ h0 h1
    have h0' := (mem_parityRect (by decide : 0 ≤ 1)).mp h0
    have h1' := (mem_parityRect (by decide : 1 ≤ 1)).mp h1
    omega
  have hcard (e : ℕ) : (parityRect w h e).card =
      ((w + 1 - e) / 2) * ((h + 1 - e) / 2) := by
    unfold parityRect
    rw [card_image_of_injective, card_product, card_range, card_range]
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (by dsimp at h1 ⊢; omega) (by dsimp at h2 ⊢; omega)
  rw [hunion, card_union_of_disjoint hd, hcard, hcard]
  simp

private theorem card_checker_expand (w h : ℕ) :
    (checkerRect (w + 2) (h + 2)).card = (checkerRect w h).card + w + h + 2 := by
  rw [card_checkerRect, card_checkerRect]
  have hw : (w + 1) / 2 + w / 2 = w := by omega
  have hh : (h + 1) / 2 + h / 2 = h := by omega
  rw [show (w + 2 + 1) / 2 = (w + 1) / 2 + 1 by omega,
    show (h + 2 + 1) / 2 = (h + 1) / 2 + 1 by omega,
    show (w + 2) / 2 = w / 2 + 1 by omega,
    show (h + 2) / 2 = h / 2 + 1 by omega]
  nlinarith only [hw, hh]

private theorem balanced_capacity (w h : ℕ) (hw : w ≤ h) (hh : h ≤ w + 1) (N : ℕ) :
    N ≤ (checkerRect w h).card ↔ 8 * N ≤ (w + h) ^ 2 + 4 := by
  rw [card_checkerRect]
  by_cases he : w % 2 = 0
  · let k := w / 2
    have hwk : w = 2 * k := by dsimp [k]; omega
    rcases (show h = w ∨ h = w + 1 by omega) with rfl | rfl
    · rw [hwk]
      simp only [show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega]
      have h : (2 * k + 2 * k) ^ 2 + 4 = 8 * (k * k + k * k) + 4 := by ring
      rw [h]
      omega
    · rw [hwk]
      simp only [show (2 * k + 1 + 1) / 2 = k + 1 by omega,
        show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega]
      have h : (2 * k + (2 * k + 1)) ^ 2 + 4 = 8 * (k * (k + 1) + k * k) + 5 := by ring
      rw [h]
      omega
  · let k := w / 2
    have hwk : w = 2 * k + 1 := by dsimp [k]; omega
    rcases (show h = w ∨ h = w + 1 by omega) with rfl | rfl
    · rw [hwk]
      simp only [show (2 * k + 1 + 1) / 2 = k + 1 by omega,
        show (2 * k + 1) / 2 = k by omega]
      have h : (2 * k + 1 + (2 * k + 1)) ^ 2 + 4 =
          8 * ((k + 1) * (k + 1) + k * k) := by ring
      rw [h]
      omega
    · rw [hwk]
      simp only [show (2 * k + 1 + 1 + 1) / 2 = k + 1 by omega,
        show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega]
      have h : (2 * k + 1 + (2 * k + 1 + 1)) ^ 2 + 4 =
          8 * ((k + 1) * (k + 1) + k * (k + 1)) + 5 := by ring
      rw [h]
      omega

private def checkerPoint (u v : ℕ) : Point :=
  (((u : ℤ) + (v : ℤ)) / 2, ((u : ℤ) - (v : ℤ)) / 2)

private theorem checkerPoint_coords {u v : ℕ} (hp : u % 2 = v % 2) :
    (checkerPoint u v).1 + (checkerPoint u v).2 = (u : ℤ) ∧
      (checkerPoint u v).1 - (checkerPoint u v).2 = (v : ℤ) := by
  have h : (u : ℤ) % 2 = (v : ℤ) % 2 := by exact_mod_cast hp
  dsimp [checkerPoint]
  omega

private theorem checkerPoint_inj {u v u' v' : ℕ}
    (hp : u % 2 = v % 2) (hp' : u' % 2 = v' % 2)
    (h : checkerPoint u v = checkerPoint u' v') : u = u' ∧ v = v' := by
  have h1 := checkerPoint_coords hp
  have h2 := checkerPoint_coords hp'
  rw [h] at h1
  omega

private theorem checkerPoint_adj {u v u' v' : ℕ}
    (hp : u % 2 = v % 2) (hp' : u' % 2 = v' % 2)
    (hu : u + 1 = u' ∨ u' + 1 = u) (hv : v + 1 = v' ∨ v' + 1 = v) :
    squareGrid.Adj (checkerPoint u v) (checkerPoint u' v') := by
  have h1 := checkerPoint_coords hp
  have h2 := checkerPoint_coords hp'
  unfold squareGrid
  change (_ + 1 = _ ∧ _ = _) ∨ (_ + 1 = _ ∧ _ = _) ∨
    (_ + 1 = _ ∧ _ = _) ∨ (_ + 1 = _ ∧ _ = _)
  omega

private theorem checker_board_connected {Q : Finset (ℕ × ℕ)} {w h : ℕ}
    (hw : 2 ≤ w) (hh : 2 ≤ h) (hsub : Q ⊆ checkerRect w (h + 1))
    (hfull : checkerRect w h ⊆ Q) :
    IsPolyomino (Q.image fun p => checkerPoint p.1 p.2) := by
  let P := Q.image fun p => checkerPoint p.1 p.2
  let edge := fun p q : Point => p ∈ P ∧ q ∈ P ∧ squareGrid.Adj p q
  have hzero : (0, 0) ∈ Q := hfull (mem_checkerRect.mpr ⟨by omega, by omega, rfl⟩)
  have step {u v u' v' : ℕ} (ha : (u, v) ∈ Q) (hb : (u', v') ∈ Q)
      (hu : u + 1 = u' ∨ u' + 1 = u) (hv : v + 1 = v' ∨ v' + 1 = v) :
      edge (checkerPoint u v) (checkerPoint u' v') := by
    exact ⟨mem_image_of_mem _ ha, mem_image_of_mem _ hb,
      checkerPoint_adj (mem_checkerRect.mp (hsub ha)).2.2
        (mem_checkerRect.mp (hsub hb)).2.2 hu hv⟩
  have bottom : ∀ u : ℕ, (u, 0) ∈ Q →
      Relation.ReflTransGen edge (checkerPoint u 0) (checkerPoint 0 0) := by
    intro u
    induction u using Nat.strong_induction_on with
    | h u ih =>
      intro hu
      have hdata := mem_checkerRect.mp (hsub hu)
      by_cases hz : u = 0
      · subst u
        exact .refl
      have hm : (u - 1, 1) ∈ Q := hfull (mem_checkerRect.mpr ⟨by omega, by omega, by omega⟩)
      have hl : (u - 2, 0) ∈ Q := hfull (mem_checkerRect.mpr ⟨by omega, by omega, by omega⟩)
      exact (ih (u - 2) (by omega) hl).head (step hm hl (Or.inr (by omega)) (Or.inr rfl))
        |>.head (step hu hm (Or.inr (by omega)) (Or.inl rfl))
  have path : ∀ v u : ℕ, (u, v) ∈ Q →
      Relation.ReflTransGen edge (checkerPoint u v) (checkerPoint 0 0) := by
    intro v
    induction v with
    | zero => exact bottom
    | succ v ih =>
      intro u hmem
      have hdata := mem_checkerRect.mp (hsub hmem)
      let i := if u = 0 then 1 else u - 1
      have hi : (i, v) ∈ Q := hfull (mem_checkerRect.mpr (by
        dsimp [i]
        split <;> exact ⟨by omega, by omega, by omega⟩))
      have hstep : u + 1 = i ∨ i + 1 = u := by
        dsimp [i]
        split <;> omega
      exact (ih i hi).head (step hmem hi hstep (Or.inr rfl))
  refine ⟨⟨checkerPoint 0 0, mem_image_of_mem _ hzero⟩, ?_⟩
  intro p hp q hq
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := mem_image.mp hp
  obtain ⟨⟨u', v'⟩, huv', rfl⟩ := mem_image.mp hq
  let _ : Std.Symm edge := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  exact (path v u huv).trans (symm (path v' u' huv'))

private theorem checker_card_image (Q : Finset (ℕ × ℕ)) {w h : ℕ}
    (hQ : Q ⊆ checkerRect w h) :
    (Q.image fun p => checkerPoint p.1 p.2).card = Q.card := by
  apply card_image_of_injOn
  rintro ⟨u, v⟩ hu ⟨u', v'⟩ hv heq
  obtain ⟨huu, hvv⟩ := checkerPoint_inj
    (mem_checkerRect.mp (hQ hu)).2.2 (mem_checkerRect.mp (hQ hv)).2.2 heq
  exact Prod.ext huu hvv

private theorem card_checker_next_row (w v : ℕ) :
    (checkerRect w (v + 1)).card =
      (checkerRect w v).card + (w + 1 - v % 2) / 2 := by
  rw [card_checkerRect, card_checkerRect]
  by_cases he : v % 2 = 0
  · simp only [he, Nat.sub_zero]
    rw [show (v + 1 + 1) / 2 = (v + 1) / 2 + 1 by omega,
      show (v + 1) / 2 = v / 2 by omega]
    nlinarith only [show (v + 1) / 2 = v / 2 by omega]
  · have ho : v % 2 = 1 := by omega
    simp only [ho, Nat.add_sub_cancel]
    rw [show (v + 1 + 1) / 2 = (v + 1) / 2 by omega,
      show (v + 1) / 2 = v / 2 + 1 by omega]
    nlinarith only [show (v + 1) / 2 = v / 2 + 1 by omega]

private theorem checker_translate {u v : ℕ} (hpar : u % 2 = v % 2) {c : Point} (hc : c ∈ X) :
    ∃ i j : ℕ, i ≤ 2 ∧ j ≤ 2 ∧ (u+i) % 2 = (v+j) % 2 ∧
      c + checkerPoint (u+1) (v+1) = checkerPoint (u+i) (v+j) := by
  have translate (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2)
      (h₁ : c.1 + c.2 + 1 = (i : ℤ)) (h₂ : c.1 - c.2 + 1 = (j : ℤ))
      (hij : i % 2 = j % 2) :
      ∃ i j : ℕ, i ≤ 2 ∧ j ≤ 2 ∧ (u+i) % 2 = (v+j) % 2 ∧
        c + checkerPoint (u+1) (v+1) = checkerPoint (u+i) (v+j) := by
    have hp : (u+i) % 2 = (v+j) % 2 := by omega
    refine ⟨i, j, hi, hj, hp, ?_⟩
    have ha := checkerPoint_coords (show (u+1) % 2 = (v+1) % 2 by omega)
    have hb := checkerPoint_coords hp
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  simp only [X, mem_insert, mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact translate 1 1 (by decide) (by decide) (by decide) (by decide) rfl
  · exact translate 0 0 (by decide) (by decide) (by decide) (by decide) rfl
  · exact translate 0 2 (by decide) (by decide) (by decide) (by decide) rfl
  · exact translate 2 2 (by decide) (by decide) (by decide) (by decide) rfl
  · exact translate 2 0 (by decide) (by decide) (by decide) (by decide) rfl

private theorem trimmed_checker_board (w v N : ℕ) (hw : 1 ≤ w)
    (hN : N ≤ (checkerRect w (v + 1)).card)
    (hsmall : (checkerRect w v).card ≤ N) :
    ∃ P : Finset Point, IsPolyomino P ∧ N ≤ (instances P X).card ∧
      P.card = N + w + (v + 1) + 2 := by
  let e := v % 2
  let R := (w + 1 - e) / 2
  let t := (checkerRect w (v + 1)).card - N
  let removed := (range t).image fun j => (2 * (R - t + j) + e, v)
  let large := checkerRect (w + 2) (v + 3)
  let small := checkerRect w (v + 1)
  let shift : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 2, p.2 + 2)
  let Q := large \ removed.image shift
  let P := Q.image fun p => checkerPoint p.1 p.2
  have ht : t ≤ R := by
    have hh := card_checker_next_row w v
    dsimp [t, R, e]
    omega
  have hrem : ∀ u y : ℕ, (u, y) ∈ removed ↔
      y = v ∧ u < w ∧ u % 2 = e ∧ R - t ≤ u / 2 := by
    intro u y
    constructor
    · intro hm
      obtain ⟨j, hj, huv⟩ := mem_image.mp hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
      have hjt := mem_range.mp hj
      dsimp [R, e] at *
      exact ⟨rfl, by omega, by omega, by omega⟩
    · rintro ⟨rfl, hu, hp, hlo⟩
      refine mem_image.mpr ⟨u / 2 - (R - t), mem_range.mpr ?_, ?_⟩
      · dsimp [R, e] at *
        omega
      · exact Prod.ext (by dsimp; dsimp [e] at *; omega) rfl
  have hremSmall : removed ⊆ small := by
    rintro ⟨u, y⟩ hy
    obtain ⟨rfl, hu, he, _⟩ := (hrem u y).mp hy
    exact mem_checkerRect.mpr ⟨hu, by omega, he⟩
  have hremLarge : removed.image shift ⊆ large := by
    rintro p hp
    obtain ⟨⟨u, y⟩, hy, rfl⟩ := mem_image.mp hp
    have hdata := mem_checkerRect.mp (hremSmall hy)
    apply mem_checkerRect.mpr
    dsimp [shift]
    exact ⟨by omega, by omega, by omega⟩
  have hcount : removed.card = t := by
    dsimp [removed]
    rw [card_image_of_injective, card_range]
    intro j j' h
    have hj : 2 * (R - t + j) + e = 2 * (R - t + j') + e := congrArg Prod.fst h
    omega
  have hcount' : (removed.image shift).card = t := by
    rw [card_image_of_injective, hcount]
    rintro ⟨u, y⟩ ⟨u', y'⟩ he
    obtain ⟨hu, hy⟩ := Prod.mk.inj he
    exact Prod.ext (by dsimp at hu ⊢; omega) (by dsimp at hy ⊢; omega)
  have hQ : Q ⊆ large := sdiff_subset
  have hfull : checkerRect (w + 2) (v + 2) ⊆ Q := by
    rintro ⟨u, y⟩ hy
    have hy' := mem_checkerRect.mp hy
    refine mem_sdiff.mpr ⟨mem_checkerRect.mpr ⟨hy'.1, by omega, hy'.2.2⟩, ?_⟩
    rintro hr
    obtain ⟨⟨u', y'⟩, hr', hp⟩ := mem_image.mp hr
    have hrow := ((hrem u' y').mp hr').1
    have hY : y' + 2 = y := congrArg Prod.snd hp
    omega
  refine ⟨P, checker_board_connected (by omega) (by omega) hQ hfull, ?_, ?_⟩
  · let A := small \ removed
    have hA : A.card = N := by
      rw [show A.card = small.card - removed.card from card_sdiff_of_subset hremSmall, hcount]
      dsimp [small, t]
      omega
    rw [← hA]
    apply card_le_card_of_injOn (fun p => checkerPoint (p.1 + 1) (p.2 + 1))
    · rintro ⟨u, y⟩ hmem
      have hdata := mem_checkerRect.mp (mem_sdiff.mp hmem).1
      apply (mem_instances_iff (by decide : (0 : Point) ∈ X) _).mpr
      intro c hc
      obtain ⟨i, j, hi, hj, hp, heq⟩ := checker_translate hdata.2.2 hc
      rw [heq]
      apply mem_image.mpr
      refine ⟨(u+i, y+j), mem_sdiff.mpr ⟨mem_checkerRect.mpr
        ⟨by omega, by omega, hp⟩, ?_⟩, rfl⟩
      rintro hr
      obtain ⟨⟨u', y'⟩, hm, hx⟩ := mem_image.mp hr
      have hu : u' + 2 = u + i := congrArg Prod.fst hx
      have hy : y' + 2 = y + j := congrArg Prod.snd hx
      obtain ⟨hrY, _, hrP, hrL⟩ := (hrem u' y').mp hm
      have hyv : y = v := by omega
      apply (mem_sdiff.mp hmem).2
      exact (hrem u y).mpr ⟨hyv, hdata.1, by dsimp [e]; omega, by omega⟩
    · rintro ⟨u, y⟩ hmem ⟨u', y'⟩ hmem' heq
      have ha := (mem_checkerRect.mp (mem_sdiff.mp hmem).1).2.2
      have hb := (mem_checkerRect.mp (mem_sdiff.mp hmem').1).2.2
      obtain ⟨hu, hv⟩ := checkerPoint_inj (by dsimp; omega) (by dsimp; omega) heq
      exact Prod.ext (by dsimp at hu ⊢; omega) (by dsimp at hv ⊢; omega)
  · rw [show P.card = Q.card from checker_card_image Q hQ, show Q.card = large.card -
      (removed.image shift).card from card_sdiff_of_subset hremLarge, hcount']
    have hc : large.card = (checkerRect w (v + 1)).card + w + (v + 1) + 2 :=
      card_checker_expand w (v + 1)
    dsimp only [t]
    omega

private theorem checker_capacity_comm (w h : ℕ) : (checkerRect w h).card =
    (checkerRect h w).card := by
  rw [card_checkerRect, card_checkerRect, Nat.mul_comm ((w+1)/2), Nat.mul_comm (w/2)]

private theorem x_upper {N d : ℕ} (hN : 0 < N) (hcap : 8 * N ≤ d ^ 2 + 4) :
    ∃ P : Finset Point, IsPolyomino P ∧ N ≤ (instances P X).card ∧ P.card ≤ N + d + 2 := by
  let hex : ∃ x : ℕ, 8 * N ≤ x ^ 2 + 4 := ⟨d, hcap⟩
  let k := Nat.find hex
  have hk : 8 * N ≤ k ^ 2 + 4 := Nat.find_spec hex
  have hkmin : k ≤ d := Nat.find_min' hex hcap
  have hk2 : 2 ≤ k := by
    by_contra hn
    rcases (show k = 0 ∨ k = 1 by omega) with hz | ho
    · rw [hz] at hk
      norm_num at hk
      omega
    · rw [ho] at hk
      norm_num at hk
      omega
  let w := k / 2
  let h := k - w
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hh : w ≤ h ∧ h ≤ w + 1 := by dsimp [h, w]; omega
  have hsum : w + h = k := by dsimp [h, w]; omega
  have hlarge : N ≤ (checkerRect w h).card := (balanced_capacity w h hh.1 hh.2 N).mpr
    (hsum ▸ hk)
  have hprev : ¬8 * N ≤ (k - 1) ^ 2 + 4 := fun hc => by
    have hmin := Nat.find_min' hex hc
    omega
  have hsmall : (checkerRect w (h - 1)).card < N := by
    suffices hc : N ≤ (checkerRect w (h - 1)).card ↔ 8 * N ≤ (k - 1) ^ 2 + 4 by
      exact Nat.lt_of_not_ge (fun hm => hprev (hc.mp hm))
    have hs : w + (h - 1) = k - 1 := by omega
    by_cases heq : w = h
    · rw [checker_capacity_comm]
      have ht := balanced_capacity (h - 1) w (by omega) (by omega) N
      rwa [show h - 1 + w = k - 1 by omega] at ht
    · have ht := balanced_capacity w (h - 1) (by omega) (by omega) N
      rwa [hs] at ht
  have heqh : h - 1 + 1 = h := by omega
  obtain ⟨P, hP, hI, hcP⟩ := trimmed_checker_board w (h - 1) N hw
    (by rwa [heqh]) hsmall.le
  exact ⟨P, hP, hI, by omega⟩

private theorem lower_from_threshold {B A N : ℕ} (hN : N ≤ A)
    (hA : A + 2 ≤ B ∧ 8 * A ≤ (B - A - 2) ^ 2 + 4) :
    N + 2 ≤ B ∧ 8 * N ≤ (B - N - 2) ^ 2 + 4 := by
  have hsub : B - A - 2 ≤ B - N - 2 := by omega
  exact ⟨by omega, (Nat.mul_le_mul_left _ hN).trans
    (hA.2.trans (Nat.add_le_add_right (Nat.pow_le_pow_left hsub _) _))⟩

/-- The U and X pentomino instance sequences agree at every positive threshold. -/
theorem same_minimum (N : ℕ) (hN : 0 < N) : a U N = a X N := by
  let sizes := fun p : Finset Point => {S : ℕ | ∃ P : Finset Point,
    IsPolyomino P ∧ N ≤ (instances P p).card ∧ P.card = S}
  have hex (p : Finset Point) : a p N = sInf (sizes p) := rfl
  have hcap : 8 * N ≤ (8 * N) ^ 2 + 4 := by
    have h := Nat.le_mul_self (8 * N)
    nlinarith only [h]
  obtain ⟨Xboard, hXp, hXi, _⟩ := x_upper hN hcap
  have hX : (sizes X).Nonempty := ⟨Xboard.card, Xboard, hXp, hXi, rfl⟩
  obtain ⟨P, hP, hI, hcard⟩ := Nat.sInf_mem hX
  obtain ⟨Q, hQ, hQle, hQcard⟩ := u_board_of_x_board P hP
  have hUm : Q.card ∈ sizes U := ⟨Q, hQ, hI.trans hQle, rfl⟩
  have hUX : a U N ≤ a X N := by
    rw [hex U, hex X, ← hcard, ← hQcard]
    exact Nat.sInf_le hUm
  have hU : (sizes U).Nonempty := ⟨Q.card, hUm⟩
  obtain ⟨R, _, hRi, hRcard⟩ := Nat.sInf_mem hU
  obtain ⟨_, hRcap⟩ := lower_from_threshold hRi (u_card_bound R (lt_of_lt_of_le hN hRi))
  obtain ⟨W, hW, hWi, hWcard⟩ := x_upper hN hRcap
  have hXm : W.card ∈ sizes X := ⟨W, hW, hWi, rfl⟩
  have hXW : a X N ≤ W.card := Nat.sInf_le hXm
  have hXU : a X N ≤ a U N := by
    rw [hex U, ← hRcard]
    omega
  exact le_antisymm hUX hXU

end D5.S3.Combinatorics.Polyomino.UXPentominoBounds
