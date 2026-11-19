/- GID: D5/S3/Combinatorics/Polyomino/Figure26Prismaticity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Polyomino/Figure26Prismaticity
   mirror-E: none(waiver:symbolic-lattice-minimality)
   anchors: []
   utility: none
   digest: The two displayed Figure 26 binary-colored polyhexes are prismatic. -/

import D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Polyomino.Figure26Prismaticity

open Finset
open scoped Pointwise
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory (Point)

/-- Axial differences across one edge of a hexagonal cell. -/
def hexSteps : Finset Point := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

def Adj (p q : Point) : Prop := q - p ∈ hexSteps

private instance (p q : Point) : Decidable (Adj p q) := by unfold Adj; infer_instance

private theorem adj_symm {p q : Point} (h : Adj p q) : Adj q p := by
  have hs : ∀ d ∈ hexSteps, -d ∈ hexSteps := by decide
  have hr := hs (q - p) h
  simpa only [Adj, neg_sub] using hr

def BoardReach (B : Finset Point) : Point → Point → Prop :=
  Relation.ReflTransGen fun p q => p ∈ B ∧ q ∈ B ∧ Adj p q

def IsPolyhex (B : Finset Point) : Prop :=
  B.Nonempty ∧ ∀ p ∈ B, ∀ q ∈ B, BoardReach B p q

def offsets (P : Fin 4 → Point) : Finset Point := univ.image P

def anchors (P : Fin 4 → Point) (B : Finset Point) : Finset Point :=
  (B.image fun b => b - P 0).filter fun t => ∀ i, t + P i ∈ B

private theorem mem_anchors {P : Fin 4 → Point} {B : Finset Point} {t : Point} :
    t ∈ anchors P B ↔ ∀ i, t + P i ∈ B := by
  rw [anchors, mem_filter]
  exact ⟨And.right, fun h => ⟨mem_image.mpr ⟨_, h 0, add_sub_cancel_right ..⟩, h⟩⟩

/-- A `(P, N)`-dense polyhex minimizes area among connected boards
with at least `N` occurrences of the fixed pattern. -/
def IsDense (P : Fin 4 → Point) (N : ℕ) (B : Finset Point) : Prop :=
  IsPolyhex B ∧ N ≤ (anchors P B).card ∧
    ∀ C : Finset Point, IsPolyhex C → N ≤ (anchors P C).card → B.card ≤ C.card

abbrev Word := Bool × Bool × Bool × Bool

/-- The tuple order is the order of the four cells in the source glyph. -/
def wordAt (P : Fin 4 → Point) (color : Point → Bool) (t : Point) : Word :=
  (color (t + P 0), color (t + P 1), color (t + P 2), color (t + P 3))

def IsBinaryDeBruijn (P : Fin 4 → Point) (B : Finset Point) (color : Point → Bool) : Prop :=
  ∀ w : Word, ((anchors P B).filter fun t => wordAt P color t = w).card = 1

def FigureWitness (P : Fin 4 → Point) (B : Finset Point) (color : Point → Bool) : Prop :=
  IsPolyhex (offsets P) ∧ (offsets P).card = 4 ∧
  IsPolyhex B ∧ B.card = 28 ∧ (anchors P B).card = 16 ∧ IsBinaryDeBruijn P B color

def IsPrismatic (P : Fin 4 → Point) (B : Finset Point) (color : Point → Bool) : Prop :=
  FigureWitness P B color ∧ IsDense P 16 B

/-- Figure 26 left, in axial coordinates suited to the three arms. -/
private def leftPattern : Fin 4 → Point := ![(0, 1), (0, 0), (-1, 0), (1, -1)]

/-- Figure 26 right, in axial coordinates suited to the two columns. -/
private def rightPattern : Fin 4 → Point := ![(1, 1), (1, 0), (0, 2), (0, 0)]

private def checkTree (B seen : Finset Point) : List (Point × Point) → Bool
  | [] => decide (B ⊆ seen)
  | (q, p) :: edges =>
    decide (q ∈ B ∧ p ∈ seen ∧ Adj p q) && checkTree B (insert q seen) edges

private theorem checkTree_sound (B : Finset Point) (root : Point) (edges : List (Point × Point))
    (seen : Finset Point) (hseen : ∀ p ∈ seen, p ∈ B ∧ BoardReach B root p)
    (hcheck : checkTree B seen edges = true) :
    ∀ p ∈ B, BoardReach B root p := by
  induction edges generalizing seen with
  | nil =>
    have hsub : B ⊆ seen := of_decide_eq_true hcheck
    exact fun p hp => (hseen p (hsub hp)).2
  | cons edge edges ih =>
    obtain ⟨q, p⟩ := edge
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at hcheck
    apply ih (insert q seen) ?_ hcheck.2
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · obtain ⟨hpB, hp⟩ := hseen p hcheck.1.2.1
      exact ⟨hcheck.1.1, hp.tail ⟨hpB, hcheck.1.1, hcheck.1.2.2⟩⟩
    · exact hseen x hx

private theorem tree_polyhex (B : Finset Point) (root : Point) (edges : List (Point × Point))
    (hroot : root ∈ B) (hcheck : checkTree B {root} edges = true) : IsPolyhex B := by
  have hreach := checkTree_sound B root edges {root} (by
    intro p hp
    have heq := mem_singleton.mp hp
    subst p
    exact ⟨hroot, .refl⟩) hcheck
  refine ⟨⟨root, hroot⟩, fun p hp q hq => ?_⟩
  have reverse {x y : Point} (h : BoardReach B x y) : BoardReach B y x := by
    induction h with
    | refl => exact .refl
    | tail _ h ih =>
      exact (Relation.ReflTransGen.single ⟨h.2.1, h.1, adj_symm h.2.2⟩).trans ih
  exact (reverse (hreach p hp)).trans (hreach q hq)

private def leftBoard : Finset Point :=
  {(0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1),
   (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0),
   (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1),
   (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (6, -3), (6, -2)}

private def leftGray : Finset Point :=
  {(1, 0), (1, 2), (2, -1), (2, 1), (2, 2), (3, -1), (3, 0),
   (3, 1), (4, 1), (4, 2), (5, -3), (5, 0), (6, -2)}

private def leftColor (p : Point) : Bool := decide (p ∈ leftGray)

private theorem left_pattern_polyhex : IsPolyhex (offsets leftPattern) := by
  refine tree_polyhex (offsets leftPattern) (-1, 0) [
    ((0, 0), (-1, 0)), ((0, 1), (0, 0)), ((1, -1), (0, 0))] (by decide) ?_
  decide +kernel

private theorem left_board_polyhex : IsPolyhex leftBoard := by
  refine tree_polyhex leftBoard (0, 0) [
    ((1, 0), (0, 0)), ((0, 1), (0, 0)), ((1, -1), (0, 0)), ((2, 0), (1, 0)),
    ((1, 1), (1, 0)), ((2, -1), (1, 0)), ((3, 0), (2, 0)), ((2, 1), (2, 0)),
    ((3, -1), (2, 0)), ((1, 2), (1, 1)), ((3, -2), (2, -1)), ((4, 0), (3, 0)),
    ((3, 1), (3, 0)), ((4, -1), (3, 0)), ((2, 2), (2, 1)), ((4, -2), (3, -1)),
    ((5, 0), (4, 0)), ((4, 1), (4, 0)), ((5, -1), (4, 0)), ((3, 2), (3, 1)),
    ((5, -2), (4, -1)), ((2, 3), (2, 2)), ((5, -3), (4, -2)), ((4, 2), (4, 1)),
    ((6, -2), (5, -1)), ((3, 3), (3, 2)), ((6, -3), (5, -2))] (by decide) ?_
  decide +kernel

private def rightBoard : Finset Point :=
  {(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
   (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
   (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5),
   (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2)}

private def rightGray : Finset Point :=
  {(0, 1), (0, 3), (1, 0), (1, 2), (1, 3), (1, 6), (2, 0),
   (2, 1), (2, 3), (2, 4), (2, 5), (3, 3)}

private def rightColor (p : Point) : Bool := decide (p ∈ rightGray)

private theorem right_pattern_polyhex : IsPolyhex (offsets rightPattern) := by
  refine tree_polyhex (offsets rightPattern) (0, 0) [
    ((1, 0), (0, 0)), ((1, 1), (1, 0)), ((0, 2), (1, 1))] (by decide) ?_
  decide +kernel

private theorem right_board_polyhex : IsPolyhex rightBoard := by
  refine tree_polyhex rightBoard (0, 0) [
    ((1, 0), (0, 0)), ((0, 1), (0, 0)), ((2, 0), (1, 0)), ((1, 1), (1, 0)),
    ((0, 2), (0, 1)), ((3, 0), (2, 0)), ((2, 1), (2, 0)), ((1, 2), (1, 1)),
    ((0, 3), (0, 2)), ((3, 1), (3, 0)), ((2, 2), (2, 1)), ((1, 3), (1, 2)),
    ((0, 4), (0, 3)), ((4, 1), (3, 1)), ((3, 2), (3, 1)), ((2, 3), (2, 2)),
    ((1, 4), (1, 3)), ((0, 5), (0, 4)), ((4, 2), (4, 1)), ((3, 3), (3, 2)),
    ((2, 4), (2, 3)), ((1, 5), (1, 4)), ((0, 6), (0, 5)), ((3, 4), (3, 3)),
    ((2, 5), (2, 4)), ((1, 6), (1, 5)), ((0, 7), (0, 6))] (by decide) ?_
  decide +kernel

/-- The three steps in the coordinates given by the two arm differences. -/
private def simplex : Finset Point := {0, (1, 0), (0, 1)}

/-- A horizontal or vertical fiber has an exposed endpoint in the corresponding direction. -/
private theorem boundary_of_max (S : Finset Point) (primary secondary : Point → ℤ)

    (step : Point) (hstep : step ∈ simplex)
    (hprimary : ∀ p : Point, primary (p + step) = primary p)
    (hsecondary : ∀ p : Point, secondary p < secondary (p + step))
    (i : ℤ) (hi : i ∈ S.image primary) :
    ∃ p ∈ (S + simplex) \ S, primary p = i ∧
      ∀ q ∈ S, primary q = i → secondary q < secondary p := by
  obtain ⟨z, hz, hzi⟩ := mem_image.mp hi
  obtain ⟨p, hp, hmax⟩ :=
    (S.filter fun q => primary q = i).exists_max_image secondary
      ⟨z, mem_filter.mpr ⟨hz, hzi⟩⟩
  have hpi := (mem_filter.mp hp).2
  have hsame : primary (p + step) = i := (hprimary p).trans hpi
  have hlt : ∀ q ∈ S, primary q = i → secondary q < secondary (p + step) :=
    fun q hq hqi => (hmax q (mem_filter.mpr ⟨hq, hqi⟩)).trans_lt (hsecondary p)
  refine ⟨p + step, mem_sdiff.mpr ⟨mem_add.mpr ⟨p, (mem_filter.mp hp).1, step, hstep, rfl⟩,
    fun h => (lt_irrefl _ (hlt _ h hsame))⟩, hsame, hlt⟩

/-- The first (i+1) occupied rows and the vertical fibers meeting row (i)
give disjoint portions of the outer boundary. -/
private theorem simplex_row_bound (S : Finset Point) (rows : Finset ℤ)
    (hrows : rows = S.image Prod.snd) (i : Fin rows.card) :
    (S.filter fun p => p.2 = (rows.orderIsoOfFin rfl i : ℤ)).card + (i.val + 1) ≤
      ((S + simplex) \ S).card := by
  classical
  let row := rows.orderIsoOfFin rfl
  let y : ℤ := (row i : ℤ)
  let D := (S + simplex) \ S
  have hor (j : Fin rows.card) :
      ∃ p ∈ D, p.2 = (row j : ℤ) := by
    obtain ⟨p, hp, heq, _⟩ :=
      boundary_of_max S Prod.snd Prod.fst
        (1, 0) (by decide) (by intro p; simp) (by intro p; simp)
        (row j : ℤ) (hrows ▸ (row j).property)
    exact ⟨p, hp, heq⟩
  have ver (p : Point) (hp : p ∈ S.filter (fun p => p.2 = y)) :
      ∃ q ∈ D.filter (fun q => y < q.2), q.1 = p.1 := by
    obtain ⟨hpS, hpy⟩ := mem_filter.mp hp
    obtain ⟨q, hq, heq, hmax⟩ :=
      boundary_of_max S Prod.fst Prod.snd
        (0, 1) (by decide) (by intro p; simp) (by intro p; simp)
        p.1 (mem_image_of_mem _ hpS)
    refine ⟨q, mem_filter.mpr ⟨hq, ?_⟩, heq⟩
    rw [← hpy]
    exact hmax p hpS rfl
  have hlo : i.val + 1 ≤ (D.filter fun p => ¬ y < p.2).card := by
    let embed (j : Fin (i.val + 1)) : Fin rows.card := ⟨j.val, by omega⟩
    let f (j : Fin (i.val + 1)) : Point := (hor (embed j)).choose
    have hf (j : Fin (i.val + 1)) := (hor (embed j)).choose_spec
    have hc : (univ : Finset (Fin (i.val + 1))).card ≤ (D.filter fun p => ¬ y < p.2).card := by
      apply card_le_card_of_injOn f
      · intro j _
        refine mem_filter.mpr ⟨(hf j).1, ?_⟩
        rw [(hf j).2]
        have hj : embed j ≤ i := by change j.val ≤ i.val; omega
        exact not_lt_of_ge (row.monotone hj)
      · intro j _ k _ hjk
        have he : (row (embed j) : ℤ) = (row (embed k) : ℤ) :=
          (hf j).2.symm.trans ((congrArg Prod.snd hjk).trans (hf k).2)
        exact Fin.ext (congrArg (fun k : Fin rows.card => k.val) (row.injective (Subtype.ext he)))
    simpa using hc
  have hhi : (S.filter fun p => p.2 = y).card ≤ (D.filter fun p => y < p.2).card := by
    classical
    let f (p : Point) : Point := if hp : p ∈ S.filter (fun q => q.2 = y)
      then (ver p hp).choose else p
    have hf (p : Point) (hp : p ∈ S.filter (fun q => q.2 = y)) :
        f p ∈ D.filter (fun q => y < q.2) ∧ (f p).1 = p.1 := by
      simpa only [f, dite_eq_left hp] using (ver p hp).choose_spec
    apply card_le_card_of_injOn f
    · exact fun p hp => (hf p hp).1
    · intro p hp q hq hpq
      exact Prod.ext ((hf p hp).2.symm.trans ((congrArg Prod.fst hpq).trans (hf q hq).2))
        ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
  have hpartition := D.card_filter_add_card_filter_not (fun p => y < p.2)
  change (S.filter (fun p => p.2 = y)).card + (i.val + 1) ≤ D.card
  omega

/-- The forward simplex adds a boundary of size (g), where
(2|S| le g(g-1)). This holds for arbitrary finite (S). -/
private theorem simplex_growth (S : Finset Point) :
    let g := (S + simplex).card - S.card
    2 * S.card ≤ g * (g - 1) := by
  classical
  let rows := S.image Prod.snd
  let g := ((S + simplex) \ S).card
  let row := rows.orderIsoOfFin rfl
  let count (y : ℤ) := (S.filter fun p => p.2 = y).card
  have hrank (i : Fin rows.card) : count (row i : ℤ) + (i.val + 1) ≤ g :=
    simplex_row_bound S rows rfl i
  have hk : rows.card ≤ g := by
    by_cases hp : 0 < rows.card
    · have hlast := hrank ⟨rows.card - 1, by omega⟩
      simp only at hlast
      omega
    · omega
  have hsum : S.card = ∑ i : Fin rows.card, count (row i : ℤ) := by
    rw [card_eq_sum_card_image (f := Prod.snd)]
    change (∑ y ∈ rows, count y) = _
    rw [← rows.sum_coe_sort count]
    exact
      (Fintype.sum_equiv row.toEquiv (fun i => count (row i : ℤ))
        (fun y => count (y : ℤ)) (fun _ => rfl)).symm
  have hbound : (∑ i : Fin rows.card, count (row i : ℤ)) ≤ ∑ i : Fin rows.card, (g - 1 - i.val) :=
    sum_le_sum (fun i _ => by have h := hrank i; omega)
  have htotal : (∑ i : Fin rows.card, (g - 1 - i.val)) ≤ ∑ i ∈ range g, i := by
    rw [Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑ i ∈ range g, (g - 1 - i) :=
        sum_le_sum_of_subset_of_nonneg (range_mono hk) (fun _ _ _ => Nat.zero_le _)
      _ = _ := by simpa only [Nat.sub_sub] using (sum_range_reflect (fun i : ℕ => i) g)
  have htri := sum_range_id_mul_two g
  have hsub : S ⊆ S + simplex := by
    intro p hp
    exact mem_add.mpr ⟨p, hp, 0, by decide, add_zero _⟩
  have hg : g = (S + simplex).card - S.card := card_sdiff_of_subset hsub
  dsimp
  rw [← hg]
  omega

private def residue (p : Point) : ℤ := (p.2 - p.1) % 3

private def fiber (N : Finset Point) (i : ℤ) : Finset Point :=
  N.filter fun p => residue p = i

private theorem card_fibers (N : Finset Point) :
    N.card = (fiber N 0).card + (fiber N 1).card + (fiber N 2).card := by
  have hb : ∀ p ∈ N, residue p ∈ ({0, 1, 2} : Finset ℤ) := by
    intro p _
    have h : residue p = 0 ∨ residue p = 1 ∨ residue p = 2 := by unfold residue; omega
    simpa using h
  have h := card_eq_sum_card_fiberwise hb
  simpa [fiber, sum_insert, add_assoc] using h

private def decode (i : ℤ) : Point ↪ Point where
  toFun p := (p.1 + 2 * p.2 - i, p.1 - p.2)
  inj' := by
    intro p q h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change p.1 + 2 * p.2 - i = q.1 + 2 * q.2 - i at hx
    change p.1 - p.2 = q.1 - q.2 at hy
    exact Prod.ext (by omega) (by omega)

private def encode (i : ℤ) (p : Point) : Point :=
  let b := (p.1 - p.2 + i) / 3
  (p.2 + b, b)

private theorem decode_encode {i : ℤ} {p : Point} (h : residue p = i) :
    decode i (encode i p) = p := by
  unfold residue at h
  apply Prod.ext
  · change p.2 + (p.1 - p.2 + i) / 3 + 2 * ((p.1 - p.2 + i) / 3) - i = p.1
    omega
  · change p.2 + (p.1 - p.2 + i) / 3 - (p.1 - p.2 + i) / 3 = p.2
    omega

private theorem residue_decode (i : ℤ) (p : Point) : residue (decode i p) = i % 3 := by
  change (p.1 - p.2 - (p.1 + 2 * p.2 - i)) % 3 = i % 3
  omega

private theorem decode_step (i : ℤ) (p s : Point) (hs : s ∈ simplex) :
    ∃ a ∈ offsets leftPattern, decode (i+1) (p + s) = decode i p + a := by
  have h : s = 0 ∨ s = (1, 0) ∨ s = (0, 1) := by simpa [simplex] using hs
  have combine :
      decode (i+1) (p+s) = decode i p + (s.1 + 2*s.2 - 1, s.1-s.2) := by
    apply Prod.ext
    · change p.1+s.1 + 2*(p.2+s.2) - (i+1) = (p.1+2*p.2-i) + (s.1+2*s.2-1)
      omega
    · change p.1+s.1 - (p.2+s.2) = (p.1-p.2) + (s.1-s.2)
      omega
  rcases h with rfl | rfl | rfl
  · exact ⟨(-1, 0), by decide, by simpa using combine⟩
  · exact ⟨(0, 1), by decide, by simpa using combine⟩
  · exact ⟨(1, -1), by decide, by simpa using combine⟩

/-- The three nonzero offsets send a residue fiber to a simplex expansion in the
next residue. The origin separately preserves every input fiber. -/
private theorem fiber_growth (N : Finset Point) (i : ℤ) :
    let m := (fiber N i).card
    let x := (fiber (N + offsets leftPattern) ((i+1) % 3)).card
    m ≤ x ∧ 2 * m ≤ (x-m) * (x-m-1) := by
  dsimp only
  let F := fiber N i
  let S := F.image (encode i)
  let X := fiber (N + offsets leftPattern) ((i+1) % 3)
  have hcard : S.card = F.card := by
    apply card_image_of_injOn
    intro p hp q hq he
    have hp' : residue p = i := (mem_filter.mp hp).2
    have hq' : residue q = i := (mem_filter.mp hq).2
    rw [← decode_encode hp', ← decode_encode hq', he]
  have hmap : (S + simplex).map (decode (i+1)) ⊆ X := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hq
    obtain ⟨p, hp, s, hs, rfl⟩ := mem_add.mp hv
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
    obtain ⟨hnN, hni⟩ : n ∈ N ∧ residue n = i := mem_filter.mp hn
    obtain ⟨a, ha, he⟩ := decode_step i (encode i n) s hs
    exact mem_filter.mpr
      ⟨mem_add.mpr ⟨n, hnN, a, ha, by rw [he, decode_encode hni]⟩, residue_decode _ _⟩
  have hupper : (S + simplex).card ≤ X.card := by
    simpa only [card_map] using card_le_card hmap
  have hsub : S ⊆ S + simplex :=
    fun p hp => mem_add.mpr ⟨p, hp, 0, by decide, add_zero _⟩
  have hlower := card_le_card hsub
  have hg := simplex_growth S
  change 2 * S.card ≤ ((S + simplex).card - S.card) * ((S + simplex).card - S.card - 1) at hg
  change F.card ≤ X.card ∧ 2 * F.card ≤ (X.card - F.card) * (X.card - F.card - 1)
  rw [← hcard]
  refine ⟨hlower.trans hupper, hg.trans ?_⟩
  exact Nat.mul_le_mul (by omega) (by omega)

private theorem fiber_inclusion (N : Finset Point) (i : ℤ) :
    (fiber N i).card ≤ (fiber (N + offsets leftPattern) i).card := by
  apply card_le_card
  intro p hp
  obtain ⟨h1, h2⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_add.mpr ⟨p, h1, 0, by decide, add_zero _⟩, h2⟩

/-- The least possible boundary size for input sizes up to sixteen. -/
private def delta (m : ℕ) : ℕ :=
  if m = 0 then 0 else if m ≤ 1 then 2 else if m ≤ 3 then 3 else if m ≤ 6 then 4
  else if m ≤ 10 then 5 else if m ≤ 15 then 6 else 7

private theorem delta_le {m g : ℕ} (hm : m ≤ 16) (h : 2 * m ≤ g * (g - 1)) :
    delta m ≤ g := by
  have hd : delta m ≤ 7 := by unfold delta; split_ifs <;> omega
  by_cases hg : g ≤ 16
  · have finite : ∀ a b : Fin 17, 2 * a.val ≤ b.val * (b.val - 1) → delta a.val ≤ b.val := by
      decide +kernel
    exact finite ⟨m, by omega⟩ ⟨g, by omega⟩ h
  · omega

private theorem residue_arithmetic {a b c : ℕ} (h : a + b + c = 16) :
    28 ≤ max a (c + delta c) + max b (a + delta a) + max c (b + delta b) := by
  have finite : ∀ a b c : Fin 17, a.val + b.val + c.val = 16 →
      28 ≤ max a.val (c.val + delta c.val) + max b.val (a.val + delta a.val) +
        max c.val (b.val + delta b.val) := by
    decide +kernel
  exact finite ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ h

/-- Every union of sixteen translates of the fixed left pattern has at least
twenty-eight cells. -/
private theorem left_sumset_lower (N : Finset Point) (hN : N.card = 16) :
    28 ≤ (N + offsets leftPattern).card := by
  let Y := N + offsets leftPattern
  let a := (fiber N 0).card
  let b := (fiber N 1).card
  let c := (fiber N 2).card
  let x := (fiber Y 0).card
  let y := (fiber Y 1).card
  let z := (fiber Y 2).card
  have habc : a+b+c = 16 := (card_fibers N).symm.trans hN
  have hxyz : Y.card = x+y+z := card_fibers Y
  have h0 : a ≤ x := fiber_inclusion N 0
  have h1 : b ≤ y := fiber_inclusion N 1
  have h2 : c ≤ z := fiber_inclusion N 2
  have h01 : a ≤ y ∧ 2*a ≤ (y-a)*(y-a-1) := fiber_growth N 0
  have h12 : b ≤ z ∧ 2*b ≤ (z-b)*(z-b-1) := fiber_growth N 1
  have h20 : c ≤ x ∧ 2*c ≤ (x-c)*(x-c-1) := fiber_growth N 2
  have ha : max a (c + delta c) ≤ x :=
    max_le h0 (by have hd := delta_le (by omega) h20.2; omega)
  have hb : max b (a + delta a) ≤ y :=
    max_le h1 (by have hd := delta_le (by omega) h01.2; omega)
  have hc : max c (b + delta b) ≤ z :=
    max_le h2 (by have hd := delta_le (by omega) h12.2; omega)
  have hmin := residue_arithmetic habc
  change 28 ≤ Y.card
  omega

private theorem lower_of_sumset_lower (P : Fin 4 → Point)
    (h : ∀ N : Finset Point, N.card = 16 → 28 ≤ (N + offsets P).card)
    (B : Finset Point) (hB : 16 ≤ (anchors P B).card) : 28 ≤ B.card := by
  obtain ⟨N, hsub, hN⟩ := exists_subset_card_eq hB
  apply (h N hN).trans (card_le_card ?_)
  intro p hp
  obtain ⟨t, ht, a, ha, rfl⟩ := mem_add.mp hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  exact mem_anchors.mp (hsub ht) i

private theorem left_prismatic : IsPrismatic leftPattern leftBoard leftColor := by
  have witness : FigureWitness leftPattern leftBoard leftColor := by
    refine ⟨left_pattern_polyhex, by decide, left_board_polyhex, by decide, ?_, ?_⟩
    · decide +kernel
    · unfold IsBinaryDeBruijn
      decide +kernel
  refine ⟨witness, witness.2.2.1, ?_, fun B _ hB => ?_⟩
  · exact witness.2.2.2.2.1.ge
  · have hc : leftBoard.card = 28 := witness.2.2.2.1
    simpa only [hc] using lower_of_sumset_lower leftPattern left_sumset_lower B hB

/-- For a nonempty consecutive run of (k) columns, (n_i) and (b_i)
are its input and output sizes, and (E) is its increase in area.
An increase of at most eleven bounds the run length by five. -/
private theorem right_run_bound (k : ℕ) (n b : ℕ → ℕ) (hk : 0 < k)
    (hn : ∀ i < k, 0 < n i)
    (hfirst : n 0 + 1 ≤ b 0)
    (hprev : ∀ i < k, n i + 1 ≤ b (i + 1))
    (hmiddle : ∀ i < k, 0 < i → n i + 2 ≤ b i)
    (hfirstTight : 1 < k → b 0 = n 0 + 1 → 2 * n 0 ≤ b 1)
    (E : ℕ) (hE : E = (∑ i ∈ range k, (b i - n i)) + b k) (hbudget : E ≤ 11) :
    33 * (∑ i ∈ range k, n i) ≤ 47 * E := by
  have hsum : (∑ i ∈ range k, (if i = 0 then 1 else 2)) ≤
      ∑ i ∈ range k, (b i - n i) := by
    apply sum_le_sum
    intro i hi
    have hi' := mem_range.mp hi
    by_cases h : i = 0
    · subst i
      change 1 ≤ b 0 - n 0
      omega
    · rw [ite_eq_right h]
      have hm := hmiddle i hi' (Nat.pos_of_ne_zero h)
      omega
  have hcount : (∑ i ∈ range k, (if i = 0 then 1 else 2)) = 2 * k - 1 := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [sum_range_succ']
    simp
    omega
  have hlast := hprev (k-1) (by omega)
  have hnlast := hn (k-1) (by omega)
  have hklast : k-1+1 = k := by omega
  rw [hklast] at hlast
  have hsize : k ≤ 5 := by omega
  interval_cases k <;>
    norm_num [sum_range_succ] at hE ⊢
  all_goals
    have h1 := hn 0 (by decide)
    have hp0 := hprev 0 (by decide)
    try have h2 := hn 1 (by decide)
    try have h3 := hn 2 (by decide)
    try have h4 := hn 3 (by decide)
    try have h5 := hn 4 (by decide)
    try have hp1 := hprev 1 (by decide)
    try have hp2 := hprev 2 (by decide)
    try have hp3 := hprev 3 (by decide)
    try have hp4 := hprev 4 (by decide)
    try have hm1 := hmiddle 1 (by decide) (by decide)
    try have hm2 := hmiddle 2 (by decide) (by decide)
    try have hm3 := hmiddle 3 (by decide) (by decide)
    try have hm4 := hmiddle 4 (by decide) (by decide)
    norm_num at *
    omega

private def column (N : Finset Point) (i : ℤ) : Finset ℤ :=
  (N.filter fun p => p.1 = i).image Prod.snd

private theorem mem_column {N : Finset Point} {i y : ℤ} :
    y ∈ column N i ↔ (i, y) ∈ N := by
  constructor
  · intro h
    obtain ⟨p, hp, hpy⟩ := mem_image.mp h
    obtain ⟨hpN, hpi⟩ := mem_filter.mp hp
    have h : p = (i, y) := Prod.ext hpi hpy
    exact h ▸ hpN
  · intro h
    exact mem_image.mpr ⟨(i,y), mem_filter.mpr ⟨h, rfl⟩, rfl⟩

private def verticalGrow (S : Finset ℤ) (d : ℤ) : Finset ℤ :=
  S ∪ S.image (· + d)

private theorem mem_verticalGrow {S : Finset ℤ} {d y : ℤ} :
    y ∈ verticalGrow S d ↔ y ∈ S ∨ ∃ t ∈ S, t + d = y := by
  simp only [verticalGrow, mem_union, mem_image]

private theorem right_column_exact (N : Finset Point) (i : ℤ) :
    column (N + offsets rightPattern) i =
      verticalGrow (column N i) 2 ∪ verticalGrow (column N (i-1)) 1 := by
  have hP : offsets rightPattern = {(0, 0), (0, 2), (1, 0), (1, 1)} := by decide
  ext y
  simp only [mem_column, hP, mem_union, mem_verticalGrow, mem_column]
  constructor
  · intro h
    obtain ⟨⟨x,t⟩, hp, a, ha, he⟩ := mem_add.mp h
    simp only [mem_insert, mem_singleton] at ha
    have prove (u v : ℤ) (h : a = (u,v)) : x+u=i ∧ t+v=y := by
      subst a
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    rcases ha with ha | ha | ha | ha
    · obtain ⟨hx, hy⟩ := prove 0 0 ha
      exact Or.inl (Or.inl (by simpa [← hx, ← hy] using hp))
    · obtain ⟨hx, hy⟩ := prove 0 2 ha
      exact Or.inl (Or.inr ⟨t, by simpa [← hx] using hp, hy⟩)
    · obtain ⟨hx, hy⟩ := prove 1 0 ha
      have hxi : x = i - 1 := by omega
      exact Or.inr (Or.inl (by simpa [← hxi, ← hy] using hp))
    · obtain ⟨hx, hy⟩ := prove 1 1 ha
      have hxi : x = i - 1 := by omega
      exact Or.inr (Or.inr ⟨t, by simpa [← hxi] using hp, hy⟩)
  · rintro ((h | ⟨t, ht, rfl⟩) | (h | ⟨t, ht, rfl⟩))
    · exact mem_add.mpr ⟨(i,y), h, (0,0), by decide, by simp⟩
    · exact mem_add.mpr ⟨(i,t), ht, (0,2), by decide, by simp⟩
    · exact mem_add.mpr ⟨(i-1,y), h, (1,0), by decide, Prod.ext (by simp) (by simp)⟩
    · exact mem_add.mpr ⟨(i-1,t), ht, (1,1), by decide, Prod.ext (by simp) (by simp)⟩

private theorem verticalGrow_subset_left (S : Finset ℤ) (d : ℤ) :
    S ⊆ verticalGrow S d := fun _ hx => mem_verticalGrow.mpr (Or.inl hx)

private theorem verticalGrow_mem_add {S : Finset ℤ} {d x : ℤ} (hx : x ∈ S) :
    x + d ∈ verticalGrow S d := mem_verticalGrow.mpr (Or.inr ⟨x, hx, rfl⟩)

private theorem verticalGrow_card {S : Finset ℤ} {d : ℤ} (hS : S.Nonempty) (hd : 0 < d) :
    S.card + 1 ≤ (verticalGrow S d).card := by
  let x := S.max' hS
  have hx : x ∈ S := max'_mem S hS
  have hnew : x+d ∉ S := fun h => (not_le_of_gt (by omega : x < x+d)) (le_max' S _ h)
  rw [← card_insert_of_notMem hnew]
  apply card_le_card
  intro z hz
  rcases mem_insert.mp hz with rfl | hz
  · exact verticalGrow_mem_add hx
  · exact verticalGrow_subset_left S d hz

private theorem parity_endpoint {S : Finset ℤ} {x : ℤ} (hx : x ∈ S) :
    ∃ y ∈ verticalGrow S 2, y ∉ S ∧ y % 2 = x % 2 := by
  let T := S.filter fun t => t % 2 = x % 2
  have hT : T.Nonempty := ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  let z := T.max' hT
  obtain ⟨hzS, hz⟩ : z ∈ S ∧ z % 2 = x % 2 := mem_filter.mp (max'_mem T hT)
  have hz2 : (z+2) % 2 = x % 2 := by omega
  refine ⟨z+2, verticalGrow_mem_add hzS, ?_, hz2⟩
  intro h
  have hm := le_max' T (z+2) (mem_filter.mpr ⟨h, hz2⟩)
  change z+2 ≤ z at hm
  omega

private theorem card_add_two {S Y : Finset ℤ} {a b : ℤ} (hsub : S ⊆ Y)
    (ha : a ∈ Y) (hb : b ∈ Y) (haS : a ∉ S) (hbS : b ∉ S) (hab : a ≠ b) :
    S.card + 2 ≤ Y.card := by
  have hb' : b ∉ insert a S := by simp [Ne.symm hab, hbS]
  have hcard : (insert b (insert a S)).card = S.card + 2 := by
    rw [card_insert_of_notMem hb', card_insert_of_notMem haS]
  rw [← hcard]
  exact card_le_card (insert_subset_iff.mpr ⟨hb, insert_subset_iff.mpr ⟨ha, hsub⟩⟩)

private theorem grow_card_of_two_parities {S : Finset ℤ} {x y : ℤ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x % 2 ≠ y % 2) :
    S.card + 2 ≤ (verticalGrow S 2).card := by
  obtain ⟨a, ha, haS, hax⟩ := parity_endpoint hx
  obtain ⟨b, hb, hbS, hby⟩ := parity_endpoint hy
  exact card_add_two (verticalGrow_subset_left S 2) ha hb haS hbS (by omega)

private theorem right_interior_column {S T : Finset ℤ} (hS : S.Nonempty) (hT : T.Nonempty) :
    S.card + 2 ≤ (verticalGrow S 2 ∪ verticalGrow T 1).card := by
  classical
  by_cases h : ∃ x ∈ S, ∃ y ∈ S, x % 2 ≠ y % 2
  · obtain ⟨x,hx,y,hy,hxy⟩ := h
    exact (grow_card_of_two_parities hx hy hxy).trans (card_le_card subset_union_left)
  · obtain ⟨x, hx⟩ := hS
    obtain ⟨t, ht⟩ := hT
    obtain ⟨a, ha, haS, hax⟩ := parity_endpoint hx
    have hall : ∀ y ∈ S, y % 2 = x % 2 := by
      intro y hy
      by_contra hyx
      exact h ⟨y, hy, x, hx, hyx⟩
    obtain ⟨b, hb, hbx⟩ : ∃ b ∈ verticalGrow T 1, b % 2 ≠ x % 2 := by
      by_cases ht' : t % 2 = x % 2
      · exact ⟨t+1, verticalGrow_mem_add ht, by omega⟩
      · exact ⟨t, verticalGrow_subset_left T 1 ht, ht'⟩
    exact card_add_two ((verticalGrow_subset_left S 2).trans subset_union_left)
      (mem_union_left _ ha) (mem_union_right _ hb) haS (fun h => hbx (hall _ h)) (by omega)

private theorem right_tight_first {S : Finset ℤ} (h : (verticalGrow S 2).card = S.card + 1) :
    (verticalGrow S 1).card = 2 * S.card := by
  have hall : ∀ x ∈ S, ∀ y ∈ S, x % 2 = y % 2 := by
    intro x hx y hy
    by_contra hxy
    have hh := grow_card_of_two_parities hx hy hxy
    omega
  have hdis : Disjoint S (S.image (· + 1)) := by
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hz'
    have hzy := hall (y+1) hz y hy
    omega
  have hc : (S.image (· + 1)).card = S.card :=
    card_image_of_injective S (fun x y hxy => by omega)
  rw [verticalGrow, card_union_of_disjoint hdis, hc]
  omega

private theorem column_card_eq (N : Finset Point) (i : ℤ) :
    (column N i).card = (N.filter fun p => p.1 = i).card := by
  apply card_image_of_injOn
  intro x hx y hy h
  exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) h

private theorem column_card_sum (N : Finset Point) (lo : ℤ) (k : ℕ)
    (hs : ∀ p ∈ N, lo ≤ p.1 ∧ p.1 < lo + (k : ℤ)) :
    N.card = ∑ i ∈ range k, (column N (lo + (i : ℤ))).card := by
  let index (p : Point) := (p.1 - lo).toNat
  have hindex : ∀ p ∈ N, index p ∈ range k := by
    intro p hp
    obtain ⟨hl, hu⟩ := hs p hp
    apply mem_range.mpr
    dsimp [index]
    omega
  rw [card_eq_sum_card_fiberwise hindex]
  apply sum_congr rfl
  intro i hi
  rw [column_card_eq]
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨hp, hi⟩
    have hl := (hs p hp).1
    dsimp [index] at hi
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, hi⟩
    refine ⟨hp, ?_⟩
    dsimp [index]
    omega

private theorem right_x_range :
    ∀ a ∈ offsets rightPattern, 0 ≤ a.1 ∧ a.1 ≤ 1 := by decide

private theorem first_coord_bounds {N : Finset Point} {lo hi : ℤ}
    (h : ∀ p ∈ N, lo ≤ p.1 ∧ p.1 < hi) :
    ∀ q ∈ N + offsets rightPattern, lo ≤ q.1 ∧ q.1 < hi+1 := by
  intro q hq
  obtain ⟨p, hp, a, ha, rfl⟩ := mem_add.mp hq
  have hp' := h p hp
  have ha' := right_x_range a ha
  simp only [Prod.fst_add]
  omega

private theorem right_origin_subset (N : Finset Point) : N ⊆ N + offsets rightPattern := by
  intro p hp
  exact mem_add.mpr ⟨p, hp, 0, by decide, add_zero _⟩

private theorem column_nonempty_at {N : Finset Point} {p : Point} (hp : p ∈ N) :
    (column N p.1).Nonempty :=
  ⟨p.2, mem_column.mpr hp⟩

/-- Apply the run bound when all the input columns in an interval are occupied. -/
private theorem contiguous (N : Finset Point) (lo : ℤ) (k : ℕ) (hk : 0 < k)
    (hN : ∀ p ∈ N, lo ≤ p.1 ∧ p.1 < lo + (k : ℤ))
    (hfilled : ∀ i : ℕ, i < k → (column N (lo + (i : ℤ))).Nonempty)
    (hE : (N + offsets rightPattern).card - N.card ≤ 11) :
    33 * N.card ≤ 47 * ((N + offsets rightPattern).card - N.card) := by
  let Y := N + offsets rightPattern
  let n (i : ℕ) := (column N (lo + (i : ℤ))).card
  let b (i : ℕ) := (column Y (lo + (i : ℤ))).card
  have hn : ∀ i < k, 0 < n i := fun i hi => card_pos.mpr (hfilled i hi)
  have hempty : column N (lo - 1) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hl := (hN (lo-1,y) (mem_column.mp hy)).1
    change lo ≤ lo-1 at hl
    omega
  have hout0 : column Y (lo + (0 : ℕ)) = verticalGrow (column N (lo + (0 : ℕ))) 2 := by
    rw [right_column_exact]
    simp [hempty, verticalGrow]
  have hfirst : n 0 + 1 ≤ b 0 := by
    change n 0 + 1 ≤ (column Y (lo+(0 : ℕ))).card
    rw [hout0]
    exact verticalGrow_card (hfilled 0 hk) (by decide)
  have hprev (i : ℕ) (hi : i < k) : n i + 1 ≤ b (i+1) := by
    change n i + 1 ≤ (column Y (lo+((i+1 : ℕ) : ℤ))).card
    have hs : lo + ((i+1 : ℕ) : ℤ) - 1 = lo + (i : ℤ) := by omega
    rw [right_column_exact, hs]
    exact (verticalGrow_card (hfilled i hi) (by decide : (0 : ℤ) < 1)).trans
      (card_le_card subset_union_right)
  have hmid (i : ℕ) (hi : i < k) (hpos : 0 < i) : n i + 2 ≤ b i := by
    change n i + 2 ≤ (column Y (lo + (i : ℤ))).card
    have hs : lo + (i : ℤ) - 1 = lo + ((i-1 : ℕ) : ℤ) := by omega
    rw [right_column_exact, hs]
    exact right_interior_column (hfilled i hi) (hfilled (i-1) (by omega))
  have htight (_ : 1 < k) (he : b 0 = n 0 + 1) : 2 * n 0 ≤ b 1 := by
    change (column Y (lo+(0 : ℕ))).card = n 0 + 1 at he
    rw [hout0] at he
    have hh := right_tight_first he
    change 2 * n 0 ≤ (column Y (lo+(1 : ℕ))).card
    have hs : lo + ((1 : ℕ) : ℤ) - 1 = lo + ((0 : ℕ) : ℤ) := by omega
    rw [right_column_exact, hs]
    rw [← hh]
    exact card_le_card subset_union_right
  have hsumN : N.card = ∑ i ∈ range k, n i := column_card_sum N lo k hN
  have hsumY : Y.card = (∑ i ∈ range k, b i) + b k := by
    rw [← sum_range_succ]
    exact column_card_sum Y lo (k+1)
      (fun p hp => by
        have h := first_coord_bounds hN p hp
        exact ⟨h.1, by omega⟩)
  have hnonneg (i : ℕ) (hi : i ∈ range k) : n i ≤ b i := by
    by_cases h : i = 0
    · subst i
      omega
    · have hh := hmid i (mem_range.mp hi) (Nat.pos_of_ne_zero h)
      omega
  have hs := sum_tsub_distrib (range k) hnonneg
  have hsumle : (∑ i ∈ range k, n i) ≤ ∑ i ∈ range k, b i := sum_le_sum hnonneg
  have heq : Y.card - N.card = (∑ i ∈ range k, (b i - n i)) + b k := by
    rw [hsumY, hsumN, hs]
    omega
  have bound := right_run_bound k n b hk hn hfirst hprev hmid htight _ heq hE
  rwa [← hsumN] at bound

/-- Split along an empty column. No output of the left side can reach the output
columns of the right side, so both input cardinality and expansion add. -/
private theorem right_excess_bound (N : Finset Point) :
    (N + offsets rightPattern).card - N.card ≤ 11 →
    33 * N.card ≤ 47 * ((N + offsets rightPattern).card - N.card) := by
  classical
  refine N.strongInductionOn ?_
  intro N ih hbudget
  by_cases hn : N.Nonempty
  · obtain ⟨p, hp, hmin⟩ := N.exists_min_image Prod.fst hn
    obtain ⟨q, hq, hmax⟩ := N.exists_max_image Prod.fst hn
    by_cases hfull : ∀ i : ℤ, p.1 ≤ i → i ≤ q.1 → (column N i).Nonempty
    · let k := (q.1 - p.1 + 1).toNat
      have hpq := hmin q hq
      have hk : 0 < k := by dsimp [k]; omega
      refine contiguous N p.1 k hk ?_ ?_ hbudget
      · intro r hr
        have hl := hmin r hr
        have hu := hmax r hr
        exact ⟨hl, by dsimp [k]; omega⟩
      · intro i hi
        apply hfull
        · omega
        · dsimp [k] at hi
          omega
    · push Not at hfull
      obtain ⟨gap, hlo, hhi, heq⟩ := hfull
      have hno (r : Point) (hr : r ∈ N) : r.1 ≠ gap := by
        intro hh
        have h := column_nonempty_at hr
        rw [hh, heq] at h
        exact not_nonempty_empty h
      let L := N.filter fun r => r.1 < gap
      let R := N.filter fun r => gap < r.1
      let A := offsets rightPattern
      have hL : L ⊂ N := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, ?_⟩
        intro he
        have hh := (mem_filter.mp (show q ∈ L from he.symm ▸ hq)).2
        exact (not_lt_of_ge hhi) hh
      have hR : R ⊂ N := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, ?_⟩
        intro he
        have hh := (mem_filter.mp (show p ∈ R from he.symm ▸ hp)).2
        exact (not_lt_of_ge hlo) hh
      have hsplit : N = L ∪ R := by
        ext r
        simp only [L, R, mem_union, mem_filter]
        constructor
        · intro hr
          rcases lt_or_gt_of_ne (hno r hr) with h | h
          · exact Or.inl ⟨hr, h⟩
          · exact Or.inr ⟨hr, h⟩
        · exact fun h => h.elim And.left And.left
      have hd : Disjoint L R := by
        rw [disjoint_left]
        intro r hr hs
        exact lt_asymm (mem_filter.mp hr).2 (mem_filter.mp hs).2
      have hsumN : N.card = L.card + R.card := by
        rw [hsplit, card_union_of_disjoint hd]
      have hsplitY : N + A = (L + A) ∪ (R + A) := by
        rw [hsplit]
        ext r
        simp only [mem_add, mem_union]
        constructor
        · rintro ⟨t, (ht | ht), a, ha, he⟩
          · exact Or.inl ⟨t, ht, a, ha, he⟩
          · exact Or.inr ⟨t, ht, a, ha, he⟩
        · rintro (⟨t, ht, a, ha, he⟩ | ⟨t, ht, a, ha, he⟩)
          · exact ⟨t, Or.inl ht, a, ha, he⟩
          · exact ⟨t, Or.inr ht, a, ha, he⟩
      have hdY : Disjoint (L + A) (R + A) := by
        rw [disjoint_left]
        intro r hr hs
        obtain ⟨x, hx, a, ha, hxr⟩ := mem_add.mp hr
        obtain ⟨y, hy, b, hb, hyr⟩ := mem_add.mp hs
        have hxa := congrArg Prod.fst hxr
        have hyb := congrArg Prod.fst hyr
        simp only [Prod.fst_add] at hxa hyb
        have hl : x.1 < gap := (mem_filter.mp hx).2
        have hh : gap < y.1 := (mem_filter.mp hy).2
        have ha' := right_x_range a ha
        have hb' := right_x_range b hb
        omega
      have hsumY : (N + A).card = (L + A).card + (R + A).card := by
        rw [hsplitY, card_union_of_disjoint hdY]
      have hsubL := card_le_card (right_origin_subset L)
      have hsubR := card_le_card (right_origin_subset R)
      change L.card ≤ (L + A).card at hsubL
      change R.card ≤ (R + A).card at hsubR
      change (N + A).card - N.card ≤ 11 at hbudget
      have hbl : (L + A).card - L.card ≤ 11 := by omega
      have hbr : (R + A).card - R.card ≤ 11 := by omega
      have hl := ih L hL hbl
      have hr := ih R hR hbr
      change 33 * L.card ≤ 47 * ((L + A).card - L.card) at hl
      change 33 * R.card ≤ 47 * ((R + A).card - R.card) at hr
      change 33 * N.card ≤ 47 * ((N + A).card - N.card)
      omega
  · have he : N = ∅ := not_nonempty_iff_eq_empty.mp hn
    simp [he]

/-- Every union of sixteen translates of the fixed right pattern has at least
twenty-eight cells. -/
private theorem right_sumset_lower (N : Finset Point) (hN : N.card = 16) :
    28 ≤ (N + offsets rightPattern).card := by
  by_contra h
  have hexcess : (N + offsets rightPattern).card - N.card ≤ 11 := by omega
  have bound := right_excess_bound N hexcess
  omega

private theorem right_prismatic : IsPrismatic rightPattern rightBoard rightColor := by
  have witness : FigureWitness rightPattern rightBoard rightColor := by
    refine ⟨right_pattern_polyhex, by decide, right_board_polyhex, by decide, ?_, ?_⟩
    · decide +kernel
    · unfold IsBinaryDeBruijn
      decide +kernel
  refine ⟨witness, witness.2.2.1, ?_, fun B _ hB => ?_⟩
  · exact witness.2.2.2.2.1.ge
  · have hc : rightBoard.card = 28 := witness.2.2.2.1
    simpa only [hc] using lower_of_sumset_lower rightPattern right_sumset_lower B hB

private def leftAxes : Point ≃+ Point where
  toFun p := (-p.1, -p.2)
  invFun p := (-p.1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [add_comm]

private def rightAxes : Point ≃+ Point where
  toFun p := (-p.2, -p.1)
  invFun p := (-p.2, -p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [add_comm]

/-- The offset lists of issues #31892 and #31893, in the Figure 26 word order. -/
def leftIssuePattern : Fin 4 → Point := ![(0,-1), (0,0), (1,0), (-1,1)]

def rightIssuePattern : Fin 4 → Point := ![(0,0), (1,0), (-1,1), (1,1)]

def leftIssueBoard : Finset Point := leftBoard.map leftAxes.toEquiv.toEmbedding
def rightIssueBoard : Finset Point := rightBoard.map rightAxes.toEquiv.toEmbedding
def leftIssueColor (p : Point) : Bool := leftColor (leftAxes.symm p)
def rightIssueColor (p : Point) : Bool := rightColor (rightAxes.symm p)

private theorem mem_axes {e : Point ≃+ Point} {B : Finset Point} {p : Point} :
    e p ∈ B.map e.toEquiv.toEmbedding ↔ p ∈ B := by
  exact mem_map' e.toEquiv.toEmbedding

private theorem polyhex_map (f : Point ↪ Point)
    (hf : ∀ p q, Adj p q → Adj (f p) (f q))
    (B : Finset Point) (hB : IsPolyhex B) : IsPolyhex (B.map f) := by
  have walk {p q : Point} (hpq : BoardReach B p q) :
      BoardReach (B.map f) (f p) (f q) := by
    induction hpq with
    | refl => exact .refl
    | tail _ hstep ih =>
      exact ih.tail ⟨(mem_map' f).mpr hstep.1, (mem_map' f).mpr hstep.2.1, hf _ _ hstep.2.2⟩
  obtain ⟨r, hr⟩ := hB.1
  refine ⟨⟨f r, (mem_map' f).mpr hr⟩, ?_⟩
  intro p hp q hq
  obtain ⟨p', hp', rfl⟩ := mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := mem_map.mp hq
  exact walk (hB.2 p' hp' q' hq')

private theorem adj_axes (e : Point ≃+ Point) (h : hexSteps.map e.toEquiv.toEmbedding = hexSteps)
    (p q : Point) (hpq : Adj p q) : Adj (e p) (e q) := by
  change e q - e p ∈ hexSteps
  rw [← map_sub, ← h]
  exact mem_axes.mpr hpq

private def pointAxes (e : Point ≃+ Point) (s : Point) : Point ↪ Point where
  toFun p := e p + s
  inj' := fun _ _ h => e.injective (add_right_cancel h)

private theorem adj_pointAxes (e : Point ≃+ Point) (s : Point)
    (h : hexSteps.map e.toEquiv.toEmbedding = hexSteps) (p q : Point) (hpq : Adj p q) :
    Adj (pointAxes e s p) (pointAxes e s q) := by
  change (e q + s) - (e p + s) ∈ hexSteps
  rw [add_sub_add_right_eq_sub]
  exact adj_axes e h p q hpq

private def anchorAxes (e : Point ≃+ Point) (s : Point) : Point ↪ Point where
  toFun t := e t - s
  inj' := fun _ _ h => e.injective (sub_left_inj.mp h)

private theorem anchor_target (e : Point ≃+ Point) (s t a : Point) :
    anchorAxes e s t + (e a + s) = e (t + a) := by
  change (e t - s) + (e a + s) = e (t+a)
  rw [map_add]
  abel

private theorem anchors_axes (e : Point ≃+ Point) (s : Point) (P : Fin 4 → Point) (B : Finset Point) :
    anchors (fun i => e (P i) + s) (B.map e.toEquiv.toEmbedding) =
      (anchors P B).map (anchorAxes e s) := by
  ext u
  have he : anchorAxes e s (e.symm (u+s)) = u := by
    change e (e.symm (u+s)) - s = u
    simp
  rw [← he, mem_map', mem_anchors, mem_anchors]
  simp only [anchor_target, mem_axes]

private theorem word_axes (e : Point ≃+ Point) (s : Point) (P : Fin 4 → Point)
    (color : Point → Bool) (t : Point) :
    wordAt (fun i => e (P i) + s) (fun p => color (e.symm p)) (anchorAxes e s t) =
      wordAt P color t := by
  simp only [wordAt, anchor_target, AddEquiv.symm_apply_apply]

private theorem offsets_axes (e : Point ≃+ Point) (s : Point) (P : Fin 4 → Point) :
    offsets (fun i => e (P i)+s) = (offsets P).map (pointAxes e s) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_map.mpr ⟨P i, mem_image_of_mem P (mem_univ i), rfl⟩
  · intro hp
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    exact mem_image_of_mem (fun i => e (P i) + s) (mem_univ i)

private theorem issue_prismatic (e : Point ≃+ Point) (s : Point) (P : Fin 4 → Point)
    (B : Finset Point) (color : Point → Bool)
    (hAxes : hexSteps.map e.toEquiv.toEmbedding = hexSteps)
    (hB : IsPrismatic P B color) :
    IsPrismatic (fun i => e (P i)+s) (B.map e.toEquiv.toEmbedding) (fun p => color (e.symm p)) := by
  obtain ⟨⟨hPattern, hshape, hpoly, hcard, hcount, hwords⟩, _, _, hmin⟩ := hB
  have hInvAxes : hexSteps.map e.symm.toEquiv.toEmbedding = hexSteps := by
    have hcomp : e.toEquiv.toEmbedding.trans e.symm.toEquiv.toEmbedding =
        Function.Embedding.refl Point := by
      apply Function.Embedding.ext
      intro p
      exact e.symm_apply_apply p
    calc
      _ = (hexSteps.map e.toEquiv.toEmbedding).map e.symm.toEquiv.toEmbedding :=
        congrArg (Finset.map e.symm.toEquiv.toEmbedding) hAxes.symm
      _ = hexSteps := by rw [map_map, hcomp, map_refl]
  have hpoly' := polyhex_map e.toEquiv.toEmbedding (adj_axes e hAxes) B hpoly
  have hcount' : (anchors (fun i => e (P i)+s) (B.map e.toEquiv.toEmbedding)).card = 16 := by
    rw [anchors_axes, card_map, hcount]
  refine ⟨⟨?_, ?_, hpoly', ?_, hcount', ?_⟩, hpoly', hcount'.ge, ?_⟩
  · rw [offsets_axes]
    exact polyhex_map (pointAxes e s) (adj_pointAxes e s hAxes) _ hPattern
  · rw [offsets_axes, card_map, hshape]
  · rw [card_map, hcard]
  · intro w
    rw [anchors_axes, filter_map, card_map]
    simpa only [Function.comp_apply, word_axes] using hwords w
  · intro C hCpoly hC
    let D := C.map e.symm.toEquiv.toEmbedding
    have hback : D.map e.toEquiv.toEmbedding = C := by
      ext p
      have hp : e (e.symm p) = p := e.apply_symm_apply p
      nth_rw 1 [← hp]
      rw [mem_axes]
      exact (mem_axes (e := e.symm) (B := C) (p := p))
    rw [← hback, anchors_axes, card_map] at hC
    have hD : IsPolyhex D :=
      polyhex_map e.symm.toEquiv.toEmbedding (adj_axes e.symm hInvAxes) C hCpoly
    rw [← hback, card_map, card_map]
    exact hmin D hD hC

/-- The left panel in the exact offset coordinates listed in issue #31892. -/
theorem left_issue_prismatic :
    (IsPolyhex (offsets leftIssuePattern) ∧ (offsets leftIssuePattern).card = 4 ∧
      IsPolyhex leftIssueBoard ∧ leftIssueBoard.card = 28 ∧ (anchors leftIssuePattern leftIssueBoard).card = 16 ∧
      (∀ w : Word, ((anchors leftIssuePattern leftIssueBoard).filter
        fun t => wordAt leftIssuePattern leftIssueColor t = w).card = 1)) ∧
    IsDense leftIssuePattern 16 leftIssueBoard := by
  change IsPrismatic leftIssuePattern leftIssueBoard leftIssueColor
  have hp : leftIssuePattern = fun i => leftAxes (leftPattern i) + 0 := by
    funext i
    fin_cases i <;> decide
  rw [hp]
  exact issue_prismatic leftAxes 0 leftPattern leftBoard leftColor (by decide)
    left_prismatic

/-- The right panel in the exact offset coordinates listed in issue #31893. -/
theorem right_issue_prismatic :
    (IsPolyhex (offsets rightIssuePattern) ∧ (offsets rightIssuePattern).card = 4 ∧
      IsPolyhex rightIssueBoard ∧ rightIssueBoard.card = 28 ∧ (anchors rightIssuePattern rightIssueBoard).card = 16 ∧
      (∀ w : Word, ((anchors rightIssuePattern rightIssueBoard).filter
        fun t => wordAt rightIssuePattern rightIssueColor t = w).card = 1)) ∧
    IsDense rightIssuePattern 16 rightIssueBoard := by
  change IsPrismatic rightIssuePattern rightIssueBoard rightIssueColor
  have hp : rightIssuePattern = fun i => rightAxes (rightPattern i) + (1, 1) := by
    funext i
    fin_cases i <;> decide
  rw [hp]
  exact issue_prismatic rightAxes (1,1) rightPattern rightBoard rightColor (by decide)
    right_prismatic

end D5.S3.Combinatorics.Polyomino.Figure26Prismaticity
