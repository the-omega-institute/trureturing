/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity; premises=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply,D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one
   digest: Actual labelled subsets, local windows and all-length runs share the open-grid transfer invariant. -/


import D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual subsets, finite windows and arbitrary-length runs for the ordinary open
three-row grid. The two absent-column terminal checks remain explicit. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer

open Finset

/-- Closed domination and inclusion minimality under every proper subset. -/
def MinimalDominating {V : Type} (G : SimpleGraph V) (S : Finset V) : Prop :=
  G.IsDominating (S : Set V) ∧
    ∀ T : Finset V, T ⊂ S → ¬ G.IsDominating (T : Set V)

/-- A closed neighbourhood includes its centre. -/
def Closed {V : Type} (G : SimpleGraph V) (u v : V) : Prop := u = v ∨ G.Adj u v

/-- A witness is existential information, never an extra counted choice. -/
def ClosedPrivate {V : Type} (G : SimpleGraph V) (S : Finset V) (v z : V) : Prop :=
  Closed G z v ∧ ∀ w ∈ S, Closed G z w → w = v

/-- The closed-private-witness form of minimal domination, transported from the
set characterization to finite subsets. The domination premise is retained. -/
theorem minimal_iff_closed_private {V : Type} [Finite V]
    (G : SimpleGraph V) (S : Finset V) :
    MinimalDominating G S ↔ G.IsDominating (S : Set V) ∧
      ∀ v ∈ S, ∃ z, ClosedPrivate G S v z := by
  classical
  have finite_set_bridge : MinimalDominating G S ↔
      TrapezohedralMinimalDomination.MinimalDominating G (S : Set V) := by
    rw [TrapezohedralMinimalDomination.minimalDominating_iff_proper]
    constructor
    · rintro ⟨hd, hm⟩
      refine ⟨hd, fun T hT hdom => ?_⟩
      have hTf : (Set.toFinite T).toFinset ⊂ S :=
        Set.Finite.toFinset_ssubset.mpr hT
      exact hm _ hTf (by simpa only [Set.Finite.coe_toFinset] using hdom)
    · rintro ⟨hd, hm⟩
      exact ⟨hd, fun T hT hdom => hm (T : Set V) (Finset.coe_ssubset.mpr hT) hdom⟩
  exact finite_set_bridge.trans (by
    simpa only [TrapezohedralMinimalDomination.ClosedPrivate, ClosedPrivate,
      Closed, Finset.mem_coe] using
      TrapezohedralMinimalDomination.minimalDominating_iff_private G (S : Set V))

/-- Row labels and column labels; translating both by one gives the source labels. -/
abbrev Vertex (n : ℕ) := Fin 3 × Fin n

/-- Ordinary open grid, with adjacency exactly at Manhattan distance one. -/
def grid (n : ℕ) : SimpleGraph (Vertex n) where
  Adj u v := Nat.dist u.1.val v.1.val + Nat.dist u.2.val v.2.val = 1
  symm := ⟨by intro u v h; simpa only [Nat.dist_comm] using h⟩
  loopless := ⟨by intro v; simp⟩

/-- A mask has one selection bit for each of the three labelled rows. -/
abbrev Mask := Fin 3 → Bool

/-- A word contains precisely one mask for every real column. -/
abbrev Word (n : ℕ) := Fin n → Mask

/-- Read the actual subset, without choosing witnesses or identifying symmetries. -/
def encode {n : ℕ} (S : Finset (Vertex n)) : Word n :=
  fun c r => decide ((r, c) ∈ S)

/-- Recover the selected labelled vertices from their column bits. -/
def decode {n : ℕ} (w : Word n) : Finset (Vertex n) :=
  univ.filter fun v => w v.2 v.1 = true

@[simp] theorem mem_decode {n : ℕ} (w : Word n) (v : Vertex n) :
    v ∈ decode w ↔ w v.2 v.1 = true := by simp [decode]

/-- The actual-subset/word bijection, with no quotient and no multiplicity. -/
def subsetWordEquiv (n : ℕ) : Finset (Vertex n) ≃ Word n where
  toFun := encode
  invFun := decode
  left_inv S := by ext v; simp [encode]
  right_inv w := by
    funext c r
    simp [encode]

/-- Absent columns have no vertices; a present mask may still select no rows. -/
abbrev Column := Option Mask

/-- Open padding: even a real empty mask is returned as `some`, never `none`. -/
def padded {n : ℕ} (w : Word n) (c : ℤ) : Column :=
  if h : 0 ≤ c ∧ c < n then some (w ⟨c.toNat, by omega⟩) else none

/-- The exact family of actual inclusion-minimal dominating subsets. -/
noncomputable def minimalSets (n : ℕ) : Finset (Finset (Vertex n)) := by
  classical
  exact univ.filter (MinimalDominating (grid n))

/-- This is the source count, including every actual subset exactly once. -/
noncomputable def actualCount (n : ℕ) : ℕ := (minimalSets n).card

/-- Word acceptance still refers to the independently defined actual graph. -/
def ValidWord {n : ℕ} (w : Word n) : Prop :=
  (grid n).IsDominating (decode w : Set (Vertex n)) ∧
    ∀ v ∈ decode w, ∃ z, ClosedPrivate (grid n) (decode w) v z

/-- Exact acceptance, including all real columns and both open ends. -/
theorem validWord_iff {n : ℕ} (w : Word n) :
    ValidWord w ↔ MinimalDominating (grid n) (decode w) :=
  (minimal_iff_closed_private (grid n) (decode w)).symm

/-- Restricting the bijection preserves exactly the original subset predicate. -/
noncomputable def minimalWordEquiv (n : ℕ) :
    {S : Finset (Vertex n) // MinimalDominating (grid n) S} ≃
      {w : Word n // ValidWord w} :=
  (subsetWordEquiv n).subtypeEquiv fun S => by
    change MinimalDominating (grid n) S ↔ ValidWord (encode S)
    have hd : decode (encode S) = S := (subsetWordEquiv n).left_inv S
    rw [validWord_iff, hd]

/-- Every closed neighbour is at column distance at most one. -/
private theorem closed_column_dist {n : ℕ} {u v : Vertex n}
    (h : Closed (grid n) u v) : Nat.dist u.2.val v.2.val ≤ 1 := by
  rcases h with rfl | h
  · simp
  · change Nat.dist u.1.val v.1.val + Nat.dist u.2.val v.2.val = 1 at h
    omega

/-- A neighbour of a possible private witness lies in the five-column window. -/
private theorem private_window_bound {n : ℕ} {v z u : Vertex n}
    (hz : Closed (grid n) z v) (hu : Closed (grid n) z u) :
    Nat.dist u.2.val v.2.val ≤ 2 := by
  have h₁ := closed_column_dist hz
  have h₂ := closed_column_dist hu
  have ht := Nat.dist.triangle_inequality u.2.val z.2.val v.2.val
  rw [Nat.dist_comm u.2.val z.2.val] at ht
  omega

/-- The column test only inspects selected vertices within two columns of its
centre. Candidate witnesses are actual vertices, so absent columns supply none. -/
def ColumnTest {n : ℕ} (S : Finset (Vertex n)) (c : Fin n) : Prop :=
  (∀ r : Fin 3, ∃ v ∈ S, Closed (grid n) (r, c) v) ∧
    ∀ r : Fin 3, (r, c) ∈ S → ∃ z : Vertex n,
      Closed (grid n) z (r, c) ∧
        ∀ v ∈ S, Nat.dist v.2.val c.val ≤ 2 → Closed (grid n) z v → v = (r, c)

/-- The entire original proper-subset condition is equivalent to the five-column
closed-private-witness test at every real column, for every width. -/
theorem minimal_iff_column_tests {n : ℕ} (S : Finset (Vertex n)) :
    MinimalDominating (grid n) S ↔ ∀ c, ColumnTest S c := by
  rw [minimal_iff_closed_private]
  constructor
  · rintro ⟨hd, hp⟩ c
    constructor
    · intro r
      rcases hd (r, c) with h | ⟨v, hv, hadj⟩
      · exact ⟨(r, c), h, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr hadj⟩
    · intro r hr
      obtain ⟨z, hz, huniq⟩ := hp (r, c) hr
      exact ⟨z, hz, fun v hv _ h => huniq v hv h⟩
  · intro h
    constructor
    · rintro ⟨r, c⟩
      obtain ⟨u, hu, hclosed⟩ := (h c).1 r
      rcases hclosed with heq | hadj
      · exact Or.inl (heq.symm ▸ hu)
      · exact Or.inr ⟨u, hu, hadj⟩
    · intro v hv
      obtain ⟨z, hz, huniq⟩ := (h v.2).2 v.1 hv
      exact ⟨z, hz, fun u hu hzu => huniq u hu (private_window_bound hz hzu) hzu⟩

/-- Real masks are 0 through 7; the absent symbol is 8. -/
abbrev Symbol := Fin 9
abbrev State := Fin 4672
abbrev Window := Fin 5 → Symbol

/-- The three state blocks are (8,8,a,b), (8,a,b,c), and (a,b,c,d),
in that order, with real masks in lexicographic order. -/
def columns (s : State) : Fin 4 → Symbol :=
  if h₀ : s.val < 64 then
    ![8, 8, ⟨s.val / 8, by omega⟩, ⟨s.val % 8, by omega⟩]
  else if h₁ : s.val < 576 then
    ![8, ⟨(s.val - 64) / 64, by omega⟩,
      ⟨(s.val - 64) / 8 % 8, by omega⟩, ⟨(s.val - 64) % 8, by omega⟩]
  else
    ![⟨(s.val - 576) / 512, by omega⟩, ⟨(s.val - 576) / 64 % 8, by omega⟩,
      ⟨(s.val - 576) / 8 % 8, by omega⟩, ⟨(s.val - 576) % 8, by omega⟩]

/-- Appending a real mask drops the first symbol and advances its block. -/
def append (s : State) (m : Fin 8) : State :=
  if h₀ : s.val < 64 then
    ⟨64 + (s.val / 8) * 64 + (s.val % 8) * 8 + m.val, by omega⟩
  else if h₁ : s.val < 576 then
    ⟨576 + ((s.val - 64) / 64) * 512 + ((s.val - 64) / 8 % 8) * 64 +
      ((s.val - 64) % 8) * 8 + m.val, by omega⟩
  else
    ⟨576 + ((s.val - 576) / 64 % 8) * 512 + ((s.val - 576) / 8 % 8) * 64 +
      ((s.val - 576) % 8) * 8 + m.val, by omega⟩

/-- The state encoding performs the literal left shift of its four columns. -/
theorem columns_append (s : State) (m : Fin 8) (i : Fin 4) :
    columns (append s m) i =
      if h : i.val < 3 then columns s ⟨i.val + 1, by omega⟩
      else ⟨m.val, by omega⟩ := by
  apply Fin.ext
  by_cases h₀ : s.val < 64
  · have ha : (append s m).val < 576 := by simp [append, h₀]; omega
    have hb : ¬ (append s m).val < 64 := by simp [append, h₀]; omega
    fin_cases i <;> simp [columns, h₀, ha, hb] <;> simp [append, h₀] <;> omega
  · by_cases h₁ : s.val < 576
    · have ha : ¬ (append s m).val < 576 := by simp [append, h₀, h₁]; omega
      have hb : ¬ (append s m).val < 64 := by omega
      fin_cases i <;> simp [columns, h₀, h₁, ha, hb] <;> simp [append, h₀, h₁] <;> omega
    · have ha : ¬ (append s m).val < 576 := by simp [append, h₀, h₁]; omega
      have hb : ¬ (append s m).val < 64 := by omega
      fin_cases i <;> simp [columns, h₀, h₁, ha, hb] <;> simp [append, h₀, h₁] <;> omega

/-- The pinned positional-base equivalence gives the exact little-endian mask encoding. -/
def maskEquiv : Fin 8 ≃ Mask :=
  (finFunctionFinEquiv (m := 2) (n := 3)).symm.trans
    (Equiv.piCongrRight fun _ => finTwoEquiv)

/-- The executable row bit is exactly the corresponding Boolean mask entry. -/
@[simp] theorem maskEquiv_apply (m : Fin 8) (r : Fin 3) :
    maskEquiv m r = m.val.testBit r.val := by
  have h : ∀ m : Fin 8, ∀ r : Fin 3, maskEquiv m r = m.val.testBit r.val := by decide
  exact h m r

/-- Convert a real column mask or an absent column to its distinct symbol. -/
def symbol : Column → Symbol
  | none => 8
  | some m => ⟨(maskEquiv.symm m).val, by omega⟩

/-- The five consecutive signed coordinates centred on an actual grid column. -/
def paddedWindow {n : ℕ} (w : Word n) (c : Fin n) : Window :=
  fun i => symbol (padded w ((c.val : ℤ) + i.val - 2))

/-- An absent column has no vertices, even when it would have a zero selection bit. -/
def present (w : Window) (v : Vertex 5) : Bool := decide ((w v.2).val < 8)

/-- Real mask zero has three existing, unselected vertices. -/
def selected (w : Window) (v : Vertex 5) : Bool :=
  present w v && (w v.2).val.testBit v.1.val

private def closed (u v : Vertex 5) : Bool :=
  decide (Nat.dist u.1.val v.1.val + Nat.dist u.2.val v.2.val ≤ 1)

/-- Domination and existential closed private witnesses at the real middle
column. Absent columns supply neither selected vertices nor possible witnesses. -/
def Local (w : Window) : Prop :=
  (∀ r : Fin 3, ∃ z : Vertex 5,
    present w z = true ∧ selected w z = true ∧ closed (r, 2) z = true) ∧
  (∀ r : Fin 3, selected w (r, 2) = true → ∃ z : Vertex 5,
    present w z = true ∧ closed z (r, 2) = true ∧
      ∀ u : Vertex 5, selected w u = true → closed z u = true → u = (r, 2))

instance localDecidable (w : Window) : Decidable (Local w) := by
  unfold Local
  infer_instance

private def At {n : ℕ} (c : Fin n) (i : Fin 5) (d : Fin n) : Prop :=
  (d.val : ℤ) = (c.val : ℤ) + i.val - 2

private theorem at_center {n : ℕ} (c : Fin n) : At c 2 c := by
  simp [At]

private theorem at_unique {n : ℕ} {c d e : Fin n} {i : Fin 5}
    (hd : At c i d) (he : At c i e) : d = e := by
  apply Fin.ext
  unfold At at *
  omega

private theorem at_near {n : ℕ} {c d : Fin n} {i : Fin 5} (h : At c i d) :
    Nat.dist d.val c.val ≤ 2 := by
  unfold At at h
  unfold Nat.dist
  have := i.isLt
  omega

private theorem exists_at {n : ℕ} (c d : Fin n) (h : Nat.dist d.val c.val ≤ 2) :
    ∃ i : Fin 5, At c i d := by
  unfold Nat.dist at h
  refine ⟨⟨d.val + 2 - c.val, by omega⟩, ?_⟩
  unfold At
  dsimp
  omega

private theorem at_dist {n : ℕ} {c d e : Fin n} {i j : Fin 5}
    (hd : At c i d) (he : At c j e) : Nat.dist i.val j.val = Nat.dist d.val e.val := by
  unfold At at hd he
  unfold Nat.dist
  omega

private theorem closed_distance {n : ℕ} (u v : Vertex n) :
    Closed (grid n) u v ↔ Nat.dist u.1.val v.1.val + Nat.dist u.2.val v.2.val ≤ 1 := by
  simp only [Closed, grid]
  constructor
  · rintro (rfl | h)
    · simp
    · omega
  · intro h
    by_cases he : u = v
    · exact Or.inl he
    · right
      have hp : u.1.val ≠ v.1.val ∨ u.2.val ≠ v.2.val := by
        simpa only [Prod.ext_iff, Fin.ext_iff, not_and_or] using he
      unfold Nat.dist at *
      omega

private theorem closed_at {n : ℕ} {c d e : Fin n} {i j : Fin 5}
    (r s : Fin 3) (hd : At c i d) (he : At c j e) :
    closed (r, i) (s, j) = true ↔ Closed (grid n) (r, d) (s, e) := by
  simp only [closed, decide_eq_true_eq, closed_distance]
  rw [at_dist hd he]

private theorem present_paddedWindow {n : ℕ} (w : Word n) (c : Fin n)
    (r : Fin 3) (i : Fin 5) :
    present (paddedWindow w c) (r, i) = true ↔ ∃ d : Fin n, At c i d := by
  unfold present paddedWindow padded
  dsimp
  split_ifs with h
  · change (decide ((maskEquiv.symm (w ⟨((c.val : ℤ) + i.val - 2).toNat, by omega⟩)).val < 8) = true) ↔ _
    rw [decide_eq_true_eq]
    constructor
    · intro _
      exact ⟨⟨((c.val : ℤ) + i.val - 2).toNat, by omega⟩, by unfold At; dsimp; omega⟩
    · intro _
      exact (maskEquiv.symm (w ⟨((c.val : ℤ) + i.val - 2).toNat, by omega⟩)).isLt
  · rw [decide_eq_true_eq]
    change (8 : ℕ) < 8 ↔ _
    simp only [Nat.lt_irrefl, false_iff]
    rintro ⟨d, hd⟩
    unfold At at hd
    have := d.isLt
    omega

private theorem selected_paddedWindow {n : ℕ} (w : Word n) (c : Fin n)
    (r : Fin 3) (i : Fin 5) :
    selected (paddedWindow w c) (r, i) = true ↔
      ∃ d : Fin n, At c i d ∧ w d r = true := by
  unfold selected
  rw [Bool.and_eq_true, present_paddedWindow]
  constructor
  · rintro ⟨⟨d, hd⟩, hb⟩
    refine ⟨d, hd, ?_⟩
    have h : 0 ≤ (c.val : ℤ) + i.val - 2 ∧ (c.val : ℤ) + i.val - 2 < n := by
      unfold At at hd
      have := d.isLt
      omega
    have he : (⟨((c.val : ℤ) + i.val - 2).toNat, by omega⟩ : Fin n) = d := by
      apply Fin.ext
      unfold At at hd
      dsimp
      omega
    have hw : paddedWindow w c i = symbol (some (w d)) := by
      unfold paddedWindow padded
      rw [dite_eq_left h]
      rw [he]
    rw [hw] at hb
    simpa only [symbol, ← maskEquiv_apply, Equiv.apply_symm_apply] using hb
  · rintro ⟨d, hd, hb⟩
    refine ⟨⟨d, hd⟩, ?_⟩
    have h : 0 ≤ (c.val : ℤ) + i.val - 2 ∧ (c.val : ℤ) + i.val - 2 < n := by
      unfold At at hd
      have := d.isLt
      omega
    have he : (⟨((c.val : ℤ) + i.val - 2).toNat, by omega⟩ : Fin n) = d := by
      apply Fin.ext
      unfold At at hd
      dsimp
      omega
    have hw : paddedWindow w c i = symbol (some (w d)) := by
      unfold paddedWindow padded
      rw [dite_eq_left h]
      rw [he]
    rw [hw]
    simpa only [symbol, ← maskEquiv_apply, Equiv.apply_symm_apply] using hb

/-- The finite executable window checks exactly the actual-grid column test,
including every open boundary and every present but empty column. -/
theorem local_paddedWindow_iff {n : ℕ} (w : Word n) (c : Fin n) :
    Local (paddedWindow w c) ↔ ColumnTest (decode w) c := by
  constructor
  · rintro ⟨hd, hp⟩
    constructor
    · intro r
      obtain ⟨⟨s, j⟩, _, hs, ha⟩ := hd r
      obtain ⟨d, hd, hb⟩ := (selected_paddedWindow w c s j).mp hs
      exact ⟨(s, d), (mem_decode w (s, d)).mpr hb,
        (closed_at r s (at_center c) hd).mp ha⟩
    · intro r hr
      have hs : selected (paddedWindow w c) (r, 2) = true :=
        (selected_paddedWindow w c r 2).mpr ⟨c, at_center c, (mem_decode w (r, c)).mp hr⟩
      obtain ⟨⟨s, j⟩, hj, ha, hu⟩ := hp r hs
      obtain ⟨d, hd⟩ := (present_paddedWindow w c s j).mp hj
      refine ⟨(s, d), (closed_at s r hd (at_center c)).mp ha, ?_⟩
      rintro ⟨t, e⟩ he hnear hclosed
      obtain ⟨k, hk⟩ := exists_at c e hnear
      have hsel := (selected_paddedWindow w c t k).mpr
        ⟨e, hk, (mem_decode w (t, e)).mp he⟩
      have heq := hu (t, k) hsel ((closed_at s t hd hk).mpr hclosed)
      have hr : t = r := congrArg Prod.fst heq
      have hki : k = (2 : Fin 5) := congrArg Prod.snd heq
      have hec : e = c := at_unique (hki ▸ hk) (at_center c)
      exact Prod.ext hr hec
  · rintro ⟨hd, hp⟩
    constructor
    · intro r
      obtain ⟨⟨s, d⟩, hs, ha⟩ := hd r
      have hnear : Nat.dist d.val c.val ≤ 2 := by
        have hdist := (closed_distance (r, c) (s, d)).mp ha
        rw [Nat.dist_comm c.val d.val] at hdist
        omega
      obtain ⟨j, hj⟩ := exists_at c d hnear
      exact ⟨(s, j), (present_paddedWindow w c s j).mpr ⟨d, hj⟩,
        (selected_paddedWindow w c s j).mpr ⟨d, hj, (mem_decode w (s, d)).mp hs⟩,
        (closed_at r s (at_center c) hj).mpr ha⟩
    · intro r hr
      obtain ⟨e, he, hb⟩ := (selected_paddedWindow w c r 2).mp hr
      have hec : e = c := at_unique he (at_center c)
      subst e
      obtain ⟨⟨s, d⟩, ha, hu⟩ := hp r ((mem_decode w (r, c)).mpr hb)
      have hnear : Nat.dist d.val c.val ≤ 2 := by
        have hdist := (closed_distance (s, d) (r, c)).mp ha
        change Nat.dist s.val r.val + Nat.dist d.val c.val ≤ 1 at hdist
        omega
      obtain ⟨j, hj⟩ := exists_at c d hnear
      refine ⟨(s, j), (present_paddedWindow w c s j).mpr ⟨d, hj⟩,
        (closed_at s r hj (at_center c)).mpr ha, ?_⟩
      rintro ⟨t, k⟩ hsel hclosed
      obtain ⟨e, he, hb⟩ := (selected_paddedWindow w c t k).mp hsel
      have heq := hu (t, e) ((mem_decode w (t, e)).mpr hb) (at_near he)
        ((closed_at s t hj he).mp hclosed)
      have htr : t = r := congrArg Prod.fst heq
      have hec : e = c := congrArg Prod.snd heq
      have hk : k = (2 : Fin 5) := by
        apply Fin.ext
        unfold At at he
        subst e
        omega
      exact Prod.ext htr hk

/-- Every actual minimal dominating subset corresponds to exactly the accepted
padded window condition at all its real column centres. -/
theorem validWord_iff_local {n : ℕ} (w : Word n) :
    ValidWord w ↔ ∀ c, Local (paddedWindow w c) := by
  rw [validWord_iff, minimal_iff_column_tests]
  exact forall_congr' fun c => (local_paddedWindow_iff w c).symm

/-- Numeric words are accepted by the actual padded local test at every real centre. -/
def acceptedWords (n : ℕ) : Finset (Fin n → Fin 8) :=
  Finset.univ.filter fun w => ∀ c, Local (paddedWindow (fun d => maskEquiv (w d)) c)

/-- Exact transport from the independently defined actual subset family to the
executable numeric-word family; neither witnesses nor symmetries are counted. -/
theorem actualCount_eq_acceptedWords (n : ℕ) :
    actualCount n = (acceptedWords n).card := by
  classical
  let e : (Fin n → Fin 8) ≃ Word n := Equiv.piCongrRight fun _ => maskEquiv
  let ee : {w : Fin n → Fin 8 // ∀ c, Local (paddedWindow (fun d => maskEquiv (w d)) c)} ≃
      {w : Word n // ValidWord w} := e.subtypeEquiv fun w =>
        (validWord_iff_local (e w)).symm
  calc
    actualCount n = Fintype.card {S : Finset (Vertex n) // MinimalDominating (grid n) S} := by
      simp only [actualCount, minimalSets, Fintype.card_subtype]
    _ = Fintype.card {w : Word n // ValidWord w} := Fintype.card_congr (minimalWordEquiv n)
    _ = Fintype.card {w : Fin n → Fin 8 //
        ∀ c, Local (paddedWindow (fun d => maskEquiv (w d)) c)} := Fintype.card_congr ee.symm
    _ = (acceptedWords n).card := by rw [Fintype.card_subtype]; rfl

/-- The width-one graph has the middle singleton and the pair of ends as its
only inclusion-minimal dominating subsets. -/
theorem actualCount_one : actualCount 1 = 2 := by
  rw [actualCount_eq_acceptedWords]
  decide

/-- A Boolean accepts existence, without selecting or counting witnesses. -/
def accepts (w : Window) : Bool := decide (Local w)

/-- The window checked when a fifth symbol is appended. -/
def window (s : State) (a : Symbol) : Window := Fin.snoc (columns s) a

/-- Two absent-column checks finish the last two real columns. -/
def terminal : State → ℤ := fun s =>
  if accepts (window s 8) && accepts ![columns s 1, columns s 2, columns s 3, 8, 8]
    then 1 else 0


open scoped BigOperators

/-- Backward transfer sums one contribution per accepted appended mask. -/
def fullStep : (State → ℤ) →ₗ[ℤ] (State → ℤ) where
  toFun v s := ∑ m : Fin 8,
    if accepts (window s ⟨m.val, by omega⟩) then v (append s m) else 0
  map_add' u v := by
    funext s
    change (∑ m : Fin 8, if accepts (window s ⟨m.val, by omega⟩)
      then (u (append s m) + v (append s m)) else 0) = _
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    split <;> simp_all
  map_smul' a v := by
    funext s
    change (∑ m : Fin 8, if accepts (window s ⟨m.val, by omega⟩)
      then a * v (append s m) else 0) = _
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    split <;> simp_all

/-- The backward transfer orbit counts accepted continuations before any
identification with actual subsets is made. -/
def fullOrbit : ℕ → State → ℤ
  | 0 => terminal
  | k + 1 => fullStep (fullOrbit k)

open scoped BigOperators

/-- An accepted appended-mask word has weight one; witnesses add no choices. -/
def runWeight : (k : ℕ) → State → (Fin k → Fin 8) → ℤ
  | 0, s, _ => terminal s
  | k + 1, s, w => (if accepts (window s ⟨(w 0).val, by omega⟩) then 1 else 0) *
      runWeight k (append s (w 0)) (fun i => w i.succ)

private theorem runWeight_zero_one (k : ℕ) (s : State) (w : Fin k → Fin 8) :
    runWeight k s w = 0 ∨ runWeight k s w = 1 := by
  induction k generalizing s with
  | zero => unfold runWeight terminal; split <;> simp_all
  | succ k ih =>
    simp only [runWeight]
    split
    · simpa using ih (append s (w 0)) (fun i => w i.succ)
    · simp

/-- The exact sum over appended masks, proved by the first-mask decomposition. -/
theorem sum_runWeight (k : ℕ) (s : State) :
    (∑ w : Fin k → Fin 8, runWeight k s w) = fullOrbit k s := by
  induction k generalizing s with
  | zero => simp [runWeight, fullOrbit]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 8)).sum_comp
      (fun w => runWeight (k + 1) s w), Fintype.sum_prod_type]
    change (∑ a : Fin 8, ∑ w : Fin k → Fin 8,
      runWeight (k + 1) s (Fin.cons a w)) = _
    change (∑ a : Fin 8, ∑ w : Fin k → Fin 8,
      (if accepts (window s ⟨a.val, by omega⟩) then (1 : ℤ) else 0) *
        runWeight k (append s a) w) = _
    simp_rw [← Finset.mul_sum]
    simp_rw [ih]
    change _ = ∑ m : Fin 8, if accepts (window s ⟨m.val, by omega⟩)
      then fullOrbit k (append s m) else 0
    apply Finset.sum_congr rfl
    intro m _
    split <;> simp_all

/-- Four history symbols, followed by the real suffix and then open-end absence.
The history coordinates are -2,-1,0,1. -/
def expanded {k : ℕ} (s : State) (w : Fin k → Fin 8) (j : ℤ) : Symbol :=
  if h : -2 ≤ j ∧ j < 2 then columns s ⟨(j + 2).toNat, by omega⟩
  else if h : 2 ≤ j ∧ j < k + 2 then ⟨(w ⟨(j - 2).toNat, by omega⟩).val, by omega⟩
  else 8

/-- The window with nonnegative centre c in the history-and-suffix stream. -/
def expandedWindow {k : ℕ} (s : State) (w : Fin k → Fin 8) (c : ℕ) : Window :=
  fun i => expanded s w ((c : ℤ) + i.val - 2)

private theorem expanded_shift {k : ℕ} (s : State) (w : Fin (k + 1) → Fin 8)
    (j : ℤ) (hj : -2 ≤ j) :
    expanded (append s (w 0)) (fun i => w i.succ) j = expanded s w (j + 1) := by
  by_cases hlow : j < 1
  · have hleft : -2 ≤ j ∧ j < 2 := by omega
    have hright : -2 ≤ j + 1 ∧ j + 1 < 2 := by omega
    rw [expanded, dite_eq_left hleft, expanded, dite_eq_left hright, columns_append]
    have hi : (j + 2).toNat < 3 := by omega
    rw [dite_eq_left hi]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · by_cases hone : j = 1
    · subst j
      simp [expanded, columns_append]
    · have htwo : 2 ≤ j := by omega
      by_cases htop : j < k + 2
      · have hl : ¬ (-2 ≤ j ∧ j < 2) := by omega
        have hr : ¬ (-2 ≤ j + 1 ∧ j + 1 < 2) := by omega
        have hfuture : 2 ≤ j ∧ j < k + 2 := ⟨htwo, htop⟩
        have hfuture' : 2 ≤ j + 1 ∧ j + 1 < ↑(k + 1) + 2 := by omega
        rw [expanded, dite_eq_right hl, dite_eq_left hfuture,
          expanded, dite_eq_right hr, dite_eq_left hfuture']
        have hi : (⟨(j - 2).toNat, by omega⟩ : Fin k).succ =
            (⟨(j + 1 - 2).toNat, by omega⟩ : Fin (k + 1)) := by
          apply Fin.ext
          dsimp
          omega
        apply Fin.ext
        exact congrArg (fun x : Fin (k + 1) => (w x).val) hi
      · have hl : ¬ (-2 ≤ j ∧ j < 2) := by omega
        have hr : ¬ (-2 ≤ j + 1 ∧ j + 1 < 2) := by omega
        have hfuture : ¬ (2 ≤ j ∧ j < k + 2) := by omega
        have hfuture' : ¬ (2 ≤ j + 1 ∧ j + 1 < ↑(k + 1) + 2) := by omega
        simp only [expanded, dite_eq_right hl, dite_eq_right hr,
          dite_eq_right hfuture, dite_eq_right hfuture']

private theorem expandedWindow_shift {k : ℕ} (s : State) (w : Fin (k + 1) → Fin 8)
    (c : ℕ) :
    expandedWindow (append s (w 0)) (fun i => w i.succ) c = expandedWindow s w (c + 1) := by
  funext i
  rw [expandedWindow, expanded_shift s w _ (by omega), expandedWindow]
  congr 1
  omega

private theorem expandedWindow_first {k : ℕ} (s : State) (w : Fin (k + 1) → Fin 8) :
    expandedWindow s w 0 = window s ⟨(w 0).val, by omega⟩ := by
  funext i
  fin_cases i <;> simp [expandedWindow, expanded, window, Fin.snoc] <;> congr 1

private theorem expandedWindow_zero (s : State) (w : Fin 0 → Fin 8) :
    expandedWindow s w 0 = window s 8 ∧
      expandedWindow s w 1 = ![columns s 1, columns s 2, columns s 3, 8, 8] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [expandedWindow, expanded, window, Fin.snoc] <;> congr 1

/-- The recursive run checks exactly every remaining real centre, including both
terminal checks; the statement also covers a zero-length appended suffix. -/
theorem runWeight_iff_tests (k : ℕ) (s : State) (w : Fin k → Fin 8) :
    runWeight k s w = 1 ↔ ∀ c : Fin (k + 2), Local (expandedWindow s w c.val) := by
  induction k generalizing s with
  | zero =>
    have hz := expandedWindow_zero s w
    simp only [runWeight, terminal]
    rw [Fin.forall_fin_succ, Fin.forall_fin_succ]
    simp only [Fin.val_zero, Fin.val_succ, Fin.forall_fin_zero, and_true]
    rw [hz.1, hz.2]
    simp [accepts, Bool.and_eq_true]
  | succ k ih =>
    have hrun : runWeight (k + 1) s w = 1 ↔
        accepts (window s ⟨(w 0).val, by omega⟩) = true ∧
          runWeight k (append s (w 0)) (fun i => w i.succ) = 1 := by
      simp only [runWeight]
      split <;> simp_all
    rw [hrun, ih]
    conv_rhs => rw [Fin.forall_fin_succ]
    simp only [Fin.val_zero, Fin.val_succ, expandedWindow_shift, ← expandedWindow_first]
    simp only [accepts, decide_eq_true_eq]

/-- The state containing the two initial labelled masks. -/
def start (a b : Fin 8) : State := ⟨8 * a.val + b.val, by omega⟩

private theorem columns_start (a b : Fin 8) :
    columns (start a b) = ![8, 8, ⟨a.val, by omega⟩, ⟨b.val, by omega⟩] := by
  funext i
  have h : (start a b).val < 64 := by simp [start]; omega
  apply Fin.ext
  simp only [columns, dite_eq_left h]
  fin_cases i <;> simp [start] <;> omega

private theorem expanded_start {k : ℕ} (a b : Fin 8) (w : Fin k → Fin 8)
    (c : Fin (k + 2)) :
    expandedWindow (start a b) w c.val =
      paddedWindow (fun (d : Fin (k + 2)) => maskEquiv ((Fin.cons a (Fin.cons b w) : Fin (k + 2) → Fin 8) d)) c := by
  funext i
  change expanded (start a b) w ((c.val : ℤ) + i.val - 2) =
    symbol (padded _ ((c.val : ℤ) + i.val - 2))
  generalize hjdef : ((c.val : ℤ) + i.val - 2) = j
  have hj : -2 ≤ j := by omega
  by_cases hneg : j < 0
  · have hl : -2 ≤ j ∧ j < 2 := by omega
    have hr : ¬ (0 ≤ j ∧ j < ↑(k + 2)) := by omega
    rw [expanded, dite_eq_left hl, columns_start, padded, dite_eq_right hr, symbol]
    have hc : j = -2 ∨ j = -1 := by omega
    rcases hc with rfl | rfl <;> simp
  · have hj0 : 0 ≤ j := by omega
    by_cases hsmall : j < 2
    · have hl : -2 ≤ j ∧ j < 2 := by omega
      have hr : 0 ≤ j ∧ j < ↑(k + 2) := by omega
      rw [expanded, dite_eq_left hl, columns_start, padded, dite_eq_left hr, symbol]
      have hc : j = 0 ∨ j = 1 := by omega
      rcases hc with rfl | rfl <;> simp [Fin.cons]
      have he : (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ := by
        apply Fin.ext
        simp
      rw [he]
      rfl
    · have hl : ¬ (-2 ≤ j ∧ j < 2) := by omega
      by_cases htop : j < ↑(k + 2)
      · have hfuture : 2 ≤ j ∧ j < ↑k + 2 := by omega
        have hr : 0 ≤ j ∧ j < ↑(k + 2) := ⟨hj0, htop⟩
        rw [expanded, dite_eq_right hl, dite_eq_left hfuture,
          padded, dite_eq_left hr, symbol]
        simp only [Equiv.symm_apply_apply]
        congr 1
        have he : (⟨j.toNat, by omega⟩ : Fin (k + 2)) =
            (⟨(j - 2).toNat, by omega⟩ : Fin k).succ.succ := by
          apply Fin.ext
          dsimp
          omega
        rw [he]
        rfl
      · have hfuture : ¬ (2 ≤ j ∧ j < ↑k + 2) := by omega
        have hr : ¬ (0 ≤ j ∧ j < ↑(k + 2)) := by omega
        simp only [expanded, dite_eq_right hl, dite_eq_right hfuture,
          padded, dite_eq_right hr, symbol]

/-- A numeric word is accepted precisely by its unique start and suffix run. -/
theorem accepted_cons_iff {k : ℕ} (a b : Fin 8) (w : Fin k → Fin 8) :
    (Fin.cons a (Fin.cons b w)) ∈ acceptedWords (k + 2) ↔ runWeight k (start a b) w = 1 := by
  simp only [acceptedWords, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [runWeight_iff_tests]
  exact forall_congr' fun c => by rw [expanded_start]

/-- Exact all-length actual-subset counting by the full transfer orbit. -/
theorem actualCount_fullOrbit (k : ℕ) :
    (actualCount (k + 2) : ℤ) = ∑ s : Fin 64, fullOrbit k ⟨s.val, by omega⟩ := by
  rw [actualCount_eq_acceptedWords]
  have hc : ((acceptedWords (k + 2)).card : ℤ) =
      ∑ w : Fin (k + 2) → Fin 8, if w ∈ acceptedWords (k + 2) then 1 else 0 := by
    simp
  rw [hc]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin 8)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin 8, ∑ w : Fin (k + 1) → Fin 8,
    if Fin.cons a w ∈ acceptedWords (k + 2) then (1 : ℤ) else 0) = _
  have hinner (a : Fin 8) :
      (∑ w : Fin (k + 1) → Fin 8,
        if Fin.cons a w ∈ acceptedWords (k + 2) then (1 : ℤ) else 0) =
      ∑ b : Fin 8, fullOrbit k (start a b) := by
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 8)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ b : Fin 8, ∑ w : Fin k → Fin 8,
      if Fin.cons a (Fin.cons b w) ∈ acceptedWords (k + 2) then (1 : ℤ) else 0) = _
    apply Finset.sum_congr rfl
    intro b _
    simp_rw [accepted_cons_iff]
    have hh (w : Fin k → Fin 8) :
        (if runWeight k (start a b) w = 1 then (1 : ℤ) else 0) = runWeight k (start a b) w := by
      rcases runWeight_zero_one k (start a b) w with h | h <;> simp [h]
    simp_rw [hh]
    exact sum_runWeight k (start a b)
  simp_rw [hinner]
  rw [← Fintype.sum_prod_type (fun p : Fin 8 × Fin 8 => fullOrbit k (start p.1 p.2))]
  rw [← (finProdFinEquiv (m := 8) (n := 8)).sum_comp
    (fun s : Fin 64 => fullOrbit k ⟨s.val, by omega⟩)]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Fin.ext
  simp [start, finProdFinEquiv]
  omega

end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer
