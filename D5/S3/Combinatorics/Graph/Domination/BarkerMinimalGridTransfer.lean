/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity; premises=D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply,D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one
   digest: The full open-grid frontier model distinguishes absent columns and real empty masks. -/

import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridEncoding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Pi

/-! The unpruned 4672-state model uses all 64 two-column starts and two absent
terminal checks. No actual-count equality or quotient compatibility is assumed. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer

open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridEncoding

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

end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer
