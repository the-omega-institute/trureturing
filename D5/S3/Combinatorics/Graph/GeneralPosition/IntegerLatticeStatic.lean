/- GID: D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic
   generality: G
   mirror - B: D5/B/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeStatic
   mirror - E: none
   anchors: ["mathlib/module/Mathlib.Data.Fintype.Powerset"]
   utility: none
   digest: Sharp coordinate general position bounds in positive - dimensional integer lattices. -/

module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-! Coordinate extremum and sharp recursive constructions. -/

@[expose] public section

namespace IntegerLatticeStatic

/-- Coordinate betweenness includes equality in each coordinate. -/
def Between {k : ℕ} (x y z : Fin k → ℤ) : Prop :=
  ∀ j, (x j ≤ y j ∧ y j ≤ z j) ∨ (z j ≤ y j ∧ y j ≤ x j)

/-- No three distinct selected points are coordinatewise between one another. -/
def CoordinateGP {k : ℕ} (S : Finset (Fin k → ℤ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z → ¬ Between x y z

private def Oriented {n : ℕ} (e : Fin n → Bool) (x y : Fin (n + 1) → ℤ) : Prop :=
  x 0 ≤ y 0 ∧ ∀ j, if e j then x j.succ ≤ y j.succ else y j.succ ≤ x j.succ

private theorem oriented_antisymm {n : ℕ} {e : Fin n → Bool}
    {x y : Fin (n + 1) → ℤ} (h : Oriented e x y) (h' : Oriented e y x) : x = y := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact le_antisymm h.1 h'.1
  · have a := h.2 i
    have b := h'.2 i
    cases he : e i <;> simp [he] at a b ⊢ <;> omega

private theorem oriented_between {n : ℕ} {e : Fin n → Bool}
    {x y z : Fin (n + 1) → ℤ} (h : Oriented e x y) (h' : Oriented e y z) :
    Between x y z := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact Or.inl ⟨h.1, h'.1⟩
  · have a := h.2 i
    have b := h'.2 i
    cases he : e i <;> simp [he] at a b <;> tauto

private theorem oriented_exists {n : ℕ} {x y : Fin (n + 1) → ℤ} (h : x 0 ≤ y 0) :
    ∃ e : Fin n → Bool, Oriented e x y := by
  classical
  refine ⟨fun j => decide (x j.succ ≤ y j.succ), h, fun j => ?_⟩
  by_cases hj : x j.succ ≤ y j.succ
  · simp [hj]
  · simp [hj, le_of_not_ge hj]

/-- A point is labelled by the orientations in which it has a distinct predecessor. -/
private noncomputable def predecessorCode {n : ℕ} (S : Finset (Fin (n + 1) → ℤ))
    (x : Fin (n + 1) → ℤ) : Set (Fin n → Bool) :=
  {e | ∃ y ∈ S, y ≠ x ∧ Oriented e y x}

/-- The predecessor labels distinguish all selected points, including coordinate ties. -/
private theorem predecessorCode_injective {n : ℕ} {S : Finset (Fin (n + 1) → ℤ)}
    (hg : CoordinateGP S) : Function.Injective (fun x : S => predecessorCode S x.val) := by
  intro x y hcode
  apply Subtype.ext
  by_contra hne
  have separate : ∀ (a b : S), a.val ≠ b.val → a.val 0 ≤ b.val 0 →
      predecessorCode S a.val ≠ predecessorCode S b.val := by
    intro a b hab hle heq
    obtain ⟨e, he⟩ := oriented_exists hle
    have hb : e ∈ predecessorCode S b.val := ⟨a.val, a.property, hab, he⟩
    rw [← heq] at hb
    obtain ⟨c, hc, hca, hce⟩ := hb
    have hcb : c ≠ b.val := by
      intro hcb
      subst c
      exact hab (oriented_antisymm he hce)
    exact hg c hc a.val a.property b.val b.property hca hab hcb
      (oriented_between hce he)
  rcases le_total (x.val 0) (y.val 0) with h | h
  · exact separate x y hne h hcode
  · exact separate y x (Ne.symm hne) h hcode.symm

/-- The sharp static upper bound in dimension n + 1. -/
theorem card_le {n : ℕ} {S : Finset (Fin (n + 1) → ℤ)} (hg : CoordinateGP S) :
    S.card ≤ 2 ^ (2 ^ n) := by
  classical
  have h := Fintype.card_le_of_injective _ (predecessorCode_injective hg)
  simpa using h

private theorem digit_lt {N a b c d : ℤ} (hN : 0 ≤ N)
    (hb : b < N) (hd : 0 ≤ d) (hac : a < c) : N * a + b < N * c + d := by
  have h := mul_le_mul_of_nonneg_left (show a + 1 ≤ c by omega) hN
  nlinarith

private theorem digit_le {N a b c d : ℤ} (hN : 0 ≤ N)
    (hb : 0 ≤ b) (hd : d < N) (h : N * a + b ≤ N * c + d) : a ≤ c := by
  by_contra! hac
  exact (not_le_of_gt (digit_lt hN hd hb hac)) h

private theorem digit_eq {N a b c d : ℤ} (hN : 0 ≤ N)
    (hb : 0 ≤ b ∧ b < N) (hd : 0 ≤ d ∧ d < N)
    (h : N * a + b = N * c + d) : a = c ∧ b = d := by
  have ha := digit_le hN hb.1 hd.2 h.le
  have hc := digit_le hN hd.1 hb.2 h.ge
  have hac : a = c := le_antisymm ha hc
  exact ⟨hac, by rw [hac] at h; omega⟩

private def liftPoints {α : Type} {k : ℕ} (N : ℤ)
    (A : α → Fin (k + 1) → ℤ) (p : α × α) : Fin (k + 2) → ℤ :=
  Fin.cons (N * A p.1 0 + (N - 1 - A p.2 0))
    (fun j => N * A p.1 j + A p.2 j)

private theorem lift_bounds {α : Type} {k : ℕ} {N : ℤ}
    {A : α → Fin (k + 1) → ℤ} (hN : 0 < N)
    (hr : ∀ a j, 0 ≤ A a j ∧ A a j < N) :
    ∀ p j, 0 ≤ liftPoints N A p j ∧ liftPoints N A p j < N * N := by
  intro p j
  refine Fin.cases ?_ (fun i => ?_) j
  · have ha := hr p.1 0
    have hb := hr p.2 0
    simp only [liftPoints, Fin.cons_zero]
    constructor
    · exact add_nonneg (mul_nonneg hN.le ha.1) (by omega)
    · have h := mul_le_mul_of_nonneg_left (show A p.1 0 + 1 ≤ N by omega) hN.le
      nlinarith
  · have ha := hr p.1 i
    have hb := hr p.2 i
    simp only [liftPoints, Fin.cons_succ]
    constructor
    · exact add_nonneg (mul_nonneg hN.le ha.1) hb.1
    · have h := mul_le_mul_of_nonneg_left (show A p.1 i + 1 ≤ N by omega) hN.le
      nlinarith

private theorem lift_first_injective {α : Type} {k : ℕ} {N : ℤ}
    {A : α → Fin (k + 1) → ℤ} (hN : 0 < N)
    (hr : ∀ a j, 0 ≤ A a j ∧ A a j < N)
    (hi : Function.Injective (fun a => A a 0)) :
    Function.Injective (fun p => liftPoints N A p 0) := by
  intro p q h
  simp only [liftPoints, Fin.cons_zero] at h
  have hp := hr p.2 0
  have hq := hr q.2 0
  have hh := digit_eq hN.le
    (show 0 ≤ N - 1 - A p.2 0 ∧ N - 1 - A p.2 0 < N by omega)
    (show 0 ≤ N - 1 - A q.2 0 ∧ N - 1 - A q.2 0 < N by omega) h
  exact Prod.ext (hi hh.1) (hi (by linarith [hh.2]))

private theorem lift_coordinate_injective {α : Type} {k : ℕ} {N : ℤ}
    {A : α → Fin (k + 1) → ℤ} (hN : 0 < N)
    (hr : ∀ a j, 0 ≤ A a j ∧ A a j < N)
    (hi : ∀ j, Function.Injective (fun a => A a j)) :
    ∀ j, Function.Injective (fun p => liftPoints N A p j) := by
  intro j
  refine Fin.cases (lift_first_injective hN hr (hi 0)) (fun i => ?_) j
  intro p q h
  simp only [liftPoints, Fin.cons_succ] at h
  have hh := digit_eq hN.le (hr p.2 i) (hr q.2 i) h
  exact Prod.ext (hi i hh.1) (hi i hh.2)

private theorem lift_between_blocks {α : Type} {k : ℕ} {N : ℤ}
    {A : α → Fin (k + 1) → ℤ} (hN : 0 < N)
    (hr : ∀ a j, 0 ≤ A a j ∧ A a j < N)
    {p q r : α × α} (h : Between (liftPoints N A p) (liftPoints N A q)
      (liftPoints N A r)) : Between (A p.1) (A q.1) (A r.1) := by
  intro j
  have hj := h j.succ
  simp only [liftPoints, Fin.cons_succ] at hj
  rcases hj with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨digit_le hN.le (hr p.2 j).1 (hr q.2 j).2 h1,
      digit_le hN.le (hr q.2 j).1 (hr r.2 j).2 h2⟩
  · exact Or.inr ⟨digit_le hN.le (hr r.2 j).1 (hr q.2 j).2 h1,
      digit_le hN.le (hr q.2 j).1 (hr p.2 j).2 h2⟩

private theorem same_block_digits {N a b d c e : ℤ} (hN : 0 < N)
    (hd : 0 ≤ d ∧ d < N) (he : 0 ≤ e ∧ e < N)
    (hac : a ≠ c)
    (h : (N * a + b ≤ N * a + d ∧ N * a + d ≤ N * c + e) ∨
      (N * c + e ≤ N * a + d ∧ N * a + d ≤ N * a + b))
    (h' : (N * a + (N - 1 - b) ≤ N * a + (N - 1 - d) ∧
        N * a + (N - 1 - d) ≤ N * c + (N - 1 - e)) ∨
      (N * c + (N - 1 - e) ≤ N * a + (N - 1 - d) ∧
        N * a + (N - 1 - d) ≤ N * a + (N - 1 - b))) : b = d := by
  rcases lt_or_gt_of_ne hac with hac | hac
  · have h1 := digit_lt hN.le hd.2 he.1 hac
    have h2 := digit_lt hN.le (show N - 1 - d < N by omega)
      (show 0 ≤ N - 1 - e by omega) hac
    rcases h with h | h <;> rcases h' with h' | h' <;> omega
  · have h1 := digit_lt hN.le he.2 hd.1 hac
    have h2 := digit_lt hN.le (show N - 1 - e < N by omega)
      (show 0 ≤ N - 1 - d by omega) hac
    rcases h with h | h <;> rcases h' with h' | h' <;> omega

private theorem lift_same_left {α : Type} {k : ℕ} {N : ℤ}
    {A : α → Fin (k + 1) → ℤ} (hN : 0 < N)
    (hr : ∀ a j, 0 ≤ A a j ∧ A a j < N)
    (hi : Function.Injective (fun a => A a 0))
    {p q r : α × α} (hpq : p.1 = q.1) (hqr : q.1 ≠ r.1)
    (h : Between (liftPoints N A p) (liftPoints N A q) (liftPoints N A r)) : p = q := by
  have hac : A p.1 0 ≠ A r.1 0 := by
    intro hh
    exact hqr (hpq.symm.trans (hi hh))
  have h0 := h 0
  have h1 := h (Fin.succ 0)
  simp only [liftPoints, Fin.cons_zero, Fin.cons_succ] at h0 h1
  rw [← hpq] at h0 h1
  have hh := same_block_digits hN (hr q.2 0) (hr r.2 0) hac h1 h0
  exact Prod.ext hpq (hi hh)

private theorem between_reverse {k : ℕ} {x y z : Fin k → ℤ}
    (h : Between x y z) : Between z y x := fun j => (h j).symm

private theorem lift_gp {α : Type} {k : ℕ} {N : ℤ}
    {A : α → Fin (k + 1) → ℤ} (hN : 0 < N)
    (hr : ∀ a j, 0 ≤ A a j ∧ A a j < N)
    (hi : Function.Injective (fun a => A a 0))
    (hg : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → ¬ Between (A a) (A b) (A c)) :
    ∀ p q r, p ≠ q → q ≠ r → p ≠ r →
      ¬ Between (liftPoints N A p) (liftPoints N A q) (liftPoints N A r) := by
  intro p q r hpq hqr hpr h
  have hblocks := lift_between_blocks hN hr h
  by_cases hab : p.1 = q.1
  · by_cases hbc : q.1 = r.1
    · have hlow : Between (A p.2) (A q.2) (A r.2) := by
        intro j
        have hj := h j.succ
        simp only [liftPoints, Fin.cons_succ] at hj
        rw [hab, hbc] at hj
        rcases hj with hj | hj <;> [left; right] <;> constructor <;> omega
      exact hg p.2 q.2 r.2 (fun hh => hpq (Prod.ext hab hh))
        (fun hh => hqr (Prod.ext hbc hh))
        (fun hh => hpr (Prod.ext (hab.trans hbc) hh)) hlow
    · exact hpq (lift_same_left hN hr hi hab hbc h)
  · by_cases hbc : q.1 = r.1
    · exact hqr (lift_same_left hN hr hi hbc.symm (Ne.symm hab) (between_reverse h)).symm
    · by_cases hac : p.1 = r.1
      · have hj := hblocks 0
        rw [hac] at hj
        have hh : A q.1 0 = A r.1 0 := by rcases hj with hj | hj <;> omega
        exact hbc (hi hh)
      · exact hg p.1 q.1 r.1 hab hbc hac hblocks

private theorem sharp_size_succ (n : ℕ) :
    2 ^ (2 ^ (n + 1)) = (2 ^ (2 ^ n)) * (2 ^ (2 ^ n)) := by
  rw [pow_succ, mul_two, pow_add]

private structure SharpArray (n : ℕ) where
  Index : Type
  finiteIndex : Fintype Index
  inhabitedIndex : Nonempty Index
  point : Index → Fin (n + 1) → ℤ
  card_index : @Fintype.card Index finiteIndex = 2 ^ (2 ^ n)
  bounded : ∀ a j, 0 ≤ point a j ∧ point a j < (2 ^ (2 ^ n) : ℕ)
  coordinate_injective : ∀ j, Function.Injective (fun a => point a j)
  gp : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → ¬ Between (point a) (point b) (point c)

private def baseArray : SharpArray 0 where
  Index := Fin 2
  finiteIndex := inferInstance
  inhabitedIndex := inferInstance
  point := fun a _ => a.val
  card_index := by simp
  bounded := by
    intro a j
    constructor
    · exact_mod_cast Nat.zero_le a.val
    · simpa using (show (a.val : ℤ) < 2 by exact_mod_cast a.isLt)
  coordinate_injective := by
    intro j a b h
    change (a.val : ℤ) = (b.val : ℤ) at h
    apply Fin.ext
    exact_mod_cast h
  gp := by
    intro a b c hab hbc hac h
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

private noncomputable def extendArray {n : ℕ} (a : SharpArray n) : SharpArray (n + 1) := by
  letI := a.finiteIndex
  letI := a.inhabitedIndex
  have hN : (0 : ℤ) < (2 ^ (2 ^ n) : ℕ) := by positivity
  refine {
    Index := a.Index × a.Index
    finiteIndex := inferInstance
    inhabitedIndex := inferInstance
    point := liftPoints (2 ^ (2 ^ n) : ℕ) a.point
    card_index := ?_
    bounded := ?_
    coordinate_injective := lift_coordinate_injective hN a.bounded a.coordinate_injective
    gp := lift_gp hN a.bounded (a.coordinate_injective 0) a.gp
  }
  · rw [Fintype.card_prod, a.card_index, sharp_size_succ]
  · rw [sharp_size_succ, Nat.cast_mul]
    exact lift_bounds hN a.bounded

private noncomputable def sharpArray : (n : ℕ) → SharpArray n
  | 0 => baseArray
  | n + 1 => extendArray (sharpArray n)

/-- The coordinate bound is attained by an explicitly recursive finite nonempty set. -/
theorem exists_attaining (n : ℕ) :
    ∃ S : Finset (Fin (n + 1) → ℤ),
      CoordinateGP S ∧ S.card = 2 ^ (2 ^ n) ∧ S.Nonempty ∧
      (∀ x ∈ S, ∀ j, 0 ≤ x j ∧ x j < (2 ^ (2 ^ n) : ℕ)) ∧
      ∀ j, Set.InjOn (fun x : Fin (n + 1) → ℤ => x j) (S : Set _) := by
  classical
  let a := sharpArray n
  let _ := a.finiteIndex
  let _ := a.inhabitedIndex
  let S := Finset.univ.image a.point
  refine ⟨S, ?_, ?_, Finset.image_nonempty.mpr Finset.univ_nonempty, ?_, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hz
    exact a.gp i j l (fun hij => hxy (congrArg a.point hij))
      (fun hjl => hyz (congrArg a.point hjl)) (fun hil => hxz (congrArg a.point hil)) h
  · have hi : Function.Injective a.point := fun i j hij => a.coordinate_injective 0 (congrFun hij 0)
    simpa only [S, Finset.card_image_of_injective _ hi, Finset.card_univ] using a.card_index
  · intro x hx j
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact a.bounded i j
  · intro j x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg a.point (a.coordinate_injective j hxy)

#print axioms card_le
#print axioms exists_attaining

end IntegerLatticeStatic
