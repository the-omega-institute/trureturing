/- GID: D5/S1/Words/RankOneMorphismIterationBoundDefs
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundDefs
   mirror-E: none(waiver:source-facing-definitions)
   anchors: []
   digest: Exact binary morphism, Parikh charge and original cyclic-block witness for Filimonova–Puzynina 2605.30306. -/
import D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs
import D5.S0.Automata.DFAOStateLowerBound
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound

open AbelianBorders.AbelianBorderQuestionDefs (letterCount factor)

abbrev Letter := Fin 2
abbrev Word := List Letter
abbrev Morphism := Letter → Word

/-- Exact Parikh vector, using the existing public List.count supplier. -/
def parikh (w : Word) : Letter → ℕ := letterCount w

/-- Extension of the two actual image words by concatenation. -/
def subst {α β : Type*} (f : α → List β) (w : List α) : List β := w.flatMap f

/-- Actual finite iterates on a letter, including the identity iterate. -/
def image {α : Type*} (f : α → List α) : ℕ → α → List α
  | 0, c => [c]
  | k + 1, c => subst f (image f k c)

def Nonerasing (f : Morphism) : Prop := ∀ c, 0 < (f c).length

def Prolongable (f : Morphism) : Prop := ∃ v : Word, v ≠ [] ∧ f 0 = 0 :: v

/-- Primitivity on the actual alphabet, not a spectral proxy. -/
def Primitive (f : Morphism) : Prop :=
  ∃ k, 0 < k ∧ ∀ c b, b ∈ image f k c

/-- Rank one of the actual two incidence columns. -/
def RankOne (f : Morphism) : Prop :=
  parikh (f 0) 0 * parikh (f 1) 1 = parikh (f 1) 0 * parikh (f 0) 1

/-- Exact, rather than frequency, abelian equivalence. -/
def AbelianEq (u v : Word) : Prop := parikh u = parikh v

/-- The complete finite word is a concatenation of nonempty blocks with vector P. -/
def Blocks (w : Word) (P : Letter → ℕ) : Prop :=
  ∃ bs : List Word, bs.flatten = w ∧ bs ≠ [] ∧
    ∀ b ∈ bs, b ≠ [] ∧ parikh b = P

/-- The paper's actual four finite words and both complete rotations. -/
def OriginalCyclicBlockWitness (f : Morphism) (K : ℕ) : Prop :=
  ∃ u v u' v' : Word, image f K 0 = u ++ v ∧ image f K 1 = u' ++ v' ∧
    AbelianEq u u' ∧ ∃ P, Blocks (v ++ u) P ∧ Blocks (v' ++ u') P

/-- Arbitrary one-sided preperiod, with positive, exactly equal-Parikh blocks. -/
def UltimatelyAbelianPeriodic (x : ℕ → Letter) : Prop :=
  ∃ r p : ℕ, 0 < p ∧ ∀ j, AbelianEq (factor x (r + j * p) p) (factor x r p)

/-- All actual iterates are prefixes of this word. Growth gives uniqueness. -/
def IsFixedWord (f : Morphism) (x : ℕ → Letter) : Prop :=
  ∀ k, factor x 0 (image f k 0).length = image f k 0

/-- Total computable bound from the two image words alone. -/
def iterationBound (f : Morphism) : ℕ := 2 ^ ((f 0).length + (f 1).length)

@[simp] theorem parikh_nil : parikh [] = 0 := by ext c; simp [parikh, letterCount]

@[simp] theorem parikh_append (u v : Word) (c : Letter) :
    parikh (u ++ v) c = parikh u c + parikh v c := by simp [parikh, letterCount]

@[simp] theorem subst_nil {α β : Type*} (f : α → List β) : subst f [] = [] := rfl
@[simp] theorem subst_cons {α β : Type*} (f : α → List β) (c : α) (w : List α) :
    subst f (c :: w) = f c ++ subst f w := rfl
@[simp] theorem subst_append {α β : Type*} (f : α → List β) (u v : List α) :
    subst f (u ++ v) = subst f u ++ subst f v := List.flatMap_append
@[simp] theorem image_zero {α : Type*} (f : α → List α) (c : α) : image f 0 c = [c] := rfl
@[simp] theorem image_succ {α : Type*} (f : α → List α) (k : ℕ) (c : α) :
    image f (k+1) c = subst f (image f k c) := rfl
@[simp] theorem image_one {α : Type*} (f : α → List α) (c : α) : image f 1 c = f c := by simp [image]

theorem parikh_binary_length (w : Word) : parikh w 0 + parikh w 1 = w.length := by
  induction w with
  | nil => simp [parikh, letterCount]
  | cons c w ih =>
    fin_cases c <;> simp_all [parikh, letterCount] <;> omega

theorem abelianEq_length {u v : Word} (h : AbelianEq u v) : u.length = v.length := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hu := parikh_binary_length u
  have hv := parikh_binary_length v
  omega

theorem parikh_subst (f : Morphism) (w : Word) (b : Letter) :
    parikh (subst f w) b = parikh w 0 * parikh (f 0) b +
      parikh w 1 * parikh (f 1) b := by
  induction w with
  | nil => simp [parikh, letterCount]
  | cons c w ih =>
    fin_cases c <;> simp_all [parikh, letterCount] <;> ring

theorem subst_image_commute {α : Type*} (f : α → List α) (k : ℕ) (w : List α) :
    subst (image f k) (subst f w) = subst f (subst (image f k) w) := by
  induction k with
  | zero => simp [subst, image]
  | succ k ih =>
    have h (v : List α) : subst (image f (k+1)) v = subst f (subst (image f k) v) := by
      induction v with
      | nil => simp
      | cons c v hv => simp [hv]
    rw [h, ih, h]

theorem image_add {α : Type*} (f : α → List α) (k t : ℕ) (c : α) :
    image f (k+t) c = subst (image f k) (image f t c) := by
  induction t with
  | zero => simp [subst]
  | succ t ih =>
    simp only [Nat.add_succ, image_succ, ih]
    exact (subst_image_commute f k (image f t c)).symm

/-- Source rank-one arithmetic data, to be extracted from the actual matrix. -/
structure Parameters (f : Morphism) where
  A : ℕ
  B : ℕ
  n : ℕ
  m : ℕ
  A_pos : 0 < A
  B_pos : 0 < B
  n_pos : 0 < n
  m_pos : 0 < m
  coprime : Nat.Coprime n m
  count_a : ∀ c, parikh (f c) 0 = (if c = 0 then n else m) * A
  count_b : ∀ c, parikh (f c) 1 = (if c = 0 then n else m) * B

namespace Parameters
variable {f : Morphism} (p : Parameters f)
def d : ℕ := p.A + p.B
def lam : ℕ := p.n * p.A + p.m * p.B
def mult (c : Letter) : ℕ := if c = 0 then p.n else p.m
def charge (w : Word) : ℤ := (p.B : ℤ) * parikh w 0 - (p.A : ℤ) * parikh w 1

theorem d_pos : 0 < p.d := by exact Nat.add_pos_left p.A_pos p.B
theorem lam_ge_two : 2 ≤ p.lam := by
  have h1 := Nat.mul_pos p.n_pos p.A_pos
  have h2 := Nat.mul_pos p.m_pos p.B_pos
  dsimp [lam]; omega

theorem image_length (c : Letter) : (f c).length = p.mult c * p.d := by
  rw [← parikh_binary_length, p.count_a, p.count_b]
  simp only [mult, d]; split_ifs <;> ring

@[simp] theorem charge_nil : p.charge [] = 0 := by simp [charge]
@[simp] theorem charge_append (u v : Word) :
    p.charge (u ++ v) = p.charge u + p.charge v := by
  simp only [charge, parikh_append, Nat.cast_add]; ring

@[simp] theorem charge_image (c : Letter) : p.charge (f c) = 0 := by
  rw [charge, p.count_a, p.count_b]
  push_cast; ring

@[simp] theorem charge_subst (w : Word) : p.charge (subst f w) = 0 := by
  induction w with
  | nil => simp
  | cons c w ih => simp [ih]

theorem charge_eq_iff {u v : Word} (hl : u.length = v.length) :
    p.charge u = p.charge v ↔ AbelianEq u v := by
  have hu := parikh_binary_length u
  have hv := parikh_binary_length v
  have hA : (0 : ℤ) < p.A := by exact_mod_cast p.A_pos
  have hB : (0 : ℤ) < p.B := by exact_mod_cast p.B_pos
  have hz : (parikh u 0 : ℤ) + parikh u 1 = (parikh v 0 : ℤ) + parikh v 1 := by
    exact_mod_cast (show parikh u 0 + parikh u 1 = parikh v 0 + parikh v 1 by omega)
  constructor
  · intro h
    dsimp [charge] at h
    have h0 : (parikh u 0 : ℤ) = parikh v 0 := by nlinarith
    have h1 : (parikh u 1 : ℤ) = parikh v 1 := by omega
    ext c; fin_cases c
    · exact_mod_cast h0
    · exact_mod_cast h1
  · intro h
    dsimp [charge]; rw [congrFun h 0, congrFun h 1]

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
