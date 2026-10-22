/- GID: D5/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/MariotManzoniMOCAStrength
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary arrays of mutually orthogonal bipermutive CA have strength three. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#19624; Proved)
Direct frozen dependencies: none (all declarations; pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19669
The definitions ca, IsBipermutive, AreOrthogonal, IsMOCA, mocaArray,
IsOrthogonalArray and claim express Definition 1, Eq. (6), Eq. (7),
and the strength question of Mariot and Manzoni, arXiv:2207.08280v1.
The coordinate update and the integer sign are used as expressions, not aliases.
proof_shape: bit_flip_twice: bind-only; consumers: flip_twice.
proof_shape: flip_twice: bind-only; consumers: sum_flip_zero.
proof_shape: sign_flip: bind-only; consumers: sum_flip_zero.
proof_shape: sum_flip_zero: bind-only; consumers: column_sum_zero, pair_sum_zero_of_lt, pair_sum_zero_of_orthogonal, triple_sum_zero_sorted.
proof_shape: ca_flip_outside: bind-only; consumers: pair_sum_zero_of_lt, triple_sum_zero_sorted.
proof_shape: ca_flip_left: bind-only; consumers: column_sum_zero, pair_sum_zero_of_lt, triple_sum_zero_sorted.
proof_shape: ca_flip_right: bind-only; consumers: triple_sum_zero_sorted.
proof_shape: column_sum_zero: bind-only; consumers: result.
proof_shape: pair_sum_zero_of_lt: bind-only; consumers: pair_sum_zero.
proof_shape: orthogonal_bijective: bind-only; consumers: pair_sum_zero_of_orthogonal.
proof_shape: pair_sum_zero_of_orthogonal: bind-only; consumers: pair_sum_zero.
proof_shape: pair_sum_zero: bind-only; consumers: result.
proof_shape: triple_sum_zero_sorted: bind-only; consumers: triple_sum_zero.
proof_shape: triple_sum_zero: bind-only; consumers: result.
proof_shape: indicator_three: bind-only; consumers: uniform_three_of_sums.
proof_shape: uniform_three_of_sums: bind-only; consumers: result.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Binding conventions for L. Mariot and L. Manzoni, "Building Correlation Immune Functions from Sets of Mutually
Orthogonal Cellular Automata", arXiv:2207.08280v1: the no-boundary cellular automaton `F : F₂^{2b} → F₂^b` of diameter
`d = b + 1` (Definition 1 with `n = 2(d − 1)`), bipermutive local rules, orthogonal CA (Eq. (6) on their Latin squares),
the array `A` of Eq. (7), binary orthogonal arrays of strength `t`, and the question of Section 5, "prove that the
binary OA obtained from a set of k-MOCA has always at least strength 3". -/

namespace D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength

/-- Definition 1 with length `n = 2b` and diameter `d = b + 1`: `F(x)_j = f(x_j, …, x_{j+d−1})` for the `n − d + 1 = b`
output cells. -/
def ca (b : ℕ) (f : (Fin (b + 1) → ZMod 2) → ZMod 2) (x : Fin (b + b) → ZMod 2) : Fin b → ZMod 2 :=
  fun j => f fun t => x ⟨j.1 + t.1, by omega⟩

/-- A local rule of diameter `d = b + 1` is bipermutive: `f(x₁, …, x_d) = x₁ ⊕ φ(x₂, …, x_{d−1}) ⊕ x_d` for some
`φ : F₂^{d−2} → F₂`. -/
def IsBipermutive (b : ℕ) (f : (Fin (b + 1) → ZMod 2) → ZMod 2) : Prop :=
  ∃ φ : (Fin (b - 1) → ZMod 2) → ZMod 2, ∀ y : Fin (b + 1) → ZMod 2,
    f y = y ⟨0, by omega⟩ + φ (fun t => y ⟨t.1 + 1, by omega⟩) + y ⟨b, by omega⟩

/-- Two CA are orthogonal when their Latin squares `L_F(r, c) = F(r, c)` (rows indexed by the left half, columns by the
right half of the input) are orthogonal, Eq. (6): distinct cells carry distinct superposed pairs. -/
def AreOrthogonal (b : ℕ) (f g : (Fin (b + 1) → ZMod 2) → ZMod 2) : Prop :=
  ∀ r₁ c₁ r₂ c₂ : Fin b → ZMod 2, (r₁, c₁) ≠ (r₂, c₂) →
    (ca b f (Fin.append r₁ c₁), ca b g (Fin.append r₁ c₁)) ≠
      (ca b f (Fin.append r₂ c₂), ca b g (Fin.append r₂ c₂))

/-- A set of `k`-MOCA: `k` pairwise orthogonal CA with bipermutive local rules of diameter `b + 1`. -/
def IsMOCA (b k : ℕ) (f : Fin k → (Fin (b + 1) → ZMod 2) → ZMod 2) : Prop :=
  (∀ i, IsBipermutive b (f i)) ∧ ∀ i h, i ≠ h → AreOrthogonal b (f i) (f h)

/-- Eq. (7): the `N × n` array with `N = 2^{2b}` rows indexed by the inputs and `n = kb` columns, the row of an input
being `(F₁(x), …, F_k(x))`; the column `(i, j)` is output cell `j` of `F_i`. -/
def mocaArray (b k : ℕ) (f : Fin k → (Fin (b + 1) → ZMod 2) → ZMod 2) :
    (Fin (b + b) → ZMod 2) → Fin k × Fin b → ZMod 2 :=
  fun x c => ca b (f c.1) x c.2

/-- An `OA(N, n, 2, t)`: in every `N × t` subarray (any `t` distinct columns), each binary `t`-tuple occurs exactly
`λ = N / 2^t` times. -/
def IsOrthogonalArray {R C : Type*} [Fintype R] (A : R → C → ZMod 2) (t : ℕ) : Prop :=
  ∀ cols : Fin t → C, Function.Injective cols → ∀ v : Fin t → ZMod 2,
    Fintype.card {r : R // ∀ s, A r (cols s) = v s} = Fintype.card R / 2 ^ t

/-- Section 5: the binary OA obtained from a set of `k`-MOCA always has strength at least 3. -/
def claim : Prop :=
  ∀ (b k : ℕ) (f : Fin k → (Fin (b + 1) → ZMod 2) → ZMod 2), IsMOCA b k f →
    IsOrthogonalArray (mocaArray b k f) 3

end D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength

set_option maxHeartbeats 80000
set_option maxRecDepth 4096

namespace D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength
open Finset

private theorem bit_flip_twice (z : ZMod 2) : z + 1 + 1 = z := by
  exact CharTwo.add_cancel_right z 1


private theorem flip_twice {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) :
    (fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) m ((fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) m x) = x := by
  ext q; by_cases h : q = m <;> simp [ h, bit_flip_twice]

private theorem sign_flip (z : ZMod 2) : (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (z + 1) = - (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) z := by
  revert z; decide


private theorem sum_flip_zero {n : ℕ} (g : (Fin n → ZMod 2) → ZMod 2)
    (m : Fin n) (h : ∀ x, g ((fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) m x) = g x + 1) :
    ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (g x) = 0 := by
  let e : (Fin n → ZMod 2) ≃ (Fin n → ZMod 2) :=
    ⟨(fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) m, (fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) m, flip_twice m, flip_twice m⟩
  have hh := Equiv.sum_comp e (fun x => (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (g x))
  change (∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (g ((fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) m x))) = ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (g x) at hh
  simp_rw [h, sign_flip] at hh
  rw [Finset.sum_neg_distrib] at hh
  dsimp only at hh ⊢
  linarith

private theorem ca_flip_outside {b : ℕ} (f : (Fin (b + 1) → ZMod 2) → ZMod 2)
    (j : Fin b) (m : Fin (b+b)) (hm : m.val < j.val ∨ j.val + b < m.val)
    (x : Fin (b+b) → ZMod 2) : ca b f ((fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) m x) j = ca b f x j := by
  apply congrArg f
  funext t
  have hn : (⟨j.val + t.val, by omega⟩ : Fin (b+b)) ≠ m := by
    intro he
    have heq : j.val + t.val = m.val := congrArg Fin.val he
    rcases hm with hm | hm <;> omega
  simp [ hn]

private theorem ca_flip_left {b : ℕ} (f : (Fin (b + 1) → ZMod 2) → ZMod 2)
    (hf : IsBipermutive b f) (j : Fin b) (x : Fin (b+b) → ZMod 2) :
    ca b f ((fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) ⟨j.val, by omega⟩ x) j = ca b f x j + 1 := by
  obtain ⟨φ, hφ⟩ := hf
  unfold ca
  rw [hφ, hφ]
  have hi : (fun t : Fin (b-1) => (fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) ⟨j.val, by omega⟩ x ⟨j.val + (t.val+1), by omega⟩) =
      (fun t : Fin (b-1) => x ⟨j.val + (t.val+1), by omega⟩) := by
    funext t
    have hn : (⟨j.val + (t.val+1), by omega⟩ : Fin (b+b)) ≠ ⟨j.val, by omega⟩ := by
      intro h
      have heq : j.val + (t.val+1) = j.val := congrArg Fin.val h
      omega
    simp [ hn]
  have hr : (⟨j.val + b, by omega⟩ : Fin (b+b)) ≠ ⟨j.val, by omega⟩ := by
    intro h
    have heq : j.val+b = j.val := congrArg Fin.val h
    omega
  simp only [Nat.add_zero, hi]
  simp [ hr]
  ring

private theorem ca_flip_right {b : ℕ} (f : (Fin (b + 1) → ZMod 2) → ZMod 2)
    (hf : IsBipermutive b f) (j : Fin b) (x : Fin (b+b) → ZMod 2) :
    ca b f ((fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) ⟨j.val+b, by omega⟩ x) j = ca b f x j + 1 := by
  obtain ⟨φ, hφ⟩ := hf
  unfold ca
  rw [hφ, hφ]
  have hi : (fun t : Fin (b-1) => (fun {n : ℕ} (m : Fin n) (x : Fin n → ZMod 2) => Function.update x m (x m + 1)) ⟨j.val+b, by omega⟩ x ⟨j.val + (t.val+1), by omega⟩) =
      (fun t : Fin (b-1) => x ⟨j.val + (t.val+1), by omega⟩) := by
    funext t
    have hn : (⟨j.val + (t.val+1), by omega⟩ : Fin (b+b)) ≠ ⟨j.val+b, by omega⟩ := by
      intro h
      have heq : j.val + (t.val+1) = j.val+b := congrArg Fin.val h
      omega
    simp [ hn]
  have hl : (⟨j.val, by omega⟩ : Fin (b+b)) ≠ ⟨j.val+b, by omega⟩ := by
    intro h
    have heq : j.val = j.val+b := congrArg Fin.val h
    omega
  simp only [Nat.add_zero, hi]
  simp [ hl]
  ring

end D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength

namespace D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength
open Finset

private theorem column_sum_zero {b k : ℕ}
    (f : Fin k → (Fin (b+1) → ZMod 2) → ZMod 2)
    (hf : ∀ i, IsBipermutive b (f i)) (c : Fin k × Fin b) :
    ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (mocaArray b k f x c) = 0 := by
  apply sum_flip_zero _ (⟨c.2.val, by omega⟩ : Fin (b+b))
  intro x
  exact ca_flip_left (f c.1) (hf c.1) c.2 x

private theorem pair_sum_zero_of_lt {b k : ℕ}
    (f : Fin k → (Fin (b+1) → ZMod 2) → ZMod 2)
    (hf : ∀ i, IsBipermutive b (f i)) (c d : Fin k × Fin b)
    (hcd : c.2.val < d.2.val) :
    ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (mocaArray b k f x c + mocaArray b k f x d) = 0 := by
  apply sum_flip_zero _ (⟨c.2.val, by omega⟩ : Fin (b+b))
  intro x
  dsimp only [mocaArray]
  rw [ca_flip_left _ (hf _), ca_flip_outside _ _ _ (Or.inl hcd)]
  ring

private theorem orthogonal_bijective {b : ℕ}
    (f g : (Fin (b+1) → ZMod 2) → ZMod 2) (ho : AreOrthogonal b f g) :
    Function.Bijective (fun x => (ca b f x, ca b g x)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y hxy
    let l (z : Fin (b+b) → ZMod 2) : Fin b → ZMod 2 := fun i => z (Fin.castAdd b i)
    let r (z : Fin (b+b) → ZMod 2) : Fin b → ZMod 2 := fun i => z (Fin.natAdd b i)
    have h : (l x,r x) = (l y,r y) := by
      by_contra hn
      have hh := ho (l x) (r x) (l y) (r y) hn
      simp only [l,r,Fin.append_castAdd_natAdd] at hh
      exact hh hxy
    have hl : l x = l y := congrArg Prod.fst h
    have hr : r x = r y := congrArg Prod.snd h
    calc
      x = Fin.append (l x) (r x) := Fin.append_castAdd_natAdd.symm
      _ = Fin.append (l y) (r y) := by rw [hl,hr]
      _ = y := Fin.append_castAdd_natAdd
  · simp [Fintype.card_prod, ZMod.card, pow_add]

private theorem pair_sum_zero_of_orthogonal {b : ℕ}
    (f g : (Fin (b+1) → ZMod 2) → ZMod 2) (ho : AreOrthogonal b f g)
    (j l : Fin b) :
    ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (ca b f x j + ca b g x l) = 0 := by
  rw [(orthogonal_bijective f g ho).sum_comp (fun y => (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (y.1 j + y.2 l))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro y _
  apply sum_flip_zero _ l
  intro x
  simp [ add_assoc]

private theorem pair_sum_zero {b k : ℕ}
    (f : Fin k → (Fin (b+1) → ZMod 2) → ZMod 2)
    (hf : IsMOCA b k f) (c d : Fin k × Fin b) (hcd : c ≠ d) :
    ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (mocaArray b k f x c + mocaArray b k f x d) = 0 := by
  rcases lt_trichotomy c.2.val d.2.val with h | h | h
  · exact pair_sum_zero_of_lt f hf.1 c d h
  · have hpos : c.2 = d.2 := Fin.ext h
    have hi : c.1 ≠ d.1 := by intro he; exact hcd (Prod.ext he hpos)
    exact pair_sum_zero_of_orthogonal _ _ (hf.2 _ _ hi) _ _
  · simpa only [add_comm] using pair_sum_zero_of_lt f hf.1 d c h

private theorem triple_sum_zero_sorted {b k : ℕ}
    (f : Fin k → (Fin (b+1) → ZMod 2) → ZMod 2)
    (hf : ∀ i, IsBipermutive b (f i)) (c d e : Fin k × Fin b)
    (hcd : c.2.val ≤ d.2.val) (hde : d.2.val ≤ e.2.val) :
    ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (mocaArray b k f x c + mocaArray b k f x d + mocaArray b k f x e) = 0 := by
  by_cases h01 : c.2.val < d.2.val
  · apply sum_flip_zero _ (⟨c.2.val, by omega⟩ : Fin (b+b))
    intro x
    dsimp only [mocaArray]
    rw [ca_flip_left _ (hf _), ca_flip_outside _ _ _ (Or.inl h01),
      ca_flip_outside _ _ _ (Or.inl (show c.2.val < e.2.val by omega))]
    ring
  · by_cases h12 : d.2.val < e.2.val
    · apply sum_flip_zero _ (⟨e.2.val+b, by omega⟩ : Fin (b+b))
      intro x
      dsimp only [mocaArray]
      rw [ca_flip_outside _ _ _ (Or.inr (show c.2.val+b < e.2.val+b by omega)),
        ca_flip_outside _ _ _ (Or.inr (show d.2.val+b < e.2.val+b by omega)),
        ca_flip_right _ (hf _)]
      ring
    · have h0 : c.2 = e.2 := Fin.ext (by omega)
      have h1 : d.2 = e.2 := Fin.ext (by omega)
      apply sum_flip_zero _ (⟨e.2.val, by omega⟩ : Fin (b+b))
      intro x
      dsimp only [mocaArray]
      rw [h0,h1,ca_flip_left _ (hf _),ca_flip_left _ (hf _),ca_flip_left _ (hf _)]
      ring_nf
      simp only [show (3 : ZMod 2) = 1 by decide]

private theorem triple_sum_zero {b k : ℕ}
    (f : Fin k → (Fin (b+1) → ZMod 2) → ZMod 2)
    (hf : ∀ i, IsBipermutive b (f i)) (c d e : Fin k × Fin b) :
    ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (mocaArray b k f x c + mocaArray b k f x d + mocaArray b k f x e) = 0 := by
  rcases le_total c.2.val d.2.val with hcd | hdc
  · rcases le_total d.2.val e.2.val with hde | hed
    · exact triple_sum_zero_sorted f hf c d e hcd hde
    · rcases le_total c.2.val e.2.val with hce | hec
      · simpa only [add_comm,add_left_comm,add_assoc] using triple_sum_zero_sorted f hf c e d hce hed
      · simpa only [add_comm,add_left_comm,add_assoc] using triple_sum_zero_sorted f hf e c d hec hcd
  · rcases le_total c.2.val e.2.val with hce | hec
    · simpa only [add_comm,add_left_comm,add_assoc] using triple_sum_zero_sorted f hf d c e hdc hce
    · rcases le_total d.2.val e.2.val with hde | hed
      · simpa only [add_comm,add_left_comm,add_assoc] using triple_sum_zero_sorted f hf d e c hde hec
      · simpa only [add_comm,add_left_comm,add_assoc] using triple_sum_zero_sorted f hf e d c hed hdc

end D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength

namespace D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength
open Finset

private theorem indicator_three (a b c u v w : ZMod 2) :
    8 * (if a=u ∧ b=v ∧ c=w then (1 : ℤ) else 0) =
      1 + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) a * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) u + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) b * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) v + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) c * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) w +
      (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (a+b) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (u+v) + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (a+c) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (u+w) +
      (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (b+c) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v+w) + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (a+b+c) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (u+v+w) := by
  revert a b c u v w; decide

private theorem uniform_three_of_sums {R : Type*} [Fintype R]
    (A : R → Fin 3 → ZMod 2)
    (hs : ∀ i, ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x i) = 0)
    (hp : ∀ i j, i ≠ j → ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x i + A x j) = 0)
    (ht : ∑ x, (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 0 + A x 1 + A x 2) = 0)
    (v : Fin 3 → ZMod 2) :
    Fintype.card {x : R // ∀ s, A x s = v s} = Fintype.card R / 2^3 := by
  classical
  have point (x : R) :
      8 * (if ∀ s, A x s = v s then (1 : ℤ) else 0) =
      1 + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 0) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v 0) + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 1) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v 1) +
      (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 2) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v 2) + (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 0 + A x 1) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v 0 + v 1) +
      (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 0 + A x 2) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v 0 + v 2) +
      (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 1 + A x 2) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v 1 + v 2) +
      (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (A x 0 + A x 1 + A x 2) * (fun z : ZMod 2 => if z = 0 then (1 : ℤ) else -1) (v 0 + v 1 + v 2) := by
    have he : (∀ s, A x s = v s) ↔ A x 0=v 0 ∧ A x 1=v 1 ∧ A x 2=v 2 := by
      constructor
      · intro h; exact ⟨h 0,h 1,h 2⟩
      · intro h s; fin_cases s <;> tauto
    simpa only [he] using indicator_three (A x 0) (A x 1) (A x 2) (v 0) (v 1) (v 2)
  have hh := congrArg (fun g : R → ℤ => ∑ x, g x) (funext point)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
    hs, hp 0 1 (by decide), hp 0 2 (by decide), hp 1 2 (by decide), ht,
    zero_mul, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  have hc : (∑ x, if ∀ s, A x s=v s then (1:ℤ) else 0) =
      (Fintype.card {x : R // ∀ s, A x s=v s} : ℤ) := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  rw [hc] at hh
  have hn : 8 * Fintype.card {x : R // ∀ s, A x s=v s} = Fintype.card R := by
    exact_mod_cast hh
  omega

theorem result : claim := by
  intro b k f hf cols hinj v
  apply uniform_three_of_sums (fun x s => mocaArray b k f x (cols s))
  · intro i; exact column_sum_zero f hf.1 (cols i)
  · intro i j hij; exact pair_sum_zero f hf (cols i) (cols j) (hinj.ne hij)
  · exact triple_sum_zero f hf.1 (cols 0) (cols 1) (cols 2)

end D5.S3.StatisticalMechanics.CellularAutomata.MariotManzoniMOCAStrength
