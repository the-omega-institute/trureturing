/- GID: D5/S1/Words/PostLie/AriWordProduct
   generality: I
   mirror-B: D5/B/S1/Words/PostLie/AriWordProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered primitive unshuffle realizes the finite ari product and its support bounds. -/


import D5.S1.Words.PostLie.AriProjection
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Tuple.Basic

/-! The assignment formula for the original ordered Grossman--Larson product. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false


noncomputable section
namespace D5.S1.Words.PostLie.AriWordProduct

open scoped BigOperators
open D5.S1.Words.PostLie.AriWordOperations
open D5.S1.Words.PostLie.AriProjection

/-- Subsequence in a specified slot; the original letter order is retained. -/
def slot {n : ℕ} : (A : List ℕ) → (Fin A.length → Fin n) → Fin n → Word
  | [], _, _ => 1
  | a :: A, f, j =>
    if f 0 = j then FreeMonoid.of a * slot A (fun i => f i.succ) j
    else slot A (fun i => f i.succ) j

/-- Iterated primitive unshuffle: each generator is primitive in all slots.
The target multiplication is componentwise concatenation, not a diagonal coalgebra. -/
def primitiveUnshuffle (n : ℕ) : Word →* MonoidAlgebra ℚ (Fin n → Word) :=
  FreeMonoid.lift fun a => ∑ j : Fin n,
    MonoidAlgebra.single (Function.update (fun _ => 1) j (FreeMonoid.of a)) 1

/-- All assignments occur separately, including coincident tuples from repeated letters. -/
theorem primitiveUnshuffle_assignments (n : ℕ) (A : List ℕ) :
    primitiveUnshuffle n (FreeMonoid.ofList A) =
      ∑ f : Fin A.length → Fin n, MonoidAlgebra.single (fun j => slot A f j) 1 := by
  classical
  induction A with
  | nil =>
    simp [primitiveUnshuffle, slot]
    rfl
  | cons a A ih =>
    change primitiveUnshuffle n (FreeMonoid.of a * FreeMonoid.ofList A) = _
    rw [map_mul, ih]
    have hletter : primitiveUnshuffle n (FreeMonoid.of a) =
        ∑ j : Fin n,
          MonoidAlgebra.single (Function.update (fun _ => 1) j (FreeMonoid.of a)) 1 := rfl
    rw [hletter, Finset.sum_mul]
    calc
      _ = ∑ jf : Fin n × (Fin A.length → Fin n),
          MonoidAlgebra.single (fun i => slot (a :: A) (Fin.cons jf.1 jf.2) i) 1 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f hf
        rw [MonoidAlgebra.single_mul_single, one_mul]
        congr 1
        funext i
        by_cases h : j = i
        · subst i
          simp [slot]
        · simp [slot, h, Ne.symm h, Function.update_apply]
      _ = _ := (Fin.consEquiv (fun _ : Fin (A.length + 1) => Fin n)).sum_comp
        (fun f => MonoidAlgebra.single (fun j => slot (a :: A) f j) (1 : ℚ))

/-- The concatenation product in the term for a fixed unshuffle tuple. -/
def orderedTerm (B : Word) (S : Fin (B.toList.length + 1) → Word) : H :=
  wordBasis (S 0) *
    (List.ofFn fun j : Fin B.toList.length => letterAction (S j.succ) (B.toList.get j)).prod

/-- Proposition 2.1's ordered original product on two basis words. -/
def starWord (A B : Word) : H :=
  ∑ f : Fin A.toList.length → Fin (B.toList.length + 1),
    orderedTerm B (fun j => slot A.toList f j)

/-- Applying the ordered term map to the actual primitive unshuffle gives `starWord`. -/
theorem starWord_unshuffle (A B : Word) :
    starWord A B =
      ((MonoidAlgebra.basis (Fin (B.toList.length + 1) → Word) ℚ).constr ℚ (orderedTerm B))
        (primitiveUnshuffle (B.toList.length + 1) A) := by
  classical
  have hu := primitiveUnshuffle_assignments (B.toList.length + 1) A.toList
  rw [FreeMonoid.ofList_toList] at hu
  rw [hu]
  simp only [map_sum, ← MonoidAlgebra.basis_apply,
    Module.Basis.constr_basis]
  rfl

/-- Rational bilinear extension of the ordered primitive-unshuffle product. -/
def star : H →ₗ[ℚ] H →ₗ[ℚ] H :=
  wordBasis.constr ℚ fun A => wordBasis.constr ℚ fun B =>
    ((MonoidAlgebra.basis (Fin (B.toList.length + 1) → Word) ℚ).constr ℚ (orderedTerm B))
      (primitiveUnshuffle (B.toList.length + 1) A)

/-- The primitive construction agrees with the literal assignment formula. -/
theorem star_basis (A B : Word) : star (wordBasis A) (wordBasis B) = starWord A B := by
  simp only [star, Module.Basis.constr_basis]
  exact (starWord_unshuffle A B).symm

private theorem slot_weight_sum (n : ℕ) (A : List ℕ) (f : Fin A.length → Fin n) :
    ∑ j : Fin n, weight (slot A f j) = weight (FreeMonoid.ofList A) := by
  classical
  induction A with
  | nil => simp [slot]
  | cons a A ih =>
    have hi := ih (fun i => f i.succ)
    simp only [slot]
    have he : ∀ j : Fin n,
        weight (if f 0 = j then FreeMonoid.of a * slot A (fun i => f i.succ) j
          else slot A (fun i => f i.succ) j) =
        (if j = f 0 then gamma a else 0) + weight (slot A (fun i => f i.succ) j) := by
      intro j
      by_cases h : f 0 = j
      · simp only [ite_eq_left h, ite_eq_left h.symm, weight_mul, weight_of]
      · simp only [ite_eq_right h, ite_eq_right (Ne.symm h), zero_add]
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', hi]
    simp [weight]

private theorem homogeneous_product (n : ℕ) (p : Fin n → H) (d : Fin n → ℕ)
    (hp : ∀ i, p i ∈ homogeneous (d i)) :
    (List.ofFn p).prod ∈ homogeneous (∑ i, d i) := by
  induction n with
  | zero =>
    change wordBasis (1 : Word) ∈ homogeneous 0
    exact homogeneous_basis 1
  | succ n ih =>
    simpa [List.ofFn_succ, Fin.sum_univ_succ] using
      homogeneous_mul (p 0) (List.ofFn fun i : Fin n => p i.succ).prod (d 0)
        (∑ i : Fin n, d i.succ) (hp 0) (ih (fun i : Fin n => p i.succ) (fun i : Fin n => d i.succ) (fun i : Fin n => hp i.succ))

private theorem above_product (k n : ℕ) (p : Fin n → H) (d : Fin n → ℕ)
    (hp : ∀ i, p i ∈ above k (d i)) :
    (List.ofFn p).prod ∈ above k (∑ i, d i) := by
  induction n with
  | zero =>
    change wordBasis (1 : Word) ∈ above k 0
    exact above_basis k 1
  | succ n ih =>
    simpa [List.ofFn_succ, Fin.sum_univ_succ] using
      above_mul k (p 0) (List.ofFn fun i : Fin n => p i.succ).prod (d 0)
        (∑ i : Fin n, d i.succ) (hp 0) (ih (fun i : Fin n => p i.succ) (fun i : Fin n => d i.succ) (fun i : Fin n => hp i.succ))

/-- The actual product has the sum of the two original input weights. -/
theorem starWord_homogeneous (A B : Word) :
    starWord A B ∈ homogeneous (weight A + weight B) := by
  classical
  apply (homogeneous _).sum_mem
  intro f hf
  let S : Fin (B.toList.length + 1) → Word := fun j => slot A.toList f j
  have hp := homogeneous_product B.toList.length
    (fun j => letterAction (S j.succ) (B.toList.get j))
    (fun j => weight (S j.succ) + gamma (B.toList.get j))
    (fun j => letterAction_homogeneous _ _)
  have hw := slot_weight_sum (B.toList.length + 1) A.toList f
  change (∑ j, weight (S j)) = weight A at hw
  rw [Fin.sum_univ_succ] at hw
  have hb : (∑ j : Fin B.toList.length, gamma (B.toList.get j)) = weight B := by
    simpa only [List.get_eq_getElem, weight] using
      (Fin.sum_univ_fun_getElem B.toList gamma)
  have hh := homogeneous_mul (wordBasis (S 0))
    (List.ofFn fun j => letterAction (S j.succ) (B.toList.get j)).prod
    (weight (S 0)) (∑ j : Fin B.toList.length, (weight (S j.succ) + gamma (B.toList.get j)))
    (homogeneous_basis _) hp
  rw [Finset.sum_add_distrib, hb, ← Nat.add_assoc, hw] at hh
  exact hh

/-- A supported output word has at least the right input's `k`-level. -/
theorem starWord_above (k : ℕ) (A B : Word) : starWord A B ∈ above k (level k B) := by
  classical
  apply (above k _).sum_mem
  intro f hf
  let S : Fin (B.toList.length + 1) → Word := fun j => slot A.toList f j
  have hp := above_product k B.toList.length
    (fun j => letterAction (S j.succ) (B.toList.get j))
    (fun j => level k (FreeMonoid.of (B.toList.get j)))
    (fun j => letterAction_above _ _ _)
  have hlist : ∀ l : List ℕ,
      (l.map (fun s => level k (FreeMonoid.of s))).sum = level k (FreeMonoid.ofList l) := by
    intro l
    induction l with
    | nil => exact (level_one k).symm
    | cons s l ih =>
      change level k (FreeMonoid.of s) + (l.map _).sum =
        level k (FreeMonoid.of s * FreeMonoid.ofList l)
      rw [level_mul, ih]
  have hb : (∑ j : Fin B.toList.length, level k (FreeMonoid.of (B.toList.get j))) =
      level k B := by
    calc
      _ = (B.toList.map (fun s => level k (FreeMonoid.of s))).sum := by
        simpa only [List.get_eq_getElem] using
          (Fin.sum_univ_fun_getElem B.toList (fun s => level k (FreeMonoid.of s)))
      _ = _ := hlist B.toList
  have hh := above_mul k (wordBasis (S 0))
    (List.ofFn fun j => letterAction (S j.succ) (B.toList.get j)).prod
    (level k (S 0)) (∑ j, level k (FreeMonoid.of (B.toList.get j)))
    (above_basis _ _) hp
  rw [hb] at hh
  intro w hw
  exact (Nat.le_add_left (level k B) (level k (S 0))).trans (hh w hw)

end D5.S1.Words.PostLie.AriWordProduct
