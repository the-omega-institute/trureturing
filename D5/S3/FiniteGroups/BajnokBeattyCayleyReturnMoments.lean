/- GID: D5/S3/FiniteGroups/BajnokBeattyCayleyReturnMoments
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyCayleyReturnMoments
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: The first closed-walk and adjacency-moment defect of the actual same-group Cayley graphs. -/

import D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!
proof_shape: first_return_moment_defect: content.
admission_basis: escape-witness.
escape_witness: the actual quotient return fibers are transported by the
published coordinate equivalences, then identified with inductively defined
simple-graph walks. Nonzero, distinct letters are proved from bounded second
coordinates, without assuming a short-kernel statement. Mathlib's adjacency
power theorem and the translation-independent word fiber give the trace defect.
No primality, return-count, trace, spectral, or separation assumption is added.
No literature novelty or open-problem claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments

open D5.S3.FiniteGroups.NearSquareLatticeRigidity
open D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open scoped BigOperators Classical

/-- The actual coordinate map for the `(1,9)` quotient. -/
def q19 (p D t : ℤ) : Plane →+ (ZMod p.natAbs × ZMod (p * D).natAbs) where
  toFun z :=
    (((-z 0 + z 1 : ℤ) : ZMod p.natAbs),
      ((-(3 * t) * z 0 + (3 * t - 1) * z 1 : ℤ) : ZMod (p * D).natAbs))
  map_zero' := by
    apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
      mul_zero, add_zero, neg_zero, Int.cast_zero]
  map_add' := by
    intro z w
    apply Prod.ext
    · change ((-(z 0 + w 0) + (z 1 + w 1) : ℤ) : ZMod p.natAbs) =
        ((-z 0 + z 1 : ℤ) : ZMod p.natAbs) + ((-w 0 + w 1 : ℤ) : ZMod p.natAbs)
      rw [← Int.cast_add]
      congr 1
      ring
    · change ((-(3 * t) * (z 0 + w 0) + (3 * t - 1) * (z 1 + w 1) : ℤ) :
        ZMod (p * D).natAbs) =
        ((-(3 * t) * z 0 + (3 * t - 1) * z 1 : ℤ) : ZMod (p * D).natAbs) +
        ((-(3 * t) * w 0 + (3 * t - 1) * w 1 : ℤ) : ZMod (p * D).natAbs)
      rw [← Int.cast_add]
      congr 1
      ring

/-- The actual coordinate map for the `(3,3)` quotient. -/
def q33 (p D t : ℤ) : Plane →+ (ZMod p.natAbs × ZMod (p * D).natAbs) where
  toFun z :=
    (((t * z 0 + (1 - t) * z 1 : ℤ) : ZMod p.natAbs),
      ((-(3 * t + 1) * z 0 + (3 * t - 2) * z 1 : ℤ) : ZMod (p * D).natAbs))
  map_zero' := by
    apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
      mul_zero, add_zero, Int.cast_zero]
  map_add' := by
    intro z w
    apply Prod.ext
    · change ((t * (z 0 + w 0) + (1 - t) * (z 1 + w 1) : ℤ) : ZMod p.natAbs) =
        ((t * z 0 + (1 - t) * z 1 : ℤ) : ZMod p.natAbs) +
        ((t * w 0 + (1 - t) * w 1 : ℤ) : ZMod p.natAbs)
      rw [← Int.cast_add]
      congr 1
      ring
    · change ((-(3 * t + 1) * (z 0 + w 0) + (3 * t - 2) * (z 1 + w 1) : ℤ) :
        ZMod (p * D).natAbs) =
        ((-(3 * t + 1) * z 0 + (3 * t - 2) * z 1 : ℤ) : ZMod (p * D).natAbs) +
        ((-(3 * t + 1) * w 0 + (3 * t - 2) * w 1 : ℤ) : ZMod (p * D).natAbs)
      rw [← Int.cast_add]
      congr 1
      ring

/-- The undirected simple Cayley graph of the two actual generator images.
The alphabet is the parent's `step`, in its original order. -/
def graph {G : Type*} [AddCommGroup G] (F : Plane →+ G) : SimpleGraph G :=
  SimpleGraph.addCayley
    (Set.range ![F (step 0), -F (step 0), F (step 2), -F (step 2)])

private lemma step_one : step 1 = -step 0 := by
  ext i
  fin_cases i <;> simp [step]

private lemma step_three : step 3 = -step 2 := by
  ext i
  fin_cases i <;> simp [step]

private lemma mapped_step_eq {G : Type*} [AddCommGroup G] (F : Plane →+ G) :
    (fun i => F (step i)) = ![F (step 0), -F (step 0), F (step 2), -F (step 2)] := by
  funext i
  fin_cases i <;> simp [step_one, step_three]

private lemma graph_eq_mapped {G : Type*} [AddCommGroup G] (F : Plane →+ G) :
    graph F = SimpleGraph.addCayley (Set.range (fun i => F (step i))) := by
  rw [mapped_step_eq]
  rfl

private lemma mapped_step_neg {G : Type*} [AddCommGroup G] (F : Plane →+ G) :
    ∀ i : Fin 4, ∃ j : Fin 4, F (step j) = -F (step i) := by
  intro i
  fin_cases i
  · exact ⟨1, by simp [step_one]⟩
  · exact ⟨0, by simp [step_one]⟩
  · exact ⟨3, by simp [step_three]⟩
  · exact ⟨2, by simp [step_three]⟩

private abbrev EndpointWords {G : Type*} [AddCommGroup G]
    (s : Fin 4 → G) (x y : G) (l : ℕ) :=
  {w : Fin l → Fin 4 // x + (∑ i, s (w i)) = y}

private abbrev LengthWalks {V : Type*} (C : SimpleGraph V) (x y : V) (l : ℕ) :=
  {w : C.Walk x y // w.length = l}

private lemma adj_iff_step {G : Type*} [AddCommGroup G] (s : Fin 4 → G)
    (hzero : ∀ i, s i ≠ 0) (hneg : ∀ i, ∃ j, s j = -s i) (x y : G) :
    (SimpleGraph.addCayley (Set.range s)).Adj x y ↔ ∃ i, x + s i = y := by
  rw [SimpleGraph.addCayley_adj']
  constructor
  · rintro ⟨_, g, ⟨i, rfl⟩, h | h⟩
    · exact ⟨i, h⟩
    · obtain ⟨j, hj⟩ := hneg i
      refine ⟨j, ?_⟩
      rw [h, hj]
      simp only [add_assoc, add_neg_cancel, add_zero]
  · rintro ⟨i, hi⟩
    refine ⟨?_, s i, ⟨i, rfl⟩, Or.inl hi⟩
    intro hxy
    apply hzero i
    exact add_left_cancel
      (show x + s i = x + 0 by simpa only [add_zero] using hi.trans hxy.symm)

private def letterNeighborEquiv {G : Type*} [AddCommGroup G] (s : Fin 4 → G)
    (hinj : Function.Injective s) (hzero : ∀ i, s i ≠ 0)
    (hneg : ∀ i, ∃ j, s j = -s i) (x : G) :
    Fin 4 ≃ (SimpleGraph.addCayley (Set.range s)).neighborSet x :=
  Equiv.ofBijective
    (fun i => ⟨x + s i, (adj_iff_step s hzero hneg x _).2 ⟨i, rfl⟩⟩)
    ⟨by
      intro i j hij
      exact hinj (add_left_cancel (congrArg Subtype.val hij)),
     by
      intro z
      obtain ⟨i, hi⟩ := (adj_iff_step s hzero hneg x z.val).1 z.property
      exact ⟨i, Subtype.ext hi⟩⟩

private def wordHeadEquiv {G : Type*} [AddCommGroup G]
    (s : Fin 4 → G) (x y : G) (l : ℕ) :
    EndpointWords s x y (l + 1) ≃ Σ i : Fin 4, EndpointWords s (x + s i) y l where
  toFun w := ⟨w.val 0, ⟨Fin.tail w.val, by
    simpa only [Fin.sum_univ_succ, Fin.tail, add_assoc] using w.property⟩⟩
  invFun v := ⟨Fin.cons v.1 v.2.val, by
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]
      using v.2.property⟩
  left_inv w := by
    apply Subtype.ext
    exact Fin.cons_self_tail w.val
  right_inv := by
    rintro ⟨i, w⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl

private def walkHeadEquiv {V : Type*} (C : SimpleGraph V) (x y : V) (l : ℕ) :
    LengthWalks C x y (l + 1) ≃ Σ z : C.neighborSet x, LengthWalks C z.val y l where
  toFun := by
    rintro ⟨q, hq⟩
    cases q with
    | nil => simp at hq
    | @cons u z v h p =>
      exact ⟨⟨z, h⟩, ⟨p, Nat.succ.inj hq⟩⟩
  invFun v := ⟨SimpleGraph.Walk.cons v.1.property v.2.val, by
    exact congrArg Nat.succ v.2.property⟩
  left_inv := by
    rintro ⟨q, hq⟩
    cases q with
    | nil => simp at hq
    | cons h p => rfl
  right_inv := by
    rintro ⟨⟨z, h⟩, ⟨p, hp⟩⟩
    rfl

private def zeroEquiv {G : Type*} [AddCommGroup G] (s : Fin 4 → G) (x y : G) :
    EndpointWords s x y 0 ≃ LengthWalks (SimpleGraph.addCayley (Set.range s)) x y 0 where
  toFun w := by
    have hxy : x = y := by simpa using w.property
    subst y
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  invFun q := ⟨Fin.elim0, by
    simpa using SimpleGraph.Walk.eq_of_length_eq_zero q.property⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  right_inv := by
    rintro ⟨q, hq⟩
    have hxy : x = y := SimpleGraph.Walk.eq_of_length_eq_zero hq
    subst y
    have hnil : q = SimpleGraph.Walk.nil :=
      SimpleGraph.Walk.eq_nil_iff_nil.mpr (SimpleGraph.Walk.length_eq_zero_iff.mp hq)
    subst q
    rfl

private def endpointEquiv {G : Type*} [AddCommGroup G] (s : Fin 4 → G)
    (hinj : Function.Injective s) (hzero : ∀ i, s i ≠ 0)
    (hneg : ∀ i, ∃ j, s j = -s i) (l : ℕ) :
    ∀ x y, EndpointWords s x y l ≃
      LengthWalks (SimpleGraph.addCayley (Set.range s)) x y l := by
  induction l with
  | zero => exact zeroEquiv s
  | succ l ih =>
    intro x y
    let C := SimpleGraph.addCayley (Set.range s)
    let e : Fin 4 ≃ C.neighborSet x := letterNeighborEquiv s hinj hzero hneg x
    let tails : (Σ i : Fin 4, LengthWalks C (x + s i) y l) ≃
        (Σ z : C.neighborSet x, LengthWalks C z.val y l) :=
      Equiv.sigmaCongr e (fun _ => Equiv.refl _)
    exact (wordHeadEquiv s x y l).trans
      ((Equiv.sigmaCongrRight (fun i => ih (x + s i) y)).trans
        (tails.trans (walkHeadEquiv C x y l).symm))

private def returnEndpointEquiv {G : Type*} [AddCommGroup G]
    (F : Plane →+ G) (x : G) (l : ℕ) :
    ReturnWords F l ≃ EndpointWords (fun i => F (step i)) x x l where
  toFun w := ⟨w.val, by
    have hz : (∑ i, F (step (w.val i))) = 0 := by
      simpa only [endpoint, map_sum] using w.property
    rw [hz, add_zero]⟩
  invFun w := ⟨w.val, by
    have hz : (∑ i, F (step (w.val i))) = 0 :=
      add_left_cancel
        (show x + (∑ i, F (step (w.val i))) = x + 0 by
          simpa only [add_zero] using w.property)
    simpa only [endpoint, map_sum] using hz⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def returnWordWalkEquiv {G : Type*} [AddCommGroup G]
    (F : Plane →+ G) (hinj : Function.Injective (fun i => F (step i)))
    (hzero : ∀ i, F (step i) ≠ 0) (x : G) (l : ℕ) :
    ReturnWords F l ≃ LengthWalks (graph F) x x l := by
  rw [graph_eq_mapped]
  exact (returnEndpointEquiv F x l).trans
    (endpointEquiv (fun i => F (step i)) hinj hzero (mapped_step_neg F) l x x)

private theorem walk_card_eq_W {G : Type*} [AddCommGroup G]
    (F : Plane →+ G) (hinj : Function.Injective (fun i => F (step i)))
    (hzero : ∀ i, F (step i) ≠ 0) (x : G) (l : ℕ) :
    Nat.card (LengthWalks (graph F) x x l) = W F l :=
  (Nat.card_congr (returnWordWalkEquiv F hinj hzero x l)).symm

private theorem trace_eq_card_mul_W {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (F : Plane →+ G) [DecidableRel (graph F).Adj] (hinj : Function.Injective (fun i => F (step i)))
    (hzero : ∀ i, F (step i) ≠ 0) (l : ℕ) :
    Matrix.trace ((graph F).adjMatrix ℂ ^ l) =
      (Fintype.card G : ℂ) * (W F l : ℂ) := by
  have hdiag (x : G) : ((graph F).adjMatrix ℂ ^ l) x x = (W F l : ℂ) := by
    rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
    have hc : Fintype.card (LengthWalks (graph F) x x l) = W F l := by
      rw [← Nat.card_eq_fintype_card]
      exact walk_card_eq_W F hinj hzero x l
    exact_mod_cast hc
  simp only [Matrix.trace, Matrix.diag_apply, hdiag, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

private def returnWordsMapEquiv {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (F : Plane →+ G) (Q : Plane →+ K) (e : G ≃+ K)
    (he : ∀ z, e (F z) = Q z) (l : ℕ) : ReturnWords F l ≃ ReturnWords Q l where
  toFun w := ⟨w.val, by rw [← he, w.property, map_zero]⟩
  invFun w := ⟨w.val, by
    apply e.injective
    rw [he, w.property, map_zero]⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem parameter_bounds (p t : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t) :
    let m : ℤ := 6 * t - 1
    let D : ℤ := (m ^ 2 - 9)/2
    0 < D ∧ 6 * t + 2 < D ∧ D < p * D := by
  dsimp only
  have hnum : (6 * t - 1) ^ 2 - 9 = 2 * ((3 * t + 1) * (6 * t - 4)) := by ring
  have hfactor : ((6 * t - 1) ^ 2 - 9)/2 = (3 * t + 1) * (6 * t - 4) := by
    rw [hnum]
    omega
  have hbound : 8 * (3 * t + 1) ≤ ((6 * t - 1) ^ 2 - 9)/2 := by
    rw [hfactor]
    nlinarith
  have hDpos : 0 < ((6 * t - 1) ^ 2 - 9)/2 := by omega
  have hmul : ((6 * t - 1) ^ 2 - 9)/2 < p * (((6 * t - 1) ^ 2 - 9)/2) := by
    nlinarith
  exact ⟨hDpos, by omega, hmul⟩

private theorem vertices_finite (p t : ℤ) (hp3 : 3 ≤ p) (ht : 2 ≤ t) :
    Finite (ZMod p.natAbs × ZMod (p * (((6 * t - 1) ^ 2 - 9)/2)).natAbs) := by
  have hp : 0 < p := by omega
  have hD := (parameter_bounds p t hp3 ht).1
  letI : NeZero p.natAbs := ⟨Int.natAbs_ne_zero.mpr hp.ne'⟩
  letI : NeZero (p * (((6 * t - 1) ^ 2 - 9)/2)).natAbs :=
    ⟨Int.natAbs_ne_zero.mpr (mul_pos hp hD).ne'⟩
  infer_instance

private lemma cast_eq_of_bounds (M B a b : ℤ) (hM : 2 * B < M)
    (ha : -B ≤ a ∧ a ≤ B) (hb : -B ≤ b ∧ b ≤ B)
    (he : (a : ZMod M.natAbs) = (b : ZMod M.natAbs)) : a = b := by
  have hMpos : 0 < M := by omega
  have hdvd : M ∣ b - a := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub a b M.natAbs).mp he
    simpa only [Int.natCast_natAbs, abs_of_pos hMpos] using h
  have hab : |b - a| < M := by rw [abs_lt]; constructor <;> omega
  have hz : |b - a| = 0 :=
    Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) hab ((dvd_abs _ _).mpr hdvd)
  have := abs_eq_zero.mp hz
  omega

private lemma separated_of_second {L : ℕ} (M B : ℤ)
    (s : Fin 4 → (ZMod L × ZMod M.natAbs)) (c : Fin 4 → ℤ)
    (hM : 2 * B < M) (hB : 0 ≤ B)
    (hc : ∀ i, -B ≤ c i ∧ c i ≤ B) (hcinj : Function.Injective c)
    (hczero : ∀ i, c i ≠ 0) (hs : ∀ i, (s i).2 = (c i : ZMod M.natAbs)) :
    Function.Injective s ∧ ∀ i, s i ≠ 0 := by
  constructor
  · intro i j hij
    apply hcinj
    apply cast_eq_of_bounds M B (c i) (c j) hM (hc i) (hc j)
    simpa only [hs] using congrArg Prod.snd hij
  · intro i hi
    apply hczero i
    apply cast_eq_of_bounds M B (c i) 0 hM (hc i) (by omega)
    simpa only [hs, Prod.snd_zero, Int.cast_zero] using congrArg Prod.snd hi

private theorem actual_steps_separated (p D t : ℤ) (ht : 2 ≤ t)
    (hM : 6 * t + 2 < p * D) :
    (Function.Injective (fun i => q19 p D t (step i)) ∧
      ∀ i, q19 p D t (step i) ≠ 0) ∧
    (Function.Injective (fun i => q33 p D t (step i)) ∧
      ∀ i, q33 p D t (step i) ≠ 0) := by
  constructor
  · apply separated_of_second (p * D) (3 * t + 1)
      (fun i => q19 p D t (step i)) ![-3 * t, 3 * t, 3 * t - 1, 1 - 3 * t]
    · omega
    · omega
    · intro i
      fin_cases i <;> simp <;> omega
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i
      fin_cases i <;> simp <;> omega
    · intro i
      fin_cases i <;> simp [q19, step]
  · apply separated_of_second (p * D) (3 * t + 1)
      (fun i => q33 p D t (step i)) ![-(3 * t + 1), 3 * t + 1, 3 * t - 2, 2 - 3 * t]
    · omega
    · omega
    · intro i
      fin_cases i <;> simp <;> omega
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · intro i
      fin_cases i <;> simp <;> omega
    · intro i
      fin_cases i <;> simp [q33, step]

/-- For all odd integers `p ≥ 3` (including composite ones) and `t ≥ 2`, the
two actual simple Cayley graphs on `H` have equal rooted closed-walk counts
and complex adjacency traces below `n = p * (6*t-4)`. At `n`, the second graph
has exactly two extra walks at every root and trace defect `2 * p^2 * D`.
The finite instance is constructed from the displayed parameters. -/
theorem first_return_moment_defect (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6 * t - 1
    let D : ℤ := (m ^ 2 - 9)/2
    let H := ZMod p.natAbs × ZMod (p * D).natAbs
    let N : ℤ := p ^ 2 * D
    let n : ℕ := (p * (m - 3)).toNat
    letI : Finite H := vertices_finite p t hp3 ht
    letI : Fintype H := Fintype.ofFinite H
    let C19 : SimpleGraph H := graph (q19 p D t)
    let C33 : SimpleGraph H := graph (q33 p D t)
    let A19 : Matrix H H ℂ := C19.adjMatrix ℂ
    let A33 : Matrix H H ℂ := C33.adjMatrix ℂ
    (Nat.card H : ℤ) = N ∧
    (∀ k : ℕ, k < n → ∀ x : H,
      Nat.card {w : C19.Walk x x // w.length = k} =
        Nat.card {w : C33.Walk x x // w.length = k}) ∧
    (∀ x : H, Nat.card {w : C33.Walk x x // w.length = n} =
      Nat.card {w : C19.Walk x x // w.length = n} + 2) ∧
    (∀ k : ℕ, k < n → Matrix.trace (A19 ^ k) = Matrix.trace (A33 ^ k)) ∧
    Matrix.trace (A33 ^ n) - Matrix.trace (A19 ^ n) = 2 * (N : ℂ) := by
  classical
  let m : ℤ := 6 * t - 1
  let D : ℤ := (m ^ 2 - 9)/2
  let H := ZMod p.natAbs × ZMod (p * D).natAbs
  let N : ℤ := p ^ 2 * D
  let n : ℕ := (p * (m - 3)).toNat
  letI : Finite H := vertices_finite p t hp3 ht
  letI : Fintype H := Fintype.ofFinite H
  let Q19 : Plane →+ H := q19 p D t
  let Q33 : Plane →+ H := q33 p D t
  change (Nat.card H : ℤ) = N ∧
    (∀ k : ℕ, k < n → ∀ x : H,
      Nat.card (LengthWalks (graph Q19) x x k) =
        Nat.card (LengthWalks (graph Q33) x x k)) ∧
    (∀ x : H, Nat.card (LengthWalks (graph Q33) x x n) =
      Nat.card (LengthWalks (graph Q19) x x n) + 2) ∧
    (∀ k : ℕ, k < n → Matrix.trace ((graph Q19).adjMatrix ℂ ^ k) =
      Matrix.trace ((graph Q33).adjMatrix ℂ ^ k)) ∧
    Matrix.trace ((graph Q33).adjMatrix ℂ ^ n) -
      Matrix.trace ((graph Q19).adjMatrix ℂ ^ n) = 2 * (N : ℂ)
  have hp : 0 < p := by omega
  have hDpos : 0 < D := (parameter_bounds p t hp3 ht).1
  have hbounds := (parameter_bounds p t hp3 ht).2
  have hM : 6 * t + 2 < p * D := hbounds.1.trans hbounds.2
  obtain ⟨⟨hinj19, hzero19⟩, ⟨hinj33, hzero33⟩⟩ := actual_steps_separated p D t ht hM
  let v119 : Plane := ![p * (m - 1)/2, p * (m + 1)/2]
  let v219 : Plane := ![p * (m - 9)/2, -(p * (m + 9)/2)]
  let v133 : Plane := ![p * (m - 3)/2, p * (m + 3)/2]
  let v233 : Plane := ![p * (m - 3)/2, -(p * (m + 3)/2)]
  let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
  let G19 := Plane ⧸ K19
  let G33 := Plane ⧸ K33
  let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
  obtain ⟨e19, e33, he19, he33, hshort, hfirst⟩ := first_return_defect p t hp3 hpo ht
  have he19' : ∀ z : Plane, e19 (F19 z) = Q19 z := he19
  have he33' : ∀ z : Plane, e33 (F33 z) = Q33 z := he33
  have hW19 (l : ℕ) : W Q19 l = W F19 l :=
    (Nat.card_congr (returnWordsMapEquiv F19 Q19 e19 he19' l)).symm
  have hW33 (l : ℕ) : W Q33 l = W F33 l :=
    (Nat.card_congr (returnWordsMapEquiv F33 Q33 e33 he33' l)).symm
  have hshortQ (k : ℕ) (hk : k < n) : W Q19 k = W Q33 k := by
    rw [hW19, hW33]
    exact hshort k hk
  have hfirstQ : W Q33 n = W Q19 n + 2 := by
    rw [hW19, hW33]
    exact hfirst
  have hcardH : (Nat.card H : ℤ) = N := by
    simp only [H, N, Nat.card_prod, Nat.card_zmod, Nat.cast_mul,
      Int.natCast_natAbs, abs_of_pos hp, abs_of_pos (mul_pos hp hDpos)]
    ring
  refine ⟨hcardH, ?_, ?_, ?_, ?_⟩
  · intro k hk x
    rw [walk_card_eq_W Q19 hinj19 hzero19, walk_card_eq_W Q33 hinj33 hzero33]
    exact hshortQ k hk
  · intro x
    rw [walk_card_eq_W Q19 hinj19 hzero19, walk_card_eq_W Q33 hinj33 hzero33]
    exact hfirstQ
  · intro k hk
    rw [trace_eq_card_mul_W Q19 hinj19 hzero19,
      trace_eq_card_mul_W Q33 hinj33 hzero33, hshortQ k hk]
  · rw [trace_eq_card_mul_W Q33 hinj33 hzero33,
      trace_eq_card_mul_W Q19 hinj19 hzero19]
    have hcardC : (Fintype.card H : ℂ) = (N : ℂ) := by
      have hc : (Fintype.card H : ℤ) = N := by
        simpa only [Nat.card_eq_fintype_card] using hcardH
      exact_mod_cast hc
    have hfirstC : (W Q33 n : ℂ) = (W Q19 n : ℂ) + 2 := by exact_mod_cast hfirstQ
    rw [hcardC, hfirstC]
    ring

end D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments
