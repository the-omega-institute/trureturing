/- GID: D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Integer translations, Euclidean block addresses, legal splices and exact counted-edge coordinates supply the actual fixed-block construction and rigidity proofs. -/

import D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
import D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Mathlib.Logic.Function.Conjugate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

universe u v w
section Histories
variable {V : Type u} {E : Type v} {D : Type w}
variable {G : DirectedMultigraph V E} {F : DirectedMultigraph V D}

/-- The exact integer translation of the actual legal history. -/
def translate (G : DirectedMultigraph V E) (a : ℤ) (x : History G) : History G :=
  ⟨fun i => x.val (i + a), fun i => by
    simpa [add_assoc, add_comm, add_left_comm] using x.property (i + a)⟩

@[simp] private theorem translate_zero (x : History G) : translate G 0 x = x := by
  apply Subtype.ext
  funext i
  simp [translate]

@[simp] private theorem translate_add (a b : ℤ) (x : History G) :
    translate G a (translate G b x) = translate G (a + b) x := by
  apply Subtype.ext
  funext i
  simp [translate, add_assoc]

/-- Only the original one-step commutation is assumed. -/
theorem translate_commutation
    (h : History G → History F)
    (hstep : ∀ x, h (shift G x) = shift F (h x)) :
    ∀ a x, h (translate G a x) = translate F a (h x) := by
  have one : ∀ x, h (translate G 1 x) = translate F 1 (h x) := hstep
  have negOne : ∀ x, h (translate G (-1) x) = translate F (-1) (h x) := by
    intro x
    have t := congrArg (translate F (-1)) (one (translate G (-1) x))
    simpa using t.symm
  have pos : ∀ n : ℕ, ∀ x, h (translate G (n : ℤ) x) = translate F (n : ℤ) (h x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      calc
        h (translate G ((n + 1 : ℕ) : ℤ) x) =
            h (translate G 1 (translate G (n : ℤ) x)) := by
          congr 1
          rw [translate_add]
          congr 1
          omega
        _ = translate F 1 (h (translate G (n : ℤ) x)) := one _
        _ = translate F ((n + 1 : ℕ) : ℤ) (h x) := by
          rw [ih, translate_add]
          congr 1
          omega
  have neg : ∀ n : ℕ, ∀ x, h (translate G (-(n : ℤ)) x) =
      translate F (-(n : ℤ)) (h x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      calc
        h (translate G (-((n + 1 : ℕ) : ℤ)) x) =
            h (translate G (-1) (translate G (-(n : ℤ)) x)) := by
          congr 1
          rw [translate_add]
          congr 1
          omega
        _ = translate F (-1) (h (translate G (-(n : ℤ)) x)) := negOne _
        _ = translate F (-((n + 1 : ℕ) : ℤ)) (h x) := by
          rw [ih, translate_add]
          congr 1
          omega
  intro a x
  cases a with
  | ofNat n => exact pos n x
  | negSucc n => simpa [Int.negSucc_eq] using neg (n + 1) x

/-- Euclidean addresses, including every negative position. -/
def blockAddress {k : ℕ} (hk : 0 < k) (i : ℤ) : ℤ × Fin k :=
  (i / (k : ℤ), ⟨(i % (k : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg i (show (k : ℤ) ≠ 0 by omega)
    have hlt := Int.emod_lt_of_pos i (show (0 : ℤ) < k by omega)
    omega⟩)

def assemble (k : ℕ) (p : ℤ × Fin k) : ℤ := p.1 * (k : ℤ) + p.2.val

private theorem assemble_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (assemble k) := by
  intro a b hab
  rcases a with ⟨a,r⟩
  rcases b with ⟨b,s⟩
  have hp : (0 : ℤ) < k := by omega
  have hr : (0 : ℤ) ≤ r.val ∧ (r.val : ℤ) < k := by omega
  have hs : (0 : ℤ) ≤ s.val ∧ (s.val : ℤ) < k := by omega
  change a * (k : ℤ) + r.val = b * (k : ℤ) + s.val at hab
  have qab : a = b := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hd : 1 ≤ b - a := by omega
      have hm : (k : ℤ) ≤ (b - a) * k := by nlinarith
      nlinarith
    · have hd : 1 ≤ a - b := by omega
      have hm : (k : ℤ) ≤ (a - b) * k := by nlinarith
      nlinarith
  subst b
  have rs : r = s := by apply Fin.ext; omega
  subst s
  rfl

theorem assemble_address {k : ℕ} (hk : 0 < k) (i : ℤ) :
    assemble k (blockAddress hk i) = i := by
  have hnonneg := Int.emod_nonneg i (show (k : ℤ) ≠ 0 by omega)
  have hdiv := Int.ediv_mul_add_emod i (k : ℤ)
  simp only [assemble, blockAddress, Int.toNat_of_nonneg hnonneg]
  nlinarith

theorem address_assemble {k : ℕ} (hk : 0 < k) (p : ℤ × Fin k) :
    blockAddress hk (assemble k p) = p :=
  assemble_injective hk (assemble_address hk (assemble k p))

/-- Past from x, future from y, joined at their shared actual edge. -/
def splice (x y : History G) (hzero : x.val 0 = y.val 0) : History G :=
  ⟨fun i => if i ≤ 0 then x.val i else y.val i, by
    intro i
    by_cases hi : i ≤ 0
    · by_cases hnext : i + 1 ≤ 0
      · simpa only [if_pos hi, if_pos hnext] using x.property i
      · have iz : i = 0 := by omega
        subst i
        simpa only [le_refl, if_true, show ¬ (1 : ℤ) ≤ 0 by omega, if_false,
          zero_add, hzero] using y.property 0
    · have hnext : ¬ i + 1 ≤ 0 := by omega
      simpa only [if_neg hi, if_neg hnext] using y.property i⟩

theorem shift_iterate_translate {V E : Type*} (G : DirectedMultigraph V E)
    (m : ℕ) (x : History G) : (shift G)^[m] x = translate G (m:ℤ) x := by
  induction m with
  | zero => exact (translate_zero x).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih]
    apply Subtype.ext
    funext i
    change x.val (i+1+(m:ℤ)) = x.val (i+((m+1:ℕ):ℤ))
    apply congrArg x.val
    simp only [Int.natCast_add, Int.natCast_one]
    omega

section Finite
variable [Fintype V] [Fintype E] [Fintype D] [DecidableEq V]

theorem edge_occurs (hG : Essential G) (e : E) :
    ∃ x : History G, x.val 0 = e := by
  let w : LegalWord G 1 := ⟨fun _ => e, by intro i hi; omega⟩
  obtain ⟨x, hx⟩ := exists_history_containing G hG w (by decide)
  exact ⟨x, by simpa [w] using hx ⟨0, by decide⟩⟩

end Finite
end Histories

section CountedEdges
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)
variable {H : Type u} [Group H] [Fintype H] {n : ℕ}

private def edgeCoordinates (A : GroupMat H n n) : Edge A ≃
    (Σ i : Fin n, Σ j : Fin n, Σ g : H, Fin ((A i j).coeff g)) where
  toFun e := ⟨e.source, e.target, e.label, e.number⟩
  invFun e := ⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨i,j,g,t⟩; rfl

theorem edge_eq_of_coordinates {A : GroupMat H n n} {a b : Edge A}
    (hs : a.source = b.source) (ht : a.target = b.target)
    (hl : a.label = b.label) (hn : a.number.val = b.number.val) : a = b := by
  cases a with
  | mk i j g t =>
    cases b with
    | mk i' j' g' t' =>
      dsimp at hs ht hl hn
      subst i'
      subst j'
      subst g'
      have h : t = t' := Fin.ext hn
      subst t'
      rfl

private noncomputable instance edgeFintype (A : GroupMat H n n) : Fintype (Edge A) :=
  Fintype.ofEquiv _ (edgeCoordinates A).symm

end CountedEdges

end D5.S3.ConceptDynamics.Coding.FixedBlockRigidity.BlockCoordinates
