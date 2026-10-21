/- GID: D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.claim; result=D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.result; claim=D5/S3/Combinatorics/Lattices/ShalaCosetLikeAtomisticLattice.claim
   digest: A twelve-element lattice refutes the universal coset-like implication in Question 7.4. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#19710; Refuted)
proof_shape: J: bind-only; consumer: Jx, index, claim
proof_shape: Jx: bind-only; consumer: index, StronglyCosetLike, Counterexample.J_eq, Counterexample.Jx_card
proof_shape: index: bind-only; consumer: P
proof_shape: P: bind-only; consumer: WeaklyCosetLike, Counterexample.zeta_formula
proof_shape: StronglyCosetLike: bind-only; consumer: claim, Counterexample.not_strong
proof_shape: WeaklyCosetLike: bind-only; consumer: claim, Counterexample.weak
proof_shape: claim: bind-only; consumer: result
proof_shape: below: bind-only; consumer: Counterexample instance declarations
proof_shape: Counterexample private declarations: bind-only; consumer: result through Counterexample.not_strong and Counterexample.weak
Direct frozen dependencies: none (the module imports no D5 modules).
The claim body is written with its source convention inlined; the proofs use the same definitions directly.
The public result is the designated refutation result (basis=refutes) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Irreducible
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option autoImplicit false

namespace D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice

variable {L : Type} [Lattice L] [BoundedOrder L] [Fintype L] [DecidableEq L] [DecidableLE L]

/-- `J`: the join-irreducible elements (Mathlib's `SupIrred`). -/
noncomputable def J (L : Type) [Lattice L] [BoundedOrder L] [Fintype L] : Finset L := by
  classical exact Finset.univ.filter SupIrred

/-- `J_x = {j ∈ J : j ≤ x}`. -/
noncomputable def Jx (x : L) : Finset L := by
  classical exact (J L).filter (· ≤ x)

/-- `[J : J_x] = |J| / |J_x|`. -/
noncomputable def index (x : L) : ℚ :=
  ((J L).card : ℚ) / ((Jx x).card : ℚ)

/-- Equation (3.1): `P(L, s) = ∑_{x ≠ 0̂} μ(x, 1̂) [J : J_x]^{−s}`, with `μ` Mathlib's Möbius function. -/
noncomputable def P [LocallyFiniteOrder L] (s : ℂ) : ℂ :=
  ∑ x ∈ Finset.univ.erase (⊥ : L), (IncidenceAlgebra.mu ℤ x (⊤ : L) : ℂ) * ((index x : ℚ) : ℂ) ^ (-s)

/-- Definition 5.1. -/
def StronglyCosetLike : Prop :=
  ∀ x : L, x ≠ ⊥ → (Jx x).card ∣ (J L).card

/-- Definition 5.2: `P(L, s)` is a finite ordinary Dirichlet series `∑_{n=1}^{N} a_n n^{−s}`. -/
def WeaklyCosetLike [LocallyFiniteOrder L] : Prop :=
  ∃ (N : ℕ) (a : ℕ → ℤ), ∀ s : ℂ, P (L := L) s = ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * (n : ℂ) ^ (-s)

/-- The statement whose failure answers Question 7.4 positively: every weakly coset-like atomistic finite lattice is
strongly coset-like. -/
def claim : Prop :=
  ∀ (L : Type) [Lattice L] [BoundedOrder L] [Fintype L] [DecidableEq L] [DecidableLE L] [LocallyFiniteOrder L],
    IsAtomistic L → WeaklyCosetLike (L := L) → StronglyCosetLike (L := L)

end D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice

namespace D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice.Counterexample
private inductive E
  | bot | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | x | a | top
  deriving DecidableEq
open E
private instance : Fintype E where
  elems := {bot, p0, p1, p2, p3, p4, p5, p6, p7, x, a, top}
  complete := by intro u; cases u <;> simp

private def below : E → E → Prop
  | bot, _ => True
  | _, top => True
  | p0, x | p1, x | p2, x => True
  | p0, a | p1, a | p2, a | p3, a | x, a => True
  | u, v => u = v
private instance : DecidableRel below := by intro u v; cases u <;> cases v <;> unfold below <;> infer_instance
private instance : PartialOrder E where
  le := below
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
private instance : DecidableLE E := inferInstanceAs (DecidableRel below)

private instance : DecidableLT E := decidableLTOfDecidableLE

private def join (u v : E) : E :=
  if u ≤ v then v else if v ≤ u then u else
  match u, v with
  | p0, p1 | p0, p2 | p1, p0 | p1, p2 | p2, p0 | p2, p1 => x
  | p0, p3 | p1, p3 | p2, p3 | x, p3 | p3, p0 | p3, p1 | p3, p2 | p3, x => a
  | _, _ => top

private def meet (u v : E) : E := if u ≤ v then u else if v ≤ u then v else bot
private instance : Lattice E where
  sup := join
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf := meet
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
private instance : BoundedOrder E where
  top := top
  le_top := by decide
  bot := bot
  bot_le := by decide
private instance : LocallyFiniteOrder E := Fintype.toLocallyFiniteOrder

private theorem atoms : ∀ u : E, IsAtom u ↔ u = p0 ∨ u = p1 ∨ u = p2 ∨ u = p3 ∨ u = p4 ∨ u = p5 ∨ u = p6 ∨ u = p7 := by
  unfold IsAtom
  decide
private theorem atomistic : IsAtomistic E := by
  constructor
  intro b
  refine ⟨{u | IsAtom u ∧ u ≤ b}, ?_, ?_⟩
  · change (∀ u : E, IsAtom u ∧ u ≤ b → u ≤ b) ∧ ∀ c : E, (∀ u : E, IsAtom u ∧ u ≤ b → u ≤ c) → b ≤ c
    revert b
    simp only [atoms]
    decide
  · intro u h
    exact h.1
private theorem irreducibles : ∀ u : E, SupIrred u ↔ u = p0 ∨ u = p1 ∨ u = p2 ∨ u = p3 ∨ u = p4 ∨ u = p5 ∨ u = p6 ∨ u = p7 := by
  unfold SupIrred IsMin
  decide


open D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice

private lemma J_eq : J E = {p0, p1, p2, p3, p4, p5, p6, p7} := by
  classical
  ext u
  simp [J, irreducibles]

private def atomCount : E → ℕ
  | bot => 0
  | x => 3
  | a => 4
  | top => 8
  | _ => 1
private lemma Jx_card (u : E) : (Jx u).card = atomCount u := by
  classical
  cases u <;> simp [Jx, J_eq, Finset.filter_insert, Finset.filter_singleton, below, atomCount, LE.le]

private lemma J_card : (J E).card = 8 := by rw [J_eq]; decide

private lemma mu_a : IncidenceAlgebra.mu ℤ a top = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : a ≠ top)]
  have hi : Finset.Ioc a top = {top} := Finset.val_eq_singleton_iff.mp rfl
  rw [hi]
  simp
private lemma mu_x : IncidenceAlgebra.mu ℤ x top = 0 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : x ≠ top)]
  have hi : Finset.Ioc x top = {a, top} := Finset.val_inj.mp rfl
  rw [hi]
  simp [mu_a]
private lemma mu_p0 : IncidenceAlgebra.mu ℤ p0 top = 0 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p0 ≠ top)]
  have hi : Finset.Ioc p0 top = {x, a, top} := Finset.val_inj.mp rfl
  rw [hi]
  simp [mu_x, mu_a]
private lemma mu_p1 : IncidenceAlgebra.mu ℤ p1 top = 0 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p1 ≠ top)]
  have hi : Finset.Ioc p1 top = {x, a, top} := Finset.val_inj.mp rfl
  rw [hi]
  simp [mu_x, mu_a]
private lemma mu_p2 : IncidenceAlgebra.mu ℤ p2 top = 0 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p2 ≠ top)]
  have hi : Finset.Ioc p2 top = {x, a, top} := Finset.val_inj.mp rfl
  rw [hi]
  simp [mu_x, mu_a]
private lemma mu_p3 : IncidenceAlgebra.mu ℤ p3 top = 0 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p3 ≠ top)]
  have hi : Finset.Ioc p3 top = {a, top} := Finset.val_inj.mp rfl
  rw [hi]
  simp [mu_a]
private lemma mu_p4 : IncidenceAlgebra.mu ℤ p4 top = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p4 ≠ top)]
  have hi : Finset.Ioc p4 top = {top} := Finset.val_eq_singleton_iff.mp rfl
  rw [hi]
  simp
private lemma mu_p5 : IncidenceAlgebra.mu ℤ p5 top = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p5 ≠ top)]
  have hi : Finset.Ioc p5 top = {top} := Finset.val_eq_singleton_iff.mp rfl
  rw [hi]
  simp
private lemma mu_p6 : IncidenceAlgebra.mu ℤ p6 top = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p6 ≠ top)]
  have hi : Finset.Ioc p6 top = {top} := Finset.val_eq_singleton_iff.mp rfl
  rw [hi]
  simp
private lemma mu_p7 : IncidenceAlgebra.mu ℤ p7 top = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne (by decide : p7 ≠ top)]
  have hi : Finset.Ioc p7 top = {top} := Finset.val_eq_singleton_iff.mp rfl
  rw [hi]
  simp

private lemma not_strong : ¬ StronglyCosetLike (L := E) := by
  intro h
  have hdiv := h x (by decide)
  rw [Jx_card, J_card] at hdiv
  norm_num [atomCount] at hdiv

private lemma zeta_formula (s : ℂ) : P (L := E) s = 1 - (2 : ℂ) ^ (-s) - 4 * (8 : ℂ) ^ (-s) := by
  classical
  have hu : (Finset.univ : Finset E).erase (⊥ : E) = {p0,p1,p2,p3,p4,p5,p6,p7,x,a,top} := Eq.symm (Finset.val_inj.mp rfl)
  rw [P, hu]
  have ht : (⊤ : E) = top := WithBot.top_eq_coe.mp rfl
  simp [ht, index, J_card, Jx_card, atomCount, mu_p0, mu_p1, mu_p2, mu_p3,
    mu_p4, mu_p5, mu_p6, mu_p7, mu_x, mu_a]
  ring

private lemma weak : WeaklyCosetLike (L := E) := by
  refine ⟨8, (fun n => if n = 1 then 1 else if n = 2 then -1 else if n = 8 then -4 else 0), ?_⟩
  intro s
  rw [zeta_formula]
  have hi : Finset.Icc 1 8 = {1,2,3,4,5,6,7,8} := Finset.val_inj.mp rfl
  rw [hi]
  norm_num
  ring
end D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice.Counterexample
namespace D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice

theorem result : ¬ claim := by
  intro h
  exact Counterexample.not_strong (h Counterexample.E Counterexample.atomistic Counterexample.weak)

end D5.S3.Combinatorics.Lattices.ShalaCosetLikeAtomisticLattice
