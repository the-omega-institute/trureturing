/- GID: D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz
   generality: I
   mirror-B: D5/B/S1/Recurrence/GallardoRahavandrainyBinaryCollatz
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary polynomial Collatz lengths of powers of M squared plus M plus one. -/

/-
admission_basis: open-problem-resolution (#19299; Proved)
escape_witness: Dynamics.square_doubling, Dynamics.q_square_doubling
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19534 (result).
Direct frozen dependencies: none (all imports are pinned Mathlib).
The source's oddness predicate is used directly as IsCoprime A (X * (X + 1)).
Composition is used directly as Polynomial.comp; the auxiliary polynomial q is M
in the same coefficient ring. The source length counts both initial and terminal terms.
The public length retains the source formula; the proof uses Mathlib hittingAfter
through the private correspondence h_sInf.
M: proof_shape: bind-only; consumers: oddSeq, claim, mq, q_odd, degree_q, q_ne_zero, A, B, degree_A, degree_B, nextCoeff_q, nextCoeff_A, auxiliary, R_A_top, R_A_two_adjacent, R_q, q_square_doubling, q_power_height, iota_m, iota_q, transport, q_reverse, q_pow_reverse, seq_transport, q_power_hitting_set, length_q_power; escape_witness: none; Direct frozen dependencies: none.
oddPart: proof_shape: bind-only; consumers: oddSeq, oddPart_factor, oddPart_iota_factor, transport, initial_oddPart, seq_transport; escape_witness: none; Direct frozen dependencies: none.
oddSeq: proof_shape: bind-only; consumers: collatzLength, seq_transport, q_power_hitting_set, length_q_power; escape_witness: none; Direct frozen dependencies: none.
collatzLength: proof_shape: bind-only; consumers: claim, length_q_power; escape_witness: none; Direct frozen dependencies: none.
claim: proof_shape: bind-only; consumers: result; escape_witness: none; Direct frozen dependencies: none.
m: proof_shape: bind-only; consumers: R, mq, R_one, m_ne_zero, degree_m, m_odd, odd_R, degree_m_mul, degree_pow_m_mul, odd_pow_m_mul, R_top_add, same_step_delete, gap, R_m, degree_one_eq_m, termination, height_gap, B, degree_B, nextCoeff_m, R_erase, degree_R_le, degree_R_square, square_two_steps, auxiliary, R_A_top, R_A_two_adjacent, R_q, q_square_doubling, iota_m, T, numerator_ne_zero, T_odd, T_factor, transport, reverse_m, reversal_conjugacy; escape_witness: none; Direct frozen dependencies: none.
R: proof_shape: bind-only; consumers: h, Terminates, h_sInf, R_one, h_one, terminates_one, h_spec, h_min, h_eq, terminates_prepend, terminates_next, h_step, odd_R, R_top_add, same_step_delete, gap, R_m, termination, height_step, height_delete, R_erase, degree_R_le, degree_R_square, square_two_steps, square_doubling, auxiliary, R_A_top, R_A_adjacent_degree, R_A_two_adjacent, R_q, q_square_doubling, reversal_conjugacy, T_iterate_reverse, q_power_hitting_set, length_q_power; escape_witness: none; Direct frozen dependencies: none.
h: proof_shape: bind-only; consumers: h_sInf, h_one, h_spec, h_min, h_eq, h_step, gap, termination, height_step, height_delete, height_gap, delete_height, square_doubling, auxiliary, q_square_doubling, q_power_height, length_q_power; escape_witness: none; Direct frozen dependencies: none.
Terminates: proof_shape: bind-only; consumers: h_spec, terminates_prepend, terminates_next, h_step, gap, termination, height_delete, height_gap; escape_witness: none; Direct frozen dependencies: none.
h_sInf: proof_shape: bind-only; consumers: h_one, h_spec, h_min, h_eq, length_q_power; escape_witness: none; Direct frozen dependencies: none.
mq: proof_shape: bind-only; consumers: R_A_top, R_q; escape_witness: none; Direct frozen dependencies: none.
R_one: proof_shape: bind-only; consumers: terminates_next; escape_witness: none; Direct frozen dependencies: none.
h_one: proof_shape: bind-only; consumers: square_doubling, q_square_doubling, q_power_height; escape_witness: none; Direct frozen dependencies: none.
terminates_one: proof_shape: bind-only; consumers: termination; escape_witness: none; Direct frozen dependencies: none.
h_spec: proof_shape: bind-only; consumers: h_step; escape_witness: none; Direct frozen dependencies: none.
h_min: proof_shape: bind-only; consumers: h_step; escape_witness: none; Direct frozen dependencies: none.
h_eq: proof_shape: bind-only; consumers: h_step; escape_witness: none; Direct frozen dependencies: none.
terminates_prepend: proof_shape: bind-only; consumers: gap; escape_witness: none; Direct frozen dependencies: none.
terminates_next: proof_shape: bind-only; consumers: gap; escape_witness: none; Direct frozen dependencies: none.
h_step: proof_shape: bind-only; consumers: gap, height_step; escape_witness: none; Direct frozen dependencies: none.
nonzero_of_odd: proof_shape: bind-only; consumers: m_ne_zero, q_ne_zero, gap, odd_erase, erase_degree_lt, degree_one_eq_m, termination, delete_height, degree_R_le, degree_R_square, auxiliary, R_A_adjacent_degree, q_square_doubling, oddPart_factor, reversal_conjugacy; escape_witness: none; Direct frozen dependencies: none.
nonzero_eq_one: proof_shape: bind-only; consumers: monic_of_nezero, T_odd; escape_witness: none; Direct frozen dependencies: none.
monic_of_nezero: proof_shape: bind-only; consumers: erase_top, degree_one_eq_m, nextCoeff_square, nextCoeff_A, degree_R_square; escape_witness: none; Direct frozen dependencies: none.
m_ne_zero: proof_shape: bind-only; consumers: degree_m_mul, degree_pow_m_mul, R_erase, degree_R_le, degree_R_square; escape_witness: none; Direct frozen dependencies: none.
degree_m: proof_shape: bind-only; consumers: degree_m_mul, degree_pow_m_mul, R_m; escape_witness: none; Direct frozen dependencies: none.
m_odd: proof_shape: bind-only; consumers: odd_R; escape_witness: none; Direct frozen dependencies: none.
q_odd: proof_shape: bind-only; consumers: q_ne_zero, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
degree_q: proof_shape: bind-only; consumers: degree_A, nextCoeff_q, R_q, q_reverse; escape_witness: none; Direct frozen dependencies: none.
q_ne_zero: proof_shape: bind-only; consumers: degree_A, degree_B, nextCoeff_A; escape_witness: none; Direct frozen dependencies: none.
odd_R: proof_shape: bind-only; consumers: height_step, degree_R_le, square_doubling, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
degree_m_mul: proof_shape: bind-only; consumers: gap, degree_B, R_erase, degree_R_le, degree_R_square, auxiliary, reversal_conjugacy; escape_witness: none; Direct frozen dependencies: none.
degree_pow_m_mul: proof_shape: bind-only; consumers: termination, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
odd_pow_m_mul: proof_shape: bind-only; consumers: termination, height_gap, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
degree_top_add: proof_shape: bind-only; consumers: top_add_ne_one, R_top_add, R_A_top; escape_witness: none; Direct frozen dependencies: none.
top_add_ne_one: proof_shape: bind-only; consumers: gap; escape_witness: none; Direct frozen dependencies: none.
R_top_add: proof_shape: bind-only; consumers: same_step_delete, gap, R_A_two_adjacent; escape_witness: none; Direct frozen dependencies: none.
same_step_delete: proof_shape: bind-only; consumers: gap, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
gap: proof_shape: content; consumers: termination, height_gap, height_delete; escape_witness: none; Direct frozen dependencies: none.
erase_top: proof_shape: bind-only; consumers: odd_erase, termination, delete_height, R_erase, auxiliary, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
odd_erase: proof_shape: bind-only; consumers: erase_degree_lt, termination, delete_height, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
erase_degree_lt: proof_shape: bind-only; consumers: termination, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
eq_one_of_degree_zero: proof_shape: bind-only; consumers: termination, square_doubling, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
R_m: proof_shape: bind-only; consumers: termination; escape_witness: none; Direct frozen dependencies: none.
degree_one_eq_m: proof_shape: bind-only; consumers: termination; escape_witness: none; Direct frozen dependencies: none.
termination: proof_shape: content; consumers: height_step, height_delete, height_gap; escape_witness: none; Direct frozen dependencies: none.
height_step: proof_shape: content; consumers: square_doubling, auxiliary, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
height_delete: proof_shape: content; consumers: delete_height; escape_witness: none; Direct frozen dependencies: none.
height_gap: proof_shape: content; consumers: q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
A: proof_shape: bind-only; consumers: A_odd, degree_A, degree_B, A_ne_one, nextCoeff_A, auxiliary, R_A_top, R_A_adjacent_degree, R_A_two_adjacent, q_square_doubling, q_power_height; escape_witness: none; Direct frozen dependencies: none.
B: proof_shape: bind-only; consumers: B_odd, degree_B, B_ne_one, auxiliary, R_A_top, R_A_adjacent_degree, R_A_two_adjacent, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
A_odd: proof_shape: bind-only; consumers: auxiliary, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
B_odd: proof_shape: bind-only; consumers: auxiliary, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
degree_A: proof_shape: bind-only; consumers: degree_B, A_ne_one, auxiliary, R_A_top; escape_witness: none; Direct frozen dependencies: none.
degree_B: proof_shape: bind-only; consumers: B_ne_one, auxiliary, R_A_adjacent_degree, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
A_ne_one: proof_shape: bind-only; consumers: q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
B_ne_one: proof_shape: bind-only; consumers: auxiliary; escape_witness: none; Direct frozen dependencies: none.
nextCoeff_m: proof_shape: bind-only; consumers: degree_R_square; escape_witness: none; Direct frozen dependencies: none.
nextCoeff_q: proof_shape: bind-only; consumers: nextCoeff_A; escape_witness: none; Direct frozen dependencies: none.
nextCoeff_square: proof_shape: bind-only; consumers: nextCoeff_A, degree_R_square; escape_witness: none; Direct frozen dependencies: none.
nextCoeff_A: proof_shape: bind-only; consumers: auxiliary; escape_witness: none; Direct frozen dependencies: none.
delete_height: proof_shape: content; consumers: auxiliary; escape_witness: none; Direct frozen dependencies: none.
R_erase: proof_shape: bind-only; consumers: degree_R_le, degree_R_square; escape_witness: none; Direct frozen dependencies: none.
degree_R_le: proof_shape: bind-only; consumers: q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
degree_R_square: proof_shape: bind-only; consumers: square_two_steps, square_doubling; escape_witness: none; Direct frozen dependencies: none.
square_two_steps: proof_shape: bind-only; consumers: square_doubling; escape_witness: none; Direct frozen dependencies: none.
square_doubling: proof_shape: content; consumers: q_power_height; escape_witness: none; Direct frozen dependencies: none.
auxiliary: proof_shape: content; consumers: q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
R_A_top: proof_shape: bind-only; consumers: R_A_adjacent_degree, R_A_two_adjacent, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
R_A_adjacent_degree: proof_shape: bind-only; consumers: R_A_two_adjacent, q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
R_A_two_adjacent: proof_shape: bind-only; consumers: q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
R_q: proof_shape: bind-only; consumers: q_square_doubling; escape_witness: none; Direct frozen dependencies: none.
q_square_doubling: proof_shape: content; consumers: q_power_height; escape_witness: none; Direct frozen dependencies: none.
q_power_height: proof_shape: content; consumers: length_q_power; escape_witness: none; Direct frozen dependencies: none.
iota_m: proof_shape: bind-only; consumers: transport; escape_witness: none; Direct frozen dependencies: none.
iota_q: proof_shape: bind-only; consumers: q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
iota_injective: proof_shape: bind-only; consumers: q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
oddPart_factor: proof_shape: bind-only; consumers: oddPart_iota_factor; escape_witness: none; Direct frozen dependencies: none.
iota_factor: proof_shape: bind-only; consumers: oddPart_iota_factor; escape_witness: none; Direct frozen dependencies: none.
oddPart_iota_factor: proof_shape: bind-only; consumers: transport, initial_oddPart; escape_witness: none; Direct frozen dependencies: none.
T: proof_shape: bind-only; consumers: T_odd, T_factor, transport, reversal_conjugacy, T_iterate_odd, T_iterate_reverse, seq_transport, q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
numerator_ne_zero: proof_shape: bind-only; consumers: T_odd; escape_witness: none; Direct frozen dependencies: none.
T_odd: proof_shape: bind-only; consumers: transport, T_iterate_odd, T_iterate_reverse; escape_witness: none; Direct frozen dependencies: none.
T_factor: proof_shape: bind-only; consumers: transport, reversal_conjugacy; escape_witness: none; Direct frozen dependencies: none.
transport: proof_shape: bind-only; consumers: seq_transport; escape_witness: none; Direct frozen dependencies: none.
reverse_degree: proof_shape: bind-only; consumers: reverse_invol, reversal_conjugacy; escape_witness: none; Direct frozen dependencies: none.
reverse_invol: proof_shape: bind-only; consumers: reverse_eq_one; escape_witness: none; Direct frozen dependencies: none.
reverse_m: proof_shape: bind-only; consumers: reversal_conjugacy; escape_witness: none; Direct frozen dependencies: none.
reversal_conjugacy: proof_shape: bind-only; consumers: T_iterate_reverse; escape_witness: none; Direct frozen dependencies: none.
reverse_one: proof_shape: bind-only; consumers: reverse_eq_one; escape_witness: none; Direct frozen dependencies: none.
q_reverse: proof_shape: bind-only; consumers: q_pow_reverse; escape_witness: none; Direct frozen dependencies: none.
q_pow_reverse: proof_shape: bind-only; consumers: q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
T_iterate_odd: proof_shape: bind-only; consumers: q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
T_iterate_reverse: proof_shape: bind-only; consumers: q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
initial_oddPart: proof_shape: bind-only; consumers: seq_transport; escape_witness: none; Direct frozen dependencies: none.
seq_transport: proof_shape: bind-only; consumers: q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
reverse_eq_one: proof_shape: bind-only; consumers: q_power_hitting_set; escape_witness: none; Direct frozen dependencies: none.
q_power_hitting_set: proof_shape: bind-only; consumers: length_q_power; escape_witness: none; Direct frozen dependencies: none.
length_q_power: proof_shape: content; consumers: result; escape_witness: none; Direct frozen dependencies: none.
result: proof_shape: content; consumers: terminal result; escape_witness: Dynamics.q_power_height; Direct frozen dependencies: none.
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Probability.Process.HittingTime
import Mathlib.RingTheory.Algebraic.Basic

namespace D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz

open Polynomial

/-- `M := x² + x + 1`, "the first odd and non-constant" binary polynomial. -/
noncomputable def M : (ZMod 2)[X] := X ^ 2 + X + 1

/-- The odd part: `S = x^{val_x(S)} (x + 1)^{val_{x+1}(S)} S₁` with `S₁` odd, read through the multiplicities of the roots
`0` and `1` (in characteristic 2, `x + 1 = x − 1`). -/
noncomputable def oddPart (S : (ZMod 2)[X]) : (ZMod 2)[X] :=
  S /ₘ (X ^ S.rootMultiplicity 0 * (X - C 1) ^ S.rootMultiplicity 1)

/-- The odd sequence `[A_1, A_3, A_5, …]`: `A_1` is the odd part of `A`, and `A_{2k+1}` is the odd part of
`A_{2k} = 1 + M A_{2k−1}`. -/
noncomputable def oddSeq (A : (ZMod 2)[X]) : ℕ → (ZMod 2)[X]
  | 0 => oddPart A
  | k + 1 => oddPart (1 + M * oddSeq A k)

/-- `ℓ_A`: the length of the odd sequence `[A_1, …, A_{2m−1}, 1]`, counting the first term and the terminal `1`. -/
noncomputable def collatzLength (A : (ZMod 2)[X]) : ℕ :=
  sInf {k : ℕ | oddSeq A k = 1} + 1

/-- Conjecture 3.11: "If `A = (M² + M + 1)ⁿ` with `n ≥ 2`, then `ℓ_A` equals `n + 1`." -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → collatzLength ((M ^ 2 + M + 1) ^ n) = n + 1

end D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz


namespace D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics
open Polynomial
open scoped CharTwo
private noncomputable def m : (ZMod 2)[X] := 1 + X
private noncomputable def R (f : (ZMod 2)[X]) : (ZMod 2)[X] := m * f + X ^ (f.natDegree + 1)
private noncomputable def h (f : (ZMod 2)[X]) : ℕ :=
  (MeasureTheory.hittingAfter (fun k (g : (ZMod 2)[X]) => R^[k] g) {1} 0 f).untopD 0
private def Terminates (f : (ZMod 2)[X]) : Prop := ∃ k : ℕ, R^[k] f = 1

private theorem h_sInf (f : (ZMod 2)[X]) : h f = sInf {k : ℕ | R^[k] f = 1} := by
  classical
  unfold h
  by_cases he : ∃ k : ℕ, R^[k] f = 1
  · simp only [MeasureTheory.hittingAfter, Nat.zero_le, Set.mem_singleton_iff, true_and,
      ite_eq_left he, WithTop.untopD_coe]
  · have hs : {k : ℕ | R^[k] f = 1} = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    simp only [MeasureTheory.hittingAfter, Nat.zero_le, Set.mem_singleton_iff, true_and,
      ite_eq_right he, WithTop.untopD_top, hs, Nat.sInf_empty]

private theorem mq : m*M=1+X^3 := by
  dsimp [m,M]
  ring_nf; simp

private theorem R_one : R 1 = 1 := by
  simp [R,m]

private theorem h_one : h 1 = 0 := by
  rw [h_sInf]
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le (Set.mem_ofPred.mpr (show R^[0] (1 : (ZMod 2)[X]) = 1 from rfl))

private theorem terminates_one : Terminates 1 := ⟨0,rfl⟩

private theorem h_spec (f : (ZMod 2)[X]) (hf : Terminates f) : R^[h f] f = 1 := by
  rw [h_sInf]
  exact Nat.sInf_mem hf

private theorem h_min (f : (ZMod 2)[X]) (n : ℕ) (hn : R^[n] f = 1) : h f ≤ n := by
  rw [h_sInf]
  exact Nat.sInf_le hn

private theorem h_eq (f : (ZMod 2)[X]) (n : ℕ) (hn : R^[n] f = 1)
    (hbefore : ∀ j < n, R^[j] f ≠ 1) : h f = n := by
  classical
  rw [h_sInf, Nat.sInf_def ⟨n, hn⟩]
  exact (@Nat.find_eq_iff n (fun k : ℕ => k ∈ {k : ℕ | R^[k] f = 1})
    (fun k => Classical.propDecidable _) ⟨n, hn⟩).2 ⟨hn, hbefore⟩

private theorem terminates_prepend (f : (ZMod 2)[X]) (hf : Terminates (R f)) : Terminates f := by
  obtain ⟨n,hn⟩ := hf
  exact ⟨n+1,by simpa only [Function.iterate_succ_apply] using hn⟩

private theorem terminates_next (f : (ZMod 2)[X]) (hf : Terminates f) : Terminates (R f) := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  rw [← Function.iterate_succ_apply,Function.iterate_succ_apply',hn,R_one]

private theorem h_step (f : (ZMod 2)[X]) (hne : f ≠ 1) (hf : Terminates (R f)) : h f = h (R f)+1 := by
  apply h_eq
  · simpa only [Function.iterate_succ_apply] using h_spec (R f) hf
  · intro j hj heq
    cases j with
    | zero => exact hne heq
    | succ j =>
      rw [Function.iterate_succ_apply] at heq
      have := h_min (R f) j heq
      omega

private theorem nonzero_of_odd (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) : f ≠ 0 := by
  intro he; simp [he] at hf

private theorem nonzero_eq_one (c : ZMod 2) (h : c ≠ 0) : c = 1 := by
  exact Fin.eq_one_of_ne_zero c h

private theorem monic_of_nezero (f : (ZMod 2)[X]) (hf : f ≠ 0) : f.Monic := by
  change f.leadingCoeff=1
  exact nonzero_eq_one _ (leadingCoeff_ne_zero.mpr hf)

private theorem m_ne_zero : m ≠ 0 := nonzero_of_odd m (by simp [m])

private theorem degree_m : m.natDegree = 1 := by simp [m]

private theorem m_odd : m.eval 0 = 1 := by simp [m]

private theorem q_odd : M.eval 0 = 1 := by simp [M]

private theorem degree_q : M.natDegree = 2 := by
  dsimp [M]
  compute_degree; exact one_ne_zero

private theorem q_ne_zero : M ≠ 0 := nonzero_of_odd M q_odd

private theorem odd_R (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) : (R f).eval 0 = 1 := by
  simp [R,m_odd,hf]

private theorem degree_m_mul (f : (ZMod 2)[X]) (hf : f ≠ 0) : (m*f).natDegree = f.natDegree+1 := by
  rw [natDegree_mul m_ne_zero hf,degree_m]
  omega

private theorem degree_pow_m_mul (n : ℕ) (f : (ZMod 2)[X]) (hf : f ≠ 0) :
    (m^n*f).natDegree=n+f.natDegree := by
  rw [natDegree_mul (pow_ne_zero n m_ne_zero) hf,natDegree_pow,degree_m,mul_one]

private theorem odd_pow_m_mul (n : ℕ) (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) :
    (m^n*f).eval 0 = 1 := by simp [m,hf]

private theorem degree_top_add (d : ℕ) (G : (ZMod 2)[X]) (hG : G.natDegree < d) :
    (X^d+G).natDegree = d := by
  rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hG),natDegree_X_pow]

private theorem top_add_ne_one (d : ℕ) (G : (ZMod 2)[X]) (hG : G.natDegree < d) :
    X^d+G ≠ 1 := by
  intro heq
  have := congrArg Polynomial.natDegree heq
  rw [degree_top_add d G hG,natDegree_one] at this
  omega

private theorem R_top_add (d : ℕ) (G : (ZMod 2)[X]) (hG : G.natDegree < d) :
    R (X^d+G) = X^d + m*G := by
  rw [R,degree_top_add d G hG]
  dsimp [m]
  rw [pow_succ]
  ring_nf; simp

private theorem same_step_delete (d : ℕ) (G : (ZMod 2)[X]) (hG : G.natDegree+1=d) :
    R (X^d+G)=R G := by
  rw [R_top_add d G (by omega),R,hG]
  exact add_comm _ _

/-- A degree-gap reduction, with the degree-one boundary excluded. -/
private theorem gap (r d : ℕ) (G : (ZMod 2)[X]) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hG : G.eval 0 = 1) (hgap : G.natDegree+r=d)
    (ht : Terminates (m^(r-1)*G)) :
    Terminates (X^d+G) ∧ h (X^d+G)=r-1+h (m^(r-1)*G) := by
  induction r generalizing G with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=0
    · subst r
      have htG : Terminates G := by simpa using ht
      have hnG : G ≠ 1 := by
        intro heq; simp [heq] at hgap; omega
      have hstep := same_step_delete d G (by simpa using hgap)
      have htRG := terminates_next G htG
      have htRF : Terminates (R (X^d+G)) := by simpa only [hstep] using htRG
      refine ⟨terminates_prepend _ htRF,?_⟩
      rw [h_step _ (top_add_ne_one d G (by omega)) htRF,hstep,
        ← h_step G hnG htRG]
      simp
    · have hnG := nonzero_of_odd G hG
      have hmG : (m*G).natDegree+r=d := by rw [degree_m_mul G hnG]; omega
      have hmul : m^(r-1)*(m*G)=m^r*G := by
        rw [← mul_assoc,← pow_succ,show r-1+1=r from Nat.succ_pred_eq_of_ne_zero hr0]
      have htt : Terminates (m^(r-1)*(m*G)) := by simpa [hmul] using ht
      obtain ⟨htR,hhR⟩ := ih (m*G) (by omega) (by simp [m,hG]) hmG htt
      have heq := R_top_add d G (by omega)
      have htRF : Terminates (R (X^d+G)) := by simpa only [heq] using htR
      refine ⟨terminates_prepend _ htRF,?_⟩
      rw [h_step _ (top_add_ne_one d G (by omega)) htRF,heq,hhR,hmul]
      simp only [Nat.add_sub_cancel]
      omega



private theorem erase_top (f : (ZMod 2)[X]) (hf : f ≠ 0) : f.eraseLead = f+X^f.natDegree := by
  rw [← self_sub_C_mul_X_pow, (monic_of_nezero f hf).leadingCoeff,
    C_1,one_mul,CharTwo.sub_eq_add]

private theorem odd_erase (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) (hd : 0 < f.natDegree) :
    f.eraseLead.eval 0 = 1 := by
  rw [erase_top f (nonzero_of_odd f hf)]
  simp [hf,Nat.ne_of_gt hd]

private theorem erase_degree_lt (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) (hd : 0 < f.natDegree) :
    f.eraseLead.natDegree < f.natDegree := by
  exact natDegree_lt_natDegree (nonzero_of_odd _ (odd_erase f hf hd))
    (degree_eraseLead_lt (nonzero_of_odd f hf))

private theorem eq_one_of_degree_zero (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) (hd : f.natDegree=0) : f=1 := by
  rw [eq_C_of_natDegree_eq_zero hd]
  simp only [coeff_zero_eq_eval_zero,hf,C_1]

private theorem R_m : R m = 1 := by
  rw [R,degree_m]
  dsimp [m]
  ring_nf; simp

private theorem degree_one_eq_m (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) (hd : f.natDegree = 1) : f=m := by
  simpa [m, coeff_zero_eq_eval_zero, hf, add_comm] using
    (monic_of_nezero f (nonzero_of_odd f hf)).eq_X_add_C hd

private theorem termination (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) : Terminates f := by
  generalize hd : f.natDegree=d
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases hd0 : d=0
    · have he := eq_one_of_degree_zero f hf (by omega)
      simpa [he] using terminates_one
    by_cases hd1 : d=1
    · rw [degree_one_eq_m f hf (by omega)]
      exact ⟨1,by simpa only [Function.iterate_one] using R_m⟩
    have hpos : 0<f.natDegree := by omega
    let G := f.eraseLead
    have hG : G.eval 0=1 := odd_erase f hf hpos
    have hlt : G.natDegree < d := by simpa [G,hd] using erase_degree_lt f hf hpos
    let r := d-G.natDegree
    have hr : 1≤r := Nat.le_sub_of_add_le' hlt
    have hgap : G.natDegree+r=d := by dsimp [r]; omega
    have hUdeg : (m^(r-1)*G).natDegree < d := by
      rw [degree_pow_m_mul _ G (nonzero_of_odd G hG)]
      omega
    have htU := ih _ hUdeg (m^(r-1)*G) (odd_pow_m_mul _ G hG) rfl
    have hh := (gap r d G (by omega) hr hG hgap htU).1
    have heq : X^d+G=f := by
      dsimp [G]
      rw [erase_top f (nonzero_of_odd f hf),hd]
      rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
    rwa [heq] at hh

private theorem height_step (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) (hne : f≠1) :
    h f = 1+h (R f) := by
  rw [h_step f hne (termination (R f) (odd_R f hf))]
  omega

private theorem height_delete (d : ℕ) (G : (ZMod 2)[X]) (hd : 2≤d) (hG : G.eval 0=1)
    (hgap : G.natDegree+1=d) : h (X^d+G)=h G := by
  simpa using (gap 1 d G hd (by decide) hG (by simpa using hgap)
    (by simpa using termination G hG)).2

private theorem height_gap (r d : ℕ) (G : (ZMod 2)[X]) (hd : 2≤d) (hr : 1≤r)
    (hG : G.eval 0=1) (hgap : G.natDegree+r=d) :
    h (X^d+G)=r-1+h (m^(r-1)*G) :=
  (gap r d G hd hr hG hgap (termination _ (odd_pow_m_mul _ G hG))).2


private noncomputable def A (f : (ZMod 2)[X]) : (ZMod 2)[X] := M*f^2
private noncomputable def B (f : (ZMod 2)[X]) : (ZMod 2)[X] := m*M*f^2

private theorem A_odd (f : (ZMod 2)[X]) (hf : f.eval 0=1) : (A f).eval 0=1 := by simp [A,M,hf]

private theorem B_odd (f : (ZMod 2)[X]) (hf : f.eval 0=1) : (B f).eval 0=1 := by simp [B,m,M,hf]

private theorem degree_A (f : (ZMod 2)[X]) (hf : f≠0) : (A f).natDegree=2*f.natDegree+2 := by
  rw [A,natDegree_mul q_ne_zero (pow_ne_zero 2 hf),degree_q,natDegree_pow]
  omega

private theorem degree_B (f : (ZMod 2)[X]) (hf : f≠0) : (B f).natDegree=2*f.natDegree+3 := by
  have heq : B f=m*A f := by exact mul_assoc m M (f^2)
  have hA0 : A f≠0 := mul_ne_zero q_ne_zero (pow_ne_zero 2 hf)
  rw [heq,degree_m_mul (A f) hA0,degree_A f hf]

private theorem A_ne_one (f : (ZMod 2)[X]) (hf : f≠0) : A f≠1 := by
  intro heq
  have hd := degree_A f hf
  simp [heq] at hd

private theorem B_ne_one (f : (ZMod 2)[X]) (hf : f≠0) : B f≠1 := by
  intro heq
  have hd := degree_B f hf
  simp [heq] at hd

private theorem nextCoeff_m : m.nextCoeff=1 := by simp [Polynomial.nextCoeff,m]

private theorem nextCoeff_q : M.nextCoeff=1 := by
  rw [Polynomial.nextCoeff,degree_q]
  norm_num [M,Polynomial.coeff_one]

private theorem nextCoeff_square (f : (ZMod 2)[X]) (hf : f≠0) : (f^2).nextCoeff=0 := by
  rw [(monic_of_nezero f hf).nextCoeff_pow]
  simp

private theorem nextCoeff_A (f : (ZMod 2)[X]) (hf : f≠0) : (A f).nextCoeff=1 := by
  rw [A,(monic_of_nezero M q_ne_zero).nextCoeff_mul ((monic_of_nezero f hf).pow 2),
    nextCoeff_q,nextCoeff_square f hf,add_zero]

private theorem delete_height (f : (ZMod 2)[X]) (hf : f.eval 0=1) (hd : 2≤f.natDegree)
    (hn : f.nextCoeff≠0) : h f=h f.eraseLead := by
  have hpos : 0<f.natDegree := natDegree_pos_of_nextCoeff_ne_zero hn
  have he : X^f.natDegree+f.eraseLead=f := by
    rw [erase_top f (nonzero_of_odd f hf)]
    rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
  have hh := height_delete f.natDegree f.eraseLead hd (odd_erase f hf hpos)
    (natDegree_eraseLead_add_one hn)
  rwa [he] at hh

private theorem R_erase (f : (ZMod 2)[X]) (hf : f≠0) : R f=(m*f).eraseLead := by
  rw [erase_top _ (mul_ne_zero m_ne_zero hf),degree_m_mul f hf]
  rfl

private theorem degree_R_le (f : (ZMod 2)[X]) (hf : f.eval 0=1) : (R f).natDegree≤f.natDegree := by
  have hnon := nonzero_of_odd f hf
  have ht : (R f).natDegree < (m*f).natDegree := by
    rw [R_erase f hnon]
    exact natDegree_lt_natDegree (by rw [← R_erase f hnon]; exact nonzero_of_odd _ (odd_R f hf))
      (degree_eraseLead_lt (mul_ne_zero m_ne_zero hnon))
  rw [degree_m_mul f hnon] at ht
  omega

private theorem degree_R_square (f : (ZMod 2)[X]) (hf : f.eval 0=1) : (R (f^2)).natDegree=2*f.natDegree := by
  have hf0 := nonzero_of_odd f hf
  have hs0 : f^2≠0 := pow_ne_zero 2 hf0
  have hn : (m*f^2).nextCoeff≠0 := by
    rw [(monic_of_nezero m m_ne_zero).nextCoeff_mul ((monic_of_nezero f hf0).pow 2),
      nextCoeff_m,nextCoeff_square f hf0,add_zero]
    exact one_ne_zero
  rw [R_erase _ hs0,natDegree_eraseLead hn,degree_m_mul _ hs0,natDegree_pow]
  omega

private theorem square_two_steps (f : (ZMod 2)[X]) (hf : f.eval 0=1) : R (R (f^2))=(R f)^2 := by
  rw [R,degree_R_square f hf,R,R,CharTwo.add_sq]
  have hp : (X^(f.natDegree+1))^2=(X : (ZMod 2)[X])^(2*f.natDegree+2) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hp]
  have hp2 : (X : (ZMod 2)[X])^(2*f.natDegree+2)=X*X^(2*f.natDegree+1) :=
    pow_succ' X (2*f.natDegree+1)
  rw [hp2]
  rw [natDegree_pow]
  dsimp [m]
  ring_nf; simp

private theorem square_doubling (f : (ZMod 2)[X]) (hf : f.eval 0=1) : h (f^2)=2*h f := by
  generalize hh : h f=n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases he : f=1
    · simp [he,h_one] at hh
      simp [he,h_one,← hh]
    have hd : 0<f.natDegree := by
      by_contra hd0
      exact he (eq_one_of_degree_zero f hf (by omega))
    have hsodd : (f^2).eval 0=1 := by simp [hf]
    have hsqne : f^2≠1 := by
      intro hsq
      exact he (CharTwo.sq_inj.mp (by simpa only [one_pow] using hsq))
    have hRne : R (f^2)≠1 := by
      intro hR
      have := degree_R_square f hf
      simp [hR] at this
      omega
    have hhf := height_step f hf he
    have ihR := ih (h (R f)) (by omega) (R f) (odd_R f hf) rfl
    rw [height_step _ hsodd hsqne,height_step _ (odd_R _ hsodd) hRne,
      square_two_steps f hf,ihR]
    omega

private theorem auxiliary (f : (ZMod 2)[X]) (hf : f.eval 0=1) : h (B f)=1+h (A (m*f)) := by
  have hf0 := nonzero_of_odd f hf
  have hmf : (m*f).eval 0=1 := by simp [m,hf]
  have hmf0 := nonzero_of_odd _ hmf
  have he : R (B f)=(A (m*f)).eraseLead := by
    rw [R,degree_B f hf0,erase_top _ (nonzero_of_odd _ (A_odd _ hmf)),
      degree_A _ hmf0,degree_m_mul f hf0]
    have hexp : 2*f.natDegree+3+1=2*(f.natDegree+1)+2 := Nat.add_left_inj.mpr rfl
    rw [hexp]
    dsimp [A,B]
    rw [mul_pow]
    simpa only [pow_two, mul_assoc] using
      congrArg (fun z : (ZMod 2)[X] => z * (f*f) + X^(2*(f.natDegree+1)+2))
        (mul_rotate M m m).symm
  rw [height_step _ (B_odd f hf) (B_ne_one f hf0),he,
    ← delete_height _ (A_odd _ hmf) (by rw [degree_A _ hmf0]; omega)
      (by rw [nextCoeff_A _ hmf0]; exact one_ne_zero)]


private theorem R_A_top (d : ℕ) (G : (ZMod 2)[X]) (hG : G.natDegree<d) :
    R (A (X^d+G))=X^(2*d)+B G := by
  have hF : X^d+G≠(0:(ZMod 2)[X]) := by
    apply ne_zero_of_natDegree_gt (n:=0)
    rw [degree_top_add d G hG]
    omega
  have hp : (X : (ZMod 2)[X])^(2*(X^d+G).natDegree+2+1)=X^3*(X^d)^2 := by
    rw [degree_top_add d G hG,← pow_mul,← pow_add]
    congr 1
    omega
  rw [R,degree_A _ hF,hp,A,CharTwo.add_sq]
  have he : m*(M*((X^d)^2+G^2))+X^3*(X^d)^2 = (X^d)^2+m*M*G^2 := by
    rw [← mul_assoc,mq]
    ring_nf; simp
  rw [he]
  dsimp [B]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

private theorem R_A_adjacent_degree (d : ℕ) (G : (ZMod 2)[X]) (hodd : G.eval 0=1)
    (hgap : G.natDegree+1=d) : (R (A (X^d+G))).natDegree=2*d+1 := by
  rw [R_A_top d G (by omega)]
  rw [natDegree_add_eq_right_of_natDegree_lt (by
    rw [natDegree_X_pow,degree_B G (nonzero_of_odd G hodd)]
    omega),degree_B G (nonzero_of_odd G hodd)]
  omega

private theorem R_A_two_adjacent (d : ℕ) (G : (ZMod 2)[X]) (hodd : G.eval 0=1)
    (hgap : G.natDegree+1=d) :
    R (R (A (X^d+G)))=A (R (X^d+G)) := by
  rw [R,R_A_adjacent_degree d G hodd hgap,R_A_top d G (by omega),
    R_top_add d G (by omega)]
  dsimp [A,B]
  rw [CharTwo.add_sq]
  have hp : (X : (ZMod 2)[X])^(2*d+1+1)=X^2*(X^d)^2 := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  rw [hp]
  dsimp [m,M]
  ring_nf

private theorem R_q : R M=1 := by
  rw [R,degree_q,mq]
  ring_nf; simp

/-- The universal M-times-square doubling identity. -/
private theorem q_square_doubling (f : (ZMod 2)[X]) (hf : f.eval 0=1) : h (A f)=2*h f+1 := by
  generalize hd : f.natDegree=d
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases he : f=1
    · have hA : A (1:(ZMod 2)[X])=M := by simp [A]
      rw [he,hA,height_step M q_odd (by simpa [A] using A_ne_one 1 one_ne_zero),R_q,h_one]
    have hpos : 0<f.natDegree := by
      by_contra hn
      exact he (eq_one_of_degree_zero f hf (by omega))
    let G := f.eraseLead
    have hG : G.eval 0=1 := odd_erase f hf hpos
    have hG0 := nonzero_of_odd G hG
    have hlt : G.natDegree<d := by simpa [G,hd] using erase_degree_lt f hf hpos
    have hrepr : X^d+G=f := by
      dsimp [G]
      rw [erase_top f (nonzero_of_odd f hf),hd]
      rw [add_left_comm,CharTwo.add_self_eq_zero,add_zero]
    let r := d-G.natDegree
    have hr : 1≤r := Nat.le_sub_of_add_le' hlt
    have hgap : G.natDegree+r=d := by dsimp [r]; omega
    by_cases hr1 : r=1
    · have hgap1 : G.natDegree+1=d := by omega
      have hRFlt : (R f).natDegree<d := by
        rw [← hrepr,same_step_delete d G hgap1]
        have := degree_R_le G hG
        omega
      have hAF := A_odd f hf
      have hRA : R (A f)≠1 := by
        intro heq
        have hdeg : (R (A f)).natDegree=2*d+1 := by
          rw [← hrepr]; exact R_A_adjacent_degree d G hG hgap1
        simp [heq] at hdeg
      have htwo : R (R (A f))=A (R f) := by
        rw [← hrepr]; exact R_A_two_adjacent d G hG hgap1
      have ihR := ih _ hRFlt (R f) (odd_R f hf) rfl
      rw [height_step _ hAF (A_ne_one f (nonzero_of_odd f hf)),
        height_step _ (odd_R _ hAF) hRA,htwo,ihR]
      have := height_step f hf he
      omega
    · have hr2 : 2≤r := by omega
      have hd2 : 2≤d := by omega
      let H := m^(r-2)*G
      let U := m^(r-1)*G
      have hH : H.eval 0=1 := odd_pow_m_mul _ G hG
      have hU : U.eval 0=1 := odd_pow_m_mul _ G hG
      have hUlt : U.natDegree<d := by
        dsimp [U]
        rw [degree_pow_m_mul _ G hG0]
        omega
      have hRA : R (A f)=X^(2*d)+B G := by
        rw [← hrepr]; exact R_A_top d G hlt
      have hgRA : (B G).natDegree+(2*r-3)=2*d := by rw [degree_B G hG0]; omega
      have hnorm : m^((2*r-3)-1)*B G=B H := by
        have hp : (2*r-3)-1+1=(r-2)*2+1 := by omega
        calc
          _ = m^((2*r-3)-1+1)*M*G^2 := by
            simp only [B, pow_succ, mul_assoc]
          _ = m^((r-2)*2+1)*M*G^2 := by rw [hp]
          _ = B H := by
            dsimp [B,H]
            rw [pow_succ,pow_mul,mul_pow, mul_rotate ((m^(r-2))^2) m M, mul_assoc]
      have hUeq : m*H=U := by
        dsimp [H,U]
        rw [← mul_assoc,← pow_succ',show r-2+1=r-1 by omega]
      have hhRA := height_gap (2*r-3) (2*d) (B G) (by omega) (by omega)
        (B_odd G hG) hgRA
      rw [height_step _ (A_odd f hf) (A_ne_one f (nonzero_of_odd f hf)),hRA,hhRA,hnorm,
        auxiliary H hH,hUeq,ih _ hUlt U hU rfl]
      have hhf := height_gap r d G hd2 hr hG hgap
      rw [hrepr] at hhf
      change h f=r-1+h U at hhf
      omega

private theorem q_power_height (n : ℕ) : h (M^n)=n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · simp [hn,h_one]
    let a := n/2
    have ha : a<n := Nat.bitwise_rec_lemma hn
    have hqa : (M^a).eval 0=1 := by simp [M]
    have ihA := ih a ha
    have hmod := Nat.mod_add_div n 2
    have hsmall := Nat.mod_lt n (by decide : 0<2)
    by_cases heven : n%2=0
    · have hn2 : n=a*2 := by dsimp [a]; omega
      rw [hn2,pow_mul,square_doubling _ hqa,ihA]
      omega
    · have hn2 : n=a*2+1 := by dsimp [a]; omega
      have heq : M^n=A (M^a) := by
        rw [hn2,pow_succ,pow_mul]
        exact mul_comm ((M^a)^2) M
      rw [heq,q_square_doubling _ hqa,ihA]
      omega

end D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics

namespace D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics
open Polynomial
open scoped CharTwo
private theorem iota_m : (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) m = D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M := by
  simp [m,D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M]
  ring

private theorem iota_q : (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) M = D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M^2 +
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M + 1 := by
  simp [M,D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M]
  ring_nf; simp

private theorem iota_injective : Function.Injective (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) := by
  have hd : (X * (X + 1) : (ZMod 2)[X]).natDegree = 2 := by
    compute_degree
    exact one_ne_zero
  have hm : (X * (X + 1) : (ZMod 2)[X]).Monic := by
    simpa only [Polynomial.C_1] using
      (Polynomial.monic_X.mul (Polynomial.monic_X_add_C (1 : ZMod 2)))
  simpa only [Polynomial.comp_eq_aeval] using
    (transcendental_iff_injective.mp
      (Polynomial.transcendental (X * (X + 1) : (ZMod 2)[X])
        (by omega)
        (by rw [hm.leadingCoeff]; exact one_mem _)))

private theorem oddPart_factor (a b : ℕ) (u : (ZMod 2)[X])
    (hu0 : u.eval 0 = 1) (hu1 : u.eval 1 = 1) :
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddPart
      (X ^ a * (X - C 1) ^ b * u) = u := by
  have hu : u ≠ 0 := nonzero_of_odd u hu0
  have u0 : u.rootMultiplicity 0 = 0 := rootMultiplicity_eq_zero (by simp [IsRoot,hu0])
  have u1 : u.rootMultiplicity 1 = 0 := rootMultiplicity_eq_zero (by simp [IsRoot,hu1])
  have v0 : ((X - C 1)^b * u).rootMultiplicity 0 = 0 :=
    rootMultiplicity_eq_zero (by simp [IsRoot,hu0])
  have v1 : ((X : (ZMod 2)[X])^a * u).rootMultiplicity 1 = 0 :=
    rootMultiplicity_eq_zero (by simp [IsRoot,hu1])
  have ha : (X^a * (X-C 1)^b * u).rootMultiplicity 0 = a := by
    have := rootMultiplicity_mul_X_sub_C_pow (a := (0 : ZMod 2)) (n := a)
      (mul_ne_zero (pow_ne_zero b (X_sub_C_ne_zero 1)) hu)
    rw [v0,zero_add] at this
    have heq : ((X-C 1)^b*u)*(X-C 0)^a=X^a*(X-C 1)^b*u := by
      simpa only [Polynomial.C_0, sub_zero] using
        (mul_rotate ((X : (ZMod 2)[X])^a) ((X-C 1)^b) u).symm
    rwa [heq] at this
  have hb : (X^a * (X-C 1)^b * u).rootMultiplicity 1 = b := by
    have := rootMultiplicity_mul_X_sub_C_pow (a := (1 : ZMod 2)) (n := b)
      (mul_ne_zero (pow_ne_zero a X_ne_zero) hu)
    rw [v1,zero_add] at this
    have heq : ((X:(ZMod 2)[X])^a*u)*(X-C 1)^b=X^a*(X-C 1)^b*u := by
      exact mul_right_comm (X^a) u ((X-C 1)^b)
    rwa [heq] at this
  unfold D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddPart
  rw [ha,hb]
  exact mul_divByMonic_cancel_left u ((monic_X.pow a).mul ((monic_X_sub_C 1).pow b))

private theorem iota_factor (v : ℕ) (u : (ZMod 2)[X]) :
    (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) (X^v * u) = X^v * (X-C 1)^v * (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) u := by
  simp [mul_pow,mul_assoc]

private theorem oddPart_iota_factor (v : ℕ) (u : (ZMod 2)[X]) (hu : u.eval 0 = 1) :
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddPart ((fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) (X^v * u)) = (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) u := by
  rw [iota_factor]
  apply oddPart_factor <;> simp [eval_comp,hu]

private noncomputable def T (f : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (1 + m*f) /ₘ X ^ (1+m*f).rootMultiplicity 0

private theorem numerator_ne_zero (f : (ZMod 2)[X]) : 1 + m*f ≠ 0 := by
  intro h
  have hh := congrArg (Polynomial.eval (1 : ZMod 2)) h
  norm_num [m] at hh

private theorem T_odd (f : (ZMod 2)[X]) : (T f).eval 0 = 1 := by
  apply nonzero_eq_one
  simpa [T] using eval_divByMonic_pow_rootMultiplicity_ne_zero 0 (numerator_ne_zero f)

private theorem T_factor (f : (ZMod 2)[X]) : 1 + m*f = X ^ (1+m*f).rootMultiplicity 0 * T f := by
  unfold T
  have he := pow_mul_divByMonic_rootMultiplicity_eq (1+m*f) (0 : ZMod 2)
  simp only [Polynomial.C_0,sub_zero] at he
  exact he.symm

private theorem transport (f : (ZMod 2)[X]) :
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddPart
      (1 + D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M * (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) f) = (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) (T f) := by
  have hi : 1 + D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M * (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) f = (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) (1+m*f) := by
    simp [ ← iota_m]
  rw [hi,T_factor]
  exact oddPart_iota_factor _ _ (T_odd f)

end D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics

namespace D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics
open Polynomial
open scoped CharTwo

private theorem reverse_degree (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) : f.reverse.natDegree = f.natDegree := by
  rw [Polynomial.reverse_natDegree]
  have ht : f.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr (by
    simpa only [coeff_zero_eq_eval_zero, hf] using (one_ne_zero : (1 : ZMod 2) ≠ 0)))
  simp [ht]

private theorem reverse_invol (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) : f.reverse.reverse = f := by
  change (f.reverse).reflect f.reverse.natDegree=f
  rw [reverse_degree f hf]
  exact Polynomial.reflect_reflect

private theorem reverse_m : m.reverse = m := by
  ext i
  simp [Polynomial.reverse,m,Polynomial.reflect_add,
    show (1 + (X : (ZMod 2)[X])).natDegree = 1 by simp, Polynomial.reflect_one_X, Polynomial.reflect_one,add_comm]

private theorem reversal_conjugacy (f : (ZMod 2)[X]) (hf : f.eval 0 = 1) :
    (T f).reverse = R f.reverse := by
  have hn : (m*f).natDegree = f.natDegree+1 :=
    degree_m_mul f (nonzero_of_odd f hf)
  have he : (1+m*f).reverse = (T f).reverse := by
    conv_lhs => rw [T_factor f]
    rw [Polynomial.reverse_X_pow_mul]
  rw [← he]
  have hm : (1+m*f).reverse = (m*f).reverse + X^(m*f).natDegree := by
    simpa only [C_1,one_mul,add_comm] using Polynomial.reverse_C_add (m*f) (1 : ZMod 2)
  rw [hm,Polynomial.reverse_mul_of_domain,reverse_m,hn]
  simp [R,reverse_degree f hf]

end D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics

namespace D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics
open Polynomial
open scoped CharTwo

private theorem reverse_one : (1 : (ZMod 2)[X]).reverse=1 := by
  simpa only [Polynomial.C_1] using Polynomial.reverse_C (1 : ZMod 2)

private theorem q_reverse : M.reverse=M := by
  rw [Polynomial.reverse,D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.degree_q]
  have hx : (X : (ZMod 2)[X]).reflect 2=X := by
    have ht := Polynomial.reflect_monomial (R:=ZMod 2) 2 1
    rw [Polynomial.revAt_le (by decide : 1≤2)] at ht
    simpa using ht
  have hx2 : (X^2 : (ZMod 2)[X]).reflect 2=1 := by
    rw [Polynomial.reflect_monomial,Polynomial.revAt_le (by decide : 2≤2)]
    simp
  simp only [M,Polynomial.reflect_add,Polynomial.reflect_one,hx,hx2]
  rw [add_right_comm, add_comm 1 (X^2), add_right_comm]

private theorem q_pow_reverse (n : ℕ) : (M^n).reverse=M^n := by
  let reverseHom : (ZMod 2)[X] →* (ZMod 2)[X] :=
    { toFun := Polynomial.reverse
      map_one' := by simpa only [Polynomial.C_1] using Polynomial.reverse_C (1 : ZMod 2)
      map_mul' := Polynomial.reverse_mul_of_domain }
  change reverseHom (M^n) = M^n
  rw [map_pow]
  change M.reverse^n = M^n
  rw [q_reverse]

private theorem T_iterate_odd (f : (ZMod 2)[X]) (hf : f.eval 0=1) (k : ℕ) : (T^[k] f).eval 0=1 := by
  cases k with
  | zero => exact hf
  | succ k => rw [Function.iterate_succ_apply']; exact T_odd _

private theorem T_iterate_reverse (f : (ZMod 2)[X]) (hf : f.eval 0=1) (k : ℕ) :
    (T^[k] f).reverse=R^[k] f.reverse := by
  let U : Set (ZMod 2)[X] := {g | g.eval 0 = 1}
  have ht : Set.MapsTo T U U := fun g _ => T_odd g
  let rev : U → (ZMod 2)[X] := fun g => g.val.reverse
  have hs : Function.Semiconj rev ht.restrict R := fun g => reversal_conjugacy g.val g.property
  have hh := hs.iterate_right k ⟨f, hf⟩
  simpa only [rev, ht.coe_iterate_restrict] using hh

private theorem initial_oddPart (f : (ZMod 2)[X]) (hf : f.eval 0=1) :
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddPart ((fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) f)=(fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) f := by
  simpa using oddPart_iota_factor 0 f hf

private theorem seq_transport (f : (ZMod 2)[X]) (hf : f.eval 0=1) (k : ℕ) :
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddSeq ((fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) f) k=(fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) (T^[k] f) := by
  induction k with
  | zero => exact initial_oddPart f hf
  | succ k ih => rw [D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddSeq,ih,transport,
      Function.iterate_succ_apply']

private theorem reverse_eq_one (f : (ZMod 2)[X]) (hf : f.eval 0=1) : f.reverse=1 ↔ f=1 := by
  constructor
  · intro hh
    have he := congrArg Polynomial.reverse hh
    rw [reverse_invol f hf,reverse_one] at he
    exact he
  · rintro rfl; exact reverse_one

private theorem q_power_hitting_set (n k : ℕ) :
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddSeq
      ((D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M^2+D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M+1)^n) k=1 ↔
      D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.R^[k] (D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M^n)=1 := by
  have hodd : (M^n).eval 0=1 := by simp [M]
  have hi : (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) (M^n)=
      (D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M^2+D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M+1)^n := by
    simp only [pow_comp]
    exact congrArg (fun f : (ZMod 2)[X] => f^n) iota_q
  rw [← hi,seq_transport _ hodd]
  have hio : (fun f : (ZMod 2)[X] => f.comp (X * (X + 1))) (T^[k] (M^n))=1 ↔ T^[k] (M^n)=1 := by
    simpa only [one_comp] using
      (iota_injective.eq_iff (a := T^[k] (M^n)) (b := 1))
  rw [hio,← reverse_eq_one _ (T_iterate_odd _ hodd k),T_iterate_reverse _ hodd k,q_pow_reverse]

private theorem length_q_power (n : ℕ) :
    D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.collatzLength
      ((D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M^2+D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M+1)^n)=n+1 := by
  unfold D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.collatzLength
  have he : {k | D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.oddSeq
      ((D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M^2+D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M+1)^n) k=1}=
      {k | D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.R^[k] (D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.M^n)=1} := by
    ext k
    exact q_power_hitting_set n k
  rw [he]
  rw [← h_sInf]
  rw [D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.q_power_height]
end D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics

namespace D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz
theorem result : claim := by
  intro n hn
  exact D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz.Dynamics.length_q_power n
end D5.S1.Recurrence.GallardoRahavandrainyBinaryCollatz
