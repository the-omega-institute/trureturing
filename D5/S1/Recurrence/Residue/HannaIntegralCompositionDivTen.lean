/- GID: D5/S1/Recurrence/Residue/HannaIntegralCompositionDivTen
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaIntegralCompositionDivTen
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral triangular composition proves Hanna's A277403 divisibility conjecture. -/

/-
proof_shape: result: content (unit-diagonal induction and integral recursive construction).
escape_witness: composition_top, used by seq_unique and a_equation.
admission_basis: open-problem-resolution (#21746; Proved).
Direct frozen dependencies (declaration statement_id, with same-module helpers expanded):
  F1: D5/S1/Recurrence/Residue/IntegralEGFComposition.composition
    sha256:625b50b4d744289c7e083463b92679d186557afa907938dbadf19290366dcd9f
  F2: D5/S1/Recurrence/Residue/IntegralEGFComposition.composition.eq_1
    sha256:27fab2c8bd6729578a073a93b34997112d573f14c5ee659aeccdad3d49a41fbc
  F3: D5/S1/Recurrence/Residue/IntegralEGFComposition.composition.eq_2
    sha256:ef4100ef6c01ebb83df9e99c68266acf83ddca560412a9a686857003794ea1ec
  F4: D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_congr
    sha256:79b68f43ccf15fca6bb19b58a476ef123f8802a02fcf37d02ed44f3fefc23bdd
  F5: D5/S1/Recurrence/Residue/IntegralEGFComposition.composition_map
    sha256:51cd29cbf773fdd8c04d53eac10d55b7c396742abfdbd1797d3aec53a8a227e7
  F6: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
    sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330
  F7: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_X
    sha256:974c185500a284d632cbc5fbe4ff12c0670c9663fb9879ad4297746cb405f82a
  F8: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_composition
    sha256:cfc2a9920533c237c950cb53f2d3ba45b014313381b5b9eda5bfe399b1fef9ce
  F9: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_derivative
    sha256:d8c528ef732aa837c3d79d7314200e072b40f5bcdc873683da352f1acf37c5c8
  F10: D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
    sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054
  F11: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.constantCoeff_encode
    sha256:7ab6eca00f6e60caaf4d33e7a1ca32c3800e019418309254c586377c79ffb747
  F12: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
    sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7
  F13: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_ext
    sha256:be297942dba1d71d921d56e5059d2544375954e34dd6e505146ebcbbed2baaff
  F14: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
    sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840
Per-declaration classifications; dependency labels refer to the identities above.
  IsSolution: proof_shape=definition; escape_witness=none;
    consumers=claim, solution_seq, source_equation, result; Direct frozen dependencies=none.
  claim: proof_shape=definition; escape_witness=none;
    consumers=result; Direct frozen dependencies=F6.
  composition_top: proof_shape=content; escape_witness=composition_top;
    consumers=seq_unique, a_equation; Direct frozen dependencies=F1, F2, F3, F4.
  inner: proof_shape=definition; escape_witness=none;
    consumers=SeqSolution, inner_congr, seq_unique, inner_map, seq_map, a, a_equation, solution_seq, source_equation, argument_coeff, p_equation, p_mod; Direct frozen dependencies=none.
  SeqSolution: proof_shape=definition; escape_witness=none;
    consumers=seq_unique, seq_map, a_equation, solution_seq, source_equation, p_mod; Direct frozen dependencies=F1.
  inner_congr: proof_shape=bind-only; escape_witness=none;
    consumers=seq_unique, a_equation; Direct frozen dependencies=none.
  seq_unique: proof_shape=content; escape_witness=composition_top;
    consumers=result; Direct frozen dependencies=F1, F2, F3, F4.
  inner_map: proof_shape=bind-only; escape_witness=none;
    consumers=seq_map, p_mod; Direct frozen dependencies=none.
  seq_map: proof_shape=bind-only; escape_witness=none;
    consumers=source_equation, result; Direct frozen dependencies=F1, F5.
  a: proof_shape=definition; escape_witness=none;
    consumers=a_equation, sourceA, sourceG, source_equation, result; Direct frozen dependencies=F1.
  a_equation: proof_shape=content; escape_witness=composition_top;
    consumers=source_equation, result; Direct frozen dependencies=F1, F2, F3, F4.
  ecoeff_add: proof_shape=bind-only; escape_witness=none;
    consumers=solution_seq, source_equation; Direct frozen dependencies=F6.
  ecoeff_sub: proof_shape=bind-only; escape_witness=none;
    consumers=solution_seq, source_equation, argument_coeff, p_equation; Direct frozen dependencies=F6.
  solution_seq: proof_shape=bind-only; escape_witness=none;
    consumers=result; Direct frozen dependencies=F1, F6, F7, F8, F9, F10.
  sourceA: proof_shape=definition; escape_witness=none;
    consumers=source_equation, result; Direct frozen dependencies=F1, F14.
  sourceG: proof_shape=definition; escape_witness=none;
    consumers=source_equation, result; Direct frozen dependencies=F1, F14.
  source_equation: proof_shape=content; escape_witness=composition_top;
    consumers=result; Direct frozen dependencies=F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14.
  p: proof_shape=definition; escape_witness=none;
    consumers=p_coeff, j_coeff, argument_coeff, p_equation, p_mod, result; Direct frozen dependencies=none.
  residualWitness: proof_shape=definition; escape_witness=none;
    consumers=residual_coeff, p_equation, p_mod; Direct frozen dependencies=none.
  P: proof_shape=definition; escape_witness=none;
    consumers=p_coeff, J_derivative, j_coeff, residual_identity, residual_coeff, p_equation; Direct frozen dependencies=none.
  J: proof_shape=definition; escape_witness=none;
    consumers=J_derivative, j_coeff, argument_coeff, residual_identity, residual_coeff, p_equation; Direct frozen dependencies=none.
  p_coeff: proof_shape=bind-only; escape_witness=none;
    consumers=j_coeff, p_equation; Direct frozen dependencies=F6.
  J_derivative: proof_shape=bind-only; escape_witness=none;
    consumers=j_coeff; Direct frozen dependencies=none.
  j_coeff: proof_shape=bind-only; escape_witness=none;
    consumers=argument_coeff, p_equation; Direct frozen dependencies=F6, F9.
  argument_coeff: proof_shape=bind-only; escape_witness=none;
    consumers=p_equation; Direct frozen dependencies=F6, F7, F9, F10.
  residual_identity: proof_shape=bind-only; escape_witness=none;
    consumers=residual_coeff; Direct frozen dependencies=none.
  residual_coeff: proof_shape=bind-only; escape_witness=none;
    consumers=p_equation; Direct frozen dependencies=F6.
  p_equation: proof_shape=bind-only; escape_witness=none;
    consumers=p_mod; Direct frozen dependencies=F1, F5, F6, F7, F8, F9, F10.
  p_mod: proof_shape=bind-only; escape_witness=none;
    consumers=result; Direct frozen dependencies=F1, F5, F6, F7, F8, F9, F10.
  result: proof_shape=content; escape_witness=composition_top;
    consumers=terminal result; Direct frozen dependencies=F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22179
The source equation and factorial-scaled coefficients retain the expressions of #21746;
eCoeff and encode are reused from their original owners.
utility: none: an unbounded symbolic congruence, with a consumed polynomial identity;
no bounded enumeration, checker interface, numerical reduction, or standalone instance.
-/

import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition

namespace D5.S1.Recurrence.Residue.HannaIntegralCompositionDivTen

open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition

/-- Literal defining equation with its zero-constant formal integral. -/
def IsSolution (A G : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧
  constantCoeff G = 0 ∧
  PowerSeries.derivative G = A ∧
  A.subst (X - G) = X + G

/-- Integral EGF coefficients, divisible by 10 at every index n>2 (offset 1). -/
def claim : Prop :=
  ∀ (A : PowerSeries ℚ) (G : PowerSeries ℚ), IsSolution A G →
    (∀ (n : ℕ), 1 ≤ n → ∃ (a : ℤ), eCoeff A n = (a : ℚ)) ∧
    (∀ (n : ℕ), 2 < n → ∃ (k : ℤ), eCoeff A n = ((10 * k : ℤ) : ℚ))


private theorem composition_top {R : Type*} [CommRing R]
    (f f' g g' : ℕ → R) (n : ℕ)
    (hf : ∀ j < n, f j = f' j) (hg : ∀ j ≤ n, g j = g' j)
    (h1 : g 1 = 1) (h1' : g' 1 = 1) :
    composition f g n - composition f' g' n = f n - f' n := by
  induction n generalizing f f' with
  | zero => simp only [composition]
  | succ n ih =>
    simp only [composition, Fin.sum_univ_castSucc]
    have low : ∑ i : Fin n, (n.choose i.val : R) *
        composition (fun j => f (j+1)) g i.val * g (n-i.val+1) =
        ∑ i : Fin n, (n.choose i.val : R) *
        composition (fun j => f' (j+1)) g' i.val * g' (n-i.val+1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [composition_congr (fun j hj => hf (j+1) (by omega))
        (fun j hj => hg j (by omega)), hg (n-i.val+1) (by omega)]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.choose_self, Nat.cast_one,
      Nat.sub_self, zero_add, one_mul, h1, h1', mul_one]
    rw [low]
    have hh := ih (fun j => f (j+1)) (fun j => f' (j+1))
      (fun j hj => hf (j+1) (by omega)) (fun j hj => hg j (by omega))
    linear_combination hh



private def inner {R : Type*} [Ring R] (a : ℕ → R) (j : ℕ) : R :=
  if j = 0 then 0 else if j = 1 then 1 else -a (j-1)

private def SeqSolution {R : Type*} [CommRing R] (a : ℕ → R) : Prop :=
  a 0 = 0 ∧ ∀ n, composition a (inner a) (n+1) = (if n = 0 then 1 else 0) + a n

private theorem inner_congr {R : Type*} [CommRing R] {a b : ℕ → R} {n : ℕ}
    (h : ∀ j < n, a j = b j) : ∀ j ≤ n, inner a j = inner b j := by
  intro j hj
  unfold inner
  split_ifs <;> try rfl
  rw [h (j-1) (by omega)]

private theorem seq_unique {R : Type*} [CommRing R] {a b : ℕ → R}
    (ha : SeqSolution a) (hb : SeqSolution b) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ha.1.trans hb.1.symm
    | succ n =>
      have ht := composition_top a b (inner a) (inner b) (n+1) ih
        (inner_congr ih) (by simp [inner]) (by simp [inner])
      rw [ha.2 n, hb.2 n, ih n (by omega)] at ht
      exact sub_eq_zero.mp (by linear_combination -ht)

private theorem inner_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : ℕ → R) :
    (fun j => φ (inner a j)) = inner (fun j => φ (a j)) := by
  funext j
  simp only [inner]
  split_ifs <;> simp

private theorem seq_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {a : ℕ → R} (ha : SeqSolution a) :
    SeqSolution (fun j => φ (a j)) := by
  constructor
  · simp [ha.1]
  · intro n
    have h := congrArg φ (ha.2 n)
    rw [composition_map, inner_map] at h
    simpa only [map_add, apply_ite φ, map_one, map_zero] using h

private noncomputable def a (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
    (if n = 1 then 1 else 0) + a (n-1) -
      composition (fun j => if _hj : j < n then a j else 0)
        (inner (fun j => if _hj : j < n then a j else 0)) n
termination_by n

decreasing_by all_goals omega

private theorem a_equation : SeqSolution a := by
  constructor
  · rw [a, dite_eq_left rfl]
  · intro n
    have he : a (n+1) = (if n = 0 then 1 else 0) + a n -
        composition ((fun j => if j < n+1 then a j else 0)) (inner ((fun j => if j < n+1 then a j else 0))) (n+1) := by
      rw [a, dite_eq_right (by omega)]
      simp only [Nat.add_sub_cancel, Nat.add_eq_right]
      rfl
    have ht := composition_top a ((fun j => if j < n+1 then a j else 0)) (inner a)
      (inner ((fun j => if j < n+1 then a j else 0))) (n+1)
      (fun j hj => by simp [hj])
      (inner_congr (fun j hj => by simp [hj]))
      (by simp [inner]) (by simp [inner])
    simp only [lt_self_iff_false, ite_false] at ht
    linear_combination ht + he

private theorem ecoeff_add (f g : PowerSeries ℚ) (n : ℕ) :
    eCoeff (f+g) n = eCoeff f n + eCoeff g n := by
  simp only [eCoeff, map_add, mul_add]

private theorem ecoeff_sub (f g : PowerSeries ℚ) (n : ℕ) :
    eCoeff (f-g) n = eCoeff f n - eCoeff g n := by
  simp only [eCoeff, map_sub, mul_sub]

private theorem solution_seq {A G : PowerSeries ℚ} (h : IsSolution A G) :
    SeqSolution (eCoeff A) := by
  have hg (n : ℕ) : eCoeff G (n+1) = eCoeff A n := by
    rw [← eCoeff_derivative, h.2.2.1]
  have hi : eCoeff (X-G) = inner (eCoeff A) := by
    funext j
    cases j with
    | zero => simp [inner, h.2.1]
    | succ j =>
      rw [ecoeff_sub, hg]
      cases j with
      | zero => simp [inner, h.1]
      | succ j => simp [inner]
  constructor
  · simpa using h.1
  · intro n
    have hc := congrArg (fun s => eCoeff s (n+1)) h.2.2.2
    rw [eCoeff_composition _ _ (by simp [h.2.1]), hi] at hc
    rw [ecoeff_add, eCoeff_X, hg] at hc
    simpa only [Nat.add_eq_right] using hc

open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)

private noncomputable def sourceA : PowerSeries ℚ := encode (fun n => (a n : ℚ))
private noncomputable def sourceG : PowerSeries ℚ :=
  encode (fun n => if n = 0 then 0 else (a (n-1) : ℚ))

private theorem source_equation : IsSolution sourceA sourceG := by
  have ha : SeqSolution (fun j => (a j : ℚ)) := seq_map (Int.castRingHom ℚ) a_equation
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [sourceA, a_equation.1]
  · simp [sourceG]
  · apply eCoeff_ext
    intro n
    simp [sourceA, sourceG]
  · apply eCoeff_ext
    intro n
    rw [eCoeff_composition _ _ (by simp [sourceG])]
    have hi : eCoeff (X-sourceG) = inner (fun n => (a n : ℚ)) := by
      funext j
      cases j with
      | zero => simp [sourceG, inner]
      | succ j =>
        rw [ecoeff_sub]
        simp only [sourceG, eCoeff_encode]
        cases j with
        | zero => simp [inner, a_equation.1]
        | succ j => simp [inner]
    rw [hi]
    simp only [sourceA, show eCoeff (encode (fun n => (a n : ℚ))) =
      (fun n => (a n : ℚ)) from funext (eCoeff_encode _)]
    cases n with
    | zero => simp [composition, sourceG, a_equation.1]
    | succ n =>
      rw [ha.2 n]
      rw [ecoeff_add, eCoeff_X]
      simp [sourceG]


private def p (n : ℕ) : ℤ := if n = 1 then 1 else if n = 2 then 2 else 0
private def residualWitness (n : ℕ) : ℤ :=
  if n = 3 then -1 else if n = 4 then -1 else if n = 5 then 4 else if n = 6 then 8 else 0
private noncomputable def P : PowerSeries ℚ := X + X^2
private noncomputable def J : PowerSeries ℚ := C (1/2) * X^2 + C (1/3) * X^3

private theorem p_coeff (n : ℕ) : eCoeff P n = (p n : ℚ) := by
  by_cases h1 : n = 1
  · subst n; norm_num [P, p, eCoeff, coeff_X]
  by_cases h2 : n = 2
  · subst n; norm_num [P, p, eCoeff, coeff_X]
  simp [P, p, eCoeff, coeff_X, coeff_X_pow, h1, h2]

private theorem J_derivative : PowerSeries.derivative (R := ℚ) J = P := by
  ext n
  by_cases h1 : n = 1
  · subst n; norm_num [J, P, coeff_derivative, coeff_X]
  by_cases h2 : n = 2
  · subst n; norm_num [J, P, coeff_derivative, coeff_X]
  simp [J, P, coeff_X, coeff_X_pow, h1, h2]

private theorem j_coeff (n : ℕ) : eCoeff J (n+1) = (p n : ℚ) := by
  rw [← eCoeff_derivative, J_derivative, p_coeff]

private theorem argument_coeff : eCoeff (X-J) = (fun n => ((inner p n : ℤ) : ℚ)) := by
  funext n
  cases n with
  | zero => simp [inner, J]
  | succ n =>
    rw [ecoeff_sub]
    rw [eCoeff_X, j_coeff]
    cases n with
    | zero => norm_num [inner, p]
    | succ n => simp [inner]

private theorem residual_identity :
    P.subst (X-J) - X - J =
      C (-5/3) * X^3 + C (-5/12) * X^4 + C (1/3) * X^5 + C (1/9) * X^6 := by
  have hz0 : constantCoeff (X-J) = 0 := by simp [J]
  have hz : PowerSeries.HasSubst (X-J) := .of_constantCoeff_zero hz0
  rw [P, subst_add hz, subst_pow hz, subst_X hz]
  let j : Polynomial ℚ := Polynomial.C (1/2) * Polynomial.X^2 +
    Polynomial.C (1/3) * Polynomial.X^3
  have hp : (Polynomial.X-j) + (Polynomial.X-j)^2 - Polynomial.X - j =
      Polynomial.C (-5/3) * Polynomial.X^3 + Polynomial.C (-5/12) * Polynomial.X^4 +
      Polynomial.C (1/3) * Polynomial.X^5 + Polynomial.C (1/9) * Polynomial.X^6 := by
    apply Polynomial.funext
    intro x
    simp only [j, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simpa [j, J] using congrArg (fun q : Polynomial ℚ => (q : PowerSeries ℚ)) hp

private theorem residual_coeff (n : ℕ) :
    eCoeff (P.subst (X-J) - X - J) n = ((10 * residualWitness n : ℤ) : ℚ) := by
  rw [residual_identity]
  by_cases h3 : n = 3
  · subst n; norm_num [eCoeff, residualWitness]
  by_cases h4 : n = 4
  · subst n; norm_num [eCoeff, residualWitness]
  by_cases h5 : n = 5
  · subst n; norm_num [eCoeff, residualWitness]
  by_cases h6 : n = 6
  · subst n; norm_num [eCoeff, residualWitness]
  simp [eCoeff, coeff_X_pow, residualWitness, h3, h4, h5, h6]

private theorem p_equation (n : ℕ) :
    composition p (inner p) (n+1) = (if n = 0 then 1 else 0) + p n +
      10 * residualWitness (n+1) := by
  have hc := residual_coeff (n+1)
  have hm := composition_map (Int.castRingHom ℚ) p (inner p) (n+1)
  have hs : eCoeff (P.subst (X-J)) (n+1) =
      ((composition p (inner p) (n+1) : ℤ) : ℚ) := by
    rw [eCoeff_composition _ _ (by simp [J]), argument_coeff,
      show eCoeff P = (fun n => (p n : ℚ)) from funext p_coeff]
    exact hm.symm
  rw [ecoeff_sub, ecoeff_sub, hs, eCoeff_X, j_coeff] at hc
  have he : (((composition p (inner p) (n+1) : ℤ)) : ℚ) =
      (if n = 0 then 1 else 0) + (p n : ℚ) + (10 * residualWitness (n+1) : ℤ) := by
    have hc' := hc
    simp only [Nat.add_eq_right] at hc'
    linear_combination hc'
  exact_mod_cast he


private theorem p_mod : SeqSolution (fun n => (p n : ZMod 10)) := by
  constructor
  · norm_num [p]
  · intro n
    have h := congrArg (Int.castRingHom (ZMod 10)) (p_equation n)
    rw [composition_map, inner_map] at h
    simpa [apply_ite, show (10 : ZMod 10) = 0 from ZMod.natCast_self 10] using h

theorem result : claim := by
  intro A G h
  have hcoeff : eCoeff A = eCoeff sourceA :=
    seq_unique (solution_seq h) (solution_seq source_equation)
  have he (n : ℕ) : eCoeff A n = (a n : ℚ) := by
    rw [congrFun hcoeff n]
    exact eCoeff_encode _ n
  have hmod : (fun n => (a n : ZMod 10)) = (fun n => (p n : ZMod 10)) :=
    seq_unique (seq_map (Int.castRingHom (ZMod 10)) a_equation) p_mod
  constructor
  · intro n _
    exact ⟨a n, he n⟩
  · intro n hn
    have hz : (a n : ZMod 10) = 0 := by
      rw [congrFun hmod n]
      simp [p, show n ≠ 1 by omega, show n ≠ 2 by omega]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 10).mp hz
    exact ⟨k, (he n).trans (by exact_mod_cast hk)⟩

end D5.S1.Recurrence.Residue.HannaIntegralCompositionDivTen
