/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.claim
   digest: Invariant weights cannot maximize the Fiedler value at fixed resistance on K23. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#15242; Refuted)
   Direct frozen dependencies: none (only pinned Mathlib imports).
   Definitions and the named decidability instance: proof_shape not-applicable.
   lap_weights: proof_shape: bind-only; escape_witness: none; consumers: energy,
   voltage_harmonic, effRes_value, lambda2_asym, lambda2_sym.
   energy: proof_shape: bind-only; escape_witness: none; consumers: harmonic_unique, asym_sos,
   sym_sos.
   harmonic_unique: proof_shape: bind-only; escape_witness: none; consumers: harmonicExt_eq.
   voltage_harmonic: proof_shape: bind-only; escape_witness: none; consumers: harmonicExt_eq.
   harmonicExt_eq: proof_shape: bind-only; escape_witness: none; consumers: effRes_value.
   effRes_value: proof_shape: bind-only; escape_witness: none; consumers: totalRes_weights.
   totalRes_weights: proof_shape: bind-only; escape_witness: none; consumers: totalRes_const,
   candidate_feasible.
   norm_pos: proof_shape: bind-only; escape_witness: none; consumers: lambda2_eq_of_rayleigh.
   lambda2_eq_of_rayleigh: proof_shape: bind-only; escape_witness: none; consumers: lambda2_asym,
   lambda2_sym.
   asym_sos: proof_shape: bind-only; escape_witness: none; consumers: lambda2_asym.
   sym_sos: proof_shape: bind-only; escape_witness: none; consumers: lambda2_sym.
   lambda2_asym: proof_shape: bind-only; escape_witness: none; consumers: candidate_lambda2.
   lambda2_sym: proof_shape: bind-only; escape_witness: none; consumers: invariant_feasible.
   weights_one: proof_shape: bind-only; escape_witness: none; consumers: invariant_feasible,
   candidate_feasible.
   totalRes_const: proof_shape: bind-only; escape_witness: none; consumers: invariant_feasible,
   candidate_feasible.
   lap_congr: proof_shape: bind-only; escape_witness: none; consumers: invariants_congr.
   invariants_congr: proof_shape: bind-only; escape_witness: none; consumers: invariant_feasible.
   invariant_constant: proof_shape: bind-only; escape_witness: none; consumers:
   invariant_feasible.
   invariant_feasible: proof_shape: bind-only; escape_witness: none; consumers: result.
   candidate_feasible: proof_shape: bind-only; escape_witness: none; consumers: result.
   candidate_lambda2: proof_shape: bind-only; escape_witness: none; consumers: result.
   K23_connected: proof_shape: bind-only; escape_witness: none; consumers: result.
   result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation

def wLap {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) : Matrix (Fin n) (Fin n) Real :=
  fun i j => if i = j then ∑ k with G.Adj i k, w s(i,k)
    else if G.Adj i j then -w s(i,j) else 0

def lambda2 {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) : Real :=
  sInf {r | ∃ x : Fin n → Real, x ≠ 0 ∧ ∑ i, x i = 0 ∧
    r = dotProduct x (wLap G w *ᵥ x) / dotProduct x x}

def Harmonic {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) (i j : Fin n) (x : Fin n → Real) : Prop :=
  x i = 1 ∧ x j = 0 ∧ ∀ k, k ≠ i → k ≠ j → (wLap G w *ᵥ x) k = 0

def harmonicExt {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) (i j : Fin n) : Fin n → Real := by
  classical
  exact if h : ∃ x, Harmonic G w i j x then Classical.choose h else 0

def effRes {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) (i j : Fin n) : Real :=
  if i = j then 0 else 1 / (wLap G w *ᵥ harmonicExt G w i j) i

def pairRes {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) : Sym2 (Fin n) → Real :=
  Sym2.lift ⟨fun i j => effRes G w (min i j) (max i j), by
    intro i j; dsimp; rw [min_comm, max_comm]⟩

def totalRes {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) : Real :=
  ∑ p : Sym2 (Fin n) with ¬ p.IsDiag, pairRes G w p

def Feasible {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) : Prop :=
  (∀ e ∈ G.edgeSet, 0 < w e) ∧ totalRes G w = totalRes G 1

def AutInvariant {n : Nat} (G : SimpleGraph (Fin n))
    (w : Sym2 (Fin n) → Real) : Prop :=
  ∀ σ : G ≃g G, ∀ e ∈ G.edgeSet, w (e.map σ) = w e

def claim : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected → 3 ≤ n →
    ∃ w, Feasible G w ∧ AutInvariant G w ∧
      ∀ w', Feasible G w' → lambda2 G w' ≤ lambda2 G w


def K23 : SimpleGraph (Fin 5) :=
  (completeBipartiteGraph (Fin 2) (Fin 3)).comap
    (finSumFinEquiv (m := 2) (n := 3)).symm

instance K23_dec : DecidableRel K23.Adj := by
  unfold K23 SimpleGraph.comap completeBipartiteGraph; infer_instance

private def weights (a b : Real) : Sym2 (Fin 5) → Real :=
  Sym2.lift ⟨fun i j => if i = 0 ∨ j = 0 then a else b, by
    intro i j; dsimp; simp only [or_comm]⟩

private lemma lap_weights (a b : Real) : wLap K23 (weights a b) =
    !![3*a,0,-a,-a,-a; 0,3*b,-b,-b,-b;
       -a,-b,a+b,0,0; -a,-b,0,a+b,0; -a,-b,0,0,a+b] := by
  ext i j
  simp only [wLap, Finset.sum_filter]
  fin_cases i <;> fin_cases j <;>
    norm_num [K23, SimpleGraph.comap, completeBipartiteGraph, finSumFinEquiv, Fin.addCases, Fin.sum_univ_succ, weights, Sym2.lift_mk] <;> ring

private lemma energy (a b : Real) (x : Fin 5 → Real) :
    dotProduct x (wLap K23 (weights a b) *ᵥ x) =
      a*((x 0-x 2)^2+(x 0-x 3)^2+(x 0-x 4)^2) +
      b*((x 1-x 2)^2+(x 1-x 3)^2+(x 1-x 4)^2) := by
  rw [lap_weights]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

private lemma harmonic_unique (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin 5) (x y : Fin 5 → Real)
    (hx : Harmonic K23 (weights a b) i j x)
    (hy : Harmonic K23 (weights a b) i j y) : x = y := by
  let d := x-y
  have hdi : d i = 0 := by simp [d, hx.1, hy.1]
  have hdj : d j = 0 := by simp [d, hx.2.1, hy.2.1]
  have hdL (k : Fin 5) (hi : k ≠ i) (hj : k ≠ j) :
      (wLap K23 (weights a b) *ᵥ d) k = 0 := by
    simp only [d, Matrix.mulVec_sub, Pi.sub_apply, hx.2.2 k hi hj, hy.2.2 k hi hj,
      sub_self]
  have hz : dotProduct d (wLap K23 (weights a b) *ᵥ d) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hi : k = i
    · subst k; simp [hdi]
    by_cases hj : k = j
    · subst k; simp [hdj]
    simp [hdL k hi hj]
  rw [energy] at hz
  have hs0 : 0 ≤ (d 0-d 2)^2+(d 0-d 3)^2+(d 0-d 4)^2 := by positivity
  have hs1 : 0 ≤ (d 1-d 2)^2+(d 1-d 3)^2+(d 1-d 4)^2 := by positivity
  have hz0 : (d 0-d 2)^2+(d 0-d 3)^2+(d 0-d 4)^2 = 0 := by
    nlinarith [mul_nonneg (le_of_lt hb) hs1]
  have hz1 : (d 1-d 2)^2+(d 1-d 3)^2+(d 1-d 4)^2 = 0 := by
    nlinarith [mul_nonneg (le_of_lt ha) hs0]
  have h02 : d 0 = d 2 := by nlinarith [sq_nonneg (d 0-d 3),sq_nonneg (d 0-d 4)]
  have h03 : d 0 = d 3 := by nlinarith [sq_nonneg (d 0-d 2),sq_nonneg (d 0-d 4)]
  have h04 : d 0 = d 4 := by nlinarith [sq_nonneg (d 0-d 2),sq_nonneg (d 0-d 3)]
  have h12 : d 1 = d 2 := by nlinarith [sq_nonneg (d 1-d 3),sq_nonneg (d 1-d 4)]
  have hc (k : Fin 5) : d k = d 0 := by
    fin_cases k <;> first | exact rfl | exact h12.trans h02.symm | exact h02.symm | exact h03.symm | exact h04.symm
  have hzero (k : Fin 5) : d k = 0 := by rw [hc, ← hc i, hdi]
  funext k
  have := hzero k
  dsimp [d] at this
  exact sub_eq_zero.mp this

private def voltage (a b : Real) (i j : Fin 5) : Fin 5 → Real :=
  if i = 0 ∧ j = 1 then ![1,0,a/(a+b),a/(a+b),a/(a+b)]
  else if i = 0 then fun k =>
    if k = 0 then 1 else if k = j then 0 else if k = 1 then 2*a/(3*a+b)
    else 3*a/(3*a+b)
  else if i = 1 then fun k =>
    if k = 1 then 1 else if k = j then 0 else if k = 0 then 2*b/(a+3*b)
    else 3*b/(a+3*b)
  else fun k => if k = i then 1 else if k = j then 0 else 1/2

private lemma voltage_harmonic (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin 5) (hij : i < j) :
    Harmonic K23 (weights a b) i j (voltage a b i j) := by
  have hab : a+b ≠ 0 := by positivity
  have h3ab : 3*a+b ≠ 0 := by positivity
  have ha3b : a+3*b ≠ 0 := by positivity
  rw [Harmonic, lap_weights]
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    simp [voltage] <;> intro k hi hj <;> fin_cases k <;>
    simp_all [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;>
    field_simp [ha.ne', hb.ne', hab, h3ab, ha3b] <;> ring

private lemma harmonicExt_eq (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin 5) (hij : i < j) :
    harmonicExt K23 (weights a b) i j = voltage a b i j := by
  have h : ∃ x, Harmonic K23 (weights a b) i j x :=
    ⟨_, voltage_harmonic a b ha hb i j hij⟩
  rw [harmonicExt, dif_pos h]
  exact harmonic_unique a b ha hb i j _ _ (Classical.choose_spec h)
    (voltage_harmonic a b ha hb i j hij)

private def resistanceValue (a b : Real) (i j : Fin 5) : Real :=
  if i = 0 ∧ j = 1 then (a+b)/(3*a*b)
  else if i = 0 then (3*a+b)/(3*a*(a+b))
  else if i = 1 then (a+3*b)/(3*b*(a+b))
  else 2/(a+b)

private lemma effRes_value (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin 5) (hij : i < j) :
    effRes K23 (weights a b) i j = resistanceValue a b i j := by
  have hab : a+b ≠ 0 := by positivity
  have h3ab : 3*a+b ≠ 0 := by positivity
  have ha3b : a+3*b ≠ 0 := by positivity
  rw [effRes, if_neg (ne_of_lt hij), harmonicExt_eq a b ha hb i j hij, lap_weights]
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    simp [voltage, resistanceValue, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp [ha.ne', hb.ne', hab, h3ab, ha3b] <;> ring_nf <;>
    field_simp [ha.ne', hb.ne', hab, h3ab, ha3b] <;> ring

private lemma totalRes_weights (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    totalRes K23 (weights a b) = (a+b)/(3*a*b) +
      (3*a+b)/(a*(a+b)) + (a+3*b)/(b*(a+b)) + 6/(a+b) := by
  have hp : (Finset.univ.filter (fun p : Sym2 (Fin 5) => ¬ p.IsDiag)) =
      {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4)} := by
    decide
  unfold totalRes
  rw [hp]
  simp [pairRes, effRes_value a b ha hb, resistanceValue]
  field_simp
  <;> ring

private lemma norm_pos {n : Nat} (x : Fin n → Real) (hx : x ≠ 0) :
    0 < dotProduct x x := by
  simpa only [star_trivial] using (dotProduct_star_self_pos_iff (v := x)).mpr hx

private lemma lambda2_eq_of_rayleigh {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Real) (r : Real)
    (hlower : ∀ x : Fin n → Real, ∑ i, x i = 0 →
      r * dotProduct x x ≤ dotProduct x (wLap G w *ᵥ x))
    (v : Fin n → Real) (hv : v ≠ 0) (hsum : ∑ i, v i = 0)
    (heigen : wLap G w *ᵥ v = r • v) : lambda2 G w = r := by
  let S := {q | ∃ x : Fin n → Real, x ≠ 0 ∧ ∑ i, x i = 0 ∧
    q = dotProduct x (wLap G w *ᵥ x) / dotProduct x x}
  have hmem : r ∈ S := by
    refine ⟨v,hv,hsum,?_⟩
    rw [heigen, dotProduct_smul, smul_eq_mul]
    exact (mul_div_cancel_right₀ r (ne_of_gt (norm_pos v hv))).symm
  have hbound : ∀ q ∈ S, r ≤ q := by
    rintro q ⟨x,hx,hs,hq⟩
    rw [hq]
    exact (le_div_iff₀ (norm_pos x hx)).mpr (hlower x hs)
  apply le_antisymm
  · exact csInf_le ⟨r,hbound⟩ hmem
  · exact le_csInf ⟨r,hmem⟩ hbound

private lemma asym_sos (t : Real) (x : Fin 5 → Real) (hs : ∑ i, x i = 0) :
    dotProduct x (wLap K23 (weights (2*t) t) *ᵥ x) -
      3*t*dotProduct x x =
      t*((x 0+x 1)^2+(2*x 0+x 1)^2+2*(x 0)^2) := by
  rw [energy]
  simp [dotProduct, Fin.sum_univ_succ] at hs ⊢
  linear_combination -2*t*(2*x 0+x 1)*hs

private lemma sym_sos (t : Real) (x : Fin 5 → Real) (hs : ∑ i, x i = 0) :
    dotProduct x (wLap K23 (weights t t) *ᵥ x) -
      2*t*dotProduct x x = t*((x 0)^2+(x 1)^2+2*(x 0+x 1)^2) := by
  rw [energy]
  simp [dotProduct, Fin.sum_univ_succ] at hs ⊢
  linear_combination -2*t*(x 0+x 1)*hs

private def fiedlerVector : Fin 5 → Real := ![0,0,1,-1,0]

private lemma lambda2_asym (t : Real) (ht : 0 < t) :
    lambda2 K23 (weights (2*t) t) = 3*t := by
  refine lambda2_eq_of_rayleigh _ _ _ ?_ fiedlerVector ?_ ?_ ?_
  · intro x hs
    have := asym_sos t x hs
    have hn : 0 ≤ t*((x 0+x 1)^2+(2*x 0+x 1)^2+2*(x 0)^2) := by positivity
    linarith
  · intro h
    have := congrFun h 2
    change (1 : Real) = 0 at this
    norm_num at this
  · norm_num [fiedlerVector, Fin.sum_univ_succ]
  · rw [lap_weights]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, fiedlerVector] <;> ring

private lemma lambda2_sym (t : Real) (ht : 0 < t) :
    lambda2 K23 (weights t t) = 2*t := by
  refine lambda2_eq_of_rayleigh _ _ _ ?_ fiedlerVector ?_ ?_ ?_
  · intro x hs
    have := sym_sos t x hs
    have hn : 0 ≤ t*((x 0)^2+(x 1)^2+2*(x 0+x 1)^2) := by positivity
    linarith
  · intro h
    have := congrFun h 2
    change (1 : Real) = 0 at this
    norm_num at this
  · norm_num [fiedlerVector, Fin.sum_univ_succ]
  · rw [lap_weights]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, fiedlerVector] <;> ring

private lemma weights_one : weights 1 1 = (1 : Sym2 (Fin 5) → Real) := by
  funext e
  induction e using Sym2.ind with
  | _ i j => simp [weights, Sym2.lift_mk]

private lemma totalRes_const (t : Real) (ht : 0 < t) :
    totalRes K23 (weights t t) = (23/3)/t := by
  rw [totalRes_weights t t ht ht]
  field_simp
  <;> ring

private lemma lap_congr {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w w' : Sym2 (Fin n) → Real) (hw : ∀ e ∈ G.edgeSet, w e = w' e) :
    wLap G w = wLap G w' := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [wLap, if_pos rfl, if_true]
    apply Finset.sum_congr rfl
    intro k hk
    exact hw _ (by simpa only [SimpleGraph.mem_edgeSet] using (Finset.mem_filter.mp hk).2)
  · simp only [wLap, if_neg hij]
    by_cases h : G.Adj i j
    · rw [if_pos h, if_pos h, hw _ (by simpa only [SimpleGraph.mem_edgeSet] using h)]
    · rw [if_neg h, if_neg h]

private lemma invariants_congr {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w w' : Sym2 (Fin n) → Real) (hw : ∀ e ∈ G.edgeSet, w e = w' e) :
    lambda2 G w = lambda2 G w' ∧ totalRes G w = totalRes G w' := by
  have hL := lap_congr G w w' hw
  have hh : harmonicExt G w = harmonicExt G w' := by
    unfold harmonicExt Harmonic
    rw [hL]
  constructor
  · unfold lambda2; rw [hL]
  · unfold totalRes
    apply Finset.sum_congr rfl
    intro p hp
    induction p using Sym2.ind with
    | _ i j =>
      simp only [pairRes, Sym2.lift_mk, effRes]
      rw [hL, hh]

private def hubSwap : K23 ≃g K23 where
  toEquiv := Equiv.swap 0 1
  map_rel_iff' := by decide

private def leafSwap23 : K23 ≃g K23 where
  toEquiv := Equiv.swap 2 3
  map_rel_iff' := by decide

private def leafSwap24 : K23 ≃g K23 where
  toEquiv := Equiv.swap 2 4
  map_rel_iff' := by decide

private lemma invariant_constant (w : Sym2 (Fin 5) → Real) (hw : AutInvariant K23 w) :
    ∀ e ∈ K23.edgeSet, w e = weights (w s(0,2)) (w s(0,2)) e := by
  have h03 := hw leafSwap23 s(0,2) (by decide)
  have h04 := hw leafSwap24 s(0,2) (by decide)
  have h12 := hw hubSwap s(0,2) (by decide)
  have h13 := hw hubSwap s(0,3) (by decide)
  have h14 := hw hubSwap s(0,4) (by decide)
  change w s(0,3) = w s(0,2) at h03
  change w s(0,4) = w s(0,2) at h04
  change w s(1,2) = w s(0,2) at h12
  change w s(1,3) = w s(0,3) at h13
  change w s(1,4) = w s(0,4) at h14
  intro e he
  induction e using Sym2.ind with
  | _ i j =>
    simp only [SimpleGraph.mem_edgeSet] at he
    simp only [weights, Sym2.lift_mk, ite_self]
    fin_cases i <;> fin_cases j <;> norm_num [K23, SimpleGraph.comap, completeBipartiteGraph, finSumFinEquiv, Fin.addCases] at he
    all_goals first
      | exact rfl
      | exact h03
      | exact h04
      | exact h12
      | exact h13.trans h03
      | exact h14.trans h04
      | exact congrArg w Sym2.eq_swap
      | exact (congrArg w Sym2.eq_swap).trans h03
      | exact (congrArg w Sym2.eq_swap).trans h04
      | exact (congrArg w Sym2.eq_swap).trans h12
      | exact (congrArg w Sym2.eq_swap).trans (h13.trans h03)
      | exact (congrArg w Sym2.eq_swap).trans (h14.trans h04)

private lemma invariant_feasible (w : Sym2 (Fin 5) → Real)
    (hf : Feasible K23 w) (hi : AutInvariant K23 w) :
    (∀ e ∈ K23.edgeSet, w e = 1) ∧ lambda2 K23 w = 2 := by
  let c := w s(0,2)
  have hc : 0 < c := hf.1 s(0,2) (by decide)
  have heq := invariant_constant w hi
  have hv := invariants_congr K23 w (weights c c) heq
  have hbudget := hf.2
  have hbase : totalRes K23 1 = 23/3 := by
    rw [← weights_one, totalRes_const 1 (by norm_num)]
    norm_num
  rw [hv.2, totalRes_const c hc, hbase] at hbudget
  have hc1 : c = 1 := by
    have := (div_eq_iff (ne_of_gt hc)).mp hbudget
    linarith
  constructor
  · intro e he
    rw [heq e he]
    change weights c c e = 1
    rw [hc1, weights_one]
    rfl
  · rw [hv.1, hc1, lambda2_sym 1 (by norm_num)]
    norm_num

private def candidate : Sym2 (Fin 5) → Real := weights (32/23) (16/23)

private lemma candidate_feasible : Feasible K23 candidate := by
  constructor
  · intro e he
    induction e using Sym2.ind with
    | _ i j =>
      simp only [candidate, weights, Sym2.lift_mk]
      split_ifs <;> norm_num
  · have hbase : totalRes K23 1 = 23/3 := by
      rw [← weights_one, totalRes_const 1 (by norm_num)]
      norm_num
    rw [hbase]
    unfold candidate
    rw [totalRes_weights _ _ (by norm_num) (by norm_num)]
    norm_num

private lemma candidate_lambda2 : lambda2 K23 candidate = 48/23 := by
  have h := lambda2_asym (16/23) (by norm_num)
  norm_num [candidate] at h ⊢
  exact h

lemma K23_connected : K23.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable K23).mpr
  refine ⟨2,?_⟩
  intro i
  fin_cases i
  · exact (show K23.Adj 2 0 by decide).reachable
  · exact (show K23.Adj 2 1 by decide).reachable
  · exact SimpleGraph.Reachable.refl _
  · exact (show K23.Adj 2 0 by decide).reachable.trans (show K23.Adj 0 3 by decide).reachable
  · exact (show K23.Adj 2 0 by decide).reachable.trans (show K23.Adj 0 4 by decide).reachable

theorem result : ¬ claim := by
  intro h
  obtain ⟨w,hf,hi,hm⟩ := h 5 K23 K23_connected (by decide)
  have hconstant := invariant_feasible w hf hi
  have hbound := hm candidate candidate_feasible
  rw [candidate_lambda2, hconstant.2] at hbound
  norm_num at hbound


end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
