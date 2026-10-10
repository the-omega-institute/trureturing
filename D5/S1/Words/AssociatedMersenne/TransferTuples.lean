/- GID: D5/S1/Words/AssociatedMersenne/TransferTuples
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/TransferTuples
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite transfer coefficients enumerate tuples with the singleton correction. -/

/-
admission_basis: escape-witness
Module content theorem: trace_coefficient_tuples
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  none (the other D5 imports belong to this delivery).
Declarations:
  geom_mul: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.geom_X2
  det_A: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.transferDet_factor
  geom_X2: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.Rser_aS
  geom_YX: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.cS_gS
  sum_matrix_pow_letters: proof_shape: content; escape_witness: TransferTuples.sum_matrix_pow_letters;
  AgreeUpTo.refl: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.letterPartial_approx
  AgreeUpTo.add: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.runPartial_approx
  AgreeUpTo.mul: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.letterPartial_approx
  matrix_approx_mul: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.matrix_approx_pow
  matrix_approx_pow: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.trace_coefficient_tuples
  geom_finite_identity: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.geom_monomial_approx
  geom_monomial_approx: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.coeff_gS
  pair_product_entry: proof_shape: content; escape_witness: TransferTuples.pair_product_entry;
  trace_pair_product: proof_shape: content; escape_witness: TransferTuples.trace_pair_product;
  adjacency_states: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.provisionalDegree_eq_tupleDegree
  openDegree_zip: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.provisionalDegree_zip
  provisionalDegree_zip: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.provisionalDegree_eq_tupleDegree
  cyclic_zip_sum: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.provisionalDegree_eq_tupleDegree
  provisionalDegree_eq_tupleDegree: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.tuple_transfer_coefficient
  provisionalDegree_singleton: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.singleton_weight_correction
  singleton_weight_correction: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.singleton_correction_coefficient
  runPartial_explicit: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.runPartial_approx
  runPartial_approx: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.letterPartial_approx
  slackPartial_approx: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.letterPartial_approx
  pair_slack_sum_zero: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.letterPartial_explicit
  pair_slack_sum_one: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.letterPartial_explicit
  letterPartial_explicit: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.letterPartial_approx
  letterPartial_approx: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.trace_coefficient_tuples
  transferLength_eq_tupleList: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.pair_bound_of_mem
  pair_bound_of_mem: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.alphabet_boundRunTuple
  alphabet_boundRunTuple: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.boundedList_boundRunTuple
  boundedList_boundRunTuple: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.boundedTupleEquiv
  bounded_weight_sum: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.trace_coefficient_tuples
  trace_letterPartial_coefficient: proof_shape: content; escape_witness: TransferTuples.trace_letterPartial_coefficient;
  trace_coefficient_tuples: proof_shape: content; escape_witness: TransferTuples.trace_coefficient_tuples;
  correction_run_monomial: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.singleton_correction_coefficient
  bounded_singleton: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.singleton_correction_coefficient
  singleton_correction_coefficient: proof_shape: content; escape_witness: TransferTuples.singleton_correction_coefficient;
  tuple_transfer_coefficient: proof_shape: content; escape_witness: TransferTuples.tuple_transfer_coefficient;
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

import D5.S1.Words.AssociatedMersenne.MarkedDegreeEnumeration

open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open D5.S1.Words.AssociatedMersenne.SingleRunDegrees
open D5.S1.Words.AssociatedMersenne.MultiRunDegrees
open D5.S1.Words.AssociatedMersenne.MarkedDegreeEnumeration

namespace D5.S1.Words.AssociatedMersenne.TransferTuples

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

local notation "Y" => (PowerSeries.C (Polynomial.X : Polynomial ℤ) : PowerSeries (Polynomial ℤ))

local notation "X" => (PowerSeries.X : PowerSeries (Polynomial ℤ))

set_option backward.isDefEq.respectTransparency false

local notation "y" => (Polynomial.X : (Polynomial ℤ))

def geom (z : PowerSeries (Polynomial ℤ)) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.invOfUnit (1-z) 1

def Rser : PowerSeries (Polynomial ℤ) :=
  X ^ 3 * Y + X ^ 5 * Y ^ 2 * geom (X ^ 2)

def Qser : PowerSeries (Polynomial ℤ) := X * geom (Y * X)

def A : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) :=
  !![Rser, Rser * Qser; Rser, Rser * Y * Qser]

private lemma geom_mul (z : PowerSeries (Polynomial ℤ)) (hz : PowerSeries.constantCoeff z = 0) :
    (1-z) * geom z = 1 := by
  exact PowerSeries.mul_invOfUnit (1-z) 1 (by simp [hz])

lemma det_A : Matrix.det (1 - A) =
    1 - Rser - Rser * Y * Qser + Rser ^ 2 * (Y-1) * Qser := by
  simp [A, Matrix.det_fin_two]
  ring

lemma geom_X2 : (1 - (PowerSeries.X : PowerSeries (Polynomial ℤ)) ^ 2) * geom ((PowerSeries.X : PowerSeries (Polynomial ℤ)) ^ 2) = 1 := by
  apply geom_mul
  simp

lemma geom_YX : (1 - (PowerSeries.C (Polynomial.X : Polynomial ℤ) : PowerSeries (Polynomial ℤ)) * (PowerSeries.X : PowerSeries (Polynomial ℤ))) * geom ((PowerSeries.C (Polynomial.X : Polynomial ℤ) : PowerSeries (Polynomial ℤ)) * (PowerSeries.X : PowerSeries (Polynomial ℤ))) = 1 := by
  apply geom_mul
  simp

private theorem sum_matrix_pow_letters {B : Type*} [Fintype B]
    (E : B → Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) (ell : Nat) :
    (∑ b, E b)^ell =
      ∑ t : Fin ell → B, ((List.ofFn t).map E).prod := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    rw [pow_succ',ih,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    let e := Fin.consEquiv (fun _ : Fin (ell+1) => B)
    calc
      _ = ∑ p : B × (Fin ell → B), ((List.ofFn (e p)).map E).prod := by
        simp [e,Fintype.sum_prod_type,List.ofFn_succ]
      _ = _ := e.sum_comp (fun t => ((List.ofFn t).map E).prod)

def AgreeUpTo (N : Nat) (f g : (PowerSeries (Polynomial ℤ))) : Prop :=
  ∀ n, n≤N → PowerSeries.coeff n f=PowerSeries.coeff n g

private lemma AgreeUpTo.refl (N : Nat) (f : (PowerSeries (Polynomial ℤ))) : AgreeUpTo N f f := fun _ _ => rfl

private lemma AgreeUpTo.add {N : Nat} {f g u v : (PowerSeries (Polynomial ℤ))}
    (h : AgreeUpTo N f g) (k : AgreeUpTo N u v) : AgreeUpTo N (f+u) (g+v) := by
  intro n hn
  simp only [map_add,h n hn,k n hn]

private lemma AgreeUpTo.mul {N : Nat} {f g u v : (PowerSeries (Polynomial ℤ))}
    (h : AgreeUpTo N f g) (k : AgreeUpTo N u v) : AgreeUpTo N (f*u) (g*v) := by
  intro n hn
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [h p.1 (by omega),k p.2 (by omega)]

private lemma matrix_approx_mul {N : Nat} {M M' K K' : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))}
    (h : ∀ i j, AgreeUpTo N (M i j) (M' i j))
    (k : ∀ i j, AgreeUpTo N (K i j) (K' i j)) :
    ∀ i j, AgreeUpTo N ((M*K) i j) ((M'*K') i j) := by
  intro i j n hn
  simp only [Matrix.mul_apply,map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact (h i q).mul (k q j) n hn

private lemma matrix_approx_pow {N : Nat} {M M' : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))}
    (h : ∀ i j, AgreeUpTo N (M i j) (M' i j)) (ell : Nat) :
    ∀ i j, AgreeUpTo N ((M^ell) i j) ((M'^ell) i j) := by
  induction ell with
  | zero => intro i j; exact AgreeUpTo.refl _ _
  | succ ell ih => simpa only [pow_succ] using matrix_approx_mul ih h

private lemma geom_finite_identity (z : (PowerSeries (Polynomial ℤ))) (N : Nat) (hz : PowerSeries.constantCoeff z=0) :
    geom z = (∑ j ∈ Finset.range (N+1), z^j) + z^(N+1)*geom z := by
  have ht : (1-z)*(∑ j ∈ Finset.range (N+1), z^j)=1-z^(N+1) :=
    mul_neg_geom_sum z (N+1)
  have hg := geom_mul z hz
  linear_combination (∑ j ∈ Finset.range (N+1), z^j)*hg - geom z*ht

theorem geom_monomial_approx (m d N : Nat) (hm : 0 < m) :
    AgreeUpTo N (geom (PowerSeries.monomial m ((Polynomial.X : Polynomial ℤ)^d)))
      (∑ j ∈ Finset.range (N+1),
        (PowerSeries.monomial m ((Polynomial.X : Polynomial ℤ)^d))^j) := by
  intro n hn
  rw [geom_finite_identity _ N (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    change PowerSeries.coeff 0 (PowerSeries.monomial m ((Polynomial.X : Polynomial ℤ)^d))=0
    simp [PowerSeries.coeff_monomial,Ne.symm (ne_of_gt hm)])]
  simp only [map_add,PowerSeries.monomial_pow]
  have hlt : n<(N+1)*m := by nlinarith
  rw [PowerSeries.monomial_eq_C_mul_X_pow, mul_assoc,
    PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  simp [show ¬(N+1)*m≤n by omega]

def slackState (s : Nat) : Fin 2 := if s=0 then 0 else 1

private def pairLength (b : Nat × Nat) : Nat := 2*b.1+1+b.2

def pairLocal (b : Nat × Nat) : Nat := min b.1 2+(b.2-1)

def adjacency (i j : Fin 2) : Nat := if i=1 ∧ j=1 then 1 else 0

private def pairMatrix (b : Nat × Nat) : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) :=
  fun i j => if i=slackState b.2 then
    PowerSeries.monomial (pairLength b) ((Polynomial.X : (Polynomial ℤ))^(pairLocal b+adjacency i j)) else 0

def openDegree (j : Fin 2) : List (Nat × Nat) → Nat
  | [] => 0
  | [b] => pairLocal b+adjacency (slackState b.2) j
  | b::c::t => pairLocal b+adjacency (slackState b.2) (slackState c.2)+openDegree j (c::t)

private def transferLength (t : List (Nat × Nat)) : Nat := (t.map pairLength).sum

def provisionalDegree (t : List (Nat × Nat)) : Nat :=
  match t with
  | [] => 0
  | b::u => openDegree (slackState b.2) (b::u)

private lemma pair_product_entry (b : Nat × Nat) (t : List (Nat × Nat)) (i j : Fin 2) :
    (((b::t).map pairMatrix).prod) i j =
      if i=slackState b.2 then
        PowerSeries.monomial (transferLength (b::t)) ((Polynomial.X : (Polynomial ℤ))^openDegree j (b::t)) else 0 := by
  induction t generalizing b i j with
  | nil =>
    by_cases hi : i=slackState b.2 <;> simp [pairMatrix,transferLength,openDegree,hi]
  | cons c t ih =>
    change (pairMatrix b*((c::t).map pairMatrix).prod) i j = _
    rw [Matrix.mul_apply]
    simp_rw [ih]
    rw [Finset.sum_eq_single (slackState c.2)]
    · by_cases hi : i=slackState b.2
      · simp only [hi,pairMatrix,if_true]
        rw [PowerSeries.monomial_mul_monomial,← pow_add]
        rfl
      · simp [pairMatrix,hi]
    · intro k hk hne
      simp only [if_neg hne,mul_zero]
    · simp

private theorem trace_pair_product (b : Nat × Nat) (t : List (Nat × Nat)) :
    Matrix.trace (((b::t).map pairMatrix).prod) =
      PowerSeries.monomial (transferLength (b::t)) ((Polynomial.X : (Polynomial ℤ))^provisionalDegree (b::t)) := by
  simp only [Matrix.trace,Matrix.diag,pair_product_entry]
  simp [provisionalDegree]

private lemma adjacency_states (s u : Nat) : adjacency (slackState s) (slackState u)=
    if 1 ≤ s ∧ 1 ≤ u then 1 else 0 := by
  by_cases hs : s=0 <;> by_cases hu : u=0 <;> simp [adjacency,slackState,hs,hu] <;> omega

private def pairEdge (b c : Nat × Nat) : Nat :=
  pairLocal b+adjacency (slackState b.2) (slackState c.2)

private lemma openDegree_zip (b c : Nat × Nat) (t : List (Nat × Nat)) :
    openDegree (slackState c.2) (b::t) =
      (List.zipWith pairEdge (b::t) (t++[c])).sum := by
  induction t generalizing b with
  | nil => simp [openDegree,pairEdge]
  | cons d t ih => simp [openDegree,List.zipWith,pairEdge,ih]

private lemma provisionalDegree_zip (t : List (Nat × Nat)) :
    provisionalDegree t = (List.zipWith pairEdge t (t.rotate 1)).sum := by
  cases t with
  | nil => simp [provisionalDegree]
  | cons b t => simpa [provisionalDegree] using openDegree_zip b b t

private lemma cyclic_zip_sum (t : List (Nat × Nat)) :
    (List.zipWith pairEdge t (t.rotate 1)).sum =
      ∑ p : Fin t.length,
        pairEdge t[p.val]
          (t[(p.val+1)%t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt))) := by
  let z := List.zipWith pairEdge t (t.rotate 1)
  have hz : z.length=t.length := by simp [z]
  let e : Fin t.length ≃ Fin z.length := finCongr hz.symm
  have hs := e.sum_comp (fun p => z[p.val])
  have hev : ∀ p : Fin t.length, (e p).val=p.val := fun _ => rfl
  simp only [hev] at hs
  rw [Fin.sum_univ_getElem] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro p hp
  simp [z,List.getElem_zipWith,List.getElem_rotate]

private theorem provisionalDegree_eq_tupleDegree (t : List (Nat × Nat)) (h : t.length≠1) :
    provisionalDegree t=tupleDegree t := by
  rw [provisionalDegree_zip,cyclic_zip_sum,tupleDegree,if_neg h]
  apply Finset.sum_congr rfl
  intro p hp
  simp [pairEdge,pairLocal,adjacency_states]

private lemma provisionalDegree_singleton (r s : Nat) :
    provisionalDegree [(r,s)]=min r 2 + if s=0 then 0 else s := by
  simp only [provisionalDegree,openDegree,pairLocal,adjacency_states]
  by_cases hs : s=0
  · simp [hs]
  · have hp : 1 ≤ s := by omega
    simp only [if_neg hs,if_pos (show 1 ≤ s ∧ 1 ≤ s from ⟨hp,hp⟩)]
    omega

private theorem singleton_weight_correction (r s : Nat) :
    (Polynomial.X : Polynomial ℤ)^tupleDegree [(r,s)] =
      Polynomial.X^provisionalDegree [(r,s)] +
      if s=1 then Polynomial.X^min r 2-Polynomial.X^(min r 2+1) else 0 := by
  rw [provisionalDegree_singleton]
  simp only [tupleDegree,List.length_singleton,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero]
  by_cases hs0 : s=0
  · simp [hs0]
  · by_cases hs1 : s=1
    · simp [hs1]
    · have hs2 : 2 ≤ s := by omega
      simp [hs0,hs1,hs2]

private def runPartial (N : Nat) : (PowerSeries (Polynomial ℤ)) :=
  ∑ a : Fin (N+2), PowerSeries.monomial (2*(a.val+1)+1) ((Polynomial.X : (Polynomial ℤ))^min (a.val+1) 2)

private def slackPartial (N : Nat) : (PowerSeries (Polynomial ℤ)) := X*(∑ j : Fin (N+1), (Y*X)^j.val)

private def alphabetPair {N : Nat} (b : Fin (N+2) × Fin (N+2)) : Nat × Nat :=
  (b.1.val+1,b.2.val)

private def letterPartial (N : Nat) : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) :=
  ∑ b : Fin (N+2) × Fin (N+2), pairMatrix (alphabetPair b)

private lemma runPartial_explicit (N : Nat) : runPartial N =
    X^3*Y+X^5*Y^2*(∑ j : Fin (N+1), (X^2)^j.val) := by
  rw [runPartial,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,Nat.zero_add,show min 1 2=1 from rfl,pow_one]
  rw [show (2*1+1:Nat)=3 from rfl,PowerSeries.monomial_eq_C_mul_X_pow]
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    have hr : min (j.val+1+1) 2=2 := by omega
    rw [hr,PowerSeries.monomial_eq_C_mul_X_pow,map_pow]
    have he : 2*(j.val+1+1)+1=5+2*j.val := by omega
    rw [he,pow_add,← pow_mul]
    ring

private lemma runPartial_approx (N : Nat) : AgreeUpTo N Rser (runPartial N) := by
  rw [runPartial_explicit]
  have h : AgreeUpTo N (geom (X^2)) (∑ j : Fin (N+1), (X^2)^j.val) := by
    have he : PowerSeries.monomial 2 ((Polynomial.X : (Polynomial ℤ))^0)=(X:(PowerSeries (Polynomial ℤ)))^2 := by simp [PowerSeries.X_pow_eq]
    have ha := geom_monomial_approx 2 0 N (by omega)
    rw [he] at ha
    simpa only [Fin.sum_univ_eq_sum_range] using ha
  exact (AgreeUpTo.refl N (X^3*Y)).add ((AgreeUpTo.refl N (X^5*Y^2)).mul h)

private lemma slackPartial_approx (N : Nat) : AgreeUpTo N Qser (slackPartial N) := by
  have he : PowerSeries.monomial 1 ((Polynomial.X : (Polynomial ℤ))^1)=Y*X := by
    simp [PowerSeries.monomial_eq_C_mul_X_pow]
  have ha := geom_monomial_approx 1 1 N (by omega)
  rw [he] at ha
  have h : AgreeUpTo N (geom (Y*X)) (∑ j : Fin (N+1), (Y*X)^j.val) := by
    simpa only [Fin.sum_univ_eq_sum_range] using ha
  exact (AgreeUpTo.refl N X).mul h

private lemma pair_slack_sum_zero (r N : Nat) (j : Fin 2) :
    (∑ s : Fin (N+2), pairMatrix (r,s.val) 0 j) =
      PowerSeries.monomial (2*r+1) ((Polynomial.X : (Polynomial ℤ))^min r 2) := by
  rw [Fin.sum_univ_succ]
  simp [pairMatrix,pairLength,pairLocal,adjacency,slackState]

private lemma pair_slack_sum_one (r N : Nat) (j : Fin 2) :
    (∑ s : Fin (N+2), pairMatrix (r,s.val) 1 j) =
      PowerSeries.monomial (2*r+1) ((Polynomial.X : (Polynomial ℤ))^min r 2)*
        slackPartial N*Y^adjacency 1 j := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ]
  have hz : pairMatrix (r,0) 1 j=0 := by simp [pairMatrix,slackState]
  rw [hz,zero_add]
  unfold slackPartial
  rw [mul_assoc,Finset.mul_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Fin.val_succ,pairMatrix,slackState,Nat.add_eq_zero_iff,Nat.one_ne_zero,
    and_false,if_false,if_true,pairLength,pairLocal,Prod.fst,Prod.snd,
    Nat.add_sub_cancel]
  simp only [PowerSeries.monomial_eq_C_mul_X_pow,map_pow,map_mul,pow_add,mul_pow]
  ring

private lemma letterPartial_explicit (N : Nat) :
    letterPartial N=!![runPartial N,runPartial N;
      runPartial N*slackPartial N,runPartial N*Y*slackPartial N] := by
  funext i j
  simp only [letterPartial,Matrix.sum_apply,Fintype.sum_prod_type,alphabetPair]
  fin_cases i
  · calc
      _ = runPartial N := by
        apply Finset.sum_congr rfl
        intro r hr
        exact pair_slack_sum_zero (r.val+1) N j
      _ = _ := by fin_cases j <;> rfl
  · calc
      _ = runPartial N*slackPartial N*Y^adjacency 1 j := by
        simp only [runPartial,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        exact pair_slack_sum_one (r.val+1) N j
      _ = _ := by fin_cases j <;> simp [adjacency] <;> ring

private theorem letterPartial_approx (N : Nat) :
    ∀ i j, AgreeUpTo N (A.transpose i j) (letterPartial N i j) := by
  rw [letterPartial_explicit]
  intro i j
  fin_cases i <;> fin_cases j
  · exact runPartial_approx N
  · exact runPartial_approx N
  · exact (runPartial_approx N).mul (slackPartial_approx N)
  · exact ((runPartial_approx N).mul (AgreeUpTo.refl N Y)).mul (slackPartial_approx N)

private def boundedList (n ell : Nat) (f : Fin ell → Fin (n+2) × Fin (n+2)) : List (Nat × Nat) :=
  List.ofFn (fun p => alphabetPair (f p))

private def BoundedTuples (n ell : Nat) :=
  {f : Fin ell → Fin (n+2) × Fin (n+2) // transferLength (boundedList n ell f)=n}

private lemma transferLength_eq_tupleList (t : List (Nat × Nat)) :
    transferLength t=(tupleList t).length := tupleList_length t |>.symm

private lemma pair_bound_of_mem {n : Nat} (t : GoodTuple n) (b : Nat × Nat) (hb : b ∈ t.val) :
    0 < b.1 ∧ b.1 ≤ n ∧ b.2 ≤ n := by
  have he : pairLength b ≤ transferLength t.val :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨b,hb,rfl⟩)
  rw [transferLength_eq_tupleList,t.property.2.2] at he
  exact ⟨t.property.2.1 b hb,by unfold pairLength at he; omega,
    by unfold pairLength at he; omega⟩

private def boundRunTuple {n ell : Nat} (t : RunTuples n ell) :
    Fin ell → Fin (n+2) × Fin (n+2) := fun p => by
  have hpi : p.val < t.val.val.length := by rw [t.property]; exact p.isLt
  let b := t.val.val[p.val]'hpi
  have hb := pair_bound_of_mem t.val b (List.getElem_mem hpi)
  exact (⟨b.1-1,by omega⟩,⟨b.2,by omega⟩)

private lemma alphabet_boundRunTuple {n ell : Nat} (t : RunTuples n ell) (p : Fin ell) :
    alphabetPair (boundRunTuple t p) =
      t.val.val[p.val]'(by rw [t.property];exact p.isLt) := by
  have hb := pair_bound_of_mem t.val
    (t.val.val[p.val]'(by rw [t.property];exact p.isLt))
    (List.getElem_mem (by rw [t.property];exact p.isLt))
  have hpi : p.val < t.val.val.length := by rw [t.property];exact p.isLt
  apply Prod.ext
  · change (t.val.val[p.val].1-1)+1=t.val.val[p.val].1
    omega
  · rfl

private lemma boundedList_boundRunTuple {n ell : Nat} (t : RunTuples n ell) :
    boundedList n ell (boundRunTuple t)=t.val.val := by
  apply List.ext_getElem
  · simp [boundedList,t.property]
  · intro p hp hp'
    have hpell : p < ell := by simpa [boundedList] using hp
    simpa [boundedList] using alphabet_boundRunTuple t ⟨p,hpell⟩

private def unboundTuple {n ell : Nat} (f : BoundedTuples n (ell+1)) : RunTuples n (ell+1) :=
  ⟨⟨boundedList n (ell+1) f.val,by simp [boundedList],by
    intro b hb
    obtain ⟨p,hp⟩ := List.mem_ofFn.mp hb
    rw [← hp]
    simp [alphabetPair]
  ,by rw [← transferLength_eq_tupleList];exact f.property⟩,by simp [boundedList]⟩

private def boundedTupleEquiv (n ell : Nat) : BoundedTuples n (ell+1) ≃ RunTuples n (ell+1) where
  toFun := unboundTuple
  invFun t := ⟨boundRunTuple t,by rw [boundedList_boundRunTuple,transferLength_eq_tupleList];exact t.val.property.2.2⟩
  left_inv f := by
    apply Subtype.ext
    funext p
    have hp := alphabet_boundRunTuple (unboundTuple f) p
    have he : alphabetPair (boundRunTuple (unboundTuple f) p)=alphabetPair (f.val p) := by
      change alphabetPair (boundRunTuple (unboundTuple f) p) =
        (List.ofFn (fun q : Fin (ell+1) => alphabetPair (f.val q)))[p.val] at hp
      simpa only [List.getElem_ofFn,Fin.eta] using hp
    apply Prod.ext <;> apply Fin.ext
    · have h := congrArg Prod.fst he
      simpa [alphabetPair] using h
    · exact congrArg Prod.snd he
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    exact boundedList_boundRunTuple t

private theorem bounded_weight_sum (n ell : Nat) (g : List (Nat × Nat) → Polynomial ℤ) :
    (∑ f : Fin (ell+1) → Fin (n+2) × Fin (n+2),
      if transferLength (boundedList n (ell+1) f)=n then
        g (boundedList n (ell+1) f) else 0) =
      ∑ t : RunTuples n (ell+1), g t.val.val := by
  rw [← Finset.sum_filter]
  let e := boundedTupleEquiv n ell
  refine Finset.sum_bij
    (fun f hf => e ⟨f,(Finset.mem_filter.mp hf).2⟩)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro f hf u hu he
    exact congrArg Subtype.val (e.injective he)
  · intro t ht
    let f := e.symm t
    have hf : f.val ∈ Finset.univ.filter
        (fun f : Fin (ell+1) → Fin (n+2) × Fin (n+2) =>
          transferLength (boundedList n (ell+1) f)=n) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,f.property⟩
    exact ⟨f.val,hf,e.apply_symm_apply t⟩
  · intro f hf
    rfl

private lemma trace_letterPartial_coefficient (n ell : Nat) :
    PowerSeries.coeff n (Matrix.trace ((letterPartial n)^(ell+1))) =
      ∑ f : Fin (ell+1) → Fin (n+2) × Fin (n+2),
        if transferLength (boundedList n (ell+1) f)=n then
          (Polynomial.X : (Polynomial ℤ))^provisionalDegree (boundedList n (ell+1) f) else 0 := by
  rw [letterPartial,sum_matrix_pow_letters,Matrix.trace_sum,map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  have he : ((List.ofFn f).map (fun b => pairMatrix (alphabetPair b))) =
      (boundedList n (ell+1) f).map pairMatrix := by simp only [boundedList,List.map_ofFn,Function.comp_def]
  rw [he]
  have hne : boundedList n (ell+1) f ≠ [] := by simp [boundedList]
  cases ht : boundedList n (ell+1) f with
  | nil => exact False.elim (hne ht)
  | cons b t =>
    rw [trace_pair_product,PowerSeries.coeff_monomial]
    by_cases hn : transferLength (b::t)=n
    · simp [hn]
    · simp [hn,Ne.symm hn]

theorem trace_coefficient_tuples (n ell : Nat) :
    PowerSeries.coeff n (Matrix.trace (A^(ell+1))) =
      ∑ t : RunTuples n (ell+1), (Polynomial.X : (Polynomial ℤ))^provisionalDegree t.val.val := by
  have hmat := matrix_approx_pow (letterPartial_approx n) (ell+1)
  have htrace : PowerSeries.coeff n (Matrix.trace (A^(ell+1))) =
      PowerSeries.coeff n (Matrix.trace ((letterPartial n)^(ell+1))) := by
    rw [← Matrix.trace_transpose,Matrix.transpose_pow]
    simp only [Matrix.trace,Matrix.diag,map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hmat i i n (le_refl n)
  rw [htrace,trace_letterPartial_coefficient]
  exact bounded_weight_sum n ell (fun t => (Polynomial.X : (Polynomial ℤ))^provisionalDegree t)

private lemma correction_run_monomial (r : Nat) :
    X*(1-Y)*PowerSeries.monomial (2*r+1) (y^min r 2) =
      PowerSeries.monomial (2*r+2) (y^min r 2-y^(min r 2+1)) := by
  simp only [PowerSeries.monomial_eq_C_mul_X_pow,map_sub,map_pow,map_mul,pow_succ]
  ring

private lemma bounded_singleton (n : Nat) (f : Fin 1 → Fin (n+2) × Fin (n+2)) :
    boundedList n 1 f=[alphabetPair (f 0)] := by
  simp [boundedList,List.ofFn_succ]

private theorem singleton_correction_coefficient (n : Nat) :
    tuplePolynomial n 1 = PowerSeries.coeff n (Matrix.trace A)+
      PowerSeries.coeff n (X*(1-Y)*Rser) := by
  rw [tuplePolynomial_eq_sum]
  have hp := trace_coefficient_tuples n 0
  simp only [Nat.zero_add,pow_one] at hp
  rw [hp]
  have hdiff : (∑ t : RunTuples n 1, y^tupleDegree t.val.val) -
      (∑ t : RunTuples n 1, y^provisionalDegree t.val.val) =
      PowerSeries.coeff n (X*(1-Y)*Rser) := by
    rw [← Finset.sum_sub_distrib]
    rw [← bounded_weight_sum n 0 (fun t => y^tupleDegree t-y^provisionalDegree t)]
    let e := Equiv.funUnique (Fin 1) (Fin (n+2) × Fin (n+2))
    have he : (∑ f : Fin 1 → Fin (n+2) × Fin (n+2),
        if transferLength (boundedList n 1 f)=n then
          y^tupleDegree (boundedList n 1 f)-y^provisionalDegree (boundedList n 1 f) else 0) =
      ∑ b : Fin (n+2) × Fin (n+2),
        if pairLength (alphabetPair b)=n then
          y^tupleDegree [alphabetPair b]-y^provisionalDegree [alphabetPair b] else 0 := by
      have hs := e.sum_comp (fun b => if pairLength (alphabetPair b)=n then
        y^tupleDegree [alphabetPair b]-y^provisionalDegree [alphabetPair b] else 0)
      simpa [e,Equiv.funUnique,Equiv.piUnique,bounded_singleton,transferLength] using hs
    rw [he,Fintype.sum_prod_type]
    have ha := (AgreeUpTo.refl n (X*(1-Y))).mul (runPartial_approx n)
    rw [ha n (le_refl n)]
    simp only [runPartial,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [correction_run_monomial,PowerSeries.coeff_monomial]
    rw [Finset.sum_eq_single (⟨1,by omega⟩ : Fin (n+2))]
    · simp only [alphabetPair,Prod.fst,Prod.snd,Fin.val_mk]
      rw [singleton_weight_correction]
      simp only [if_true]
      have hl : pairLength (r.val+1,1)=2*(r.val+1)+2 := by
        simp [pairLength]
      by_cases hn : pairLength (r.val+1,1)=n
      · have hn' : n=2*(r.val+1)+2 := hn.symm.trans hl
        simp only [if_pos hn,if_pos hn']
        ring
      · have hn' : n≠2*(r.val+1)+2 := by
          intro he
          exact hn (hl.trans he.symm)
        simp only [if_neg hn,if_neg hn']
    · intro s hs hne
      have hs1 : s.val≠1 := by intro hv; apply hne; exact Fin.ext hv
      rw [singleton_weight_correction]
      simp [alphabetPair,hs1]
    · simp
  linear_combination hdiff

theorem tuple_transfer_coefficient (n ell : Nat) :
    tuplePolynomial n (ell+1) =
      PowerSeries.coeff n (Matrix.trace (A^(ell+1)))+
      if ell=0 then PowerSeries.coeff n (X*(1-Y)*Rser) else 0 := by
  by_cases he : ell=0
  · subst ell
    simpa using singleton_correction_coefficient n
  · rw [if_neg he,add_zero,trace_coefficient_tuples,tuplePolynomial_eq_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [provisionalDegree_eq_tupleDegree t.val.val (by rw [t.property];omega)]

end
end TransferTuples
