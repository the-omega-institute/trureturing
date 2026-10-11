/- GID: D5/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/MarkedDegreeEnumeration
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Degree-refined marked words and ordered tuples satisfy a double count. -/

/-
admission_basis: escape-witness
Module content theorem: marked_degree_double_count
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  none (the other D5 imports belong to this delivery).
Declarations:
  extractMarked_degree: proof_shape: content; escape_witness: RunTupleBijection.alternating_data_pairs;
  marked_degree_double_count: proof_shape: content; escape_witness: MarkedDegreeEnumeration.marked_degree_double_count;
  degree_le: proof_shape: bind-only; escape_witness: none; consumer: MarkedDegreeEnumeration.tupleDegree_le
  runCount_le: proof_shape: bind-only; escape_witness: none; consumer: MarkedDegreeEnumeration.N_eq_sum_run_counts
  runCount_zero_iff: proof_shape: content; escape_witness: CircularWords.admissible_nonzero_has_marked_start;
  N_eq_sum_run_counts: proof_shape: bind-only; escape_witness: none; consumer: MarkedDegreeEnumeration.degreePolynomial_partition
  zero_run_degree_count: proof_shape: content; escape_witness: CircularWords.admissible_nonzero_has_marked_start;
  goodTuple_n_pos: proof_shape: bind-only; escape_witness: none; consumer: MarkedDegreeEnumeration.tupleDegree_le
  tupleDegree_le: proof_shape: bind-only; escape_witness: none; consumer: MarkedDegreeEnumeration.tuplePolynomial_eq_sum
  polynomial_marked_double_count: proof_shape: content; escape_witness: MarkedDegreeEnumeration.polynomial_marked_double_count;
  tuplePolynomial_eq_sum: proof_shape: bind-only; escape_witness: none; consumer: TransferTuples.singleton_correction_coefficient
  degreePolynomial_partition: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.degSeries_eq_graphTransferSeries
  runPolynomial_zero: proof_shape: content; escape_witness: CircularWords.admissible_nonzero_has_marked_start;
-/

import D5.S1.Words.AssociatedMersenne.MultiRunDegrees
import Mathlib.Algebra.Polynomial.Basic

open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open D5.S1.Words.AssociatedMersenne.SingleRunDegrees
open D5.S1.Words.AssociatedMersenne.MultiRunDegrees

namespace D5.S1.Words.AssociatedMersenne.MarkedDegreeEnumeration

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

def DegreeTuples (n ell k : Nat) :=
  {t : GoodTuple n // t.val.length=ell ∧ tupleDegree t.val=k}

instance instFintypeDegreeTuples (n ell k : Nat) : Fintype (DegreeTuples n ell k) := inferInstanceAs
  (Fintype {t : GoodTuple n // t.val.length=ell ∧ tupleDegree t.val=k})

private lemma extractMarked_degree {n : Nat} (x : MarkedWords n) :
    degree x.val.1 = tupleDegree (extractMarked x).2.val := by
  have h := degree_wordOfTuple (extractMarked x).1 (extractMarked x).2
  have he := congrArg (fun y : MarkedWords n => y.val.1) ((markedTupleEquiv n).left_inv x)
  change wordOfTuple (extractMarked x).1 (extractMarked x).2.val
    (extractMarked x).2.property.2.2 = x.val.1 at he
  rw [he] at h
  exact h

private def markedDegreeTupleEquiv (n ell k : Nat) :
    MarkedDegreeRunWords n ell k ≃ Fin n × DegreeTuples n ell k where
  toFun x := by
    let y : MarkedWords n := ⟨(x.1.val,x.2.val),x.1.property.1,x.2.property⟩
    exact ((extractMarked y).1,⟨(extractMarked y).2,
      (extractMarked_runs y).symm.trans x.1.property.2.2,
      (extractMarked_degree y).symm.trans x.1.property.2.1⟩)
  invFun x := ⟨⟨wordOfTuple x.1 x.2.val.val x.2.val.property.2.2,
      tuple_word_admissible x.1 x.2.val.val x.2.val.property.1 x.2.val.property.2.1
        x.2.val.property.2.2,
      (degree_wordOfTuple x.1 x.2.val).trans x.2.property.2,
      (runCount_wordOfTuple x.1 x.2.val.val x.2.val.property.2.1 x.2.val.property.2.2).trans
        x.2.property.1⟩,
      ⟨x.1,tuple_word_marked x.1 x.2.val.val x.2.val.property.1 x.2.val.property.2.1
        x.2.val.property.2.2⟩⟩
  left_inv := by
    intro x
    let y : MarkedWords n := ⟨(x.1.val,x.2.val),x.1.property.1,x.2.property⟩
    have h := (markedTupleEquiv n).left_inv y
    apply Sigma.ext
    · apply Subtype.ext
      exact congrArg (fun z : MarkedWords n => z.val.1) h
    · have hw : (reconstructMarked (extractMarked y)).val.1 = x.1.val :=
        congrArg (fun z : MarkedWords n => z.val.1) h
      apply (Subtype.heq_iff_coe_eq (fun q => by
        change IsMarkedStart (reconstructMarked (extractMarked y)).val.1 q ↔
          IsMarkedStart x.1.val q
        rw [hw])).mpr
      rfl
  right_inv := by
    intro x
    have h := (markedTupleEquiv n).right_inv (x.1,x.2.val)
    apply Prod.ext
    · have hf : (extractMarked (reconstructMarked (x.1,x.2.val))).1=x.1 := congrArg Prod.fst h
      exact hf
    · apply Subtype.ext
      have hs : (extractMarked (reconstructMarked (x.1,x.2.val))).2=x.2.val := congrArg Prod.snd h
      exact hs

theorem marked_degree_double_count (n ell k : Nat) :
    ell * Fintype.card (DegreeRunWords n ell k) =
      n * Fintype.card (DegreeTuples n ell k) :=
  marked_double_count_of_equiv n ell k (DegreeTuples n ell k) (markedDegreeTupleEquiv n ell k)

noncomputable def degreePolynomial (n : Nat) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (N n k : ℤ) * Polynomial.X ^ k

instance instFintypeRunTuples (n ell : Nat) : Fintype (RunTuples n ell) := inferInstanceAs
  (Fintype {t : GoodTuple n // t.val.length = ell})

private lemma degree_le {n : Nat} (w : Fin n → Bool) : degree w ≤ n := by
  classical
  unfold degree
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)

lemma runCount_le {n : Nat} (w : Fin n → Bool) : runCount w ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)

lemma runCount_zero_iff {n : Nat} (w : Fin n → Bool) (ha : Admissible w) :
    runCount w = 0 ↔ w = (fun _ => false) := by
  constructor
  · intro hz
    funext q
    by_contra hn
    have hqt : w q = true := Bool.eq_true_of_not_eq_false hn
    obtain ⟨i,hi⟩ := admissible_nonzero_has_marked_start w ha ⟨q,hqt⟩
    have hp : 0 < runCount w := Finset.card_pos.mpr
      ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    omega
  · intro he
    rw [he]
    unfold runCount
    apply Finset.card_eq_zero.mpr
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    intro hm
    exact Bool.noConfusion (marked_start_true hm)

private theorem N_eq_sum_run_counts (n k : Nat) :
    N n k = ∑ ell ∈ Finset.range (n+1), (Fintype.card (DegreeRunWords n ell k)) := by
  let W : Finset (Fin n → Bool) := Finset.univ.filter (fun w => Admissible w ∧ degree w=k)
  have hf : ∀ w ∈ W, runCount w ∈ Finset.range (n+1) := by
    intro w hw
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (runCount_le w))
  have hs := Finset.sum_fiberwise_of_maps_to hf (fun _ : Fin n → Bool => (1:Nat))
  have he : ∀ ell, (Fintype.card (DegreeRunWords n ell k)) =
      (W.filter (fun w => runCount w=ell)).card := by
    intro ell
    exact Fintype.card_of_subtype (W.filter (fun w => runCount w=ell))
      (fun w => by simp [W,and_assoc])
  simp only [Finset.sum_const,one_smul] at hs
  simp_rw [he]
  simpa [N,W] using hs.symm

private lemma zero_run_degree_count (n k : Nat) :
    (Fintype.card (DegreeRunWords n 0 k)) = if k = (if n≤2 then 0 else n) then 1 else 0 := by
  have he : Finset.univ.filter (fun w : Fin n → Bool =>
      Admissible w ∧ degree w=k ∧ runCount w=0) =
      if k=(if n≤2 then 0 else n) then {fun _ : Fin n => false} else ∅ := by
    ext w
    by_cases hk : k=(if n≤2 then 0 else n)
    · simp only [hk,if_true,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · intro hw
        exact (runCount_zero_iff w hw.1).mp hw.2.2
      · intro hw
        rw [hw]
        exact ⟨zero_admissible n,zero_degree n,
          (runCount_zero_iff _ (zero_admissible n)).mpr rfl⟩
    · simp only [hk,if_false,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
      intro hw
      have hwz := (runCount_zero_iff w hw.1).mp hw.2.2
      rw [hwz,zero_degree] at hw
      exact hk hw.2.1.symm
  have hcard : (Fintype.card (DegreeRunWords n 0 k)) = (Finset.univ.filter (fun w : Fin n → Bool =>
      Admissible w ∧ degree w=k ∧ runCount w=0)).card :=
    Fintype.card_of_subtype _ (fun w => by simp)
  rw [hcard,he]
  split_ifs <;> simp

local notation "y" => (Polynomial.X : Polynomial ℤ)

def runPolynomial (n ell : Nat) : (Polynomial ℤ) :=
  ∑ k ∈ Finset.range (n+1), Polynomial.C ((Fintype.card (DegreeRunWords n ell k)) : ℤ)*y^k

def tuplePolynomial (n ell : Nat) : (Polynomial ℤ) :=
  ∑ k ∈ Finset.range (n+1), Polynomial.C ((Fintype.card (DegreeTuples n ell k)) : ℤ)*y^k

private lemma goodTuple_n_pos {n : Nat} (t : GoodTuple n) : 0 < n := by
  cases ht : t.val with
  | nil => exact False.elim (t.property.1 ht)
  | cons b u =>
    have he := t.property.2.2
    have hb := t.property.2.1 b (by rw [ht];simp)
    rw [ht,tupleList_length,List.map_cons,List.sum_cons] at he
    omega

private lemma tupleDegree_le {n : Nat} (t : GoodTuple n) : tupleDegree t.val ≤ n := by
  let i : Fin n := ⟨0,goodTuple_n_pos t⟩
  have h := degree_le (wordOfTuple i t.val t.property.2.2)
  rw [degree_wordOfTuple i t] at h
  exact h

theorem polynomial_marked_double_count (n ell : Nat) :
    (ell:(Polynomial ℤ))*runPolynomial n ell=(n:(Polynomial ℤ))*tuplePolynomial n ell := by
  simp only [runPolynomial,tuplePolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := marked_degree_double_count n ell k
  have hz : (ell:ℤ)*(Fintype.card (DegreeRunWords n ell k))=(n:ℤ)*(Fintype.card (DegreeTuples n ell k)) := by exact_mod_cast h
  have hp := congrArg (fun z : ℤ => Polynomial.C z*y^k) hz
  simpa only [map_mul,map_natCast,mul_assoc] using hp

theorem tuplePolynomial_eq_sum (n ell : Nat) : tuplePolynomial n ell=
    ∑ t : RunTuples n ell, y^tupleDegree t.val.val := by
  let T : Finset (GoodTuple n) := Finset.univ.filter (fun t => t.val.length=ell)
  have hf : ∀ t ∈ T, tupleDegree t.val ∈ Finset.range (n+1) := by
    intro t ht
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (tupleDegree_le t))
  have hs := Finset.sum_fiberwise_of_maps_to hf (fun t : GoodTuple n => y^tupleDegree t.val)
  have hblock (k : Nat) :
      ∑ t ∈ T.filter (fun t => tupleDegree t.val=k), y^tupleDegree t.val =
        Polynomial.C ((Fintype.card (DegreeTuples n ell k)) : ℤ)*y^k := by
    have hcard : (T.filter (fun t => tupleDegree t.val=k)).card=(Fintype.card (DegreeTuples n ell k)) := by
      exact (Fintype.card_of_subtype _ (fun t => by simp [T,and_comm])).symm
    calc
      _ = ∑ t ∈ T.filter (fun t => tupleDegree t.val=k), y^k := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      _ = _ := by simp [hcard,nsmul_eq_mul,map_natCast,map_intCast]
  have hsub : (∑ t ∈ T, y^tupleDegree t.val) =
      ∑ t : RunTuples n ell, y^tupleDegree t.val.val :=
    Finset.sum_subtype T (fun t => by simp [T]) (fun t => y^tupleDegree t.val)
  rw [← hsub,← hs]
  simp only [tuplePolynomial,hblock]

lemma degreePolynomial_partition (n : Nat) :
    degreePolynomial n=∑ ell ∈ Finset.range (n+1), runPolynomial n ell := by
  unfold degreePolynomial runPolynomial
  simp_rw [N_eq_sum_run_counts,Nat.cast_sum,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

lemma runPolynomial_zero (n : Nat) : runPolynomial n 0=y^(if n≤2 then 0 else n) := by
  simp only [runPolynomial,zero_run_degree_count,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    apply_ite,map_one,map_zero,ite_mul,zero_mul,one_mul]
  by_cases hn : n ≤ 2 <;> simp [hn,Finset.sum_ite_eq']

end
end MarkedDegreeEnumeration
