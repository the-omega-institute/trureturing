/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalCodeCircuitReplication
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalCodeCircuitReplication
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derive actual diagonal-circuit Walsh signs for arbitrary tagged repetition, including the exact even-size threshold. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication

/-- A uniformly explicit open interval of negative three-hit coefficients
for a circuit on n distinct nonparallel columns. This sign lemma does not
assume that the coefficient is a genuine probability. -/
theorem three_hit_negative (n : ℕ) (hn : 3≤n) (x : ℝ) (hx : x<1)
    (hδ : 1-x ≤ (1/2:ℝ)^n) :
    (1-x)^3*(1+x)^(n-3)-x^(n-1)*(1-x)<0 := by
  have hhalf : (1/2:ℝ) ≤ x := by
    have hpow : (1/2:ℝ)^n ≤ (1/2:ℝ)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at hpow
    linarith
  have hnorm : ((1/2:ℝ)^n)^2 * (2:ℝ)^n = (1/2:ℝ)^n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← mul_pow]
    norm_num
  have hfirst : (1-x)^2*(1+x)^(n-3) ≤ (1/2:ℝ)^n := by
    rw [← hnorm]
    refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
    · exact pow_le_pow_left₀ (by linarith) hδ _
    · exact (pow_le_pow_left₀ (by linarith) (by linarith) _).trans
        (pow_le_pow_right₀ (by norm_num) (by omega))
  have hmiddle : (1/2:ℝ)^n < (1/2:ℝ)^(n-1) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hlast : (1/2:ℝ)^(n-1) ≤ x^(n-1) :=
    pow_le_pow_left₀ (by norm_num) hhalf _
  rw [show (1-x)^3*(1+x)^(n-3)-x^(n-1)*(1-x) =
    (1-x)*((1-x)^2*(1+x)^(n-3)-x^(n-1)) by ring]
  exact mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr (hfirst.trans_lt (hmiddle.trans_le hlast)))

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
private theorem prod_sign_weight (T S : Finset I) (x : ℝ) :
    (∏ i ∈ S, if i∈T then -x else x) = (-1:ℝ)^(T∩S).card*x^S.card := by
  have hp (i : I) : (if i∈T then -x else x) = (if i∈T then (-1:ℝ) else 1)*x := by
    split <;> simp_all
  simp only [hp,Finset.prod_mul_distrib,Finset.prod_const]
  rw [←Finset.prod_filter,Finset.filter_mem_eq_inter,Finset.inter_comm S T]
  simp

private theorem independent_walsh (T : Finset I) (x : ℝ) :
    (∑ S : Finset I, (-1:ℝ)^(T∩S).card*x^S.card) =
      (1-x)^T.card*(1+x)^(Fintype.card I-T.card) := by
  have he :
      (∏ i : I, if i∈T then 1-x else 1+x) =
      ∑ S : Finset I, (-1:ℝ)^(T∩S).card*x^S.card := by
    have hw (i : I) : (if i∈T then 1-x else 1+x) = (if i∈T then -x else x) + 1 := by
      split <;> ring
    simp only [hw]
    rw [Finset.prod_add]
    simp [prod_sign_weight]
  rw [←he,Finset.prod_ite]
  simp [Finset.filter_notMem_eq_sdiff,Finset.card_sdiff]

def oneCircuitMoment (x : ℝ) (S : Finset I) : ℝ :=
  if S=univ then x^(Fintype.card I-1) else x^S.card

theorem one_circuit_walsh_three (x : ℝ) (T : Finset I) (hT : T.card=3) :
    (∑ S : Finset I, (-1:ℝ)^(T∩S).card * oneCircuitMoment x S) =
      (1-x)^3*(1+x)^(Fintype.card I-3) - x^(Fintype.card I-1)*(1-x) := by
  have hn : 3≤Fintype.card I := hT ▸ Finset.card_le_univ T
  have hpow : x^(Fintype.card I) = x^(Fintype.card I-1)*x := by
    conv_lhs => rw [show Fintype.card I = (Fintype.card I-1)+1 by omega, pow_succ]
  have step (S : Finset I) :
      (-1:ℝ)^(T∩S).card * oneCircuitMoment x S =
      (-1:ℝ)^(T∩S).card*x^S.card -
        if S=univ then x^(Fintype.card I-1)*(1-x) else 0 := by
    by_cases hS : S=univ
    · subst S
      simp [oneCircuitMoment,hT,hpow]
      ring
    · simp [oneCircuitMoment,hS]
  simp only [step,sum_sub_distrib,independent_walsh,hT]
  congr 1
  rw [sum_eq_single univ]
  · simp
  · intro S _ hS; simp [hS]
  · simp

theorem one_circuit_negative_three (x : ℝ) (T : Finset I) (hT : T.card=3)
    (hx : x<1) (hδ : 1-x≤(1/2:ℝ)^Fintype.card I) :
    (∑ S : Finset I, (-1:ℝ)^(T∩S).card * oneCircuitMoment x S)<0 := by
  rw [one_circuit_walsh_three _ _ hT]
  exact three_hit_negative _ (hT ▸ Finset.card_le_univ T) _ hx hδ

/-- The exact unnormalised Walsh coefficient for every labelled subset. -/
theorem one_circuit_walsh (x : ℝ) (T : Finset I) (hn : 1≤Fintype.card I) :
    (∑ S : Finset I, (-1:ℝ)^(T∩S).card * oneCircuitMoment x S) =
      (1-x)^T.card*(1+x)^(Fintype.card I-T.card) +
        (-1:ℝ)^T.card * x^(Fintype.card I-1)*(1-x) := by
  have e : x^(Fintype.card I) = x^(Fintype.card I-1)*x := by
    conv_lhs => rw [show Fintype.card I=(Fintype.card I-1)+1 by omega,pow_succ]
  have h (S : Finset I) :
      (-1:ℝ)^(T∩S).card*oneCircuitMoment x S =
      (-1:ℝ)^(T∩S).card*x^S.card +
        if S=univ then (-1:ℝ)^T.card*x^(Fintype.card I-1)*(1-x) else 0 := by
    by_cases hS : S=univ
    · subst S
      simp [oneCircuitMoment,e]
      ring
    · simp [oneCircuitMoment,hS]
  simp only [h,sum_add_distrib,independent_walsh]
  congr 1
  rw [sum_eq_single univ]
  · simp
  · intro S _ hS; simp [hS]
  · simp

/-- All labels are nonnegative for x at most one half, at every circuit size. -/
theorem one_circuit_nonneg_le_half (x : ℝ) (hx : 0≤x) (hx' : x≤1/2)
    (T : Finset I) (hn : 1≤Fintype.card I) :
    0≤(∑ S : Finset I, (-1:ℝ)^(T∩S).card*oneCircuitMoment x S) := by
  rw [one_circuit_walsh _ _ hn]
  have h₁ : 0≤1-x := by linarith
  have h₂ : 0≤1+x := by linarith
  have hc : T.card≤Fintype.card I := card_le_univ T
  have hdom : (1-x)^Fintype.card I ≤ (1-x)^T.card*(1+x)^(Fintype.card I-T.card) := by
    conv_lhs => rw [show Fintype.card I = T.card+(Fintype.card I-T.card) by omega,pow_add]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg h₁ _)
    exact pow_le_pow_left₀ h₁ (by linarith) _
  have hcor : x^(Fintype.card I-1)*(1-x) ≤ (1-x)^Fintype.card I := by
    conv_rhs => rw [show Fintype.card I=(Fintype.card I-1)+1 by omega,pow_succ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx (by linarith) _) h₁
  rcases Nat.even_or_odd T.card with hT | hT
  · rw [hT.neg_one_pow]
    positivity
  · rw [hT.neg_one_pow]
    linarith [hcor.trans hdom]

/-- For an odd circuit of size at least three, the full label is strictly
negative above one half. Together with positivity this gives its exact threshold. -/
theorem odd_circuit_full_neg (x : ℝ) (hx : 1/2<x) (hx' : x<1) (hn : 3≤Fintype.card I)
    (hOdd : Odd (Fintype.card I)) :
    (∑ S : Finset I, (-1:ℝ)^S.card*oneCircuitMoment x S)<0 := by
  have e := one_circuit_walsh (I:=I) x univ (by omega)
  simp only [univ_inter,card_univ,Nat.sub_self,pow_zero,mul_one,hOdd.neg_one_pow] at e
  rw [e]
  have h : (1-x)^(Fintype.card I-1) < x^(Fintype.card I-1) :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
  have h' := mul_lt_mul_of_pos_right h (by linarith : 0<1-x)
  conv_lhs at h' => rw [←pow_succ, show (Fintype.card I-1)+1=Fintype.card I by omega]
  linarith

private theorem independent_term_anti (x : ℝ) (hx : 0≤x) (hx' : x≤1)
    {a b n : ℕ} (hab : a≤b) (hbn : b≤n) :
    (1-x)^b*(1+x)^(n-b) ≤ (1-x)^a*(1+x)^(n-a) := by
  have h1 : 0≤1-x := sub_nonneg.mpr hx'
  have h2 : 0≤1+x := by positivity
  have e1 : b=a+(b-a) := by omega
  have e2 : n-a=(b-a)+(n-b) := by omega
  conv_lhs => rw [e1,pow_add]
  rw [show n-(a+(b-a))=n-b by omega,e2,pow_add,←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg h2 _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 (by linarith) _) (pow_nonneg h1 _)

/-- Even masks always have nonnegative coefficients. Among odd masks the
largest odd cardinality is the exact obstruction. -/
theorem circuit_worst_odd (x : ℝ) (hx : 0≤x) (hx' : x≤1) (L : Finset I)
    (hL : Odd L.card) (hmax : ∀ T : Finset I, Odd T.card → T.card≤L.card) :
    (∀ T : Finset I, 0≤(∑ S : Finset I, (-1:ℝ)^(T∩S).card*oneCircuitMoment x S)) ↔
    x^(Fintype.card I-1)*(1-x) ≤ (1-x)^L.card*(1+x)^(Fintype.card I-L.card) := by
  have h₁ : 0≤1-x := sub_nonneg.mpr hx'
  have h₂ : 0≤1+x := by positivity
  have hpos : 1≤Fintype.card I := by
    have hcard := Finset.card_le_univ L
    obtain ⟨k,hk⟩ := hL
    omega
  simp_rw [one_circuit_walsh x _ hpos]
  constructor
  · intro h
    have t := h L
    rw [hL.neg_one_pow] at t
    linarith
  · intro h T
    rcases Nat.even_or_odd T.card with ht | ht
    · rw [ht.neg_one_pow]
      positivity
    · rw [ht.neg_one_pow]
      have h' := h.trans (independent_term_anti x hx hx' (hmax T ht) (Finset.card_le_univ L))
      linarith

/-- Exact cancellation over one nonempty copy block, and the residual
minus-one if any selected site has a mark. -/
theorem nonempty_fiber_sign (T : Finset I) :
    (∑ S ∈ (univ : Finset (Finset I)).erase ∅, (-1:ℝ)^(T∩S).card) =
      if T=∅ then (2:ℝ)^Fintype.card I-1 else -1 := by
  have hh := independent_walsh T 1
  simp only [one_pow,mul_one,sub_self,one_add_one_eq_two] at hh
  rw [←Finset.sum_erase_add univ (fun S : Finset I => (-1:ℝ)^(T∩S).card) (Finset.mem_univ ∅)] at hh
  simp only [inter_empty,card_empty,pow_zero] at hh
  by_cases ht : T=∅
  · subst T
    simp only [card_empty,pow_zero,one_mul,Nat.sub_zero] at hh
    simp only [ite_true]
    linarith
  · have hp : T.card≠0 := by simpa using ht
    rw [zero_pow hp,zero_mul] at hh
    rw [ite_eq_right ht]
    linarith

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Normalised product for an odd occupied support. The unoccupied sites have
a factor equal to the moment parameter plus the reciprocal of their nontrivial
subset count. -/
noncomputable def replicatedIndependent (x : ℝ) (a : I → ℝ) (U : Finset I) : ℝ :=
  ∏ i : I, if i ∈ U then (1-x) else a i

theorem replicated_small_x (x : ℝ) (hx : 0≤x) (hsmall : x≤1/2)
    (a : I → ℝ) (ha : ∀ i, x≤a i)
    (U : Finset I) (hU : U.Nonempty) :
    x^(Fintype.card I-1)*(1-x)≤replicatedIndependent x a U := by
  obtain ⟨j,hj⟩ := hU
  unfold replicatedIndependent
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), ite_eq_left hj]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ j), ← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun _ _ => hx)
  intro i _
  split
  · linarith
  · exact ha i

theorem replicated_anti (x : ℝ) (hx : x≤1) (a : I → ℝ) (ha : ∀ i, 1-x ≤ a i)
    {U V : Finset I} (h : U⊆V) :
    replicatedIndependent x a V ≤ replicatedIndependent x a U := by
  unfold replicatedIndependent
  apply Finset.prod_le_prod₀
  · intro i _
    split
    · linarith
    · exact (sub_nonneg.mpr hx).trans (ha i)
  · intro i _
    by_cases hi : i ∈ U
    · simp [hi,h hi]
    · by_cases hv : i ∈ V <;> simp [hi,hv,ha i]

theorem replicated_omit_one (x : ℝ) (a : I → ℝ) (j : I) :
    replicatedIndependent x a (univ.erase j) = (1-x)^(Fintype.card I-1)*a j := by
  unfold replicatedIndependent
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_univ, and_true,
    ite_false]
  congr 1
  rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ j), ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro i hi
  rw [ite_eq_left (Finset.mem_erase.mp hi).1]

/-- For even circuit size and x at least one half, it suffices to omit just
one class, and the weakest remaining factor is the only one that matters. -/
theorem replicated_even_minimum (x : ℝ) (hx : x≤1) (a : I → ℝ)
    (ha : ∀ i, 1-x≤a i) (nEven : Even (Fintype.card I))
    (j : I) (hj : ∀ i, a j≤a i) :
    (∀ U : Finset I, Odd U.card →
      x^(Fintype.card I-1)*(1-x) ≤ replicatedIndependent x a U) ↔
      x^(Fintype.card I-1)*(1-x) ≤ (1-x)^(Fintype.card I-1)*a j := by
  constructor
  · intro h
    have hjcard : Odd (univ.erase j).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ]
      have hp : 0<Fintype.card I := Fintype.card_pos_iff.mpr ⟨j⟩
      obtain ⟨v,hv⟩ := nEven
      exact ⟨v-1,by omega⟩
    simpa only [replicated_omit_one] using h _ hjcard
  · intro h U hU
    have hproper : U ≠ univ := by
      intro he
      subst U
      rw [Finset.card_univ] at hU
      obtain ⟨k,hk⟩ := hU
      obtain ⟨v,hv⟩ := nEven
      omega
    have hex : ∃ i : I, i ∉ U := by
      by_contra! hall
      exact hproper (Finset.eq_univ_iff_forall.mpr hall)
    obtain ⟨i,hi⟩ := hex
    have hsub : U ⊆ univ.erase i := fun v hv =>
      Finset.mem_erase.mpr ⟨fun he => hi (he ▸ hv),Finset.mem_univ v⟩
    apply h.trans (le_trans _ (replicated_anti x hx a ha hsub))
    rw [replicated_omit_one]
    exact mul_le_mul_of_nonneg_left (hj i) (pow_nonneg (sub_nonneg.mpr hx) _)

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- The algebraic form of Walsh cancellation along arbitrary finite copy
fibers. The two terms distinguish whether all original classes are occupied. -/
theorem fiber_circuit_factor (x d : ℝ) (z : ∀ i, A i)
    (w : ∀ i, A i → ℝ) (hw : ∀ i, w i (z i)=1) :
    (∑ f : ∀ i, A i,
      (∏ i : I, w i (f i)) *
        ((∏ i : I, if f i=z i then 1 else x)+d*(∏ i : I, if f i=z i then 0 else 1))) =
    (∏ i : I, (1+x*(∑ a ∈ (univ : Finset (A i)).erase (z i), w i a))) +
      d*(∏ i : I, ∑ a ∈ (univ : Finset (A i)).erase (z i), w i a) := by
  let b (i : I) (a : A i) : ℝ := if a=z i then 1 else x
  let e (i : I) (a : A i) : ℝ := if a=z i then 0 else 1
  have hterm (f : ∀ i, A i) :
      (∏ i : I, w i (f i))*((∏ i : I, b i (f i))+d*(∏ i : I, e i (f i))) =
      (∏ i : I, w i (f i)*b i (f i))+d*(∏ i : I, w i (f i)*e i (f i)) := by
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    ring
  change (∑ f : ∀ i, A i, (∏ i : I, w i (f i))*((∏ i : I, b i (f i))+
    d*(∏ i : I, e i (f i)))) = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Fintype.prod_sum (fun i a => w i a * b i a),
    ← Fintype.prod_sum (fun i a => w i a * e i a)]
  have hb i : (∑ a : A i, w i a*b i a) = 1+x*(∑ a ∈ (univ : Finset (A i)).erase (z i), w i a) := by
    rw [←Finset.sum_erase_add univ (fun a => w i a*b i a) (Finset.mem_univ (z i)),hw i]
    simp only [b,ite_eq_left rfl,mul_one]
    rw [add_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ite_eq_right (Finset.mem_erase.mp ha).1,mul_comm]
  have he i : (∑ a : A i, w i a*e i a) = ∑ a ∈ (univ : Finset (A i)).erase (z i), w i a := by
    rw [← Finset.sum_erase_add univ (fun a => w i a*e i a) (Finset.mem_univ (z i)),hw i]
    simp only [e,ite_eq_left rfl,mul_zero,add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ite_eq_right (Finset.mem_erase.mp ha).1,mul_one]
  simp only [hb,he]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

/-- Subsets of tagged copies are exactly choices of one subset in each fiber. -/
def fiberEquiv : (∀ i, Finset (J i)) ≃ Finset (Sigma J) where
  toFun f := univ.sigma f
  invFun S i := univ.filter (fun j => Sigma.mk i j ∈ S)
  left_inv f := by
    funext i
    ext j
    simp
  right_inv s := by
    ext v
    obtain ⟨i,j⟩ := v
    simp

theorem fiber_sigma_inter_card (T S : ∀ i, Finset (J i)) :
    ((fiberEquiv T) ∩ (fiberEquiv S)).card =
      ∑ i : I, (T i∩S i).card := by
  rw [← card_sigma]
  congr 1
  ext a
  obtain ⟨i,j⟩ := a
  simp [fiberEquiv]

theorem fiber_image (f : ∀ i, Finset (J i)) :
    (fiberEquiv f).image Sigma.fst = univ.filter (fun i => (f i).Nonempty) := by
  ext i
  simp only [fiberEquiv,Equiv.coe_fn_mk,mem_image,mem_sigma,mem_univ,true_and,mem_filter]
  constructor
  · rintro ⟨⟨j,k⟩,hk,rfl⟩
    exact ⟨k,hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨⟨i,k⟩,hk,rfl⟩

theorem fiber_shape (x : ℝ) (hn : 1 ≤ Fintype.card I) (f : ∀ i, Finset (J i)) :
    oneCircuitMoment x ((fiberEquiv f).image Sigma.fst) =
    (∏ i : I, if f i=∅ then 1 else x) +
      x^(Fintype.card I-1)*(1-x)*(∏ i : I, if f i=∅ then 0 else 1) := by
  classical
  let a := (fiberEquiv f).image Sigma.fst
  change oneCircuitMoment x a = _
  have hbase : (∏ i : I, if f i=∅ then 1 else x) = x^a.card := by
    have hh (i : I) : (if f i=∅ then (1:ℝ) else x) = if (f i).Nonempty then x else 1 := by
      by_cases hi : f i=∅
      · simp [hi]
      · simp [hi,Finset.nonempty_iff_ne_empty.mpr hi]
    simp_rw [hh]
    rw [←Finset.prod_filter]
    simp [a,fiber_image]
  have hfull : (∏ i : I, if f i=∅ then (0:ℝ) else 1) = if a=univ then 1 else 0 := by
    by_cases h : a=univ
    · have hnon (i : I) : f i ≠ ∅ := by
        have hi : i ∈ a := h ▸ Finset.mem_univ i
        exact Finset.nonempty_iff_ne_empty.mp (by simpa [a,fiber_image] using hi)
      simp [hnon,h]
    · have hex : ∃ i : I, i∉a := by
        by_contra! hall
        exact h (Finset.eq_univ_iff_forall.mpr hall)
      obtain ⟨i,hi⟩ := hex
      have he : f i=∅ := by
        by_contra! he
        exact hi (by simpa [a,fiber_image] using he)
      rw [ite_eq_right h, Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [he]
  rw [hbase,hfull]
  by_cases he : a=univ
  · have hpow : x ^ Fintype.card I = x ^ (Fintype.card I-1)*x := by
      conv_lhs => rw [show Fintype.card I=(Fintype.card I-1)+1 by omega,pow_succ]
    simp [oneCircuitMoment,he,hpow]
    ring
  · simp [oneCircuitMoment,he]

set_option maxHeartbeats 600000 in
/-- The signed Walsh numerator for the circuit-moment pullback. Empty
copy fibers are allowed; their zero nonempty-sign factor removes the
circuit correction exactly. -/
theorem fiber_walsh_formula (x : ℝ) (hn : 1≤Fintype.card I)
    (T : ∀ i, Finset (J i)) :
    let c (i : I) := if T i=∅ then (2:ℝ)^Fintype.card (J i)-1 else -1
    (∑ S : Finset (Sigma J), (-1:ℝ)^((fiberEquiv T)∩S).card *
      oneCircuitMoment x (S.image Sigma.fst)) =
      (∏ i : I, (1+x*c i)) + x^(Fintype.card I-1)*(1-x)*(∏ i : I, c i) := by
  dsimp only
  let d := x^(Fintype.card I-1)*(1-x)
  let w (i : I) (a : Finset (J i)) := (-1:ℝ)^((T i)∩a).card
  calc
    _ = ∑ f : ∀ i, Finset (J i), (-1:ℝ)^((fiberEquiv T)∩fiberEquiv f).card *
        oneCircuitMoment x ((fiberEquiv f).image Sigma.fst) :=
      (Equiv.sum_comp fiberEquiv _).symm
    _ = ∑ f : ∀ i, Finset (J i), (∏ i : I, w i (f i)) *
        ((∏ i : I, if f i=∅ then 1 else x)+d*(∏ i : I, if f i=∅ then 0 else 1)) := by
      apply sum_congr rfl
      intro f _
      rw [fiber_sigma_inter_card, fiber_shape x hn f]
      unfold w d
      rw [Finset.prod_pow_eq_pow_sum]
    _ = _ := by
      rw [fiber_circuit_factor x d (fun _ => ∅) w (by intro i; simp [w])]
      unfold w
      simp only [nonempty_fiber_sign]
      rfl

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Normalize away all positive fiber factors. The only surviving sign is
the parity of the occupied original classes. -/
theorem normalize_fiber (x d : ℝ) (U : Finset I) (z : I → ℝ)
    (hz : ∀ i, 0<z i) :
    let c (i : I) := if i∈U then (-1:ℝ) else z i
    (∏ i : I, (1+x*c i))+d*(∏ i : I, c i) =
      (∏ i : I, if i∈U then (1:ℝ) else z i) *
        (replicatedIndependent x (fun i => x + (z i)⁻¹) U + (-1:ℝ)^U.card*d) := by
  dsimp only
  let w (i : I) := if i∈U then (1:ℝ) else z i
  have h₁ (i : I) : 1+x*(if i∈U then (-1:ℝ) else z i) =
      w i*(if i∈U then 1-x else x+(z i)⁻¹) := by
    by_cases hi : i∈U
    · simp [hi,w]
      ring
    · simp [hi,w,mul_add,(hz i).ne']
      ring
  have h₂ (i : I) : (if i∈U then (-1:ℝ) else z i) =
      w i*(if i∈U then (-1:ℝ) else 1) := by
    by_cases hi : i∈U <;> simp [hi,w]
  have hsign : (∏ i : I, if i∈U then (-1:ℝ) else 1) = (-1:ℝ)^U.card := by
    rw [←prod_filter]
    simp
  simp_rw [h₁,h₂,Finset.prod_mul_distrib,hsign,replicatedIndependent]
  ring

theorem normalize_fiber_sign (x d : ℝ) (U : Finset I) (z : I → ℝ)
    (hz : ∀ i, 0<z i) :
    let c (i : I) := if i∈U then (-1:ℝ) else z i
    0 ≤ (∏ i : I, (1+x*c i))+d*(∏ i : I, c i) ↔
      0 ≤ replicatedIndependent x (fun i => x + (z i)⁻¹) U + (-1:ℝ)^U.card*d := by
  dsimp only
  rw [normalize_fiber x d U z hz]
  have hp : 0 < ∏ i : I, if i∈U then (1:ℝ) else z i := by
    apply Finset.prod_pos
    intro i _
    split
    · norm_num
    · exact hz i
  exact mul_nonneg_iff_of_pos_left hp

/-- All occupied sets are tested by the maximally weak omitted fiber. -/
theorem normalized_even_criterion (x : ℝ) (hx : 0≤x) (hx' : x<1)
    (a : I → ℝ) (ha : ∀ i, x≤a i) (hn : 4≤Fintype.card I)
    (he : Even (Fintype.card I)) (j : I) (hj : ∀ i, a j≤a i) :
    (∀ U : Finset I,
      0≤replicatedIndependent x a U+(-1:ℝ)^U.card*(x^(Fintype.card I-1)*(1-x))) ↔
      x^(Fintype.card I-1) ≤ (1-x)^(Fintype.card I-2)*a j := by
  have hp : 0<1-x := by linarith
  have hodd :
      (∀ U : Finset I,
        0≤replicatedIndependent x a U+(-1:ℝ)^U.card*(x^(Fintype.card I-1)*(1-x))) ↔
      (∀ U : Finset I, Odd U.card →
        x^(Fintype.card I-1)*(1-x)≤replicatedIndependent x a U) := by
    constructor
    · intro h U hU
      have hh := h U
      rw [hU.neg_one_pow] at hh
      linarith
    · intro h U
      rcases Nat.even_or_odd U.card with hU | hU
      · rw [hU.neg_one_pow,one_mul]
        apply add_nonneg _ (mul_nonneg (pow_nonneg hx _) hp.le)
        unfold replicatedIndependent
        apply Finset.prod_nonneg
        intro i _
        split
        · exact hp.le
        · exact hx.trans (ha i)
      · rw [hU.neg_one_pow]
        linarith [h U hU]
  rw [hodd]
  by_cases hs : x≤1/2
  · have hright : x^(Fintype.card I-1) ≤ (1-x)^(Fintype.card I-2)*a j := by
      conv_lhs => rw [show Fintype.card I-1=(Fintype.card I-2)+1 by omega,pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ hx (by linarith) _) (ha j) hx (pow_nonneg hp.le _)
    refine ⟨fun _ => hright,fun _ U hU => ?_⟩
    have hpos : 0 < U.card := by obtain ⟨k,hk⟩ := hU; omega
    exact replicated_small_x x hx hs a ha U (Finset.card_pos.mp hpos)
  · rw [replicated_even_minimum x hx'.le a (fun i => le_trans (by linarith) (ha i)) he j hj]
    rw [show (1-x)^(Fintype.card I-1) = (1-x)^(Fintype.card I-2)*(1-x) by
      conv_lhs => rw [show Fintype.card I-1=(Fintype.card I-2)+1 by omega,pow_succ]]
    rw [mul_right_comm, mul_le_mul_iff_of_pos_right hp]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
open Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

noncomputable section

variable {F V I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype (Module.Dual F V)]
  [Fintype I] [DecidableEq I]

section CircuitHypotheses

variable {F₀ V₀ I₀ : Type*} [Field F₀] [AddCommGroup V₀] [Module F₀ V₀]
  [FiniteDimensional F₀ V₀] [Fintype I₀] [DecidableEq I₀]

/-- The intrinsic linear-algebraic circuit condition. -/
def IsColumnCircuit (v : I₀ → V₀) : Prop :=
  ¬ LinearIndependent F₀ v ∧
    ∀ S : Finset I₀, S ≠ univ → LinearIndependent F₀ (fun i : S => v i)

omit [AddCommGroup V₀] [Fintype I₀] [DecidableEq I₀] in
private theorem col_range (v : I₀ → V₀) (S : Finset I₀) :
    Set.range (fun i : S => v i) = v '' (S : Set I₀) := by
  ext y
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

omit [FiniteDimensional F₀ V₀] [DecidableEq I₀] in
theorem circuit_proper_rank (v : I₀ → V₀) (h : IsColumnCircuit (F₀:=F₀) v)
    (S : Finset I₀) (hS : S ≠ univ) :
    Module.finrank F₀ (columns (F:=F₀) v S) = S.card := by
  rw [columns, ← col_range]
  simpa only [Fintype.card_coe] using finrank_span_eq_card (h.2 S hS)

theorem circuit_full_rank (v : I₀ → V₀) (h : IsColumnCircuit (F₀:=F₀) v)
    [Nonempty I₀] : Module.finrank F₀ (columns (F:=F₀) v univ) = Fintype.card I₀ - 1 := by
  classical
  let i : I₀ := Classical.choice inferInstance
  let S : Finset I₀ := univ.erase i
  have hmem : i ∉ S := by simp [S]
  have hne : S ≠ univ := fun e => hmem (e ▸ mem_univ i)
  have hlo := circuit_proper_rank v h S hne
  have hcard : S.card = Fintype.card I₀ - 1 := by simp [S]
  have hm : columns (F:=F₀) v S ≤ columns (F:=F₀) v univ :=
    Submodule.span_mono (Set.image_mono (by simp))
  have hlo' := Submodule.finrank_mono hm
  rw [hlo,hcard] at hlo'
  have hupper : Module.finrank F₀ (columns (F:=F₀) v univ) < Fintype.card I₀ := by
    rw [columns, Finset.coe_univ, Set.image_univ]
    apply lt_of_le_of_ne (finrank_range_le_card v)
    exact fun e => h.1 ((linearIndependent_iff_card_eq_finrank_span).mpr e.symm)
  omega

end CircuitHypotheses

private theorem moment_of_rank_circuit (v : I → V)
    (hfull : Module.finrank F (columns (F:=F) v (univ : Finset I)) = Fintype.card I-1)
    (hproper : ∀ S : Finset I, S ≠ univ → Module.finrank F (columns (F:=F) v S) = S.card)
    {K : ℝ} (hK : 0<K) :
    (fun S => (((mixedMarginal (F:=F) v S) ^ K).trace).re) =
      oneCircuitMoment ((Fintype.card F:ℝ)^(1-K)) := by
  funext S
  rw [actual_column_moment _ _ hK]
  by_cases he : S = univ
  · subst S
    simp [oneCircuitMoment,hfull]
  · simp [oneCircuitMoment,hproper S he,he]

/-- The nonnegativity obstruction concerns actual reduced density moments. The
rank hypothesis is the intrinsically checkable proper/full circuit identity. -/
theorem actual_circuit_no_hit (v : I → V)
    (hfull : Module.finrank F (columns (F:=F) v (univ : Finset I)) = Fintype.card I-1)
    (hproper : ∀ S : Finset I, S ≠ univ → Module.finrank F (columns (F:=F) v S) = S.card)
    (T : Finset I) (hT : T.card=3) {K : ℝ} (hK : 1<K)
    (hδ : 1-(Fintype.card F:ℝ)^(1-K) ≤ (1/2:ℝ)^Fintype.card I) :
    ¬ hitLaw (fun S => (((mixedMarginal (F:=F) v S)^K).trace).re) := by
  let x : ℝ := (Fintype.card F:ℝ)^(1-K)
  have hF : 1 < (Fintype.card F:ℝ) := by exact_mod_cast Fintype.one_lt_card (α:=F)
  have hx : x<1 := Real.rpow_lt_one_of_one_lt_of_neg hF (by linarith)
  rw [moment_of_rank_circuit v hfull hproper (by linarith)]
  have hnonempty : (univ : Finset I) ≠ ∅ := by
    have : 3 ≤ Fintype.card I := hT ▸ Finset.card_le_univ T
    intro e
    have he := congrArg Finset.card e
    simp at he
    omega
  have h0 : oneCircuitMoment x (∅ : Finset I)=1 := by
    simp [oneCircuitMoment,Ne.symm hnonempty]
  intro h
  have hm := (hitLaw_iff _ h0).mp h T
  rw [inverse] at hm
  simp only [sign_as_power,mul_comm (oneCircuitMoment x _)] at hm
  have hn := one_circuit_negative_three x T hT hx hδ
  exact (div_neg_of_neg_of_pos hn (by unfold walshNorm; positivity)).not_ge hm

/-- Exact positivity criterion, checking only the largest odd label, for
the actual finite-field diagonal density of any circuit. -/
theorem actual_circuit_coverage_iff (v : I → V)
    (hfull : Module.finrank F (columns (F:=F) v (univ : Finset I)) = Fintype.card I-1)
    (hproper : ∀ S : Finset I, S ≠ univ → Module.finrank F (columns (F:=F) v S) = S.card)
    (L : Finset I) (hL : Odd L.card)
    (hmax : ∀ T : Finset I, Odd T.card → T.card≤L.card) {K : ℝ} (hK : 1<K) :
    let x := (Fintype.card F:ℝ)^(1-K)
    hitLaw (fun S => (((mixedMarginal (F:=F) v S)^K).trace).re) ↔
      x^(Fintype.card I-1)*(1-x) ≤ (1-x)^L.card*(1+x)^(Fintype.card I-L.card) := by
  let x : ℝ := (Fintype.card F:ℝ)^(1-K)
  change hitLaw _ ↔ x^(Fintype.card I-1)*(1-x) ≤ _
  have hF : 1 < (Fintype.card F:ℝ) := by exact_mod_cast Fintype.one_lt_card (α:=F)
  have hx : 0≤x := by dsimp [x]; positivity
  have hx' : x≤1 := (Real.rpow_lt_one_of_one_lt_of_neg hF (by linarith)).le
  rw [moment_of_rank_circuit v hfull hproper (by linarith)]
  have hn : 1≤Fintype.card I := by
    have hc := card_le_univ L
    obtain ⟨j,hj⟩ := hL
    omega
  have hne : (∅ : Finset I) ≠ univ := by
    intro e
    have he := congrArg Finset.card e
    simp at he
    omega
  have h0 : oneCircuitMoment x (∅ : Finset I)=1 := by simp [oneCircuitMoment,hne]
  rw [hitLaw_iff _ h0]
  have hnorm : 0 < walshNorm I := by unfold walshNorm; positivity
  simp_rw [inverse,div_eq_mul_inv,mul_nonneg_iff_of_pos_right (inv_pos.mpr hnorm),sign_as_power,mul_comm (oneCircuitMoment x _)]
  exact circuit_worst_odd x hx hx' L hL hmax

theorem actual_circuit_walsh (v : I → V) (h : IsColumnCircuit (F₀:=F) v)
    (T : Finset I) (hn : 1≤Fintype.card I) {K : ℝ} (hK : 0<K) :
    let x := (Fintype.card F:ℝ)^(1-K)
    inverse (fun S => (((mixedMarginal (F:=F) v S)^K).trace).re) T =
      ((1-x)^T.card*(1+x)^(Fintype.card I-T.card) +
        (-1:ℝ)^T.card*x^(Fintype.card I-1)*(1-x)) / walshNorm I := by
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  rw [moment_of_rank_circuit v (circuit_full_rank v h) (circuit_proper_rank v h) hK,inverse]
  simp only [sign_as_power,mul_comm (oneCircuitMoment _ _)]
  rw [one_circuit_walsh _ _ hn]

/-- An odd minimal linear dependency protects every label exactly at x ≤ 1/2. -/
theorem actual_odd_circuit_threshold (v : I → V) (h : IsColumnCircuit (F₀:=F) v)
    (hn : 3≤Fintype.card I) (hodd : Odd (Fintype.card I)) {K : ℝ} (hK : 1<K) :
    hitLaw (fun S => (((mixedMarginal (F:=F) v S)^K).trace).re) ↔
      (Fintype.card F:ℝ)^(1-K) ≤ 1/2 := by
  let x : ℝ := (Fintype.card F:ℝ)^(1-K)
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hF : 1 < (Fintype.card F:ℝ) := by exact_mod_cast Fintype.one_lt_card (α:=F)
  have hx : 0≤x := by dsimp [x]; positivity
  have hx' : x<1 := Real.rpow_lt_one_of_one_lt_of_neg hF (by linarith)
  have hr := actual_circuit_coverage_iff v (circuit_full_rank v h) (circuit_proper_rank v h)
    (univ : Finset I) (by simpa using hodd) (fun t _ => by simpa using card_le_univ t) hK
  dsimp only at hr
  rw [hr]
  change x^(Fintype.card I-1)*(1-x) ≤
    (1-x)^((univ : Finset I).card)*(1+x)^(Fintype.card I-(univ : Finset I).card) ↔ x≤1/2
  simp only [card_univ,Nat.sub_self,pow_zero,mul_one]
  rw [show (1-x)^Fintype.card I=(1-x)^(Fintype.card I-1)*(1-x) by
    conv_lhs => rw [show Fintype.card I=(Fintype.card I-1)+1 by omega,pow_succ]]
  rw [mul_le_mul_iff_of_pos_right (show 0<1-x by linarith)]
  constructor
  · intro hle
    by_contra! hgt
    have hl : (1-x)^(Fintype.card I-1) < x^(Fintype.card I-1) :=
      pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
    exact hl.not_ge hle
  · intro hle
    exact pow_le_pow_left₀ hx (by linarith) _

/-- The sharp even-circuit threshold is again one inequality. A largest
odd label is obtained by omitting one of the coordinates. -/
theorem actual_even_circuit_threshold (v : I → V) (h : IsColumnCircuit (F₀:=F) v)
    (hn : 4≤Fintype.card I) (heven : Even (Fintype.card I)) {K : ℝ} (hK : 1<K) :
    let x := (Fintype.card F:ℝ)^(1-K)
    hitLaw (fun S => (((mixedMarginal (F:=F) v S)^K).trace).re) ↔
      x^(Fintype.card I-1) ≤ (1-x)^(Fintype.card I-2)*(1+x) := by
  let x : ℝ := (Fintype.card F:ℝ)^(1-K)
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let i : I := Classical.choice inferInstance
  let L : Finset I := univ.erase i
  have hL : L.card = Fintype.card I - 1 := by simp [L]
  have ho : Odd L.card := by
    rw [hL]
    obtain ⟨j,hj⟩ := heven
    exact ⟨j-1,by omega⟩
  have hmax (T : Finset I) (ht : Odd T.card) : T.card≤L.card := by
    rw [hL]
    have hle := card_le_univ T
    obtain ⟨a,ha⟩ := ht
    obtain ⟨b,hb⟩ := heven
    omega
  have hF : 1 < (Fintype.card F:ℝ) := by exact_mod_cast Fintype.one_lt_card (α:=F)
  have hx' : x<1 := Real.rpow_lt_one_of_one_lt_of_neg hF (by linarith)
  have hr := actual_circuit_coverage_iff v (circuit_full_rank v h) (circuit_proper_rank v h) L ho hmax hK
  change hitLaw _ ↔ x^(Fintype.card I-1) ≤ (1-x)^(Fintype.card I-2)*(1+x)
  dsimp only at hr
  rw [hr]
  change _ * (1-x) ≤ (1-x)^L.card*(1+x)^(Fintype.card I-L.card) ↔ _
  rw [hL,show Fintype.card I-(Fintype.card I-1)=1 by omega,pow_one]
  rw [show (1-x)^(Fintype.card I-1)=(1-x)^(Fintype.card I-2)*(1-x) by
    conv_lhs => rw [show Fintype.card I-1=(Fintype.card I-2)+1 by omega,pow_succ]]
  rw [mul_right_comm, mul_le_mul_iff_of_pos_right (show 0<1-x by linarith)]

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
open Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
variable {F V I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype (Module.Dual F V)]
  [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

/-- This repeated Walsh formula is for the actual normalized diagonal density
on the tagged copy system, not just an abstract signed circuit model. -/
theorem physical_fiber_circuit_numerator (v : I → V) (h : IsColumnCircuit (F₀:=F) v)
    (T : ∀ i, Finset (J i)) (hn : 1≤Fintype.card I) {K : ℝ} (hK : 0<K) :
    let x := (Fintype.card F:ℝ)^(1-K)
    let c (i : I) := if T i=∅ then (2:ℝ)^Fintype.card (J i)-1 else -1
    (∑ S : Finset (Sigma J), (-1:ℝ)^((fiberEquiv T)∩S).card *
      (((mixedMarginal (F:=F) (v ∘ Sigma.fst) S)^K).trace).re) =
      (∏ i : I, (1+x*c i)) + x^(Fintype.card I-1)*(1-x)*(∏ i : I, c i) := by
  dsimp only
  let x := (Fintype.card F:ℝ)^(1-K)
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have eqm (S : Finset (Sigma J)) :
      (((mixedMarginal (F:=F) (v ∘ Sigma.fst) S)^K).trace).re =
        oneCircuitMoment x (S.image Sigma.fst) := by
    rw [actual_column_moment _ _ hK]
    have he : columns (F:=F) (v ∘ Sigma.fst) S = columns (F:=F) v (S.image Sigma.fst) := by
      unfold columns
      rw [Finset.coe_image,Set.image_image]
      rfl
    rw [he]
    by_cases hs : S.image Sigma.fst = univ
    · rw [hs,circuit_full_rank v h]
      simp [x,oneCircuitMoment]
    · simp [x,oneCircuitMoment,hs,circuit_proper_rank v h _ hs]
  simp_rw [eqm]
  exact fiber_walsh_formula x hn T

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
variable {F V I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype (Module.Dual F V)]
  [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

/-- In every even circuit, arbitrary positive replication counts affect the
classical coverage threshold only through the largest replication count. -/
theorem physical_even_fiber_threshold [∀ i, Nonempty (J i)]
    (v : I → V) (h : IsColumnCircuit (F₀:=F) v)
    (hn : 4≤Fintype.card I) (he : Even (Fintype.card I))
    (j : I) (hj : ∀ i, Fintype.card (J i)≤Fintype.card (J j)) {K : ℝ} (hK : 1<K) :
    let x := (Fintype.card F:ℝ)^(1-K)
    hitLaw (fun S => (((mixedMarginal (F:=F) (v ∘ Sigma.fst : Sigma J → V) S)^K).trace).re) ↔
      x^(Fintype.card I-1) ≤ (1-x)^(Fintype.card I-2)*
        (x+((2:ℝ)^Fintype.card (J j)-1)⁻¹) := by
  dsimp only
  let x := (Fintype.card F:ℝ)^(1-K)
  let z (i : I) := (2:ℝ)^Fintype.card (J i)-1
  let g (S : Finset (Sigma J)) :=
    (((mixedMarginal (F:=F) (v ∘ Sigma.fst : Sigma J → V) S)^K).trace).re
  change hitLaw g ↔ x^(Fintype.card I-1) ≤ (1-x)^(Fintype.card I-2)*(x+(z j)⁻¹)
  have hx : 0≤x := by dsimp [x]; positivity
  have hF : 1 < (Fintype.card F:ℝ) := by exact_mod_cast Fintype.one_lt_card (α:=F)
  have hx' : x<1 := Real.rpow_lt_one_of_one_lt_of_neg hF (by linarith)
  have hz i : 0<z i := by
    apply sub_pos.mpr
    exact one_lt_pow₀ (by norm_num) (Fintype.card_pos.ne')
  have h0 : g ∅=1 := by
    unfold g
    rw [actual_column_moment _ _ (by linarith : 0<K), columns,Finset.coe_empty,Set.image_empty,
      Submodule.span_empty,finrank_bot,pow_zero]
  rw [hitLaw_iff _ h0]
  have hnorm : 0<walshNorm (Sigma J) := by unfold walshNorm; positivity
  let occupied (T : ∀ i, Finset (J i)) : Finset I := univ.filter (fun i => (T i).Nonempty)
  have hf (T : ∀ i, Finset (J i)) :
      (0 ≤ inverse g (fiberEquiv T)) ↔
      0≤replicatedIndependent x (fun i => x+(z i)⁻¹) (occupied T) +
        (-1:ℝ)^(occupied T).card*(x^(Fintype.card I-1)*(1-x)) := by
    rw [inverse,div_eq_mul_inv,mul_nonneg_iff_of_pos_right (inv_pos.mpr hnorm)]
    simp only [sign_as_power,mul_comm (g _)]
    have hf' := physical_fiber_circuit_numerator (J:=J) v h T (by omega) (by linarith : 0<K)
    dsimp only at hf'
    rw [show (∑ S, (-1:ℝ)^((fiberEquiv T)∩S).card*g S) = _ from hf']
    have hc (i : I) :
        (if T i=∅ then z i else (-1:ℝ)) = (if i∈occupied T then -1 else z i) := by
      by_cases hi : T i=∅
      · simp [hi,occupied]
      · simp [hi,occupied,Finset.nonempty_iff_ne_empty.mpr hi]
    change 0 ≤ (∏ i : I, (1+x*(if T i=∅ then z i else -1))) +
      x^(Fintype.card I-1)*(1-x)*(∏ i : I, if T i=∅ then z i else -1) ↔ _
    simp_rw [hc]
    exact normalize_fiber_sign x _ (occupied T) z hz
  have hsur (U : Finset I) : ∃ T : ∀ i, Finset (J i), occupied T=U := by
    classical
    refine ⟨fun i => if i∈U then {Classical.choice (inferInstance : Nonempty (J i))} else ∅,?_⟩
    ext i
    by_cases hi : i∈U <;> simp [hi,occupied]
  have hcomm :
      (∀ T, 0 ≤ inverse g T) ↔
      ∀ U : Finset I, 0≤replicatedIndependent x (fun i => x+(z i)⁻¹) U +
        (-1:ℝ)^U.card*(x^(Fintype.card I-1)*(1-x)) := by
    constructor
    · intro h U
      obtain ⟨T,rfl⟩ := hsur U
      exact (hf T).mp (h _)
    · intro h T
      obtain ⟨U,rfl⟩ := fiberEquiv.surjective T
      exact (hf U).mpr (h _)
  rw [hcomm]
  apply normalized_even_criterion x hx hx' _ (fun i => le_add_of_nonneg_right (inv_nonneg.mpr (hz i).le)) hn he j
  intro i
  apply add_le_add_right
  apply (inv_le_inv₀ (hz j) (hz i)).mpr
  exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num) (hj i)) _

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

/-- The three standard vectors and their sum generate exactly the even
parity diagonal code on four binary coordinates. -/
def fourC (i : Fin 4) (j : Fin 3) : ZMod 2 :=
  if i=3 ∨ i.val=j.val then 1 else 0

private theorem zmod2_neg (a : ZMod 2) : -a=a := ZMod.neg_eq_self_mod_two a

private theorem relation_four (c : Fin 4 → ZMod 2)
    (h : (∑ i, c i • fourC i)=0) (i : Fin 4) : c i=c 3 := by
  fin_cases i
  · have h₀ := congrFun h (0:Fin 3)
    have h' : c 0+c 3=0 := by
      simpa [Fin.sum_univ_succ,fourC,Pi.smul_apply,smul_eq_mul] using h₀
    exact (add_eq_zero_iff_eq_neg.mp h').trans (zmod2_neg _)
  · have h₁ := congrFun h (1:Fin 3)
    have h' : c 1+c 3=0 := by
      simpa [Fin.sum_univ_succ,fourC,Pi.smul_apply,smul_eq_mul] using h₁
    exact (add_eq_zero_iff_eq_neg.mp h').trans (zmod2_neg _)
  · have h₂ := congrFun h (2:Fin 3)
    have h' : c 2+c 3=0 := by
      simpa [Fin.sum_univ_succ,fourC,Pi.smul_apply,smul_eq_mul] using h₂
    exact (add_eq_zero_iff_eq_neg.mp h').trans (zmod2_neg _)
  · rfl

theorem four_is_circuit : IsColumnCircuit (F₀:=ZMod 2) fourC := by
  constructor
  · intro h
    have he : (∑ i : Fin 4, (1:ZMod 2) • fourC i)=0 := by
      funext j
      fin_cases j <;> decide
    have hu := (Fintype.linearIndependent_iff.mp h) (fun _ => 1) he (0:Fin 4)
    exact one_ne_zero hu
  · intro S hS
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let d (a : Fin 4) : ZMod 2 := if ha : a∈S then c ⟨a,ha⟩ else 0
    have hsum : (∑ a : Fin 4, d a • fourC a)=0 := by
      rw [← sum_subset (subset_univ S) (fun a _ ha => by simp [d,ha])]
      rw [← sum_attach S]
      simpa [d] using hc
    obtain ⟨j,hj⟩ : ∃ j, j ∉ S := by
      by_contra! h
      exact hS (Finset.eq_univ_iff_forall.mpr h)
    have hd3 : d 3=0 := by
      rw [← relation_four d hsum j]
      simp [d,hj]
    simpa [d,i.property] using (relation_four d hsum i.val).trans hd3

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end

section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open Finset Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

noncomputable section

abbrev FourCopy := Sigma (fun _ : Fin 4 => Fin 2)

def fourMask (i : Fin 4) : Finset (Fin 2) := if i=3 then ∅ else {0}

/-- The actual repeated four-circuit label selecting one site in three
distinct classes and none in the fourth. -/
def fourObserved (K : ℝ) : ℝ :=
  inverse (fun S : Finset FourCopy =>
    (((mixedMarginal (F:=ZMod 2) (fourC ∘ Sigma.fst) S)^K).trace).re)
    (fiberEquiv fourMask)

theorem physical_four_readout (K : ℝ) (hK : 0<K) :
    let observed := fourObserved K
    let x := (2:ℝ)^(1-K)
    observed = ((1-x)^3*(1+3*x)-3*x^3*(1-x))/256 := by
  dsimp only
  unfold fourObserved
  rw [inverse]
  simp only [sign_as_power,mul_comm (((mixedMarginal _ _)^K).trace).re]
  have he := physical_fiber_circuit_numerator (J:=fun _ => Fin 2) fourC four_is_circuit fourMask
    (by decide) hK
  dsimp only at he
  rw [he]
  have hp : walshNorm FourCopy=256 := by
    unfold walshNorm
    norm_num [Fintype.card_sigma]
  rw [hp]
  have hF : (Fintype.card (ZMod 2) : ℝ)=2 := by simp
  rw [hF]
  norm_num [fourMask,Fin.prod_univ_succ]
  ring

/-- At the exact parameter 3/5 the genuine bare four-bit code admits a
classical law, while the specified doubled Walsh coefficient is negative. -/
theorem physical_four_bare_yes_double_no (K : ℝ) (hK : 1<K)
    (hx : (2:ℝ)^(1-K)=3/5) :
    hitLaw (fun S : Finset (Fin 4) =>
      (((mixedMarginal (F:=ZMod 2) fourC S)^K).trace).re) ∧
    fourObserved K = -1/3200 := by
  have hF : (Fintype.card (ZMod 2) : ℝ)=2 := by simp
  have he := actual_even_circuit_threshold fourC four_is_circuit (by decide) (by decide) hK
  dsimp only at he
  constructor
  · apply he.mpr
    rw [hF,hx]
    norm_num
  · have hw := physical_four_readout K (by linarith)
    dsimp only at hw
    rw [hw,hx]
    norm_num

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
end
