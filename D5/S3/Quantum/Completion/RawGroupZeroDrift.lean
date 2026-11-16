/- GID: D5/S3/Quantum/Completion/RawGroupZeroDrift
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawGroupZeroDrift
   mirror-E: none(waiver:abstract-group-construction)
   anchors: []
   utility: none
   digest: Countable marker-closed actual subgroups admit one all-pair zero-drift limit. -/

import D5.S3.Quantum.Completion.RawUnanchoredReplication
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Countable

noncomputable section
open Filter Topology
open scoped BigOperators
open D5.S3.Quantum.Completion.RawUnanchoredReplication
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace D5.S3.Quantum.Completion.RawGroupZeroDrift
universe u v

inductive Word (α : Type v) where
  | unit : Word α
  | source : α → Word α
  | mul : Word α → Word α → Word α
  | inv : Word α → Word α
  | mark : Word α → Word α
  deriving Countable

def eval {A : Type u} [Group A] {α : Type v} (V : A → A) (x : α → A) : Word α → A
  | .unit => 1
  | .source a => x a
  | .mul s t => eval V x s * eval V x t
  | .inv s => (eval V x s)⁻¹
  | .mark s => V (eval V x s)

def wordGroup {A : Type u} [Group A] {α : Type v} (V : A → A) (x : α → A) : Subgroup A where
  carrier := Set.range (eval V x)
  one_mem' := ⟨.unit, rfl⟩
  mul_mem' := by
    rintro a b ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨.mul s t, rfl⟩
  inv_mem' := by
    rintro a ⟨s, rfl⟩
    exact ⟨.inv s, rfl⟩

def wordMarker {A : Type u} [Group A] {α : Type v} (V : A → A) (x : α → A)
    (s : wordGroup V x) : wordGroup V x :=
  ⟨V s.val, by
    obtain ⟨e, he⟩ := s.property
    exact ⟨.mark e, by simpa only [eval] using congrArg V he⟩⟩

def label {A : Type u} [Group A] {α : Type v} (V : A → A) (x : α → A)
    (a : α) : wordGroup V x := ⟨x a, ⟨.source a, rfl⟩⟩

lemma right_invariant {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}
    (h : RawCost U c) (a b z : G) : c (a*z) (b*z) = c a b := by
  let F : G → ℝ := fun t => c (a*t) (b*t)
  let R : Set ℝ := Set.range F
  have hne : R.Nonempty := ⟨F 1, ⟨1, rfl⟩⟩
  have hbd : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact h.nonneg _ _
  have hm (t : G) : sInf R ≤ F t := csInf_le hbd ⟨t, rfl⟩
  have hstep (t w : G) : F (t*w) ≤ 3*F t - 2*sInf R := by
    have hb := h.balance (a*t) (b*t) w w
    rw [h.diagonal] at hb
    simp only [mul_assoc] at hb
    change F (t*w) + F (t*U w) + F (t*U (U w)) = 3*F t + 3*0 at hb
    linarith [hm (t*U w), hm (t*U (U w))]
  have heq (s : G) : F s = sInf R := by
    have hlow : (F s + 2*sInf R)/3 ≤ sInf R := by
      apply le_csInf hne
      rintro _ ⟨t, rfl⟩
      have ht := hstep t (t⁻¹*s)
      rw [mul_inv_cancel_left] at ht
      linarith
    exact le_antisymm (by linarith) (hm s)
  have hz := (heq z).trans (heq 1).symm
  simpa only [F, mul_one] using hz

lemma inverse_budget {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}
    (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (x : G) : c x⁻¹ 1 = c x 1 := by
  have ht := right_invariant h x⁻¹ 1 x
  simp only [inv_mul_cancel, one_mul] at ht
  exact ht.symm.trans (hs 1 x)

abbrev Product (G : Type u) := (n : ℕ) → D5.S3.Quantum.Completion.RawUnanchoredReplication.Sigma (n+1) → G

/-- Original Group19.3, with arbitrary finite indexed labels, including repeats and the empty type. -/
theorem group19_3 {G : Type u} [Group G] {α : Type v} [Finite α]
    (U : G → G) (c : G → G → ℝ) (h : RawCost U c)
    (hs : ∀ a b, c a b = c b a) (f : α → G) :
    ∃ (S : Type u) (gS : Group S), letI : Group S := gS
      ∃ (_ : Countable S) (V : S → S) (d : S → S → ℝ) (x : α → S),
        RawCost V d ∧ (∀ a b, d a b = d b a) ∧ d (V 1) 1 = 0 ∧
          ∀ a b, d (x a) (x b) = c (f a) (f b) := by
  classical
  let W : Product G → Product G := fun p n => arrayMarker U (p n)
  let X : α → Product G := fun a n => gamma U (n+1) (f a)
  let S : Type u := ↥(wordGroup W X)
  letI : Group S := inferInstanceAs (Group ↥(wordGroup W X))
  letI : Countable S := (Set.countable_range (eval W X)).to_subtype
  let V : S → S := wordMarker W X
  let x : α → S := label W X
  let cost (n : ℕ) (s t : S) := arrayCost c (n+1) (s.val n) (t.val n)
  have ha (n : ℕ) : RawCost (arrayMarker U (N := n+1)) (arrayCost c (n+1)) :=
    (raw_replication h (n+1) (Nat.succ_pos n)).1
  have has (n : ℕ) (a b : D5.S3.Quantum.Completion.RawUnanchoredReplication.Sigma (n+1) → G) :
      arrayCost c (n+1) a b = arrayCost c (n+1) b a := by
    unfold arrayCost
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hs _ _)
  have ho : 0 ≤ omega U c := by
    unfold omega
    linarith [h.nonneg (U 1) 1, h.nonneg (U (U 1)) 1,
      h.nonneg 1 (U 1), h.nonneg 1 (U (U 1))]
  have hob (n : ℕ) : omega U c / (n+1 : ℕ) ≤ omega U c := by
    apply div_le_self ho
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hb (e : Word α) : ∃ B : ℝ, ∀ n,
      arrayCost c (n+1) (eval W X e n) 1 ≤ B := by
    induction e with
    | unit =>
      refine ⟨0, fun n => ?_⟩
      exact le_of_eq ((ha n).diagonal 1)
    | source a =>
      refine ⟨3*c (f a) 1 + 3*omega U c, fun n => ?_⟩
      have hh := ((raw_replication h (n+1) (Nat.succ_pos n)).2.2.2.1 (f a)).1
      change arrayCost c (n+1) (gamma U (n+1) (f a)) 1 ≤ _
      have hn := hob n
      push_cast at hn
      push_cast at hh
      rw [mul_div_assoc] at hh
      linarith
    | mul s t ihs iht =>
      obtain ⟨Bs, hBs⟩ := ihs
      obtain ⟨Bt, hBt⟩ := iht
      refine ⟨3*(Bs+Bt), fun n => ?_⟩
      have hh := single (ha n) (eval W X s n) 1 (eval W X t n) 1
      simp only [one_mul, mul_one] at hh
      change arrayCost c (n+1) (eval W X s n * eval W X t n) 1 ≤ _
      linarith [hBs n, hBt n]
    | inv s ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨B, fun n => ?_⟩
      change arrayCost c (n+1) (eval W X s n)⁻¹ 1 ≤ _
      rw [inverse_budget (ha n) (has n)]
      exact hB n
    | mark s ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨18*B+24*omega U c, fun n => ?_⟩
      have hh := (raw_replication (ha n) 1 (by omega)).2.2.2.2 (eval W X s n) 1
      simp only [Function.iterate_one] at hh
      rw [has n 1 (eval W X s n), (raw_replication h (n+1) (Nat.succ_pos n)).2.1] at hh
      have hn := (ha n).nonneg 1 (arrayMarker U (eval W X s n))
      change arrayCost c (n+1) (arrayMarker U (eval W X s n)) 1 ≤ _
      have hw := hob n
      push_cast at hw
      push_cast at hh
      linarith [hB n]
  have hbound (s : S) : ∃ B : ℝ, ∀ n, cost n s 1 ≤ B := by
    obtain ⟨e, he⟩ := s.property
    obtain ⟨B, hB⟩ := hb e
    refine ⟨B, fun n => ?_⟩
    change arrayCost c (n+1) (s.val n) 1 ≤ B
    rw [← he]
    exact hB n
  let B : S → ℝ := fun s => Classical.choose (hbound s)
  have hB (s : S) (n : ℕ) : cost n s 1 ≤ B s := Classical.choose_spec (hbound s) n
  let C (p : S × S) := 3*(B p.1+B p.2)
  have hc (n : ℕ) : RawCost V (cost n) := by
    constructor
    · intro s t; exact (ha n).nonneg _ _
    · intro s; exact (ha n).diagonal _
    · intro a b s t
      exact (ha n).balance (a.val n) (b.val n) (s.val n) (t.val n)
  have hcs (n : ℕ) (s t : S) : cost n s t = cost n t s := has n _ _
  have hp (n : ℕ) (s t : S) : cost n s t ≤ C (s,t) := by
    have hh := unit_compare (hc n) s t
    rw [hcs n 1 t] at hh
    dsimp [C]
    linarith [hB s n, hB t n]
  let K : Set ((S × S) → ℝ) := {d | ∀ p, d p ∈ Set.Icc 0 (C p)}
  have hk : IsCompact K := isCompact_pi_infinite (fun _ => isCompact_Icc)
  let seq (n : ℕ) (p : S × S) := cost n p.1 p.2
  have hseq (n : ℕ) : seq n ∈ K := fun p => ⟨(hc n).nonneg _ _, hp n _ _⟩
  obtain ⟨d, hd, ρ, hρ, hlim⟩ := hk.tendsto_subseq hseq
  have hl (s t : S) : Tendsto (fun l => cost (ρ l) s t) atTop (𝓝 (d (s,t))) :=
    tendsto_pi_nhds.mp hlim (s,t)
  refine ⟨S, inferInstance, inferInstance, V, (fun s t => d (s,t)), x, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro s t; exact (hd (s,t)).1
    · intro s
      have hz : Tendsto (fun l => cost (ρ l) s s) atTop (𝓝 0) := by
        simpa only [(hc _).diagonal] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
      exact tendsto_nhds_unique (hl s s) hz
    · intro a b s t
      have hleft := ((hl (a*s) (b*t)).add (hl (a*V s) (b*V t))).add
        (hl (a*V (V s)) (b*V (V t)))
      have hright := ((hl a b).const_mul 3).add ((hl s t).const_mul 3)
      apply tendsto_nhds_unique hleft
      exact hright.congr' (Eventually.of_forall fun l => ((hc (ρ l)).balance a b s t).symm)
  · intro s t
    apply tendsto_nhds_unique (hl s t)
    exact (hl t s).congr' (Eventually.of_forall fun l => (hcs (ρ l) s t).symm)
  · have hOmega : Tendsto (fun l => omega V (cost (ρ l))) atTop (𝓝 0) := by
      have he (n : ℕ) : omega V (cost n) = omega U c / (n+1 : ℕ) :=
        (raw_replication h (n+1) (Nat.succ_pos n)).2.1
      simp_rw [he]
      exact (tendsto_const_div_atTop_nhds_zero_nat (omega U c)).comp
        ((tendsto_add_atTop_nat 1).comp hρ.tendsto_atTop)
    have hzero : Tendsto (fun l => cost (ρ l) (V 1) 1) atTop (𝓝 0) := by
      apply squeeze_zero (fun l => (hc (ρ l)).nonneg _ _) (fun l => ?_) hOmega
      unfold omega
      linarith [(hc (ρ l)).nonneg (V (V 1)) 1,
        (hc (ρ l)).nonneg 1 (V 1), (hc (ρ l)).nonneg 1 (V (V 1))]
    exact tendsto_nhds_unique (hl (V 1) 1) hzero
  · intro a b
    have he (n : ℕ) : cost n (x a) (x b) = c (f a) (f b) :=
      (raw_replication h (n+1) (Nat.succ_pos n)).2.2.1 (f a) (f b)
    have ht : Tendsto (fun l => cost (ρ l) (x a) (x b)) atTop (𝓝 (c (f a) (f b))) := by
      simpa only [he] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c (f a) (f b)) atTop (𝓝 (c (f a) (f b))))
    exact tendsto_nhds_unique (hl _ _) ht

end D5.S3.Quantum.Completion.RawGroupZeroDrift
