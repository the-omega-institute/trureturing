/- GID: D5/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses
   generality: I
   mirror-B: D5/B/S3/Observer/Separation/FixedSkeletonWeightedInclusion/LabelledResponses
   mirror-E: none(waiver:symbolic-existence-and-bounds)
   anchors: []
   utility: none
   digest: Common actual suffix replay, same-law coordinate entropy and labelled completion geometry. -/

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Logic.Function.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import D5.S3.Entropy.Submodularity.StrongSubadditivity
import D5.S3.Entropy.Forgetting.PushforwardComposition
import D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
import D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
import D5.S3.Entropy.EntropyEquality

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.LabelledResponses


/-- Assignments to the two separately labelled endpoint subsets. -/
def Values {I : Type*} (X Y : I → Type*) (l r : I → Prop) :=
  (∀ i : {i // l i}, X i.val) × (∀ i : {i // r i}, Y i.val)

instance finiteValues {I : Type*} [Finite I] {X Y : I → Type*}
    [∀ i, Finite (X i)] [∀ i, Finite (Y i)] (l r : I → Prop) :
    Finite (Values X Y l r) := by
  unfold Values
  infer_instance

instance nonemptyValues {I : Type*} {X Y : I → Type*}
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)] (l r : I → Prop) :
    Nonempty (Values X Y l r) := by
  unfold Values
  infer_instance


noncomputable def outputs {I : Type*} {X Y Z : I → Type*}
    (φ : ∀ i, X i → Y i → Z i) (l r : I → Prop)
    (b : Values X Y l r) (s : Values X Y (fun i => ¬l i) (fun i => ¬r i)) :
    ∀ i, Z i := by
  classical
  exact fun i => φ i (if h : l i then b.1 ⟨i,h⟩ else s.1 ⟨i,h⟩)
    (if h : r i then b.2 ⟨i,h⟩ else s.2 ⟨i,h⟩)

noncomputable def response {I O : Type*} {X Y Z : I → Type*}
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O) (l r : I → Prop)
    (b : Values X Y l r) (s : Values X Y (fun i => ¬l i) (fun i => ¬r i)) : O :=
  G (outputs φ l r b s)

/-- Designated pairs opened by the second cut and untouched by the first. -/
def extra {I : Type*} (designated B₁ P₁ : I → Prop) (i : I) : Prop :=
  designated i ∧ ¬B₁ i ∧ P₁ i

noncomputable def residualOutputs {I : Type*} {X Y Z : I → Type*}
    (φ : ∀ i, X i → Y i → Z i) (B₁ B₂ E : I → Prop)
    (b : Values X Y B₁ B₂) (z : ∀ i : {i // E i}, Z i.val)
    (d : Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)) :
    ∀ i, Z i := by
  classical
  exact fun i => if he : E i then z ⟨i,he⟩ else
    φ i (if h : B₁ i then b.1 ⟨i,h⟩ else d.1 ⟨i,h,he⟩)
      (if h : B₂ i then b.2 ⟨i,h⟩ else d.2 ⟨i,h,he⟩)

/-- Group only designated endpoints read in B and absent from P. -/
def InGroup {I : Type*} {X Y : I → Type*}
    (designated B₁ B₂ P₁ P₂ : I → Prop) (b : Values X Y B₁ B₂)
    (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
      (fun i => designated i ∧ B₂ i ∧ ¬P₂ i)) : Prop :=
  (∀ i (h : designated i ∧ B₁ i ∧ ¬P₁ i), b.1 ⟨i,h.2.1⟩ = c.1 ⟨i,h⟩) ∧
  (∀ i (h : designated i ∧ B₂ i ∧ ¬P₂ i), b.2 ⟨i,h.2.1⟩ = c.2 ⟨i,h⟩)

/-- A single P suffix works for every B prefix in its designated-coordinate group.
The cuts need not be nested. Ordinary completed pairs are encoded through a
surjective column; ordinary untouched pairs opened by P use a surjective row. -/
theorem nonnested_common_suffix_replay
    {I O : Type*} {X Y Z : I → Type*}
    [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i, Z i) → O)
    (designated B₁ B₂ P₁ P₂ : I → Prop)
    (hB : ∀ i, B₂ i → B₁ i) (hP : ∀ i, P₂ i → P₁ i)
    (hsecond : ∀ i, P₂ i → B₂ i)
    (hfirst : ∀ i, ¬designated i → B₁ i → P₁ i)
    (hordinary : ∀ i, ¬designated i →
      (∃ a : X i, Function.Surjective (φ i a)) ∧
      (∃ b : Y i, Function.Surjective (fun a => φ i a b))) :
    let E := extra designated B₁ P₁
    ∃ q : (∀ i : {i // E i}, X i.val) → Values X Y B₁ B₂ → Values X Y P₁ P₂,
      ∀ (c : Values X Y (fun i => designated i ∧ B₁ i ∧ ¬P₁ i)
          (fun i => designated i ∧ B₂ i ∧ ¬P₂ i))
        (x : ∀ i : {i // E i}, X i.val)
        (z : ∀ i : {i // E i}, Z i.val)
        (d : Values X Y (fun i => ¬B₁ i ∧ ¬E i) (fun i => ¬B₂ i ∧ ¬E i)),
      (∀ i : {i // E i}, ∃ y : Y i.val, φ i.val (x i) y = z i) →
      ∃ s : Values X Y (fun i => ¬P₁ i) (fun i => ¬P₂ i),
        ∀ b : Values X Y B₁ B₂, InGroup designated B₁ B₂ P₁ P₂ b c →
          response φ G P₁ P₂ (q x b) s = G (residualOutputs φ B₁ B₂ E b z d) := by
  classical
  let E := extra designated B₁ P₁
  let aR : ∀ i, X i := fun i => if h : designated i then Classical.choice inferInstance
    else Classical.choose (hordinary i h).1
  let bC : ∀ i, Y i := fun i => if h : designated i then Classical.choice inferInstance
    else Classical.choose (hordinary i h).2
  have row : ∀ i, ¬designated i → Function.Surjective (φ i (aR i)) := by
    intro i hi
    simpa [aR,hi] using Classical.choose_spec (hordinary i hi).1
  have col : ∀ i, ¬designated i → Function.Surjective (fun a => φ i a (bC i)) := by
    intro i hi
    simpa [bC,hi] using Classical.choose_spec (hordinary i hi).2
  let R : ∀ i, Z i → Y i := fun i z => if h : designated i then Classical.choice inferInstance
    else Classical.choose (row i h z)
  let C : ∀ i, Z i → X i := fun i z => if h : designated i then Classical.choice inferInstance
    else Classical.choose (col i h z)
  have row_spec : ∀ i, ¬designated i → ∀ z, φ i (aR i) (R i z) = z := by
    intro i hi z
    simpa [R,hi] using Classical.choose_spec (row i hi z)
  have col_spec : ∀ i, ¬designated i → ∀ z, φ i (C i z) (bC i) = z := by
    intro i hi z
    simpa [C,hi] using Classical.choose_spec (col i hi z)
  let q : (∀ i : {i // E i}, X i.val) → Values X Y B₁ B₂ → Values X Y P₁ P₂ :=
    fun x b =>
      (fun i => if hd : designated i.val then
          if hb : B₁ i.val then b.1 ⟨i.val,hb⟩ else x ⟨i.val,hd,hb,i.property⟩
        else if hb : B₂ i.val then
          if hp : P₂ i.val then b.1 ⟨i.val,hB i.val hb⟩
          else C i.val (φ i.val (b.1 ⟨i.val,hB i.val hb⟩) (b.2 ⟨i.val,hb⟩))
        else if hb : B₁ i.val then b.1 ⟨i.val,hb⟩ else aR i.val,
       fun i => b.2 ⟨i.val,hsecond i.val i.property⟩)
  refine ⟨q, ?_⟩
  intro c x z d hz
  let y : ∀ i : {i // E i}, Y i.val := fun i => Classical.choose (hz i)
  have y_spec : ∀ i : {i // E i}, φ i.val (x i) (y i) = z i :=
    fun i => Classical.choose_spec (hz i)
  let s : Values X Y (fun i => ¬P₁ i) (fun i => ¬P₂ i) :=
    (fun i => if hd : designated i.val then
        if hb : B₁ i.val then c.1 ⟨i.val,hd,hb,i.property⟩
        else d.1 ⟨i.val,hb,fun he => i.property he.2.2⟩
      else d.1 ⟨i.val,fun hb => i.property (hfirst i.val hd hb),fun he => hd he.1⟩,
     fun i => if he : E i.val then y ⟨i.val,he⟩
      else if hd : designated i.val then
        if hb : B₂ i.val then c.2 ⟨i.val,hd,hb,i.property⟩ else d.2 ⟨i.val,hb,he⟩
      else if hb₂ : B₂ i.val then bC i.val
      else if hb₁ : B₁ i.val then d.2 ⟨i.val,hb₂,he⟩
      else if hp : P₁ i.val then
        R i.val (φ i.val (d.1 ⟨i.val,hb₁,he⟩) (d.2 ⟨i.val,hb₂,he⟩))
      else d.2 ⟨i.val,hb₂,he⟩)
  refine ⟨s, ?_⟩
  intro b hg
  apply congrArg G
  funext i
  by_cases hd : designated i
  · by_cases hb₁ : B₁ i
    · have he : ¬E i := fun he => he.2.1 hb₁
      have hc₁ : ∀ hp : ¬P₁ i, c.1 ⟨i,hd,hb₁,hp⟩ = b.1 ⟨i,hb₁⟩ :=
        fun hp => (hg.1 i ⟨hd,hb₁,hp⟩).symm
      have hc₂ : ∀ hb : B₂ i, ∀ hp : ¬P₂ i, c.2 ⟨i,hd,hb,hp⟩ = b.2 ⟨i,hb⟩ :=
        fun hb hp => (hg.2 i ⟨hd,hb,hp⟩).symm
      by_cases hp₁ : P₁ i <;> by_cases hb₂ : B₂ i <;> by_cases hp₂ : P₂ i
      all_goals try { exfalso; exact hp₁ (hP i hp₂) }
      all_goals try { exfalso; exact hb₂ (hsecond i hp₂) }
      all_goals simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,hc₁,hc₂]
    · have hb₂ : ¬B₂ i := fun h => hb₁ (hB i h)
      have hp₂ : ¬P₂ i := fun h => hb₂ (hsecond i h)
      by_cases hp₁ : P₁ i
      · have he : E i := ⟨hd,hb₁,hp₁⟩
        simpa [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he] using y_spec ⟨i,he⟩
      · have he : ¬E i := fun h => hp₁ h.2.2
        simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]
  · have he : ¬E i := fun h => hd h.1
    by_cases hb₂ : B₂ i
    · have hb₁ : B₁ i := hB i hb₂
      have hp₁ : P₁ i := hfirst i hd hb₁
      by_cases hp₂ : P₂ i
      · simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]
      · simpa [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he] using
          col_spec i hd (φ i (b.1 ⟨i,hb₁⟩) (b.2 ⟨i,hb₂⟩))
    · have hp₂ : ¬P₂ i := fun h => hb₂ (hsecond i h)
      by_cases hb₁ : B₁ i
      · have hp₁ : P₁ i := hfirst i hd hb₁
        simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]
      · by_cases hp₁ : P₁ i
        · simpa [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he] using
            row_spec i hd (φ i (d.1 ⟨i,hb₁,he⟩) (d.2 ⟨i,hb₂,he⟩))
        · simp [outputs,residualOutputs,q,s,E,extra,hd,hb₁,hb₂,hp₁,hp₂,he]

/-- Fractional covers bound every normalized monotone submodular set function. -/
theorem fractional_submodular_cover {A R : Type*} [DecidableEq A] [Fintype R]
    (H : Finset A → ℝ) (hzero : H ∅ = 0)
    (hmono : ∀ s t, s ⊆ t → H s ≤ H t)
    (hsub : ∀ s t, H (s ∪ t) + H (s ∩ t) ≤ H s + H t)
    (U : Finset A) (S : R → Finset A) (hS : ∀ r, S r ⊆ U)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r)
    (hcover : ∀ a ∈ U, 1 ≤ ∑ r, if a ∈ S r then w r else 0) :
    H U ≤ ∑ r, w r * H (S r) := by
  classical
  induction U using Finset.induction_on generalizing H S with
  | empty =>
    have hs : ∀ r, S r = ∅ := fun r => Finset.subset_empty.mp (hS r)
    simp [hs,hzero]
  | @insert a U ha ih =>
    let K := fun t : Finset A => H (insert a t) - H {a}
    have kz : K ∅ = 0 := by simp [K]
    have km : ∀ s t, s ⊆ t → K s ≤ K t := by
      intro s t h; exact sub_le_sub_right (hmono _ _ (Finset.insert_subset_insert a h)) _
    have ks : ∀ s t, K (s ∪ t) + K (s ∩ t) ≤ K s + K t := by
      intro s t
      have h := hsub (insert a s) (insert a t)
      have hu : insert a s ∪ insert a t = insert a (s ∪ t) := by ext i; simp <;> tauto
      have hi : insert a s ∩ insert a t = insert a (s ∩ t) := by ext i; simp <;> tauto
      rw [hu,hi] at h
      dsimp [K]; linarith
    let T := fun r => (S r).erase a
    have ht : ∀ r, T r ⊆ U := by
      intro r i hi
      have hs := hS r (Finset.mem_of_mem_erase hi)
      exact (Finset.mem_insert.mp hs).resolve_left (Finset.ne_of_mem_erase hi)
    have hc : ∀ i ∈ U, 1 ≤ ∑ r, if i ∈ T r then w r else 0 := by
      intro i hi
      have hia : i ≠ a := fun e => ha (e ▸ hi)
      simpa [T,hia] using hcover i (Finset.mem_insert_of_mem hi)
    have hind := ih K kz km ks T ht hc
    have each : ∀ r, K (T r) ≤ H (S r) - (if a ∈ S r then H {a} else 0) := by
      intro r
      by_cases har : a ∈ S r
      · simp [K,T,har,Finset.insert_erase har]
      · have hh := hsub (S r) {a}
        have hi : S r ∩ {a} = ∅ := by ext i; simp; aesop
        have hu : S r ∪ {a} = insert a (S r) := by ext i; simp <;> tauto
        rw [hi,hu,hzero] at hh
        simpa [K,T,har] using (show H (insert a (S r)) - H {a} ≤ H (S r) by linarith)
    have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (each r) (hw r))
    have hnon : 0 ≤ H {a} := by simpa [hzero] using hmono ∅ {a} (Finset.empty_subset _)
    have hcov := mul_le_mul_of_nonneg_right (hcover a (Finset.mem_insert_self _ _)) hnon
    have hid : (∑ r, w r * (H (S r) - if a ∈ S r then H {a} else 0)) =
        (∑ r, w r * H (S r)) - (∑ r, if a ∈ S r then w r else 0) * H {a} := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib,Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr; split_ifs <;> ring
    rw [hid] at hs
    dsimp [K] at hind
    simp only [one_mul] at hcov
    linarith

open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.PushforwardComposition
open D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
open D5.S3.Entropy.Forgetting.DeterministicEntropyEquality

private theorem readout_entropy_le {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    (p : X → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (u : X → A) (v : X → B) (f : B → A) (he : u = f ∘ v) :
    shannonEntropy (pushforward u p) ≤ shannonEntropy (pushforward v p) := by
  have hq := pushforward_is_law p v hp
  rw [he,← pushforward_comp]
  by_cases hi : Set.InjOn f {b | pushforward v p b ≠ 0}
  · exact ((pushforward_entropy_eq_iff_injective_on_support _ f hq).2 hi).le
  · exact ((pushforward_entropy_lt_iff_not_injective_on_support _ f hq).2 hi).le

private theorem readout_entropy_eq {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    (p : X → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (u : X → A) (v : X → B) (f : B → A) (g : A → B)
    (hu : u = f ∘ v) (hv : v = g ∘ u) :
    shannonEntropy (pushforward u p) = shannonEntropy (pushforward v p) :=
  le_antisymm (readout_entropy_le p hp u v f hu) (readout_entropy_le p hp v u g hv)

/-- Coordinates selected from one actual finite sample; an empty selection has one tuple. -/
def coordinateTuple {X A : Type*} {V : A → Type*}
    (u : ∀ a, X → V a) (S : Finset A) (x : X) :=
  fun a : {a // a ∈ S} => u a.val x

noncomputable def coordinateEntropy {X A : Type*} [Fintype X] [DecidableEq A]
    {V : A → Type*} [∀ a, Fintype (V a)]
    (p : X → ℝ) (u : ∀ a, X → V a) (S : Finset A) : ℝ :=
  shannonEntropy (pushforward (coordinateTuple u S) p)

private def tupleRestrict {A : Type*} {V : A → Type*} {s t : Finset A}
    (h : s ⊆ t) (v : ∀ a : {a // a ∈ t}, V a.val) : ∀ a : {a // a ∈ s}, V a.val :=
  fun a => v ⟨a.val,h a.property⟩

private noncomputable def tupleJoin {A : Type*} [DecidableEq A] {V : A → Type*} (s t : Finset A)
    (v : (∀ a : {a // a ∈ s}, V a.val) × (∀ a : {a // a ∈ t}, V a.val)) :
    ∀ a : {a // a ∈ s ∪ t}, V a.val := by
  classical
  exact fun a => if h : a.val ∈ s then v.1 ⟨a.val,h⟩
    else v.2 ⟨a.val,(Finset.mem_union.mp a.property).resolve_left h⟩

private theorem coordinate_entropy_structure {X A : Type*} [Fintype X] [DecidableEq A]
    {V : A → Type*} [∀ a, Fintype (V a)]
    (p : X → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) (u : ∀ a, X → V a) :
    coordinateEntropy p u ∅ = 0 ∧
    (∀ s t, s ⊆ t → coordinateEntropy p u s ≤ coordinateEntropy p u t) ∧
    (∀ s t, coordinateEntropy p u (s ∪ t) + coordinateEntropy p u (s ∩ t) ≤
      coordinateEntropy p u s + coordinateEntropy p u t) := by
  classical
  have emptyLaw : pushforward (coordinateTuple u ∅) p = fun _ => (1 : ℝ) := by
    funext z
    simp only [pushforward]
    have he : ∀ x, coordinateTuple u ∅ x = z := fun x => Subsingleton.elim _ _
    simpa only [he,if_true] using hp.2
  refine ⟨?_,?_,?_⟩
  · simp [coordinateEntropy,emptyLaw,shannonEntropy,Real.negMulLog]
  · intro s t h
    exact readout_entropy_le p hp _ _ (tupleRestrict h) rfl
  · intro s t
    let C := (∀ a : {a // a ∈ s ∩ t}, V a.val)
    let L := (∀ a : {a // a ∈ s}, V a.val)
    let R := (∀ a : {a // a ∈ t}, V a.val)
    let q : X → C × (L × R) := fun x =>
      (coordinateTuple u (s ∩ t) x,(coordinateTuple u s x,coordinateTuple u t x))
    let mass := pushforward q p
    have hm := pushforward_is_law p q hp
    have hssa := D5.S3.Entropy.Submodularity.StrongSubadditivity.entropy_submodular mass hm
    have full : shannonEntropy mass = coordinateEntropy p u (s ∪ t) := by
      apply readout_entropy_eq p hp q (coordinateTuple u (s ∪ t))
        (fun v => (tupleRestrict (Finset.inter_subset_left.trans (Finset.subset_union_left)) v,
          (tupleRestrict Finset.subset_union_left v,tupleRestrict Finset.subset_union_right v)))
        (fun v => tupleJoin s t v.2)
      · rfl
      · funext x a
        dsimp [tupleJoin,coordinateTuple]
        split_ifs <;> rfl
    have marg : D5.S3.Divergence.ChainRule.marginal mass =
        pushforward (coordinateTuple u (s ∩ t)) p := by
      have hc := pushforward_comp p q (fun v : C × (L × R) => v.1)
      have he : pushforward (fun v : C × (L × R) => v.1) mass =
          D5.S3.Divergence.ChainRule.marginal mass := by
        funext c
        simp only [pushforward,D5.S3.Divergence.ChainRule.marginal,Fintype.sum_prod_type]
        rw [Finset.sum_eq_single c]
        · simp
        · intro c' _ hc'; simp [hc']
        · simp
      rw [he] at hc
      exact hc
    have xy : D5.S3.Entropy.Submodularity.StrongSubadditivity.xyProjection mass =
        pushforward (fun x => (coordinateTuple u (s ∩ t) x,coordinateTuple u s x)) p := by
      have hc := pushforward_comp p q (fun v : C × (L × R) => (v.1,v.2.1))
      have he : pushforward (fun v : C × (L × R) => (v.1,v.2.1)) mass =
          D5.S3.Entropy.Submodularity.StrongSubadditivity.xyProjection mass := by
        funext c
        rcases c with ⟨c,l⟩
        simp only [pushforward,D5.S3.Entropy.Submodularity.StrongSubadditivity.xyProjection,
          Fintype.sum_prod_type,Prod.mk.injEq,ite_and]
        rw [Finset.sum_eq_single c]
        · simp only [↓reduceIte]
          rw [Finset.sum_eq_single l]
          · simp
          · intro l' _ hl'; simp [hl']
          · simp
        · intro c' _ hc'; simp [hc']
        · simp
      rw [he] at hc
      exact hc
    have xz : D5.S3.Entropy.Submodularity.StrongSubadditivity.xzProjection mass =
        pushforward (fun x => (coordinateTuple u (s ∩ t) x,coordinateTuple u t x)) p := by
      have hc := pushforward_comp p q (fun v : C × (L × R) => (v.1,v.2.2))
      have he : pushforward (fun v : C × (L × R) => (v.1,v.2.2)) mass =
          D5.S3.Entropy.Submodularity.StrongSubadditivity.xzProjection mass := by
        funext c
        rcases c with ⟨c,r⟩
        simp only [pushforward,D5.S3.Entropy.Submodularity.StrongSubadditivity.xzProjection,
          Fintype.sum_prod_type,Prod.mk.injEq,ite_and]
        rw [Finset.sum_eq_single c]
        · simp only [↓reduceIte]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.sum_eq_single r]
          · simp
          · intro r' _ hr'; simp [hr']
          · simp
        · intro c' _ hc'; simp [hc']
        · simp
      rw [he] at hc
      exact hc
    have hl : shannonEntropy (pushforward
        (fun x => (coordinateTuple u (s ∩ t) x,coordinateTuple u s x)) p) =
        coordinateEntropy p u s := by
      apply readout_entropy_eq p hp _ _
        (fun v => (tupleRestrict Finset.inter_subset_left v,v)) Prod.snd <;> rfl
    have hr : shannonEntropy (pushforward
        (fun x => (coordinateTuple u (s ∩ t) x,coordinateTuple u t x)) p) =
        coordinateEntropy p u t := by
      apply readout_entropy_eq p hp _ _
        (fun v => (tupleRestrict Finset.inter_subset_right v,v)) Prod.snd <;> rfl
    rw [full,marg,xy,xz,hl,hr] at hssa
    exact hssa

/-- Arbitrary nonnegative fractional coordinate covers use literal marginals of one law. -/
theorem weighted_coordinate_entropy {X A R : Type*} [Fintype X] [Fintype A] [Fintype R]
    [DecidableEq A]
    {V : A → Type*} [∀ a, Fintype (V a)]
    (p : X → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1)
    (u : ∀ a, X → V a) (S : R → Finset A) (w : R → ℝ)
    (hw : ∀ r, 0 ≤ w r)
    (hcover : ∀ a, 1 ≤ ∑ r, if a ∈ S r then w r else 0) :
    coordinateEntropy p u Finset.univ ≤ ∑ r, w r * coordinateEntropy p u (S r) := by
  classical
  obtain ⟨hz,hm,hs⟩ := coordinate_entropy_structure p hp u
  exact fractional_submodular_cover _ hz hm hs Finset.univ S
    (fun r => Finset.subset_univ _) w hw (fun a _ => hcover a)


/-- The entropy cover bounds actual restriction images, on the uniform law of the relation. -/
theorem range_card_le_of_kernel {C A B : Type*}
    [Finite C] [Finite A] [Finite B] (f : C → A) (g : C → B)
    (hk : ∀ c c', f c = f c' → g c = g c') :
    Nat.card (Set.range g) ≤ Nat.card (Set.range f) := by
  classical
  let chooseC : Set.range f → C := fun t => Classical.choose t.property
  have hs : ∀ t, f (chooseC t) = t.val := fun t => Classical.choose_spec t.property
  let toG : Set.range f → Set.range g := fun t => ⟨g (chooseC t),Set.mem_range_self _⟩
  have hsur : Function.Surjective toG := by
    intro r
    obtain ⟨c,hc⟩ := r.property
    refine ⟨⟨f c,Set.mem_range_self _⟩,?_⟩
    apply Subtype.ext
    exact (hk _ c (hs _)).trans hc
  letI : Fintype (Set.range f) := Fintype.ofFinite _
  letI : Fintype (Set.range g) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_surjective toG hsur
open scoped Classical

section CompletionSorting

abbrev Endpoint (I : Type) := I × Bool

structure Skeleton (I : Type) [Fintype I] where
  position : Endpoint I ≃ Fin (2 * Fintype.card I)
  oriented : ∀ i, (position (i,false)).val < (position (i,true)).val

namespace Skeleton
variable {I : Type} [Fintype I]

def first (s : Skeleton I) (i : I) : ℕ := (s.position (i,false)).val
def second (s : Skeleton I) (i : I) : ℕ := (s.position (i,true)).val

private theorem first_injective (s : Skeleton I) : Function.Injective s.first := by
  intro i j h
  exact congrArg Prod.fst (s.position.injective (Fin.ext h))
private theorem second_injective (s : Skeleton I) : Function.Injective s.second := by
  intro i j h
  exact congrArg Prod.fst (s.position.injective (Fin.ext h))

/-- The number of strictly earlier completions is the actual completion rank. -/
noncomputable def rank (s : Skeleton I) (i : I) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => s.second j < s.second i)).card

private theorem rank_strict (s : Skeleton I) {i j : I}
    (h : s.second i < s.second j) : s.rank i < s.rank j := by
  classical
  let a := Finset.univ.filter (fun k => s.second k < s.second i)
  let b := Finset.univ.filter (fun k => s.second k < s.second j)
  have hn : i ∉ a := by simp [a]
  have hs : insert i a ⊆ b := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simpa [b] using h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_trans (Finset.mem_filter.mp hk).2 h⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hn] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hc

private theorem rank_lt_iff (s : Skeleton I) (i j : I) :
    s.rank i < s.rank j ↔ s.second i < s.second j := by
  constructor
  · intro h
    rcases lt_trichotomy (s.second i) (s.second j) with hij | he | hji
    · exact hij
    · have hi := s.second_injective he
      subst j
      exact (lt_irrefl _ h).elim
    · exact (lt_asymm h (s.rank_strict hji)).elim
  · exact s.rank_strict

private theorem rank_le_iff (s : Skeleton I) (i j : I) :
    s.rank i ≤ s.rank j ↔ s.second i ≤ s.second j := by
  simp only [not_lt.symm,s.rank_lt_iff]

private theorem rank_injective (s : Skeleton I) : Function.Injective s.rank := by
  intro i j h
  apply s.second_injective
  exact le_antisymm ((s.rank_le_iff i j).mp h.le)
    ((s.rank_le_iff j i).mp h.ge)

private theorem rank_lt_card (s : Skeleton I) (i : I) : s.rank i < Fintype.card I := by
  classical
  let a := Finset.univ.filter (fun j => s.second j < s.second i)
  have hn : i ∉ a := by simp [a]
  have hc := Finset.card_le_card (show insert i a ⊆ Finset.univ from fun _ _ => Finset.mem_univ _)
  rw [Finset.card_insert_of_notMem hn,Finset.card_univ] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hc

/-- Actual finite sorting, constructed without a supplied sorted permutation. -/
noncomputable def completionRank (s : Skeleton I) : I ≃ Fin (Fintype.card I) := by
  classical
  let f : I → Fin (Fintype.card I) := fun i => ⟨s.rank i,s.rank_lt_card i⟩
  have hinj : Function.Injective f := fun i j h => s.rank_injective (congrArg Fin.val h)
  let e := Fintype.equivFin I
  have hsur : Function.Surjective f := by
    have hi : Function.Injective (fun i => e.symm (f i)) := e.symm.injective.comp hinj
    have hs := Finite.surjective_of_injective hi
    intro k
    obtain ⟨i,hi⟩ := hs (e.symm k)
    exact ⟨i,e.symm.injective hi⟩
  exact Equiv.ofBijective f ⟨hinj,hsur⟩

/-- The normalized permutation reads both labels of each actual sorted pair. -/
noncomputable def completion (s : Skeleton I) : Endpoint I ≃ Fin (2 * Fintype.card I) := by
  classical
  let f : Endpoint I → Fin (2 * Fintype.card I) := fun v =>
    ⟨2*s.rank v.1 + (if v.2 then 1 else 0),by
      have h := s.rank_lt_card v.1
      cases v.2 <;> simp <;> omega⟩
  have hinj : Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    have hv := congrArg Fin.val h
    change 2*s.rank i+(if b then 1 else 0)=2*s.rank j+(if c then 1 else 0) at hv
    have hr : s.rank i = s.rank j := by cases b <;> cases c <;> simp_all <;> omega
    have hij := s.rank_injective hr
    subst j
    have hbc : b=c := by cases b <;> cases c <;> simp_all <;> omega
    subst c
    rfl
  have hsur : Function.Surjective f := by
    intro k
    let r : Fin (Fintype.card I) := ⟨k.val/2,by have hk:=k.isLt; omega⟩
    let i := s.completionRank.symm r
    have hi : s.rank i=k.val/2 := congrArg Fin.val (s.completionRank.apply_symm_apply r)
    refine ⟨(i,decide (k.val%2=1)),Fin.ext ?_⟩
    change 2*s.rank i+(if decide (k.val%2=1) then 1 else 0)=k.val
    have hm := Nat.mod_lt k.val (by omega : 0 < 2)
    by_cases h : k.val%2=1 <;> simp [h,hi] <;> omega
  exact Equiv.ofBijective f ⟨hinj,hsur⟩

end Skeleton

inductive Cut (I : Type)
  | initial
  | pair (i : I) (closed : Bool)

variable {I : Type} [Fintype I]

def firstRead (s : Skeleton I) : Cut I → I → Prop
  | .initial, _ => False
  | .pair k _, i => s.second i ≤ s.second k

def secondRead (s : Skeleton I) : Cut I → I → Prop
  | .initial, _ => False
  | .pair k closed, i => s.second i < s.second k ∨ (closed = true ∧ i=k)

noncomputable def cutSize (s : Skeleton I) : Cut I → ℕ
  | .initial => 0
  | .pair k closed => 2*s.rank k+(if closed then 2 else 1)

theorem second_implies_first (s : Skeleton I) (c : Cut I) :
    ∀ i, secondRead s c i → firstRead s c i := by
  cases c with
  | initial => exact fun _ h => h.elim
  | pair k closed =>
    intro i hi
    rcases hi with hi | ⟨_,rfl⟩
    · exact hi.le
    · exact le_rfl

/-- Exact first/second prefix predicates for the constructed labelled permutation. -/
theorem completion_prefix (s : Skeleton I) (c : Cut I) :
    cutSize s c ≤ 2*Fintype.card I ∧
    (∀ i, (s.completion (i,false)).val < cutSize s c ↔ firstRead s c i) ∧
    (∀ i, (s.completion (i,true)).val < cutSize s c ↔ secondRead s c i) := by
  cases c with
  | initial => simp [cutSize,firstRead,secondRead]
  | pair k closed =>
    have hk := s.rank_lt_card k
    have hs : cutSize s (.pair k closed) ≤ 2*Fintype.card I := by
      cases closed <;> simp [cutSize] <;> omega
    refine ⟨hs,?_,?_⟩
    · intro i
      change 2*s.rank i < 2*s.rank k+(if closed then 2 else 1) ↔ s.second i ≤ s.second k
      rw [←s.rank_le_iff]
      cases closed <;> simp <;> omega
    · intro i
      have he : i=k ↔ s.rank i=s.rank k := ⟨congrArg s.rank,fun h => s.rank_injective h⟩
      change 2*s.rank i+1 < 2*s.rank k+(if closed then 2 else 1) ↔
        s.second i < s.second k ∨ (closed=true ∧ i=k)
      rw [←s.rank_lt_iff,he]
      cases closed <;> simp <;> omega

/-- Every raw normalized layer is present, including zero and the terminal layer. -/
theorem completion_all_layers (s : Skeleton I) (t : ℕ) (ht : t ≤ 2*Fintype.card I) :
    ∃ c : Cut I, cutSize s c=t := by
  by_cases hzero : t=0
  · exact ⟨.initial,hzero.symm⟩
  let r : Fin (Fintype.card I) := ⟨(t-1)/2,by omega⟩
  let k := s.completionRank.symm r
  have hk : s.rank k=(t-1)/2 := congrArg Fin.val (s.completionRank.apply_symm_apply r)
  refine ⟨.pair k (decide (t%2=0)),?_⟩
  have hm := Nat.mod_lt t (by omega : 0 < 2)
  by_cases h : t%2=0 <;> simp [cutSize,h,hk] <;> omega

/-- Both directions of equality of cut families, on the original endpoint labels. -/
theorem completion_cut_family (s : Skeleton I) (l r : I → Prop) :
    (∃ t ≤ 2*Fintype.card I,
      (∀ i, l i ↔ (s.completion (i,false)).val < t) ∧
      (∀ i, r i ↔ (s.completion (i,true)).val < t)) ↔
    ∃ c : Cut I, (∀ i, l i↔firstRead s c i) ∧ (∀ i, r i↔secondRead s c i) := by
  constructor
  · rintro ⟨t,ht,hl,hr⟩
    obtain ⟨c,hc⟩ := completion_all_layers s t ht
    obtain ⟨_,hc1,hc2⟩ := completion_prefix s c
    refine ⟨c,?_,?_⟩
    · intro i; rw [hc] at hc1; exact (hl i).trans (hc1 i)
    · intro i; rw [hc] at hc2; exact (hr i).trans (hc2 i)
  · rintro ⟨c,hl,hr⟩
    obtain ⟨ht,hc1,hc2⟩ := completion_prefix s c
    exact ⟨cutSize s c,ht,fun i => (hl i).trans (hc1 i).symm,
      fun i => (hr i).trans (hc2 i).symm⟩

/-- Matched odd/full cuts. P ends just before/after the current second endpoint. -/
noncomputable def matchedSize (s : Skeleton I) : Cut I → ℕ
  | .initial => 0
  | .pair k closed => s.second k+(if closed then 1 else 0)

theorem matched_cut_geometry (s : Skeleton I) (c : Cut I) :
    matchedSize s c ≤ 2*Fintype.card I ∧
    (∀ i, firstRead s c i → s.first i < matchedSize s c) ∧
    (∀ i, secondRead s c i ↔ s.second i < matchedSize s c) := by
  cases c with
  | initial => simp [matchedSize,firstRead,secondRead]
  | pair k closed =>
    have hk := (s.position (k,true)).isLt
    have hle : matchedSize s (.pair k closed) ≤ 2*Fintype.card I := by
      cases closed <;> simp [matchedSize,Skeleton.second] <;> omega
    refine ⟨hle,?_,?_⟩
    · intro i hi
      have ho := s.oriented i
      change s.first i < s.second i at ho
      change s.second i ≤ s.second k at hi
      cases closed <;> simp [matchedSize] <;> omega
    · intro i
      have he : i=k ↔ s.second i=s.second k := ⟨congrArg s.second,fun h => s.second_injective h⟩
      change (s.second i < s.second k ∨ (closed=true ∧ i=k)) ↔
        s.second i < s.second k+(if closed then 1 else 0)
      rw [he]
      cases closed <;> simp <;> omega

/-- The original strict containment neighborhood, retaining designated membership. -/
def neighborhood (s : Skeleton I) (designated : I → Prop) (k i : I) : Prop :=
  designated i ∧ s.first i < s.first k ∧ s.first k < s.second k ∧ s.second k < s.second i

/-- The latest touched ordinary first endpoint is obtained from the actual finite set. -/
theorem latest_touched_ordinary (s : Skeleton I) (designated : I → Prop) (c : Cut I)
    (htouched : ∃ i, ¬designated i ∧ firstRead s c i) :
    ∃ k, ¬designated k ∧ firstRead s c k ∧
      (∀ i, ¬designated i → firstRead s c i → s.first i ≤ s.first k) ∧
      (∀ i, s.second i < s.first k+1 → secondRead s c i) ∧
      (∀ i, extra designated (firstRead s c) (fun j => s.first j < s.first k+1) i → neighborhood s designated k i) := by
  classical
  let touched := Finset.univ.filter (fun i => ¬designated i ∧ firstRead s c i)
  have hne : touched.Nonempty := by
    obtain ⟨i,hi⟩ := htouched
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image touched s.first hne
  have hkt := (Finset.mem_filter.mp hk).2
  refine ⟨k,hkt.1,hkt.2,?_,?_,?_⟩
  · intro i hd hi
    exact hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,hi⟩)
  · intro i hi
    have hok := s.oriented k
    change s.first k < s.second k at hok
    cases c with
    | initial => exact hkt.2.elim
    | pair current closed =>
      have hcur : s.second k ≤ s.second current := hkt.2
      exact Or.inl (by omega)
  · intro i hi
    have hdf : designated i := hi.1
    have hun : ¬firstRead s c i := hi.2.1
    have hfi : s.first i < s.first k+1 := hi.2.2
    have hne : i≠k := fun h => hkt.1 (h ▸ hdf)
    have hfirst : s.first i < s.first k := by
      have hn : s.first i≠s.first k := fun h => hne (s.first_injective h)
      omega
    refine ⟨hdf,hfirst,s.oriented k,?_⟩
    cases c with
    | initial => exact hkt.2.elim
    | pair current closed =>
      change ¬s.second i ≤ s.second current at hun
      have hcur : s.second k ≤ s.second current := hkt.2
      omega

/-- No normalized layer can read a second endpoint without its first. -/
theorem raw_second_implies_first (s : Skeleton I) (t : ℕ) :
    ∀ i, s.second i < t → s.first i < t :=
  fun i hi => lt_trans (s.oriented i) hi

/-- Alphabet on each separate original endpoint label. -/
def Alphabet (X Y : I → Type) : Endpoint I → Type
  | (i,false) => X i
  | (i,true) => Y i

instance alphabetFintype (X Y : I → Type) [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)]
    (v : Endpoint I) : Fintype (Alphabet X Y v) := by
  rcases v with ⟨i,e⟩
  cases e <;> dsimp [Alphabet] <;> infer_instance

abbrev Assignments (X Y : I → Type) (C : Endpoint I → Prop) :=
  ∀ v : {v // C v}, Alphabet X Y v.val

/-- Pure coordinate splitting; neither values nor the actual task are changed. -/
def splitValues (X Y : I → Type) (C : Endpoint I → Prop) :
    Assignments X Y C ≃ Values X Y (fun i => C (i,false)) (fun i => C (i,true)) where
  toFun f := (fun i => f ⟨(i.val,false),i.property⟩,fun i => f ⟨(i.val,true),i.property⟩)
  invFun b := fun ⟨(i,e),h⟩ => match e with
    | false => b.1 ⟨i,h⟩
    | true => b.2 ⟨i,h⟩
  left_inv f := by funext v; rcases v with ⟨⟨i,e⟩,h⟩; cases e <;> rfl
  right_inv b := by cases b; rfl

noncomputable def labelledTask {O : Type} {X Y Z : I → Type}
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i,Z i) → O)
    (a : ∀ v : Endpoint I, Alphabet X Y v) : O :=
  G (fun i => φ i (a (i,false)) (a (i,true)))

noncomputable def labelledResponse {O : Type} {X Y Z : I → Type}
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i,Z i) → O) (C : Endpoint I → Prop)
    (b : Assignments X Y C) (q : Assignments X Y (fun v => ¬C v)) : O := by
  classical
  exact labelledTask φ G (fun v => if h : C v then b ⟨v,h⟩ else q ⟨v,h⟩)

private theorem labelled_response_split {O : Type} {X Y Z : I → Type}
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i,Z i) → O) (C : Endpoint I → Prop)
    (b : Assignments X Y C) (q : Assignments X Y (fun v => ¬C v)) :
    labelledResponse φ G C b q = response φ G (fun i => C (i,false)) (fun i => C (i,true))
      (splitValues X Y C b) (splitValues X Y (fun v => ¬C v) q) := by
  classical
  rfl

/-- Exact response-cardinality transport on the same labelled suffix domain. -/
theorem labelled_response_card {O : Type} [Fintype O] {X Y Z : I → Type}
    [∀ i,Fintype (X i)] [∀ i,Fintype (Y i)]
    (φ : ∀ i, X i → Y i → Z i) (G : (∀ i,Z i) → O) (C : Endpoint I → Prop) :
    Nat.card (Set.range (labelledResponse φ G C)) =
      Nat.card (Set.range (response φ G (fun i => C (i,false)) (fun i => C (i,true)))) := by
  classical
  let f := labelledResponse φ G C
  let g := fun b : Assignments X Y C =>
    response φ G (fun i => C (i,false)) (fun i => C (i,true)) (splitValues X Y C b)
  have hk : ∀ b b', f b=f b' ↔ g b=g b' := by
    intro b b'
    constructor
    · intro h; funext q
      obtain ⟨r,rfl⟩ := (splitValues X Y (fun v => ¬C v)).surjective q
      simpa only [f,labelled_response_split] using congrFun h r
    · intro h; funext q
      simpa only [f,g,labelled_response_split] using
        congrFun h (splitValues X Y (fun v => ¬C v) q)
  have hr : Set.range g =
      Set.range (response φ G (fun i => C (i,false)) (fun i => C (i,true))) := by
    ext r
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨splitValues X Y C b,rfl⟩
    · rintro ⟨b,rfl⟩
      exact ⟨(splitValues X Y C).symm b,by simp [g]⟩
  have hle := range_card_le_of_kernel g f (fun b b' h => (hk b b').mpr h)
  have hge := range_card_le_of_kernel f g (fun b b' h => (hk b b').mp h)
  rw [hr] at hle hge
  exact le_antisymm hle hge

/- Labelled response cardinality feeds the original all-layer comparison in CutBounds. -/
end CompletionSorting

end D5.S3.Observer.Separation.FixedSkeletonWeightedInclusion.LabelledResponses
